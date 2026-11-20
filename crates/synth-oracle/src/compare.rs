//! Outcomes of the two engines and the matrix that turns a pair of them into a
//! verdict.
//!
//! Both outcome types live here, with no engine dependency, so the matrix is
//! unit-tested in the default build. The engines (`reference`, `emulate`)
//! only produce these values.

use crate::value::{ValType, WasmValue};

/// The wasm-level trap kind, derived from kiln's trap MESSAGE.
///
/// kiln reports almost every trap with one category and one code
/// (`Runtime`, 8601), and the same constructor also carries internal engine
/// failures ("table.set: expected value on stack"). So the code alone does not
/// identify a trap. Only a message recognised here as a WebAssembly spec trap
/// counts; anything else is [`TrapClass::Unclassified`], which the matrix never
/// accepts as agreement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TrapClass {
    Unreachable,
    IntegerDivideByZero,
    IntegerOverflow,
    InvalidConversionToInteger,
    MemoryOutOfBounds,
    TableOutOfBounds,
    IndirectCallTypeMismatch,
    UninitializedElement,
    CallStackExhausted,
    /// A host import returned an error.
    HostTrap,
    /// A trap-shaped kiln error whose message is not a recognised spec trap.
    Unclassified,
}

impl TrapClass {
    /// Classify a kiln trap message. Exact strings are taken from kiln v0.7.3
    /// `kiln-runtime/src/stackless/engine.rs`.
    pub fn from_kiln_message(msg: &str) -> Self {
        match msg {
            "unreachable" => TrapClass::Unreachable,
            "integer divide by zero" => TrapClass::IntegerDivideByZero,
            "integer overflow" => TrapClass::IntegerOverflow,
            "invalid conversion to integer" => TrapClass::InvalidConversionToInteger,
            "out of bounds memory access"
            | "Memory read out of bounds"
            | "Memory write out of bounds" => TrapClass::MemoryOutOfBounds,
            "out of bounds table access" => TrapClass::TableOutOfBounds,
            "indirect call type mismatch" => TrapClass::IndirectCallTypeMismatch,
            "uninitialized element" | "undefined element" => TrapClass::UninitializedElement,
            "call stack exhausted" => TrapClass::CallStackExhausted,
            _ => TrapClass::Unclassified,
        }
    }
}

/// What the reference engine (kiln) did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefOutcome {
    /// Returned normally.
    Values(Vec<WasmValue>),
    /// Trapped. `code` and `category` are kiln's; `class` is derived from the
    /// message.
    Trap {
        code: u16,
        category: String,
        class: TrapClass,
        message: String,
    },
    /// The fuel budget ran out. NEVER a trap: kiln reports exhaustion through
    /// the same trap constructor, and the harness separates it by message.
    Budget,
    /// kiln failed in a way that is neither a value, a trap nor the budget.
    EngineFault(String),
}

/// What the emulated machine code did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmuOutcome {
    /// Returned to the caller with the ABI intact; the values are read from
    /// the result registers.
    Values(Vec<WasmValue>),
    /// Stopped on a trap instruction: UDF on ARM, ebreak/unimp on RV32, brk
    /// on AArch64.
    Trap { pc: u64, insn: String },
    /// Any other fault (unmapped access, an undefined encoding that is not a
    /// trap idiom, a clobbered callee-saved register, an unbalanced stack).
    Illegal { pc: u64, reason: String },
    /// The instruction budget (or wall-clock backstop) ran out first.
    Budget,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    Agree,
    Disagree(String),
    /// Neither agreement nor a defect can be concluded. A gate that requires
    /// agreement treats this as a failure.
    Inconclusive(String),
}

impl Verdict {
    pub fn is_agree(&self) -> bool {
        matches!(self, Verdict::Agree)
    }
}

/// Value equality: integers bit-equal (both words of an i64); floats equal
/// when BOTH are NaN (any payload, kiln does not canonicalize) or bit-equal.
pub fn values_equal(a: WasmValue, b: WasmValue) -> bool {
    if a.ty() != b.ty() {
        return false;
    }
    if matches!(a.ty(), ValType::F32 | ValType::F64) && a.is_nan() && b.is_nan() {
        return true;
    }
    a == b
}

/// The (reference × emulator) matrix.
///
/// | reference \ emulator | Values         | Trap        | Illegal  | Budget       |
/// |----------------------|----------------|-------------|----------|--------------|
/// | Values               | equal? A : D   | D           | D        | I            |
/// | Trap (classified)    | D              | A           | D        | I            |
/// | Trap (Unclassified)  | I              | I           | D        | I            |
/// | Budget               | I              | I           | D        | I            |
/// | EngineFault          | I              | I           | D        | I            |
///
/// A = Agree, D = Disagree, I = Inconclusive. An ILLEGAL emulator outcome is a
/// disagreement whatever the reference did. A Budget is never a trap on
/// either side.
pub fn verdict(reference: &RefOutcome, emulator: &EmuOutcome) -> Verdict {
    if let EmuOutcome::Illegal { pc, reason } = emulator {
        return Verdict::Disagree(format!("ILLEGAL at pc=0x{pc:x}: {reason}"));
    }
    match (reference, emulator) {
        (RefOutcome::Budget, _) => Verdict::Inconclusive("reference ran out of fuel".into()),
        (_, EmuOutcome::Budget) => Verdict::Inconclusive("emulator ran out of budget".into()),
        (RefOutcome::EngineFault(m), _) => Verdict::Inconclusive(format!("kiln fault: {m}")),
        (
            RefOutcome::Trap {
                class: TrapClass::Unclassified,
                message,
                ..
            },
            _,
        ) => Verdict::Inconclusive(format!("unclassified kiln trap `{message}`")),
        (RefOutcome::Values(r), EmuOutcome::Values(e)) => {
            if r.len() == e.len() && r.iter().zip(e).all(|(a, b)| values_equal(*a, *b)) {
                Verdict::Agree
            } else {
                Verdict::Disagree(format!("values: reference {r:?}, emulator {e:?}"))
            }
        }
        (RefOutcome::Trap { .. }, EmuOutcome::Trap { .. }) => Verdict::Agree,
        (RefOutcome::Values(r), EmuOutcome::Trap { pc, insn }) => Verdict::Disagree(format!(
            "spurious trap: emulator stopped on {insn} at pc=0x{pc:x}, reference returned {r:?}"
        )),
        (RefOutcome::Trap { class, .. }, EmuOutcome::Values(e)) => Verdict::Disagree(format!(
            "missing trap: reference trapped ({class:?}), emulator returned {e:?}"
        )),
        (_, EmuOutcome::Illegal { .. }) => unreachable!("handled above"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn trap(class: TrapClass) -> RefOutcome {
        RefOutcome::Trap {
            code: 8601,
            category: "Runtime".into(),
            class,
            message: String::new(),
        }
    }

    fn emu_trap() -> EmuOutcome {
        EmuOutcome::Trap {
            pc: 0x10,
            insn: "udf".into(),
        }
    }

    #[test]
    fn i64_compares_both_words() {
        let r = RefOutcome::Values(vec![WasmValue::I64(0x1_0000_0002)]);
        let e = EmuOutcome::Values(vec![WasmValue::I64(0x0_0000_0002)]);
        assert!(!verdict(&r, &e).is_agree());
        let e = EmuOutcome::Values(vec![WasmValue::I64(0x1_0000_0002)]);
        assert!(verdict(&r, &e).is_agree());
    }

    #[test]
    fn nan_rule() {
        let qnan = f32::NAN.to_bits();
        let other_nan = 0x7fa0_0001;
        assert!(values_equal(
            WasmValue::F32(qnan),
            WasmValue::F32(other_nan)
        ));
        assert!(!values_equal(WasmValue::F32(qnan), WasmValue::F32(0)));
        // +0 and -0 are different bits: not equal.
        assert!(!values_equal(
            WasmValue::F64(0.0f64.to_bits()),
            WasmValue::F64((-0.0f64).to_bits())
        ));
        assert!(values_equal(
            WasmValue::F64(f64::NAN.to_bits()),
            WasmValue::F64(0xfff8_0000_0000_0001)
        ));
        // Same bits but different types are not equal.
        assert!(!values_equal(WasmValue::I32(1), WasmValue::F32(1)));
    }

    #[test]
    fn matrix() {
        let v = RefOutcome::Values(vec![WasmValue::I32(1)]);
        let ev = EmuOutcome::Values(vec![WasmValue::I32(1)]);
        let ill = EmuOutcome::Illegal {
            pc: 0,
            reason: "x".into(),
        };
        assert!(verdict(&v, &ev).is_agree());
        // A result-count mismatch never agrees (a void emulator result
        // against a one-value reference, and the reverse).
        assert!(matches!(
            verdict(&v, &EmuOutcome::Values(vec![])),
            Verdict::Disagree(_)
        ));
        assert!(matches!(
            verdict(&RefOutcome::Values(vec![]), &ev),
            Verdict::Disagree(_)
        ));
        assert!(matches!(verdict(&v, &emu_trap()), Verdict::Disagree(_)));
        assert!(matches!(verdict(&v, &ill), Verdict::Disagree(_)));
        assert!(matches!(
            verdict(&v, &EmuOutcome::Budget),
            Verdict::Inconclusive(_)
        ));
        let t = trap(TrapClass::IntegerDivideByZero);
        assert!(verdict(&t, &emu_trap()).is_agree());
        assert!(matches!(verdict(&t, &ev), Verdict::Disagree(_)));
        assert!(matches!(verdict(&t, &ill), Verdict::Disagree(_)));
        // Budget is never a trap, on either side.
        assert!(!verdict(&RefOutcome::Budget, &emu_trap()).is_agree());
        assert!(!verdict(&t, &EmuOutcome::Budget).is_agree());
        assert!(!verdict(&RefOutcome::Budget, &EmuOutcome::Budget).is_agree());
        // An unclassified kiln "trap" never agrees with a machine trap.
        assert!(!verdict(&trap(TrapClass::Unclassified), &emu_trap()).is_agree());
        assert!(matches!(
            verdict(&RefOutcome::Budget, &ill),
            Verdict::Disagree(_)
        ));
    }

    #[test]
    fn classifier() {
        assert_eq!(
            TrapClass::from_kiln_message("integer divide by zero"),
            TrapClass::IntegerDivideByZero
        );
        assert_eq!(
            TrapClass::from_kiln_message("table.set: expected value on stack"),
            TrapClass::Unclassified
        );
        assert_eq!(
            TrapClass::from_kiln_message(
                "fuel exhausted: execution exceeded the configured instruction budget"
            ),
            TrapClass::Unclassified
        );
    }
}
