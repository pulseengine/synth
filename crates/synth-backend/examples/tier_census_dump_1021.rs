//! RQ-59-TIERCENSUS (#1021) — encoder-expansion dump for the proof-tier census.
//!
//! #1021 shipped a memory-safety miscompile THROUGH a Rocq-proved rule:
//! `rule_i32_popcnt` is genuinely proved, but it emits the `ArmOp::Popcnt`
//! pseudo-op, and the defect lived in that pseudo-op's ENCODER EXPANSION
//! (R11 — the WASM linear-memory base — taken as scratch). The proof is
//! stated at pseudo-op tier, ABOVE the expansion. An atomic model of a
//! multi-instruction expansion is a silent claim that the expansion is
//! scratch-free; this dump measures how many such claims the 80-rule
//! VCR-SEL-001 surface currently makes.
//!
//! WHAT THIS DOES. For every `ArmOp` variant the shipped rule table emits
//! (derived at runtime from `sel_dsl/generated.rs` — the committed artifact
//! the `generated_lowering_is_up_to_date` test pins to `sel_dsl::RULES`),
//! encode one representative instance through the REAL encoders
//! (`ArmEncoder::new_thumb2()` and `ArmEncoder::new_arm32()`) and print one
//! JSON line per instance: variant, declared outputs/inputs, and the literal
//! bytes each backend emits. `scripts/tier_census_1021.py` consumes
//! this, decodes the bytes (capstone), executes them (unicorn), and derives
//! the pseudo-op census + the scratch-register effect census from the
//! observed machine state — a grep is a hypothesis, the executed bytes are
//! the measurement.
//!
//! COMPLETENESS IS DERIVED, NOT ASSERTED: the instance table below is checked
//! at runtime against the set of `ArmOp::` constructors appearing in the
//! shipped `generated.rs`. A rule-table change that emits a new variant makes
//! this dump FAIL LOUDLY until the instance table covers it. The residual
//! hand-written part is only the representative OPERAND choice (registers
//! rd=R0, rd_hi=R1, rn=R2, rn_hi=R3, rm=R4, rm_hi=R5 — non-aliased so every
//! write is attributable, all inside the selector's R0–R8 pool; immediates
//! typical of the rules) — no derivation can pick operands for you.
//!
//! This is MEASUREMENT ONLY (census lane): it changes no lowering and no
//! encoder byte.

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use synth_backend::arm_encoder::{ArmEncoder, expansion_scratch_contract};
use synth_synthesis::rules::Condition;
use synth_synthesis::{ArmOp, Operand2, Reg};

fn reg_name(r: Reg) -> &'static str {
    match r {
        Reg::R0 => "r0",
        Reg::R1 => "r1",
        Reg::R2 => "r2",
        Reg::R3 => "r3",
        Reg::R4 => "r4",
        Reg::R5 => "r5",
        Reg::R6 => "r6",
        Reg::R7 => "r7",
        Reg::R8 => "r8",
        Reg::R9 => "r9",
        Reg::R10 => "r10",
        Reg::R11 => "r11",
        Reg::R12 => "r12",
        Reg::SP => "sp",
        Reg::LR => "lr",
        Reg::PC => "pc",
    }
}

/// One representative instance: variant name (checked at runtime against the `ArmOp::` ident
/// in `generated.rs`), a shape tag, declared outputs, declared inputs, and the
/// op itself. The expansion's SCRATCH CONTRACT is not carried here: it is
/// DERIVED per instance from `synth_backend::arm_encoder::expansion_scratch_contract`
/// — the single declaration site next to the expansions (VCR-TIER-001; the
/// former per-instance `declared_temps` hand column was deleted with #1048's
/// fix, which removed the operand-register temps that column duplicated).
struct Instance {
    variant: &'static str,
    shape: &'static str,
    outputs: Vec<Reg>,
    inputs: Vec<Reg>,
    op: ArmOp,
}

fn all_conditions() -> [(Condition, &'static str); 10] {
    [
        (Condition::EQ, "eq"),
        (Condition::NE, "ne"),
        (Condition::LT, "lt"),
        (Condition::LE, "le"),
        (Condition::GT, "gt"),
        (Condition::GE, "ge"),
        (Condition::LO, "lo"),
        (Condition::LS, "ls"),
        (Condition::HI, "hi"),
        (Condition::HS, "hs"),
    ]
}

#[allow(clippy::too_many_lines)]
fn instances() -> Vec<Instance> {
    use Reg::{R0, R1, R2, R3, R4, R5};
    let mut v: Vec<Instance> = Vec::new();
    let mut push =
        |variant: &'static str, shape: &'static str, outputs: &[Reg], inputs: &[Reg], op: ArmOp| {
            v.push(Instance {
                variant,
                shape,
                outputs: outputs.to_vec(),
                inputs: inputs.to_vec(),
                op,
            });
        };

    // --- i32 data-processing (register + the rules' immediate forms) ---
    push(
        "Add",
        "reg",
        &[R0],
        &[R2, R4],
        ArmOp::Add {
            rd: R0,
            rn: R2,
            op2: Operand2::Reg(R4),
        },
    );
    push(
        "Add",
        "imm",
        &[R0],
        &[R2],
        ArmOp::Add {
            rd: R0,
            rn: R2,
            op2: Operand2::Imm(0x34),
        },
    );
    push(
        "Sub",
        "reg",
        &[R0],
        &[R2, R4],
        ArmOp::Sub {
            rd: R0,
            rn: R2,
            op2: Operand2::Reg(R4),
        },
    );
    push(
        "Sub",
        "imm",
        &[R0],
        &[R2],
        ArmOp::Sub {
            rd: R0,
            rn: R2,
            op2: Operand2::Imm(0x34),
        },
    );
    push(
        "Mul",
        "reg",
        &[R0],
        &[R2, R4],
        ArmOp::Mul {
            rd: R0,
            rn: R2,
            rm: R4,
        },
    );
    for (name, mk_reg, mk_imm) in [
        (
            "And",
            (|| ArmOp::And {
                rd: R0,
                rn: R2,
                op2: Operand2::Reg(R4),
            }) as fn() -> ArmOp,
            (|| ArmOp::And {
                rd: R0,
                rn: R2,
                op2: Operand2::Imm(0x34),
            }) as fn() -> ArmOp,
        ),
        (
            "Orr",
            || ArmOp::Orr {
                rd: R0,
                rn: R2,
                op2: Operand2::Reg(R4),
            },
            || ArmOp::Orr {
                rd: R0,
                rn: R2,
                op2: Operand2::Imm(0x34),
            },
        ),
        (
            "Eor",
            || ArmOp::Eor {
                rd: R0,
                rn: R2,
                op2: Operand2::Reg(R4),
            },
            || ArmOp::Eor {
                rd: R0,
                rn: R2,
                op2: Operand2::Imm(0x34),
            },
        ),
    ] {
        push(name, "reg", &[R0], &[R2, R4], mk_reg());
        push(name, "imm", &[R0], &[R2], mk_imm());
    }
    push(
        "Adds",
        "reg",
        &[R0],
        &[R2, R4],
        ArmOp::Adds {
            rd: R0,
            rn: R2,
            op2: Operand2::Reg(R4),
        },
    );
    push(
        "Adc",
        "reg",
        &[R1],
        &[R3, R5],
        ArmOp::Adc {
            rd: R1,
            rn: R3,
            op2: Operand2::Reg(R5),
        },
    );
    push(
        "Subs",
        "reg",
        &[R0],
        &[R2, R4],
        ArmOp::Subs {
            rd: R0,
            rn: R2,
            op2: Operand2::Reg(R4),
        },
    );
    push(
        "Sbc",
        "reg",
        &[R1],
        &[R3, R5],
        ArmOp::Sbc {
            rd: R1,
            rn: R3,
            op2: Operand2::Reg(R5),
        },
    );

    // --- shifts / rotates (register amount) ---
    for (name, op) in [
        (
            "LslReg",
            ArmOp::LslReg {
                rd: R0,
                rn: R2,
                rm: R4,
            },
        ),
        (
            "LsrReg",
            ArmOp::LsrReg {
                rd: R0,
                rn: R2,
                rm: R4,
            },
        ),
        (
            "AsrReg",
            ArmOp::AsrReg {
                rd: R0,
                rn: R2,
                rm: R4,
            },
        ),
        (
            "RorReg",
            ArmOp::RorReg {
                rd: R0,
                rn: R2,
                rm: R4,
            },
        ),
    ] {
        push(name, "reg", &[R0], &[R2, R4], op);
    }
    // rule_i32_rotl's `32 - amount` step (scratch rs = R6 in the rule, but the
    // RSB itself is a plain 2-operand op).
    push(
        "Rsb",
        "imm32",
        &[R0],
        &[R2],
        ArmOp::Rsb {
            rd: R0,
            rn: R2,
            imm: 32,
        },
    );

    // --- bit manipulation ---
    push("Clz", "reg", &[R0], &[R2], ArmOp::Clz { rd: R0, rm: R2 });
    push("Rbit", "reg", &[R0], &[R2], ArmOp::Rbit { rd: R0, rm: R2 });
    // The #1021 op. rd != rm so the mov-prefix (worst case) is included.
    push(
        "Popcnt",
        "reg",
        &[R0],
        &[R2],
        ArmOp::Popcnt { rd: R0, rm: R2 },
    );

    // --- extends ---
    push("Sxtb", "reg", &[R0], &[R2], ArmOp::Sxtb { rd: R0, rm: R2 });
    push("Sxth", "reg", &[R0], &[R2], ArmOp::Sxth { rd: R0, rm: R2 });

    // --- moves ---
    push(
        "Mov",
        "reg",
        &[R0],
        &[R2],
        ArmOp::Mov {
            rd: R0,
            op2: Operand2::Reg(R2),
        },
    );
    // rule_i64_extend_i32_u's zero-high-half shape.
    push("Movw", "imm0", &[R1], &[], ArmOp::Movw { rd: R1, imm16: 0 });

    // --- compares (flag-setting; no register output) ---
    push(
        "Cmp",
        "reg",
        &[],
        &[R2, R4],
        ArmOp::Cmp {
            rn: R2,
            op2: Operand2::Reg(R4),
        },
    );
    push(
        "Cmp",
        "imm0",
        &[],
        &[R2],
        ArmOp::Cmp {
            rn: R2,
            op2: Operand2::Imm(0),
        },
    );
    push(
        "Cmp",
        "imm",
        &[],
        &[R2],
        ArmOp::Cmp {
            rn: R2,
            op2: Operand2::Imm(0x34),
        },
    );

    // --- the boolean-materialization / conditional-move pseudo-ops ---
    for (cond, tag) in all_conditions() {
        push("SetCond", tag, &[R0], &[], ArmOp::SetCond { rd: R0, cond });
        push(
            "SelectMove",
            tag,
            &[R0],
            &[R4],
            ArmOp::SelectMove {
                rd: R0,
                rm: R4,
                cond,
            },
        );
    }

    // --- i64 pseudo-ops (register-pair family) ---
    for (cond, tag) in all_conditions() {
        push(
            "I64SetCond",
            tag,
            &[R0],
            &[R0, R1, R2, R3],
            ArmOp::I64SetCond {
                rd: R0,
                rn_lo: R0,
                rn_hi: R1,
                rm_lo: R2,
                rm_hi: R3,
                cond,
            },
        );
    }
    push(
        "I64SetCondZ",
        "reg",
        &[R0],
        &[R2, R3],
        ArmOp::I64SetCondZ {
            rd: R0,
            rn_lo: R2,
            rn_hi: R3,
        },
    );
    push(
        "I64Mul",
        "pair",
        &[R0, R1],
        &[R2, R3, R4, R5],
        ArmOp::I64Mul {
            rd_lo: R0,
            rd_hi: R1,
            rn_lo: R2,
            rn_hi: R3,
            rm_lo: R4,
            rm_hi: R5,
        },
    );
    // The shift family is R12-only since #1048: the pre-fix expansions masked
    // the amount IN PLACE and wrote amt-32 into rm_hi — the operand's home
    // registers — which the census caught as an undeclared clobber. Their
    // scratch contract is now empty (derived, like every instance's, from
    // `expansion_scratch_contract`).
    for (name, op) in [
        (
            "I64Shl",
            ArmOp::I64Shl {
                rd_lo: R0,
                rd_hi: R1,
                rn_lo: R2,
                rn_hi: R3,
                rm_lo: R4,
                rm_hi: R5,
            },
        ),
        (
            "I64ShrU",
            ArmOp::I64ShrU {
                rd_lo: R0,
                rd_hi: R1,
                rn_lo: R2,
                rn_hi: R3,
                rm_lo: R4,
                rm_hi: R5,
            },
        ),
        (
            "I64ShrS",
            ArmOp::I64ShrS {
                rd_lo: R0,
                rd_hi: R1,
                rn_lo: R2,
                rn_hi: R3,
                rm_lo: R4,
                rm_hi: R5,
            },
        ),
    ] {
        push(name, "pair", &[R0, R1], &[R2, R3, R4, R5], op);
    }
    for (name, op) in [
        (
            "I64Rotl",
            ArmOp::I64Rotl {
                rdlo: R0,
                rdhi: R1,
                rnlo: R2,
                rnhi: R3,
                shift: R4,
            },
        ),
        (
            "I64Rotr",
            ArmOp::I64Rotr {
                rdlo: R0,
                rdhi: R1,
                rnlo: R2,
                rnhi: R3,
                shift: R4,
            },
        ),
    ] {
        push(name, "pair", &[R0, R1], &[R2, R3, R4], op);
    }
    // The bit-count expansions are rd-only since #1048: their former trailing
    // `MOV rnhi, #0` — a hi-clear aimed at the result that landed on the
    // OPERAND's home high register on the direct selector — was deleted (the
    // selector now zeroes the result hi itself), so no temp is declared.
    for (name, op) in [
        (
            "I64Clz",
            ArmOp::I64Clz {
                rd: R0,
                rnlo: R2,
                rnhi: R3,
            },
        ),
        (
            "I64Ctz",
            ArmOp::I64Ctz {
                rd: R0,
                rnlo: R2,
                rnhi: R3,
            },
        ),
        (
            "I64Popcnt",
            ArmOp::I64Popcnt {
                rd: R0,
                rnlo: R2,
                rnhi: R3,
            },
        ),
    ] {
        push(name, "count", &[R0], &[R2, R3], op);
    }
    push(
        "I64Const",
        "wide",
        &[R0, R1],
        &[],
        ArmOp::I64Const {
            rdlo: R0,
            rdhi: R1,
            value: 0x1122_3344_5566_7788,
        },
    );
    push(
        "I64Const",
        "zero",
        &[R0, R1],
        &[],
        ArmOp::I64Const {
            rdlo: R0,
            rdhi: R1,
            value: 0,
        },
    );
    push(
        "I64ExtendI32S",
        "pair",
        &[R0, R1],
        &[R2],
        ArmOp::I64ExtendI32S {
            rdlo: R0,
            rdhi: R1,
            rn: R2,
        },
    );
    for (name, op) in [
        (
            "I64Extend8S",
            ArmOp::I64Extend8S {
                rdlo: R0,
                rdhi: R1,
                rnlo: R2,
            },
        ),
        (
            "I64Extend16S",
            ArmOp::I64Extend16S {
                rdlo: R0,
                rdhi: R1,
                rnlo: R2,
            },
        ),
        (
            "I64Extend32S",
            ArmOp::I64Extend32S {
                rdlo: R0,
                rdhi: R1,
                rnlo: R2,
            },
        ),
    ] {
        push(name, "pair", &[R0, R1], &[R2], op);
    }
    push(
        "I32WrapI64",
        "reg",
        &[R0],
        &[R2],
        ArmOp::I32WrapI64 { rd: R0, rnlo: R2 },
    );

    v
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn encode_field(enc: &ArmEncoder, op: &ArmOp) -> (String, String) {
    match catch_unwind(AssertUnwindSafe(|| enc.encode(op))) {
        Ok(Ok(bytes)) => (format!("\"{}\"", hex(&bytes)), "null".to_string()),
        Ok(Err(e)) => (
            "null".to_string(),
            format!("\"{}\"", format!("{e}").replace('"', "'")),
        ),
        Err(_) => ("null".to_string(), "\"panic\"".to_string()),
    }
}

fn json_reg_list(regs: &[Reg]) -> String {
    let names: Vec<String> = regs
        .iter()
        .map(|r| format!("\"{}\"", reg_name(*r)))
        .collect();
    format!("[{}]", names.join(","))
}

fn main() {
    // Completeness gate: every ArmOp variant the SHIPPED generated rule
    // lowerings construct must appear in the instance table (and the table
    // must not carry stale variants no rule emits any more).
    let generated_src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../synth-synthesis/src/sel_dsl/generated.rs"
    ))
    .expect("read sel_dsl/generated.rs (the shipped rule-lowering artifact)");
    let mut emitted: BTreeSet<String> = BTreeSet::new();
    let mut rest = generated_src.as_str();
    while let Some(pos) = rest.find("ArmOp::") {
        rest = &rest[pos + "ArmOp::".len()..];
        let ident: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if !ident.is_empty() {
            emitted.insert(ident);
        }
    }
    let table: BTreeSet<String> = instances().iter().map(|i| i.variant.to_string()).collect();
    let missing: Vec<&String> = emitted.difference(&table).collect();
    let stale: Vec<&String> = table.difference(&emitted).collect();
    assert!(
        missing.is_empty() && stale.is_empty(),
        "instance table out of sync with generated.rs — missing: {missing:?}, stale: {stale:?}"
    );

    let thumb = ArmEncoder::new_thumb2();
    let a32 = ArmEncoder::new_arm32();

    println!("[");
    let insts = instances();
    let n = insts.len();
    for (i, inst) in insts.iter().enumerate() {
        let (t_hex, t_err) = encode_field(&thumb, &inst.op);
        let (a_hex, a_err) = encode_field(&a32, &inst.op);
        let comma = if i + 1 == n { "" } else { "," };
        // The scratch contract is DERIVED from the shipped crate's single
        // declaration site, never hand-annotated per instance (VCR-TIER-001).
        println!(
            "{{\"variant\":\"{}\",\"shape\":\"{}\",\"outputs\":{},\"inputs\":{},\"scratch_contract\":{},\"thumb\":{},\"thumb_err\":{},\"a32\":{},\"a32_err\":{}}}{}",
            inst.variant,
            inst.shape,
            json_reg_list(&inst.outputs),
            json_reg_list(&inst.inputs),
            json_reg_list(expansion_scratch_contract(&inst.op)),
            t_hex,
            t_err,
            a_hex,
            a_err,
            comma
        );
    }
    println!("]");
}
