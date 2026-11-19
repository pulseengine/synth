//! E2 and E3: every instruction the x86-64 backend EMITS, decoded by iced-x86.
//! RQ-91-X86SKEL (#1741), VCR-X86-001 cost 4.
//!
//! iced-x86 carries its own instruction table (it does not descend from
//! LLVM's, unlike capstone), so this is a second, independent reading of the
//! bytes. It runs under `cargo test --workspace`, inside the required `Test`
//! check, with no external tool.
//!
//! For every probe module, the test compiles through the real entry point
//! ([`synth_backend_x86_64::compile_wasm`]), reads `.text` back OUT OF THE
//! EMITTED ELF (what ships, not an in-memory buffer), and decodes it
//! instruction by instruction. It requires:
//!
//! - E2: no invalid encoding and no leftover byte; each decoded length equals
//!   the length the encoder reported; the decoded instruction, printed by
//!   iced's GAS (AT&T) formatter, equals the instruction the selector asked
//!   for, printed by the backend's own printer;
//! - E3: iced's CPUID feature set for each decoded instruction lies inside the
//!   x86-64 baseline (x86-64-v1). The allowed set is a list of iced FEATURE
//!   names, never a list of opcodes: an `lzcnt` is caught because iced says it
//!   needs LZCNT, not because synth lists its bytes.
//!
//! Potency is shown in the same file: a REX.B bit dropped from the emitted
//! bytes, `lzcnt` and `popcnt`, and a truncated instruction are each refused.

use iced_x86::{CpuidFeature, Decoder, DecoderOptions, Formatter, GasFormatter, Instruction};
use object::{Object as _, ObjectSection as _};
use synth_backend_x86_64::compile_wasm;
use synth_backend_x86_64::encoder::encode;
use synth_backend_x86_64::inst::{Inst, Reg};

/// The probe set: every op the skeleton lowers, every parameter register,
/// every temporary, a void function, an early `return`, non-exported helpers
/// and a function exported under two names.
const PROBES: &[&str] = &[
    r#"(module (func (export "add") (param i32 i32) (result i32)
         local.get 0 local.get 1 i32.add))"#,
    r#"(module (func (export "id") (param i32) (result i32) local.get 0))"#,
    r#"(module (func (export "second") (param i32 i32) (result i32) local.get 1))"#,
    r#"(module (func (export "add3") (param i32 i32 i32) (result i32)
         local.get 0 local.get 1 i32.add local.get 2 i32.add))"#,
    r#"(module (func (export "ret_early") (param i32 i32) (result i32)
         local.get 0 local.get 1 i32.add return))"#,
    r#"(module (func (export "void")))"#,
    r#"(module (func (export "sum6") (param i32 i32 i32 i32 i32 i32) (result i32)
         local.get 0 local.get 1 i32.add
         local.get 2 local.get 3 i32.add
         local.get 4 local.get 5 i32.add
         i32.add i32.add))"#,
    r#"(module (func (export "rsum") (param i32 i32 i32 i32 i32 i32) (result i32)
         local.get 5 local.get 4 local.get 3 i32.add i32.add
         local.get 2 i32.add local.get 1 i32.add local.get 0 i32.add))"#,
    r#"(module
         (func (param i32) (result i32) local.get 0 local.get 0 i32.add)
         (func (export "a") (export "b") (param i32 i32) (result i32)
           local.get 1 local.get 0 i32.add)
         (func (param i32 i32 i32 i32 i32 i32) (result i32) local.get 5))"#,
];

/// x86-64-v1, the baseline: the legacy levels, long mode, and CMOV, CX8, FPU,
/// FXSR, MMX, SCE (SYSCALL), SSE, SSE2 — as iced names them.
const BASELINE: &[CpuidFeature] = &[
    CpuidFeature::INTEL8086,
    CpuidFeature::INTEL186,
    CpuidFeature::INTEL286,
    CpuidFeature::INTEL386,
    CpuidFeature::INTEL486,
    CpuidFeature::X64,
    CpuidFeature::CMOV,
    CpuidFeature::CX8,
    CpuidFeature::FPU,
    CpuidFeature::FXSR,
    CpuidFeature::MMX,
    CpuidFeature::SYSCALL,
    CpuidFeature::SSE,
    CpuidFeature::SSE2,
];

fn formatter() -> GasFormatter {
    let mut f = GasFormatter::new();
    f.options_mut().set_gas_show_mnemonic_size_suffix(true);
    f.options_mut().set_space_after_operand_separator(true);
    f
}

/// Decode `bytes` fully. Err names the first problem.
fn decode_all(bytes: &[u8]) -> Result<Vec<(Instruction, String)>, String> {
    let mut dec = Decoder::with_ip(64, bytes, 0, DecoderOptions::NONE);
    let mut fmt = formatter();
    let mut out = Vec::new();
    while dec.can_decode() {
        let pos = dec.position();
        let ins = dec.decode();
        if ins.is_invalid() {
            return Err(format!(
                "invalid encoding at .text+{pos}: {:02x?}",
                &bytes[pos..]
            ));
        }
        let mut text = String::new();
        fmt.format(&ins, &mut text);
        out.push((ins, text));
    }
    Ok(out)
}

/// E3: every feature iced reports for `ins` is in the baseline.
fn above_baseline(ins: &Instruction) -> Vec<CpuidFeature> {
    ins.cpuid_features()
        .iter()
        .copied()
        .filter(|f| !BASELINE.contains(f))
        .collect()
}

/// `.text` of the emitted object, read back with the `object` crate.
fn text_of(elf: &[u8]) -> Vec<u8> {
    let f = object::File::parse(elf).expect("the emitted object parses");
    assert_eq!(f.architecture(), object::Architecture::X86_64);
    f.section_by_name(".text")
        .expect(".text")
        .data()
        .expect("text data")
        .to_vec()
}

/// Check one emitted `.text` against what the selector asked for.
fn check(text: &[u8], insts: &[Inst], lens: &[usize]) -> Result<usize, String> {
    let decoded = decode_all(text)?;
    if decoded.len() != insts.len() {
        return Err(format!(
            "{} instructions decoded, {} requested",
            decoded.len(),
            insts.len()
        ));
    }
    for (k, ((ins, text), (want, len))) in decoded.iter().zip(insts.iter().zip(lens)).enumerate() {
        if ins.len() != *len {
            return Err(format!(
                "#{k} `{want}`: decoded length {} != encoder length {len}",
                ins.len()
            ));
        }
        if *text != want.att() {
            return Err(format!("#{k}: decoded `{text}` != requested `{want}`"));
        }
        let above = above_baseline(ins);
        if !above.is_empty() {
            return Err(format!("#{k} `{text}` needs {above:?}, above the baseline"));
        }
    }
    Ok(decoded.len())
}

#[test]
fn every_emitted_instruction_decodes_to_what_was_requested_e2_e3() {
    let mut checked = 0;
    for src in PROBES {
        let wasm = wat::parse_str(src).unwrap();
        let obj = compile_wasm(&wasm).unwrap_or_else(|e| panic!("{src}: {e}"));
        let text = text_of(&obj.elf);
        let insts: Vec<Inst> = obj.functions.iter().flat_map(|f| f.insts.clone()).collect();
        let lens: Vec<usize> = obj.functions.iter().flat_map(|f| f.lens.clone()).collect();
        checked += check(&text, &insts, &lens).unwrap_or_else(|e| panic!("{src}: {e}"));
    }
    // Non-vacuity: the probe set exercises a real number of instructions.
    assert!(checked >= 30, "only {checked} instructions decoded");
}

/// Every FORM the encoder can produce (the E1 population), decoded by iced.
#[test]
fn every_encoder_form_decodes_to_its_text_e2() {
    let mut forms = vec![Inst::Ret];
    for &d in &Reg::ALL {
        for &s in &Reg::ALL {
            forms.push(Inst::MovRR32 { dst: d, src: s });
            forms.push(Inst::AddRR32 { dst: d, src: s });
        }
    }
    assert_eq!(forms.len(), 513);
    for f in &forms {
        let b = encode(f);
        check(&b, &[*f], &[b.len()]).unwrap_or_else(|e| panic!("{f}: {e}"));
    }
}

/// Potency: a dropped REX.B makes `addl %esi, %r9d` decode as `addl %esi,
/// %ecx`, and the check refuses it.
#[test]
fn a_dropped_rex_b_is_refused() {
    let want = Inst::AddRR32 {
        dst: Reg::R9,
        src: Reg::Rsi,
    };
    let mut b = encode(&want);
    assert!(check(&b, &[want], &[b.len()]).is_ok());
    b[0] &= !1; // REX.B
    let e = check(&b, &[want], &[b.len()]).unwrap_err();
    assert!(e.contains("addl %esi, %ecx"), "{e}");
}

/// Potency: instructions above the baseline are refused by FEATURE, from
/// iced's table. `F3 0F BD` is `lzcnt` (on a CPU without LZCNT the prefix is
/// ignored and it runs as `bsr`, a different answer and no fault).
#[test]
fn above_baseline_instructions_are_refused_e3() {
    for (bytes, feature) in [
        (&[0xF3u8, 0x0F, 0xBD, 0xC7][..], CpuidFeature::LZCNT),
        (&[0xF3, 0x0F, 0xB8, 0xC7][..], CpuidFeature::POPCNT),
        (&[0xF3, 0x0F, 0xBC, 0xC7][..], CpuidFeature::BMI1), // tzcnt
    ] {
        let d = decode_all(bytes).unwrap();
        assert_eq!(d.len(), 1);
        assert!(
            above_baseline(&d[0].0).contains(&feature),
            "{bytes:02x?}: {:?}",
            d[0].0.cpuid_features()
        );
    }
    // And the plain `bsr` the same bytes decode to WITHOUT the prefix is
    // baseline: the gate is the feature, not the opcode family.
    let d = decode_all(&[0x0F, 0xBD, 0xC7]).unwrap();
    assert!(above_baseline(&d[0].0).is_empty());
}

/// Potency: a truncated instruction (leftover bytes) is refused.
#[test]
fn a_truncated_instruction_is_refused() {
    let b = encode(&Inst::AddRR32 {
        dst: Reg::R12,
        src: Reg::R13,
    });
    assert!(decode_all(&b[..b.len() - 1]).is_err());
}
