//! E2 and E3: every instruction the x86-64 backend EMITS, decoded by iced-x86.
//! RQ-91-X86SKEL, RQ-91-X86FRAME (#1741), VCR-X86-001 cost 4.
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
use synth_backend_x86_64::inst::{AluOp, Inst, Reg, Size};

mod forms;
use forms::{FORM_COUNT, all_forms};

/// The probe set: every op the skeleton lowers, every parameter register,
/// every temporary, a void function, an early `return`, non-exported helpers
/// and a function exported under two names.
const PROBES: &[&str] = &[
    // Lane X5: every control-flow shape, so every `jmp`/`jCC rel32` the
    // selector resolves decodes to the target it was resolved to.
    r#"(module
         (func (export "loop") (param i32) (result i32) (local i32 i32)
           local.get 0 i32.const 15 i32.and local.set 1
           block loop
             local.get 1 i32.eqz br_if 1
             local.get 2 local.get 1 i32.add local.set 2
             local.get 1 i32.const 1 i32.sub local.set 1
             br 0
           end end
           local.get 2)
         (func (export "ifs") (param i32 i64) (result i64)
           local.get 0 if (result i64) local.get 1 else i64.const 9 end
           local.get 0 i32.const 2 i32.and if nop else unreachable end)
         (func (export "table") (param i32) (result i32)
           block block block
             local.get 0 br_table 0 1 2
           end i32.const 1 return end i32.const 2 return end
           i32.const 3)
         (func (export "valued") (param i32) (result i32)
           i32.const 100
           block (result i32) block (result i32)
             i32.const 5 local.get 0 br_table 0 1 0
           end i32.const 1 i32.add end
           i32.sub)
         (func (export "out") (param i32) (result i32)
           i32.const 7 block (result i32) loop
             local.get 0 local.get 0 br_if 1 drop local.get 0 br 2
           end unreachable end i32.add))"#,
    // Lanes X3-X4: locals, the spill path, div/rem with their guards, and the
    // bit counts (which must decode as bsr/bsf, never lzcnt/tzcnt/popcnt).
    r#"(module
         (func (export "locals") (param i32 i64) (result i64) (local i32 i64)
           local.get 0 local.tee 2 i64.extend_i32_u local.set 3
           local.get 1 local.get 3 i64.add local.set 1
           local.get 1 local.get 2 i64.extend_i32_s i64.sub)
         (func (export "spill") (param i32) (result i32)
           local.get 0 i32.const 1 i32.const 2 i32.const 3 i32.const 4
           i32.const 5 i32.const 6 i32.const 7 i32.const 8
           i32.add i32.add i32.add i32.add i32.add i32.add i32.add i32.add)
         (func (export "big") (param i64) (result i64)
           (local i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64)
           local.get 0 local.set 17 local.get 17)
         (func (export "div32") (param i32 i32) (result i32)
           local.get 0 local.get 1 i32.div_s
           local.get 0 local.get 1 i32.div_u i32.add
           local.get 0 local.get 1 i32.rem_s i32.add
           local.get 0 local.get 1 i32.rem_u i32.add)
         (func (export "div64") (param i64 i64) (result i64)
           local.get 0 local.get 1 i64.div_s
           local.get 0 local.get 1 i64.div_u i64.add
           local.get 0 local.get 1 i64.rem_s i64.add
           local.get 0 local.get 1 i64.rem_u i64.add)
         (func (export "bits32") (param i32) (result i32)
           local.get 0 i32.clz local.get 0 i32.ctz i32.add
           local.get 0 i32.popcnt i32.add)
         (func (export "bits64") (param i64) (result i64)
           local.get 0 i64.clz local.get 0 i64.ctz i64.add
           local.get 0 i64.popcnt i64.add))"#,
    // Lane X2: every form the selector emits, through the real entry point.
    r#"(module
         (func (export "arith") (param i32 i32) (result i32)
           local.get 0 local.get 1 i32.sub
           local.get 0 local.get 1 i32.mul i32.and
           local.get 1 i32.or local.get 0 i32.xor)
         (func (export "arith64") (param i64 i64) (result i64)
           local.get 0 local.get 1 i64.sub
           local.get 0 local.get 1 i64.mul i64.and
           local.get 1 i64.or local.get 0 i64.xor)
         (func (export "shifts") (param i32 i32) (result i32)
           local.get 0 local.get 1 i32.shl local.get 1 i32.shr_s
           local.get 1 i32.shr_u local.get 1 i32.rotl local.get 1 i32.rotr)
         (func (export "shifts64") (param i64 i64 i64 i64) (result i64)
           local.get 0 local.get 1 i64.shl local.get 3 i64.shr_s
           local.get 1 i64.shr_u local.get 3 i64.rotl local.get 1 i64.rotr)
         (func (export "cmps") (param i32 i32) (result i32)
           local.get 0 local.get 1 i32.lt_s
           local.get 0 local.get 1 i32.ge_u i32.add
           local.get 0 i32.eqz i32.add)
         (func (export "cmps64") (param i64 i64) (result i32)
           local.get 0 local.get 1 i64.gt_u
           local.get 0 local.get 1 i64.le_s i32.add
           local.get 1 i64.eqz i32.add)
         (func (export "sel") (param i32 i32 i32) (result i32)
           local.get 0 local.get 1 local.get 2 select)
         (func (export "sel64") (param i64 i64 i32) (result i64)
           local.get 0 local.get 1 local.get 2 select)
         (func (export "ext") (param i32 i64) (result i64)
           local.get 0 i32.extend8_s i32.extend16_s i64.extend_i32_s
           local.get 1 i64.extend8_s i64.extend16_s i64.extend32_s i64.add
           local.get 1 i32.wrap_i64 i64.extend_i32_u i64.add)
         (func (export "consts") (result i64)
           i32.const -1 drop
           i64.const 7 i64.const -7 i64.add
           i64.const 0x1122334455667788 i64.add))"#,
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
    // Immediates as the backend's printer writes them: lowercase hex, always.
    f.options_mut().set_uppercase_hex(false);
    f.options_mut().set_small_hex_numbers_in_decimal(false);
    f
}

/// The text iced's GAS formatter prints for `want`. It is the backend's own
/// AT&T text ([`Inst::att`], what `llvm-mc` reads) with ONE spelling
/// difference, stated here rather than normalised away: asked for size
/// suffixes, iced also suffixes `setCC` with `b` (`setbb %al`), which LLVM's
/// assembler spells without (`setb %al`).
///
/// A BRANCH is the second difference: the backend prints it relative to the
/// instruction (`{disp32} jne .+0x8`, what an assembler needs to be told),
/// iced prints the absolute target. `next_ip` is the address after the
/// decoded instruction; the expected target is computed from the REQUESTED
/// displacement, so a wrong displacement byte is a text mismatch.
fn iced_text(want: &Inst, next_ip: u64) -> String {
    match want {
        Inst::SetCc { cond, dst } => format!("set{}b %{}", cond.suffix(), dst.name8()),
        Inst::Jcc { cond, rel } => format!(
            "j{} 0x{:016x}",
            cond.suffix(),
            next_ip.wrapping_add(*rel as i64 as u64)
        ),
        Inst::Jmp { rel } => format!("jmp 0x{:016x}", next_ip.wrapping_add(*rel as i64 as u64)),
        other => other.att(),
    }
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
        if *text != iced_text(want, ins.next_ip()) {
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
    assert!(checked >= 500, "only {checked} instructions decoded");
}

/// Every FORM the encoder can produce (the E1 population), decoded by iced.
#[test]
fn every_encoder_form_decodes_to_its_text_e2() {
    let forms = all_forms();
    assert_eq!(forms.len(), FORM_COUNT);
    for f in &forms {
        let b = encode(f);
        check(&b, &[*f], &[b.len()]).unwrap_or_else(|e| panic!("{f}: {e}"));
    }
    eprintln!(
        "E2: {} forms decode to their text under iced-x86",
        forms.len()
    );
}

/// Potency: a dropped REX.B makes `addl %esi, %r9d` decode as `addl %esi,
/// %ecx`, and the check refuses it.
#[test]
fn a_dropped_rex_b_is_refused() {
    let want = Inst::Alu {
        op: AluOp::Add,
        size: Size::L,
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
    let b = encode(&Inst::Alu {
        op: AluOp::Add,
        size: Size::L,
        dst: Reg::R12,
        src: Reg::R13,
    });
    assert!(decode_all(&b[..b.len() - 1]).is_err());
}
