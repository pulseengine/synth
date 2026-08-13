//! RQ-57-SENTINEL (Refs #953, #932) — end-to-end pins for the two sentinel/value
//! collisions this sweep converted, plus the fail-closed control.
//!
//! The disease (one mechanism, three shipped instances): a numeric `0` that
//! means both "unset/unknown" and a value a module can legitimately declare.
//!
//! * #932 (v0.56.0): `unwrap_or(0)` turned "no floor establishable" into
//!   "the floor is 0 bytes" and STRIPPED real bounds guards.
//! * #953 (v0.56.1): `if linear_memory_bytes > 0 {..} else { 64 * 1024 }`
//!   INVENTED a 64 KiB bound for a `(memory 0)` module on rv32.
//! * THIS SWEEP found two more:
//!   1. ARM `--safety-bounds mask` exempted `bytes == 0` from its power-of-two
//!      gate ("0 means unknown"), so a `(memory 0)` module compiled with a
//!      runtime mask of `R10 - 1 = 0 - 1 = 0xFFFFFFFF` — an IDENTITY mask.
//!      Every access executed unmasked at `[R11 + addr]`: unbounded OOB
//!      read/write in the mode whose purpose is bounding.
//!   2. The single-function CLI path forced `linear_memory_bytes: 0` for every
//!      backend except aarch64, on a comment claiming the field was never
//!      consumed there — false for RV32, whose `compile_function` reads it for
//!      the Software/Mask bound. After #953 deleted the rv32 64 KiB fallback,
//!      `--func-index` + `--safety-bounds software` on a `(memory 1)` module
//!      compiled EVERY access to the zero-size `ebreak` fold.
//!
//! Red-first evidence (recorded on the pre-fix v0.56.1 tree, 2026-08-13):
//! * `(memory 0)` + arm mask compiled with exit 0, `movw r10, #0x0` in the
//!   reset handler and AND-masked bodies — test 1 below FAILED.
//! * `(memory 1)` + rv32 `--func-index 0 --safety-bounds software` emitted
//!   `00050293 00100073` (addi; ebreak) — an unconditional trap at entry —
//!   test 2 below FAILED.
//! * `(memory 0)` + rv32 single-function emitted the same ebreak fold — the
//!   fail-closed CONTROL (test 3) passed before AND after, proving the fix
//!   restored the declared bound rather than deleting the trap fold.

use std::path::PathBuf;
use std::process::Command;

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-rq57-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

const MEM0_WAT: &str = r#"(module
  (memory 0)
  (func (export "peek") (param i32) (result i32)
    local.get 0
    i32.load)
  (func (export "poke") (param i32) (param i32)
    local.get 0
    local.get 1
    i32.store))
"#;

const MEM1_WAT: &str = r#"(module
  (memory 1)
  (func (export "peek") (param i32) (result i32)
    local.get 0
    i32.load))
"#;

/// Raw instruction words from synth's own disassembler (host-independent —
/// the #850 lesson: never depend on an installed llvm-objdump).
/// Every 4-byte little-endian word in the object's `.text`, as lowercase hex.
///
/// #850: this reads the ELF SECTION BYTES, not `synth disasm` TEXT. The first
/// version of this helper parsed `synth disasm` output — it passed on macOS and
/// returned an EMPTY vector on the ubuntu runner, so both assertions below
/// failed in CI with `words: []` while the lane's local run was green. The
/// disassembler decodes with whatever target it defaults to and its rendering is
/// host-dependent, so its text is not a reliable data source. `.text` bytes are
/// identical on every host — synth is a cross-compiler and its output is a pure
/// function of (wasm, flags), which is the same property `frozen_codegen_bytes`
/// relies on.
fn disasm_words(obj: &std::path::Path) -> Vec<String> {
    use object::{Object, ObjectSection};
    let data = std::fs::read(obj).expect("read object");
    let file = object::File::parse(&*data).expect("parse ELF");
    let text = file
        .section_by_name(".text")
        .expect("object must have a .text section")
        .data()
        .expect("read .text")
        .to_vec();
    text.chunks_exact(4)
        .map(|w| format!("{:08x}", u32::from_le_bytes([w[0], w[1], w[2], w[3]])))
        .collect()
}

/// Sweep finding 1: `--safety-bounds mask` on a `(memory 0)` module must
/// REFUSE (zero-byte memory, identity-mask hole), not emit unmasked accesses.
#[test]
fn arm_mask_zero_memory_refused() {
    let dir = workdir("mask0");
    let wat = dir.join("mem0.wat");
    std::fs::write(&wat, MEM0_WAT).unwrap();
    let elf = dir.join("mem0.elf");
    let out = Command::new(synth())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "-o",
            elf.to_str().unwrap(),
            "--all-exports",
            "--safety-bounds",
            "mask",
        ])
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "mask over a (memory 0) module must fail the compile — pre-fix it \
         succeeded and emitted an identity mask (R10=0 baked, SUB R12,R10,#1 \
         = 0xFFFFFFFF)"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("ZERO bytes"),
        "the refusal must name the zero-byte cause, got:\n{stderr}"
    );
}

/// Sweep finding 2: the rv32 single-function path must bound against the
/// module's DECLARED memory size, not a forced 0. `(memory 1)` = 65536 bytes,
/// so the software guard materializes 65536 - 4 = 65532:
/// `lui t1, 0x10` (00010337) + `addi t1, t1, -4` (ffc30313).
#[test]
fn rv32_single_func_software_uses_declared_bound() {
    let dir = workdir("rv32-declared");
    let wat = dir.join("mem1.wat");
    std::fs::write(&wat, MEM1_WAT).unwrap();
    let obj = dir.join("mem1.o");
    let out = Command::new(synth())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "-o",
            obj.to_str().unwrap(),
            "-b",
            "riscv",
            "--func-index",
            "0",
            "--safety-bounds",
            "software",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "rv32 single-function compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let words = disasm_words(&obj);
    assert!(
        words.iter().any(|w| w == "00010337") && words.iter().any(|w| w == "ffc30313"),
        "the software guard must carry the declared 1-page bound (lui t1,0x10; \
         addi t1,t1,-4 = 65532) — pre-fix the forced linear_memory_bytes=0 \
         emitted the zero-size ebreak fold instead; words: {words:?}"
    );
}

/// CONTROL (non-vacuity): `(memory 0)` through the same rv32 single-function
/// path must KEEP the #953 fail-closed behavior — an unconditional `ebreak`
/// (00100073) and no invented bound. Proves the fix threads the declared size
/// rather than resurrecting a fallback.
#[test]
fn rv32_single_func_zero_memory_stays_fail_closed() {
    let dir = workdir("rv32-mem0");
    let wat = dir.join("mem0.wat");
    std::fs::write(&wat, MEM0_WAT).unwrap();
    let obj = dir.join("mem0.o");
    let out = Command::new(synth())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "-o",
            obj.to_str().unwrap(),
            "-b",
            "riscv",
            "--func-index",
            "0",
            "--safety-bounds",
            "software",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "rv32 (memory 0) single-function compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let words = disasm_words(&obj);
    assert!(
        words.iter().any(|w| w == "00100073"),
        "(memory 0) must keep the unconditional ebreak fold (#953); words: {words:?}"
    );
    assert!(
        !words.iter().any(|w| w == "00010337"),
        "(memory 0) must NOT get a 64 KiB bound materialized (#953); words: {words:?}"
    );
}
