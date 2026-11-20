//! RQ-92-WDGTHIN (Refs #1741): `synth verify-embedder --target cortex-m0` — the
//! ARMv6-M leg — refuses a boot shim that still uses an ARMv7-M encoding.
//!
//! gale's requirement for the Cortex-M0+ board (#1741, comment of
//! 2026-11-18): "The verify-embedder ARMv6-M leg must reject a boot shim that
//! still uses the v7 encoding." A shim written for Cortex-M3/M4 establishes
//! R11/R10 with `movw`/`movt`/`mov.w`; it links for a Cortex-M0 without
//! complaint and takes a HardFault on its first instruction.
//!
//! The shims here are the bytes `arm-none-eabi-as` produced for the two
//! sources quoted at [`SHIM_V6`] and [`SHIM_V7`], wrapped in a hand-built
//! ELF32 object (so the test needs no cross toolchain), plus synth's own
//! objects. The leg reads bytes, not disassembly, so it needs no objdump;
//! the register scan that follows a passing leg does, and where the host has
//! none that scan fails — these tests therefore assert on the leg's own
//! verdict line, never on the exit status of a passing run.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// ```text
/// Reset_Handler:  ldr r0, =0x20010000 ; mov r11, r0
///                 ldr r0, =65536      ; mov r10, r0
///                 ldr r0, =0x20000000 ; mov r9, r0
///                 bl wdg_kick ; b .
///                 .ltorg
/// ```
/// `arm-none-eabi-as -march=armv6-m`: 18 bytes of code, then (`$d` at 0x12)
/// 2 bytes of padding and the three literal words.
const SHIM_V6: &[u16] = &[
    0x4804, 0x4683, 0x4804, 0x4682, 0x4804, 0x4681, 0xF7FF, 0xFFFE, 0xE7FE, // code
    0x0000, 0x0000, 0x2001, 0x0000, 0x0001, 0x0000, 0x2000, // pad + pool
];
const SHIM_V6_DATA_AT: u32 = 0x12;

/// ```text
/// Reset_Handler:  movw r11, #0 ; movt r11, #0x2001
///                 mov.w r10, #65536
///                 ldr r0, =0x20000000 ; mov r9, r0     (assembled as mov.w)
///                 bl wdg_kick ; b .
/// ```
/// `arm-none-eabi-as -march=armv7-m`: four ARMv7-M encodings.
const SHIM_V7: &[u16] = &[
    0xF240, 0x0B00, 0xF2C2, 0x0B01, 0xF44F, 0x3A80, 0xF04F, 0x5000, 0x4681, 0xF7FF, 0xFFFE, 0xE7FE,
];

#[derive(Clone, Copy)]
enum Kind {
    /// `STT_FUNC`, Thumb bit set.
    ThumbFunc,
    /// `STT_FUNC`, Thumb bit clear.
    ArmFunc,
    /// `STT_NOTYPE` (a mapping symbol).
    Mapping,
}

/// A minimal ELF32 little-endian `EM_ARM` relocatable object: `.text`
/// (`SHF_ALLOC | SHF_EXECINSTR`) holding `text`, and a symbol table.
fn elf(text: &[u16], symbols: &[(&str, u32, Kind)]) -> Vec<u8> {
    let text: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 16];
    for (name, value, kind) in symbols {
        let name_off = strtab.len() as u32;
        strtab.extend_from_slice(name.as_bytes());
        strtab.push(0);
        let (value, info) = match kind {
            Kind::ThumbFunc => (value | 1, 2u8),
            Kind::ArmFunc => (*value, 2),
            Kind::Mapping => (*value, 0),
        };
        symtab.extend_from_slice(&name_off.to_le_bytes());
        symtab.extend_from_slice(&value.to_le_bytes());
        symtab.extend_from_slice(&0u32.to_le_bytes());
        symtab.push(info); // STB_LOCAL
        symtab.push(0);
        symtab.extend_from_slice(&1u16.to_le_bytes()); // st_shndx = .text
    }
    let shstrtab = b"\0.text\0.symtab\0.strtab\0.shstrtab\0".to_vec();
    let mut out = vec![0u8; 52];
    let place = |bytes: &[u8], out: &mut Vec<u8>| -> (u32, u32) {
        while !out.len().is_multiple_of(4) {
            out.push(0);
        }
        let off = out.len() as u32;
        out.extend_from_slice(bytes);
        (off, bytes.len() as u32)
    };
    let t = place(&text, &mut out);
    let sy = place(&symtab, &mut out);
    let st = place(&strtab, &mut out);
    let sh = place(&shstrtab, &mut out);
    while !out.len().is_multiple_of(4) {
        out.push(0);
    }
    let shoff = out.len() as u32;
    // name, type, flags, addr, offset, size, link, info, align, entsize
    let nsyms = symbols.len() as u32 + 1;
    let headers: [[u32; 10]; 5] = [
        [0; 10],
        [1, 1, 0x6, 0, t.0, t.1, 0, 0, 2, 0],
        [7, 2, 0, 0, sy.0, sy.1, 3, nsyms, 4, 16],
        [15, 3, 0, 0, st.0, st.1, 0, 0, 1, 0],
        [23, 3, 0, 0, sh.0, sh.1, 0, 0, 1, 0],
    ];
    for h in headers {
        for w in h {
            out.extend_from_slice(&w.to_le_bytes());
        }
    }
    out[0..7].copy_from_slice(&[0x7F, b'E', b'L', b'F', 1, 1, 1]);
    out[16..18].copy_from_slice(&1u16.to_le_bytes()); // ET_REL
    out[18..20].copy_from_slice(&40u16.to_le_bytes()); // EM_ARM
    out[20..24].copy_from_slice(&1u32.to_le_bytes());
    out[32..36].copy_from_slice(&shoff.to_le_bytes());
    out[36..40].copy_from_slice(&0x0500_0000u32.to_le_bytes()); // EABI5
    out[40..42].copy_from_slice(&52u16.to_le_bytes());
    out[46..48].copy_from_slice(&40u16.to_le_bytes());
    out[48..50].copy_from_slice(&5u16.to_le_bytes());
    out[50..52].copy_from_slice(&4u16.to_le_bytes());
    out
}

fn dir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!(
        "synth_verify_embedder_v6m_1741_{}_{tag}",
        std::process::id()
    ));
    std::fs::create_dir_all(&d).expect("mkdir");
    d
}

struct Run {
    ok: bool,
    stdout: String,
    stderr: String,
}

fn verify(elf: &Path, flags: &[&str]) -> Run {
    let o: Output = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("verify-embedder")
        .arg(elf)
        .args(flags)
        .env("RUST_LOG", "error")
        .output()
        .expect("run synth");
    Run {
        ok: o.status.success(),
        stdout: String::from_utf8_lossy(&o.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&o.stderr).into_owned(),
    }
}

fn write(d: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    let p = d.join(name);
    std::fs::write(&p, bytes).unwrap();
    p
}

fn shim_v6() -> Vec<u8> {
    elf(
        SHIM_V6,
        &[
            ("$t", 0, Kind::Mapping),
            ("$d", SHIM_V6_DATA_AT, Kind::Mapping),
            ("Reset_Handler", 0, Kind::ThumbFunc),
        ],
    )
}

fn shim_v7() -> Vec<u8> {
    elf(
        SHIM_V7,
        &[
            ("$t", 0, Kind::Mapping),
            ("Reset_Handler", 0, Kind::ThumbFunc),
        ],
    )
}

const LEG_OK: &str = "verify-embedder ARMv6-M OK";
const LEG_RED: &str = "that are not ARMv6-M";

#[test]
fn a_v7_encoded_boot_shim_is_refused_for_cortex_m0_and_m0plus() {
    let d = dir("shim");
    let v6 = write(&d, "boot_v6.o", &shim_v6());
    let v7 = write(&d, "boot_v7.o", &shim_v7());
    for target in ["cortex-m0", "cortex-m0plus"] {
        // GREEN: the ARMv6-M shim. Its literal pool is skipped as data.
        let r = verify(
            &v6,
            &["--target", target, "--allow-writer", "Reset_Handler"],
        );
        assert!(
            r.stdout.contains(LEG_OK)
                && r.stdout.contains("18 bytes of Thumb code")
                && r.stdout.contains("(14 data bytes skipped)")
                && r.stdout.contains(&format!("[--target {target}]")),
            "{target}: {} {}",
            r.stdout,
            r.stderr
        );
        assert!(!r.stderr.contains(LEG_RED), "{target}: {}", r.stderr);

        // RED: the ARMv7-M shim, with or without the acknowledgement.
        for flags in [
            &["--target", target][..],
            &["--target", target, "--allow-writer", "Reset_Handler"][..],
        ] {
            let r = verify(&v7, flags);
            assert!(!r.ok, "{flags:?}: a v7-encoded boot shim passed");
            assert!(!r.stdout.contains(LEG_OK), "{flags:?}: {}", r.stdout);
            for needle in [
                "verify-embedder REFUSED",
                "4 instruction(s) that are not ARMv6-M",
                "<Reset_Handler> .text+0x0: `f240 0b00` — MOVW/MOVT",
                "<Reset_Handler> .text+0x4: `f2c2 0b01` — MOVW/MOVT",
                "<Reset_Handler> .text+0x8: `f44f 3a80` — wide data-processing",
                "<Reset_Handler> .text+0xc: `f04f 5000` — wide data-processing",
                "--allow-writer does not waive this check",
            ] {
                assert!(
                    r.stderr.contains(needle),
                    "{flags:?}: no `{needle}` in {}",
                    r.stderr
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&d);
}

/// The leg runs only when asked for or when the ELF says ARMv6-M — and a
/// misspelled target is an error, never a silently skipped check.
#[test]
fn the_leg_is_selected_by_target_or_by_build_attributes() {
    let d = dir("select");
    let v7 = write(&d, "boot_v7.o", &shim_v7());
    // No --target, no ARMv6-M attribute: the leg does not run. THE BOUND the
    // CLI help states: pass --target for an image whose attributes do not
    // say ARMv6-M (a linker retags the image when one object is ARMv7-M).
    let r = verify(&v7, &["--allow-writer", "Reset_Handler"]);
    assert!(!r.stderr.contains(LEG_RED) && !r.stdout.contains(LEG_OK));
    // A v7-M target: not the ARMv6-M leg.
    let r = verify(
        &v7,
        &["--target", "cortex-m4", "--allow-writer", "Reset_Handler"],
    );
    assert!(!r.stderr.contains(LEG_RED) && !r.stdout.contains(LEG_OK));
    // A misspelled target refuses.
    let r = verify(&v7, &["--target", "cortex-m0pluss"]);
    assert!(!r.ok && r.stderr.contains("verify-embedder --target cortex-m0pluss"));

    // synth's own ARMv6-M object carries Tag_CPU_arch = ARMv6-M: the leg runs
    // with no flag, and passes.
    let wat = d.join("wdg.wat");
    std::fs::write(
        &wat,
        r#"(module
  (import "env" "hal_write" (func $w (param i32 i32)))
  (func (export "wdg_kick") i32.const 0x40003000 i32.const 0xAAAA call $w))"#,
    )
    .unwrap();
    let compile = |target: &str, out: &Path| {
        let o = Command::new(env!("CARGO_BIN_EXE_synth"))
            .args(["compile", wat.to_str().unwrap(), "--target", target, "-o"])
            .arg(out)
            .env("RUST_LOG", "error")
            .output()
            .expect("run synth");
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
    };
    let m0 = d.join("wdg_m0.o");
    compile("cortex-m0", &m0);
    let r = verify(&m0, &[]);
    assert!(
        r.stdout.contains(LEG_OK) && r.stdout.contains("[Tag_CPU_arch says ARMv6-M]"),
        "{} {}",
        r.stdout,
        r.stderr
    );
    // The same module compiled for cortex-m3 is ARMv7-M code: refused for an
    // ARMv6-M core, naming its wide prologue.
    let m3 = d.join("wdg_m3.o");
    compile("cortex-m3", &m3);
    let r = verify(&m3, &["--target", "cortex-m0"]);
    assert!(!r.ok && r.stderr.contains(LEG_RED), "{}", r.stderr);
    assert!(
        r.stderr.contains("<wdg_kick>") && r.stderr.contains("`e92d 41f0`"),
        "{}",
        r.stderr
    );
    // An ARMv6-M-tagged object with one ARMv7-M instruction patched in is
    // refused with no flag: the tag selects the leg, the bytes decide.
    let mut bytes = std::fs::read(&m0).unwrap();
    let movw = [0x40u8, 0xF2, 0x00, 0x0B];
    let push = bytes
        .windows(2)
        .position(|w| w[1] == 0xB5)
        .expect("a 16-bit push {.., lr}");
    bytes[push + 2..push + 6].copy_from_slice(&movw);
    let patched = write(&d, "wdg_m0_patched.o", &bytes);
    let r = verify(&patched, &[]);
    assert!(
        !r.ok && r.stderr.contains("`f240 0b00` — MOVW/MOVT"),
        "{} {}",
        r.stdout,
        r.stderr
    );
    let _ = std::fs::remove_dir_all(&d);
}

/// Code and data are separated by the ELF's own markers, and every
/// disagreement is read the fail-closed way.
#[test]
fn code_data_separation_is_fail_closed() {
    let d = dir("regions");
    let t = &["--target", "cortex-m0"][..];
    // `bx lr`, then the word 0x0B00F240 — which is `movw r11, #0` if executed.
    let body: &[u16] = &[0x4770, 0x46C0, 0xF240, 0x0B00];
    let f = ("f", 0u32, Kind::ThumbFunc);
    // Under `$d` it is a literal: skipped, counted.
    let p = write(
        &d,
        "pool.o",
        &elf(
            body,
            &[("$t", 0, Kind::Mapping), ("$d", 4, Kind::Mapping), f],
        ),
    );
    let r = verify(&p, t);
    assert!(
        r.stdout.contains(LEG_OK)
            && r.stdout.contains("4 bytes of Thumb code")
            && r.stdout.contains("(4 data bytes skipped)"),
        "{} {}",
        r.stdout,
        r.stderr
    );
    // With no `$d` the same bytes are code, and refused.
    let p = write(&d, "nopool.o", &elf(body, &[("$t", 0, Kind::Mapping), f]));
    assert!(verify(&p, t).stderr.contains("`f240 0b00` — MOVW/MOVT"));
    // No marker at all: the section is decoded whole as Thumb code.
    let p = write(&d, "bare.o", &elf(body, &[]));
    assert!(verify(&p, t).stderr.contains("`f240 0b00` — MOVW/MOVT"));
    // A `$d` and a Thumb function at ONE address: the function wins. This is
    // synth's own object behind another object's literal pool in a linked
    // image (synth emits function symbols but no mapping symbols).
    let p = write(
        &d,
        "func_under_d.o",
        &elf(
            body,
            &[
                ("$t", 0, Kind::Mapping),
                ("$d", 4, Kind::Mapping),
                f,
                ("g", 4, Kind::ThumbFunc),
            ],
        ),
    );
    let r = verify(&p, t);
    assert!(
        !r.ok && r.stderr.contains("<g> .text+0x4: `f240 0b00` — MOVW/MOVT"),
        "{} {}",
        r.stdout,
        r.stderr
    );
    // ARM-state code, by mapping symbol or by a function without the Thumb
    // bit: an M-profile core has none.
    for syms in [
        &[("$a", 0, Kind::Mapping)][..],
        &[("h", 0, Kind::ArmFunc)][..],
    ] {
        let p = write(&d, "arm.o", &elf(&[0x0000, 0xE1A0, 0x4770, 0x46C0], syms));
        let r = verify(&p, t);
        assert!(
            !r.ok && r.stderr.contains("ARM-state (A32) code"),
            "{}",
            r.stderr
        );
    }
    // IT and CBZ, the 16-bit ARMv7-M additions.
    let p = write(&d, "it.o", &elf(&[0xBF08, 0x2000, 0xB100, 0x4770], &[f]));
    let r = verify(&p, t);
    assert!(
        r.stderr.contains("`bf08` — IT block") && r.stderr.contains("`b100` — CBZ/CBNZ"),
        "{}",
        r.stderr
    );
    // NON-VACUITY: nothing decoded is not conformance.
    let p = write(&d, "alldata.o", &elf(body, &[("$d", 0, Kind::Mapping)]));
    let r = verify(&p, t);
    assert!(
        !r.ok && r.stderr.contains("decoded 0 bytes of Thumb code"),
        "{}",
        r.stderr
    );
    let _ = std::fs::remove_dir_all(&d);
}
