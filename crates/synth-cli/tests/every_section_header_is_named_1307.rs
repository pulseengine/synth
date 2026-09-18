//! RQ-69-ELFNAMES (#1307) — every emitted section header resolves to a name.
//!
//! `.strtab` and `.symtab` named one byte early: their `sh_name` was
//! hand-counted as `".shstrtab\0".len()` (10) and
//! `".shstrtab\0.strtab\0".len()` (18), both forgetting the NUL the string
//! table starts with. An offset one byte early lands on the PREVIOUS string's
//! terminator, which reads as the empty string — so both sections were
//! unnamed, and a consumer looking either up BY NAME got nothing rather than an
//! error. That is how it was found: a v0.68 harness reported "no symbol table"
//! for an object that had one.
//!
//! THIS TEST WALKS THE WHOLE TABLE. Pinning the two known-bad entries would
//! pass an object that broke a third — and nothing checking the CLASS is why
//! this survived. Every header except the mandatory null section must resolve
//! to a non-empty name that is actually present in `.shstrtab`.

use std::path::Path;
use std::process::Command;

/// Parse the section headers straight out of the ELF32 bytes. Deliberately not
/// via a library: the test must read what synth WROTE, not what a permissive
/// reader reconstructs.
fn section_names(elf: &[u8]) -> Vec<(usize, u32, String)> {
    let u16le = |o: usize| u16::from_le_bytes([elf[o], elf[o + 1]]) as usize;
    let u32le = |o: usize| u32::from_le_bytes([elf[o], elf[o + 1], elf[o + 2], elf[o + 3]]);
    let e_shoff = u32le(0x20) as usize;
    let e_shentsize = u16le(0x2E);
    let e_shnum = u16le(0x30);
    let e_shstrndx = u16le(0x32);
    // The string table's own header gives where the names live.
    let shstr_hdr = e_shoff + e_shstrndx * e_shentsize;
    let shstr_off = u32le(shstr_hdr + 0x10) as usize;
    let shstr_size = u32le(shstr_hdr + 0x14) as usize;
    let strtab = &elf[shstr_off..shstr_off + shstr_size];
    (0..e_shnum)
        .map(|i| {
            let h = e_shoff + i * e_shentsize;
            let name_off = u32le(h);
            let s = &strtab[name_off as usize..];
            let end = s.iter().position(|&b| b == 0).unwrap_or(0);
            (i, name_off, String::from_utf8_lossy(&s[..end]).into_owned())
        })
        .collect()
}

fn compile(tag: &str, flags: &[&str]) -> Vec<u8> {
    let dir = std::env::temp_dir().join(format!("synth-elfnames-1307-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let out = dir.join(format!("{tag}.o"));
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/repro/i64_high_reg_zero_fill_916.wat");
    let st = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(fixture)
        .arg("-o")
        .arg(&out)
        .args(flags)
        .output()
        .expect("synth runs");
    assert!(
        st.status.success(),
        "{tag}: compile failed:\n{}",
        String::from_utf8_lossy(&st.stderr)
    );
    std::fs::read(&out).expect("object readable")
}

fn assert_every_header_named(tag: &str, elf: &[u8]) {
    let headers = section_names(elf);
    assert!(headers.len() > 2, "{tag}: suspiciously few sections");
    let unnamed: Vec<_> = headers
        .iter()
        .skip(1) // section 0 is the mandatory null header: name offset 0, empty by spec
        .filter(|(_, _, name)| name.is_empty())
        .collect();
    assert!(
        unnamed.is_empty(),
        "{tag}: {} section header(s) resolve to an EMPTY name — an offset that \
         lands on a previous string's terminator (#1307). Unnamed: {unnamed:?}\nAll: {headers:?}",
        unnamed.len()
    );
}

#[test]
fn relocatable_object_names_every_section_1307() {
    let elf = compile(
        "reloc",
        &["--target", "cortex-m4", "--all-exports", "--relocatable"],
    );
    assert_every_header_named("relocatable", &elf);
}

#[test]
fn self_contained_image_names_every_section_1307() {
    let elf = compile("self", &["--cortex-m"]);
    assert_every_header_named("self-contained", &elf);
}

/// The three standard names are the ones that were wrong, so pin them EXACTLY
/// — but as a supplement to the whole-table walk above, never instead of it.
#[test]
fn standard_section_names_resolve_1307() {
    let elf = compile(
        "std",
        &["--target", "cortex-m4", "--all-exports", "--relocatable"],
    );
    let names: Vec<String> = section_names(&elf).into_iter().map(|(_, _, n)| n).collect();
    for want in [".shstrtab", ".strtab", ".symtab", ".text"] {
        assert!(
            names.iter().any(|n| n == want),
            "{want} is not resolvable by name in the emitted object (#1307): {names:?}"
        );
    }
}
