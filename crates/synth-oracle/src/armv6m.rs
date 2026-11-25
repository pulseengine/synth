//! The ARMv6-M DECODE leg shared by the Cortex-M0 oracles (RQ-91-M0I32,
//! RQ-92-WDGTHIN; Refs #1301, #1741): is every instruction of a function an
//! ARMv6-M instruction under synth's v6-M contract?
//!
//! Independent of the compiler's own check (`synth_backend::armv6m`): the
//! 16-bit table is read from the frozen LLVM-derived fixture, and the rules
//! are restated here. It sees what unicorn's Cortex-M0 model does not fault
//! on (the model executes IT and CBZ/CBNZ).

/// The frozen LLVM-derived 16-bit ARMv6-M table, read from the fixture
/// (`{"legal_count": N, "legal_ranges": [[lo, hi], ...], ...}`).
pub fn legal16_table() -> Vec<(u16, u16)> {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/armv6m_legal16_1301.json"
    );
    let text = std::fs::read_to_string(path).expect("fixture");
    let key = "\"legal_ranges\":";
    let start = text.find(key).expect("legal_ranges") + key.len();
    let end = start + text[start..].find("]]").expect("end of legal_ranges");
    let ints: Vec<u32> = text[start..end]
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .map(|s| s.parse().unwrap())
        .collect();
    assert!(
        !ints.is_empty() && ints.len().is_multiple_of(2),
        "legal_ranges shape"
    );
    let t: Vec<(u16, u16)> = ints.chunks(2).map(|c| (c[0] as u16, c[1] as u16)).collect();
    // The fixture's own count, re-derived: a truncated read reds here.
    let count: usize = t
        .iter()
        .map(|&(lo, hi)| (lo..=hi).filter(|&h| !is_prefix(h)).count())
        .sum();
    let key = "\"legal_count\":";
    let c0 = text.find(key).expect("legal_count") + key.len();
    let c1 = c0 + text[c0..].find(',').expect("legal_count end");
    assert_eq!(count, text[c0..c1].trim().parse::<usize>().unwrap());
    t
}

pub fn is_prefix(h: u16) -> bool {
    matches!(h >> 11, 0b11101..=0b11111)
}

/// Every reason `bytes` is not ARMv6-M under synth's contract, as
/// `+offset: hex: why`.
pub fn v6m_violations(bytes: &[u8], table: &[(u16, u16)]) -> Vec<String> {
    let mut bad = Vec::new();
    let hw = |i: usize| u16::from_le_bytes([bytes[i], bytes[i + 1]]);
    let mut i = 0;
    while i + 1 < bytes.len() {
        let h = hw(i);
        if is_prefix(h) {
            if i + 3 >= bytes.len() {
                bad.push(format!("+{i:x}: {h:04x}: truncated 32-bit"));
                break;
            }
            let h2 = hw(i + 2);
            let bl = h >> 11 == 0b11110 && h2 & 0xD000 == 0xD000;
            let barrier = h == 0xF3BF && matches!(h2, 0x8F4F | 0x8F5F | 0x8F6F);
            if !(bl || barrier) {
                bad.push(format!("+{i:x}: {h:04x} {h2:04x}: 32-bit, not BL/barrier"));
            }
            i += 4;
            continue;
        }
        if !table.iter().any(|&(lo, hi)| (lo..=hi).contains(&h)) {
            bad.push(format!("+{i:x}: {h:04x}: not in the ARMv6-M table"));
        } else if h & 0xF800 == 0x4800 {
            bad.push(format!("+{i:x}: {h:04x}: 16-bit LDR (literal)"));
        } else if h & 0xFC00 == 0x4400 && matches!((h >> 8) & 3, 0 | 2) {
            let rd = ((h >> 4) & 0x8) | (h & 7);
            if (8..=12).contains(&rd) {
                bad.push(format!("+{i:x}: {h:04x}: writes R{rd}"));
            }
        }
        i += 2;
    }
    if !bytes.len().is_multiple_of(2) {
        bad.push("odd length".into());
    }
    bad
}
