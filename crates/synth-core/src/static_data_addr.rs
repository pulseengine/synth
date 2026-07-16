//! Static-data addressing validation (VCR-VER-003, synth #777 / #757).
//!
//! WASM active data segments are applied to linear memory **in declaration
//! order, later-wins**: when two active segments overlap the same range, the
//! later-declared one overwrites the earlier. synth's `--native-pointer-abi`
//! relocatable path splits the linear memory into one packed `.data` blob per
//! segment (`__synth_wasm_seg_K`) and retargets every static-data relocation
//! `__synth_wasm_data + C` to `__synth_wasm_seg_K + (C - seg_off_K)` (the #354
//! mixed-split). Choosing the WRONG owning segment for an address `C` that lies
//! in several overlapping segments is a **silent miscompile**: the reloc reads
//! a stale earlier segment's bytes instead of the byte the runtime image holds.
//!
//! This is exactly #757 — gale's fused `gust:os` node declared three active
//! segments all at linmem `0x100000`; the string lived in the last segment but
//! the retargeting (`.position()`) bound its reads to the first segment's
//! consts (`got=[2,0,0,0,..]` = `__synth_wasm_seg_0+8`). It survived four
//! releases because value-differential oracles are coverage-limited (7
//! synthetic reconstructions were all green). The fix resolves overlapping
//! addresses to the LAST-declared owner (`.rposition()`).
//!
//! # What this validator proves (per compilation, by construction)
//!
//! Given the module's active data segments (declaration order) and the
//! retargeting the compiler actually emitted — one [`RelocResolution`]
//! `(seg_index K, addend A)` per static-data reloc — it reconstructs the
//! RUNTIME linear-memory image (apply every segment in declaration order,
//! later-wins) **independently of K**, then asserts: the byte the packed
//! `.data` serves for that reloc (`seg[K].bytes[A]`) EQUALS the byte the
//! runtime image holds at the reloc's original access address
//! (`seg[K].off + A`). A single mismatch — the wrong-segment resolution — is a
//! [`Verdict::Mismatch`].
//!
//! # Concrete, not symbolic; unconditional
//!
//! This is a concrete byte-equality over a compiled object, not a ∀-inputs SMT
//! property, and it depends on nothing but `std` — so it lives in `synth-core`
//! and runs on **every** compilation (the shipping build is `--features riscv`,
//! *not* `verify`; a `verify`-gated check would stay dormant in exactly the
//! build that shipped #757 four times). It mirrors VCR-VER-002's *structure* (a
//! verdict enum + a per-compilation gate) but does the honest thing — a direct
//! comparison against an independently reconstructed truth image. The truth
//! side never touches `K`, so the validator cannot be satisfied by mirroring
//! the code under test (the mirror-pinning vacuity mode is structurally
//! excluded). `synth-verify` re-exports this module for the VCR-VER-003 tests.

use std::collections::HashMap;

/// One active WASM data segment: its linear-memory offset and its bytes, in
/// declaration order. The packed `.data` blob stores these bytes verbatim
/// (4-aligned per segment) under `__synth_wasm_seg_K`; index `K` in the segment
/// list is the `K` in the symbol name.
#[derive(Clone, Debug)]
pub struct DataSegment {
    /// Linear-memory offset the active segment is applied at (WASM `i32.const`).
    pub linmem_off: u32,
    /// The segment's initializer bytes.
    pub bytes: Vec<u8>,
}

/// The retargeting the compiler emitted for one static-data relocation: it now
/// points at `__synth_wasm_seg_{seg_index} + addend`. `seg_index` is the `K`
/// from the emitted symbol name; `addend` is the emitted in-place REL addend
/// (`= original_access_addr - seg[K].linmem_off`). This is the value read back
/// from what the compiler produced — NEVER recomputed by the validator (that
/// would mirror-pin the check and make it vacuous).
#[derive(Clone, Debug)]
pub struct RelocResolution {
    /// The `K` in the emitted `__synth_wasm_seg_K` symbol.
    pub seg_index: usize,
    /// The emitted addend (offset into `seg[K].bytes`).
    pub addend: u32,
    /// Optional label for diagnostics (e.g. `"func 3 @ 0x1a"`); not load-bearing.
    pub label: String,
}

/// The verdict of the addressing gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// Every static-data reloc resolves to the runtime-correct byte (segments
    /// applied in declaration order, later-wins). #757 cannot occur.
    Consistent,
    /// A reloc resolves to a byte that disagrees with the runtime image — the
    /// wrong-segment miscompile. Carries the offending resolutions.
    Mismatch(Vec<AddrMismatch>),
}

/// A single reloc that reads the wrong byte.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AddrMismatch {
    /// The reloc's diagnostic label.
    pub label: String,
    /// The emitted `K` (`__synth_wasm_seg_K`).
    pub seg_index: usize,
    /// The emitted addend.
    pub addend: u32,
    /// The original linear-memory access address (`seg[K].off + addend`).
    pub access_addr: u32,
    /// The byte the packed `.data` serves (`seg[K].bytes[addend]`).
    pub served: u8,
    /// The byte the runtime image holds at `access_addr` (the truth).
    pub runtime: u8,
}

impl AddrMismatch {
    /// A human-readable one-line diagnostic for the compile-time error.
    pub fn describe(&self) -> String {
        format!(
            "{}: __synth_wasm_seg_{}+0x{:x} -> linmem 0x{:x} serves 0x{:02x} but \
             the runtime image (segments applied later-wins) owns 0x{:02x}",
            self.label, self.seg_index, self.addend, self.access_addr, self.served, self.runtime
        )
    }
}

/// Reconstruct the runtime linear-memory image: apply every active segment in
/// declaration order, later-wins. This is the ground truth and is derived only
/// from the segment list — never from any reloc resolution.
fn runtime_image(segments: &[DataSegment]) -> HashMap<u32, u8> {
    let mut mem = HashMap::new();
    for seg in segments {
        for (j, &b) in seg.bytes.iter().enumerate() {
            mem.insert(seg.linmem_off + j as u32, b);
        }
    }
    mem
}

/// The per-compilation addressing gate. For every emitted [`RelocResolution`],
/// assert the packed byte it serves equals the runtime-image byte at the
/// original access address. See the module docs for the invariant.
///
/// Returns [`Verdict::Consistent`] if every reloc agrees, else
/// [`Verdict::Mismatch`] carrying each offending reloc. Resolutions whose
/// `seg_index`/`addend` are out of range are reported as mismatches (an
/// out-of-range resolution is itself a broken retargeting).
pub fn validate_reloc_resolutions(
    segments: &[DataSegment],
    resolutions: &[RelocResolution],
) -> Verdict {
    let runtime = runtime_image(segments);
    let mut bad = Vec::new();
    for r in resolutions {
        let Some(seg) = segments.get(r.seg_index) else {
            bad.push(AddrMismatch {
                label: r.label.clone(),
                seg_index: r.seg_index,
                addend: r.addend,
                access_addr: 0,
                served: 0,
                runtime: 0,
            });
            continue;
        };
        let access_addr = seg.linmem_off + r.addend;
        // The byte the packed .data serves for this reloc.
        let Some(&served) = seg.bytes.get(r.addend as usize) else {
            bad.push(AddrMismatch {
                label: r.label.clone(),
                seg_index: r.seg_index,
                addend: r.addend,
                access_addr,
                served: 0,
                runtime: 0,
            });
            continue;
        };
        // The byte the runtime image (independent of K) holds there.
        // Every retargeted reloc addresses a byte inside some segment, so the
        // runtime image is always defined at access_addr; a missing entry would
        // itself be a broken retargeting, so treat it as a mismatch.
        let Some(&runtime_byte) = runtime.get(&access_addr) else {
            bad.push(AddrMismatch {
                label: r.label.clone(),
                seg_index: r.seg_index,
                addend: r.addend,
                access_addr,
                served,
                runtime: 0,
            });
            continue;
        };
        if served != runtime_byte {
            bad.push(AddrMismatch {
                label: r.label.clone(),
                seg_index: r.seg_index,
                addend: r.addend,
                access_addr,
                served,
                runtime: runtime_byte,
            });
        }
    }
    if bad.is_empty() {
        Verdict::Consistent
    } else {
        Verdict::Mismatch(bad)
    }
}

/// Resolve an access address `c` to its owning segment index under a chosen
/// tie-break policy, mirroring main.rs's `.rposition()` / `.position()` search.
/// `last_wins = true` is the CORRECT WASM overwrite semantics (`.rposition()`);
/// `last_wins = false` is the #757 miscompile (`.position()`). Returns the
/// segment index and the addend `c - seg.linmem_off`, or `None` if `c` is in no
/// segment. Exposed so the red-first gate can toggle the policy as an argument
/// (no source revert), and so callers can build resolutions the same way the
/// compiler does.
pub fn resolve_owner(segments: &[DataSegment], c: u32, last_wins: bool) -> Option<RelocResolution> {
    let hit = |(off, len): (u32, usize)| c >= off && c < off + len as u32;
    let idx = if last_wins {
        segments
            .iter()
            .rposition(|s| hit((s.linmem_off, s.bytes.len())))
    } else {
        segments
            .iter()
            .position(|s| hit((s.linmem_off, s.bytes.len())))
    }?;
    Some(RelocResolution {
        seg_index: idx,
        addend: c - segments[idx].linmem_off,
        label: format!("addr 0x{c:x}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Three active segments ALL at linmem 0x100000 with DISTINCT bytes at the
    /// overlap offset — the #757 shape. seg_2 (last) owns the runtime bytes.
    fn overlapping_segments() -> Vec<DataSegment> {
        vec![
            // seg_0: stale consts (the wrong bytes #757 read)
            DataSegment {
                linmem_off: 0x100000,
                bytes: vec![0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x20, 0xAA, 0xBB],
            },
            // seg_1: a middle segment, also overwritten by seg_2 at the overlap
            DataSegment {
                linmem_off: 0x100000,
                bytes: vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0x10],
            },
            // seg_2 (last, wins): "gust:os up\n"-like distinct bytes
            DataSegment {
                linmem_off: 0x100000,
                bytes: b"gust:os up\n".to_vec(),
            },
        ]
    }

    /// The load-bearing non-vacuous gate: the SAME validator must go RED on the
    /// `.position()` (first-match, wrong) resolution and GREEN on `.rposition()`
    /// (last-match, correct) — for an overlapping-segment module. A validator
    /// green on both would be vacuous. The policy is an ARGUMENT (`last_wins`),
    /// so this is a permanent test, not a one-time source revert. (The
    /// end-to-end revert-through-main.rs RED lives in the synth-cli fixture.)
    #[test]
    fn red_on_first_match_green_on_last_match() {
        let segs = overlapping_segments();
        // Access the byte at linmem 0x100008 — the classic #757 access. All
        // three segments cover it with distinct bytes.
        let c = 0x100008;
        assert_eq!(segs[0].bytes[8], 0xAA); // seg_0 stale
        assert_eq!(segs[2].bytes[8], b'u'); // seg_2 runtime-correct ("...s Up\n"[8])

        // WRONG policy (#757: .position(), first match) -> seg_0 -> RED.
        let wrong = resolve_owner(&segs, c, /* last_wins */ false).unwrap();
        assert_eq!(wrong.seg_index, 0, "first-match must pick seg_0");
        let red = validate_reloc_resolutions(&segs, std::slice::from_ref(&wrong));
        match red {
            Verdict::Mismatch(m) => {
                assert_eq!(m.len(), 1);
                assert_eq!(m[0].seg_index, 0);
                assert_eq!(m[0].access_addr, c);
                assert_eq!(m[0].served, 0xAA, "seg_0 serves the stale byte");
                assert_eq!(m[0].runtime, b'u', "runtime image (seg_2) owns 'u'");
            }
            Verdict::Consistent => {
                panic!("VACUOUS: validator accepted the #757 wrong-segment resolution")
            }
        }

        // CORRECT policy (.rposition(), last match) -> seg_2 -> GREEN.
        let right = resolve_owner(&segs, c, /* last_wins */ true).unwrap();
        assert_eq!(right.seg_index, 2, "last-match must pick seg_2");
        assert_eq!(
            validate_reloc_resolutions(&segs, std::slice::from_ref(&right)),
            Verdict::Consistent,
            "the runtime-correct resolution must pass"
        );
    }

    /// Non-overlapping segments: every address is in exactly one segment, so
    /// first-match == last-match and both policies pass (no regression on the
    /// common case).
    #[test]
    fn non_overlapping_both_policies_consistent() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x1000,
                bytes: vec![1, 2, 3, 4],
            },
            DataSegment {
                linmem_off: 0x2000,
                bytes: vec![5, 6, 7, 8],
            },
        ];
        for &c in &[0x1002u32, 0x2003] {
            let a = resolve_owner(&segs, c, false).unwrap();
            let b = resolve_owner(&segs, c, true).unwrap();
            assert_eq!(a.seg_index, b.seg_index);
            assert_eq!(validate_reloc_resolutions(&segs, &[a]), Verdict::Consistent);
            assert_eq!(validate_reloc_resolutions(&segs, &[b]), Verdict::Consistent);
        }
    }

    /// Partial overlap: a later segment overwrites only the TAIL of an earlier
    /// one. An address in the overwritten tail must resolve to the later
    /// segment; first-match (earlier) is RED there.
    #[test]
    fn partial_overlap_tail_wins() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x100,
                bytes: vec![0x10, 0x11, 0x12, 0x13, 0x14, 0x15],
            },
            // overwrites [0x104, 0x108) with distinct bytes
            DataSegment {
                linmem_off: 0x104,
                bytes: vec![0xF4, 0xF5, 0xF6, 0xF7],
            },
        ];
        let c = 0x104; // in the overwritten tail
        let wrong = resolve_owner(&segs, c, false).unwrap();
        assert_eq!(wrong.seg_index, 0);
        assert!(matches!(
            validate_reloc_resolutions(&segs, &[wrong]),
            Verdict::Mismatch(_)
        ));
        let right = resolve_owner(&segs, c, true).unwrap();
        assert_eq!(right.seg_index, 1);
        assert_eq!(
            validate_reloc_resolutions(&segs, &[right]),
            Verdict::Consistent
        );

        // An address in the NON-overwritten head resolves to seg_0 under both.
        let head = resolve_owner(&segs, 0x100, false).unwrap();
        assert_eq!(head.seg_index, 0);
        assert_eq!(
            validate_reloc_resolutions(&segs, &[head]),
            Verdict::Consistent
        );
    }

    /// Out-of-range resolution (a broken retargeting) is a mismatch.
    #[test]
    fn out_of_range_is_mismatch() {
        let segs = vec![DataSegment {
            linmem_off: 0,
            bytes: vec![1, 2, 3],
        }];
        let bad = RelocResolution {
            seg_index: 0,
            addend: 99,
            label: "oob".into(),
        };
        assert!(matches!(
            validate_reloc_resolutions(&segs, &[bad]),
            Verdict::Mismatch(_)
        ));
    }
}
