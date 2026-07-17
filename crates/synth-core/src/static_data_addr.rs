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
//!
//! # Phase 2 (#777 follow-ups)
//!
//! Phase 1 validated the single resolved **addend byte** per reloc. Phase 2
//! extends coverage to the named follow-up classes:
//!
//! 1. **Multi-byte access spans** ([`validate_reloc_resolutions_spanned`]):
//!    a reloc whose addend byte is runtime-correct can still mis-serve TAIL
//!    bytes — an i32/i64 load starting in segment `K` whose span crosses into
//!    a range a LATER-declared segment owns at runtime (staggered overlap), or
//!    crosses `K`'s packed end into 4-align padding / the next *declared*
//!    (not next *linmem*) segment. The access width is not recorded on
//!    [`crate::backend::CodeRelocation`] (the Abs32 literal is a pointer; its
//!    consumers are ldrb/ldrh/ldr/ldrd), so the span is validated
//!    conservatively out to [`MAX_ACCESS_BYTES`] with one deliberate
//!    tolerance: a span byte whose runtime address NO segment covers is
//!    skipped (implicit-zero linear memory — flagging it would hard-error the
//!    ubiquitous "pointer near the end of a sparse segment, narrow access"
//!    shape). A span byte that IS runtime-covered must match what the packed
//!    blob actually serves at that position, byte-for-byte, so the served
//!    side reads the EMITTED init blob ([`PackedInit`]) — never a recompute.
//! 2. **Dense served images** ([`validate_served_image`] /
//!    [`pack_rom_image`]): the self-contained `--cortex-m` ROM-copy layout
//!    (#758) serves linear memory from ONE dense flash blob copied to RAM at
//!    reset — index = linmem offset, so spans/overlaps are structurally
//!    preserved and the whole obligation reduces to "every blob byte equals
//!    the runtime image byte (later-wins, zero elsewhere)". The same function
//!    with an EMPTY image validates the RISC-V single-base scheme, where the
//!    object ships NO initializer bytes at all and zeroed RAM serves every
//!    address: any nonzero runtime-image byte is then a served/runtime
//!    mismatch (the silent initializer-drop).
//! 3. **AArch64: N/A** — the `-b aarch64` integer subset has no linear-memory
//!    loads/stores (every memory op loud-declines at selection), so compiled
//!    code cannot observe static data; there is nothing to validate.

use std::collections::HashMap;

/// The widest scalar linear-memory access synth can emit (i64.load /
/// i64.store — there is no v128 support on these paths). Conservative span
/// bound used when a reloc's true access width is unknown.
pub const MAX_ACCESS_BYTES: u32 = 8;

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
    /// The original linear-memory access address of the OFFENDING byte
    /// (`seg[K].off + addend + span_byte`).
    pub access_addr: u32,
    /// The byte the packed `.data` serves at that position.
    pub served: u8,
    /// The byte the runtime image holds at `access_addr` (the truth).
    pub runtime: u8,
    /// Which byte of the (potentially multi-byte) access diverges: 0 = the
    /// addend byte itself (the phase-1 check), 1..[`MAX_ACCESS_BYTES`] = a
    /// tail byte of a conservatively-widened span (phase 2).
    pub span_byte: u32,
}

impl AddrMismatch {
    /// A human-readable one-line diagnostic for the compile-time error.
    pub fn describe(&self) -> String {
        let span = if self.span_byte == 0 {
            String::new()
        } else {
            format!(
                " (span byte +{} of a possibly {}-byte access)",
                self.span_byte, MAX_ACCESS_BYTES
            )
        };
        format!(
            "{}: __synth_wasm_seg_{}+0x{:x} -> linmem 0x{:x}{span} serves 0x{:02x} but \
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
                span_byte: 0,
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
                span_byte: 0,
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
                span_byte: 0,
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
                span_byte: 0,
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

/// The EMITTED packed-`.data` init region of the #354 mixed split: each
/// segment's bytes at its 4-aligned packed offset, in declaration order,
/// EXCLUDING the trailing `__synth_globals` slots. Both fields are read back
/// from what the compiler actually laid out / filled — the validator never
/// recomputes the packing (that would mirror-pin the check).
#[derive(Clone, Debug)]
pub struct PackedInit<'a> {
    /// Packed offset of each segment inside the init region (declaration
    /// order, parallel to the segment list).
    pub seg_packed_off: &'a [u32],
    /// The init-region bytes the object will ship (segments + 4-align
    /// padding). A span byte served from BEYOND this region (the globals
    /// slots, or past the blob) can never be a linear-memory byte.
    pub bytes: &'a [u8],
}

/// Phase-2 (#777) per-compilation addressing gate: the phase-1 addend-byte
/// check PLUS a conservative multi-byte span check per reloc.
///
/// For every emitted resolution `(K, A)` and every span byte
/// `j in 0..`[`MAX_ACCESS_BYTES`]:
///
/// - the byte SERVED is read from the emitted init blob at
///   `packed.seg_packed_off[K] + A + j` (the real artifact — for `j = 0` this
///   also pins the blob fill itself: a blob that doesn't hold `seg[K].bytes`
///   verbatim fails here);
/// - the byte OWED is the runtime image at `seg[K].off + A + j` (segments
///   applied in declaration order, later-wins, independent of `K`).
///
/// `j = 0` keeps phase-1 semantics exactly (a missing byte on either side is
/// a broken retargeting → mismatch). For `j > 0` the access width is unknown
/// (see the module docs), so one tolerance applies: when NO segment covers
/// the runtime address, the byte is implicit-zero linear memory and the span
/// byte is SKIPPED — a wide access genuinely reaching there would read packed
/// neighbours instead of zeros, but flagging it would hard-error the common
/// "pointer near a sparse segment's end, narrow access" shape; exact checking
/// of that residue needs a recorded access width (named follow-up). When the
/// runtime address IS covered by some segment, the served byte must match —
/// including bytes past `K`'s packed end (4-align padding or the next
/// *declared* segment) and bytes that escape the init region entirely (both
/// are exactly how a straddling access mis-serves).
pub fn validate_reloc_resolutions_spanned(
    segments: &[DataSegment],
    resolutions: &[RelocResolution],
    packed: &PackedInit<'_>,
) -> Verdict {
    let runtime = runtime_image(segments);
    let mut bad = Vec::new();
    // Phase-1 addend-byte check (byte 0, strict on both sides).
    if let Verdict::Mismatch(m) = validate_reloc_resolutions(segments, resolutions) {
        bad.extend(m);
    }
    for r in resolutions {
        let Some(seg) = segments.get(r.seg_index) else {
            continue; // already reported by the phase-1 pass
        };
        let Some(&poff) = packed.seg_packed_off.get(r.seg_index) else {
            continue; // impossible when layout and segments are parallel
        };
        for j in 0..MAX_ACCESS_BYTES {
            let access_addr = seg.linmem_off.wrapping_add(r.addend).wrapping_add(j);
            // Unknown-width tolerance: runtime-uncovered ⇒ implicit zero ⇒ skip
            // (for j = 0 a missing runtime byte was already flagged by the
            // strict phase-1 pass above).
            let Some(&runtime_byte) = runtime.get(&access_addr) else {
                continue;
            };
            // j = 0: the phase-1 pass already reported a divergent SEGMENT
            // byte; re-checking here would double-report it. Only the blob
            // side remains to pin — fall through when the segment byte is
            // phase-1-green so a blob-fill bug (blob ≠ seg[K].bytes at the
            // addend byte) still fails.
            if j == 0 && seg.bytes.get(r.addend as usize) != Some(&runtime_byte) {
                continue;
            }
            let p = poff as usize + r.addend as usize + j as usize;
            // Served byte: the emitted blob, or "not linear memory at all"
            // when the span escapes the init region (globals slots / past the
            // blob) — that escape can never serve a runtime-covered byte.
            let served = packed.bytes.get(p).copied();
            if served != Some(runtime_byte) {
                bad.push(AddrMismatch {
                    label: r.label.clone(),
                    seg_index: r.seg_index,
                    addend: r.addend,
                    access_addr,
                    served: served.unwrap_or(0),
                    runtime: runtime_byte,
                    span_byte: j,
                });
            }
        }
    }
    if bad.is_empty() {
        Verdict::Consistent
    } else {
        Verdict::Mismatch(bad)
    }
}

/// The verdict of a dense served-image gate ([`validate_served_image`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImageVerdict {
    /// Every linear-memory byte the image (or zeroed RAM) serves equals the
    /// runtime image byte.
    Consistent,
    /// At least one served byte disagrees with the runtime image.
    Mismatch(Vec<ImageMismatch>),
}

/// One dense-image byte that disagrees with the runtime image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImageMismatch {
    /// The linear-memory address (= image index) of the offending byte.
    pub addr: u32,
    /// The byte the image serves (0 when the image doesn't reach `addr` —
    /// zeroed RAM / no initializer shipped).
    pub served: u8,
    /// The byte the runtime image holds there (the truth).
    pub runtime: u8,
}

impl ImageMismatch {
    /// A human-readable one-line diagnostic.
    pub fn describe(&self) -> String {
        format!(
            "linmem 0x{:x} serves 0x{:02x} but the runtime image (segments \
             applied later-wins) owns 0x{:02x}",
            self.addr, self.served, self.runtime
        )
    }
}

/// Total extent of the runtime image: `max(off + len)` over the segments
/// (u64, so a hostile `off + len` cannot wrap — callers bound-check against
/// the linear-memory size before packing).
pub fn image_extent(segments: &[DataSegment]) -> u64 {
    segments
        .iter()
        .map(|s| s.linmem_off as u64 + s.bytes.len() as u64)
        .max()
        .unwrap_or(0)
}

/// Pack the #758 dense ROM init image: a `[0, extent)` blob with every active
/// segment placed AT its linmem offset. `last_wins = true` applies them in
/// declaration order (WASM instantiation semantics — later segments overwrite
/// earlier on overlap); `last_wins = false` applies them in REVERSE order
/// (first-wins — the synthetic miscompile the red-first gate toggles, phase
/// 1's `resolve_owner` pattern). The caller must have bound-checked
/// [`image_extent`] against the linear-memory size (u32 + usize safe here
/// only after that check).
pub fn pack_rom_image(segments: &[DataSegment], last_wins: bool) -> Vec<u8> {
    let mut blob = vec![0u8; image_extent(segments) as usize];
    let place = |blob: &mut Vec<u8>, s: &DataSegment| {
        let at = s.linmem_off as usize;
        blob[at..at + s.bytes.len()].copy_from_slice(&s.bytes);
    };
    if last_wins {
        for s in segments {
            place(&mut blob, s);
        }
    } else {
        for s in segments.iter().rev() {
            place(&mut blob, s);
        }
    }
    blob
}

/// Dense served-image gate: for every address in `[0, image_extent)`, the byte
/// SERVED — `image[addr]`, or `0` when the image doesn't reach `addr` (zeroed
/// RAM; an empty `image` models a target that ships NO initializer bytes, the
/// RISC-V single-base scheme) — must equal the runtime image byte (segments
/// applied in declaration order, later-wins; implicit zero where uncovered).
///
/// The truth side is reconstructed only from the segment list, never from the
/// image, so the gate cannot be satisfied by mirroring the packing code.
pub fn validate_served_image(segments: &[DataSegment], image: &[u8]) -> ImageVerdict {
    let runtime = runtime_image(segments);
    let mut bad = Vec::new();
    // Every image byte must equal the runtime byte (covered ⇒ later-wins
    // segment byte; uncovered ⇒ implicit zero, so initializer garbage in a
    // gap is caught too).
    for (addr, &served) in image.iter().enumerate() {
        let owed = runtime.get(&(addr as u32)).copied().unwrap_or(0);
        if served != owed {
            bad.push(ImageMismatch {
                addr: addr as u32,
                served,
                runtime: owed,
            });
        }
    }
    // Every runtime byte BEYOND the image is served by zeroed RAM, so any
    // nonzero one is un-served (the shipped-no-initializer mismatch). Walk
    // the covered addresses only — uncovered beyond-image bytes are 0 == 0.
    let mut beyond: Vec<(u32, u8)> = runtime
        .into_iter()
        .filter(|&(addr, owed)| addr as u64 >= image.len() as u64 && owed != 0)
        .collect();
    beyond.sort_unstable();
    for (addr, owed) in beyond {
        bad.push(ImageMismatch {
            addr,
            served: 0,
            runtime: owed,
        });
    }
    if bad.is_empty() {
        ImageVerdict::Consistent
    } else {
        ImageVerdict::Mismatch(bad)
    }
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

    /// Pack the mixed-split init region for tests exactly the way main.rs
    /// lays it out: each segment 4-aligned, declaration order.
    fn mixed_pack(segments: &[DataSegment]) -> (Vec<u32>, Vec<u8>) {
        let mut offs = Vec::with_capacity(segments.len());
        let mut cur = 0u32;
        for s in segments {
            cur = cur.next_multiple_of(4);
            offs.push(cur);
            cur += s.bytes.len() as u32;
        }
        let mut blob = vec![0u8; cur as usize];
        for (s, &o) in segments.iter().zip(offs.iter()) {
            blob[o as usize..o as usize + s.bytes.len()].copy_from_slice(&s.bytes);
        }
        (offs, blob)
    }

    /// PHASE-2 RED-FIRST (span class, the #777 follow-up): a STAGGERED overlap
    /// — seg_1 overwrites only the TAIL of seg_0's range — with a reloc whose
    /// addend byte is runtime-correct (owned by seg_0) but whose i32-wide span
    /// crosses into seg_1's runtime-owned bytes. The phase-1 addend-byte
    /// validator is GREEN on it (that is the hole this class names); the
    /// spanned validator must be RED, flagging the exact tail byte. A spanned
    /// validator green here would be vacuous.
    #[test]
    fn phase1_green_but_span_red_on_staggered_overlap() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x10004,
                bytes: vec![0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7],
            },
            // Staggered: overwrites [0x10008, 0x1000C) — seg_0's tail.
            DataSegment {
                linmem_off: 0x10008,
                bytes: vec![0xB0, 0xB1, 0xB2, 0xB3],
            },
        ];
        // Reloc at 0x10006: owner is seg_0 under the CORRECT .rposition()
        // (seg_1 does not contain 0x10006). An i32 load spans 0x10006..0x1000A
        // — bytes +2/+3 are seg_1's at runtime, seg_0's stale in the pack.
        let r = resolve_owner(&segs, 0x10006, true).unwrap();
        assert_eq!(r.seg_index, 0, "correct owner of the addend byte is seg_0");
        // Phase-1 (addend byte only) is GREEN — the documented hole.
        assert_eq!(
            validate_reloc_resolutions(&segs, std::slice::from_ref(&r)),
            Verdict::Consistent,
            "phase 1 must accept the addend byte (it IS runtime-correct)"
        );
        // Phase-2 spanned is RED at span byte +2.
        let (offs, blob) = mixed_pack(&segs);
        let packed = PackedInit {
            seg_packed_off: &offs,
            bytes: &blob,
        };
        match validate_reloc_resolutions_spanned(&segs, std::slice::from_ref(&r), &packed) {
            Verdict::Mismatch(m) => {
                assert_eq!(m[0].span_byte, 2, "first divergent byte is +2");
                assert_eq!(m[0].access_addr, 0x10008);
                assert_eq!(m[0].served, 0xA4, "packed seg_0 serves its stale byte");
                assert_eq!(m[0].runtime, 0xB0, "runtime image owns seg_1's byte");
            }
            Verdict::Consistent => {
                panic!("VACUOUS: spanned validator accepted a straddling stale-tail access")
            }
        }
    }

    /// Linmem-ADJACENT segments whose packed layout PRESERVES adjacency
    /// (4-aligned length, next declaration) — a span crossing the boundary is
    /// served the right bytes, so the spanned validator must stay GREEN (no
    /// false red on the benign crossing).
    #[test]
    fn span_green_on_adjacency_preserving_crossing() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x100,
                bytes: vec![1, 2, 3, 4],
            },
            DataSegment {
                linmem_off: 0x104,
                bytes: vec![5, 6, 7, 8],
            },
        ];
        let (offs, blob) = mixed_pack(&segs);
        let packed = PackedInit {
            seg_packed_off: &offs,
            bytes: &blob,
        };
        let r = resolve_owner(&segs, 0x102, true).unwrap();
        assert_eq!(r.seg_index, 0);
        assert_eq!(
            validate_reloc_resolutions_spanned(&segs, &[r], &packed),
            Verdict::Consistent,
            "packed adjacency == linmem adjacency: the crossing serves the right bytes"
        );
    }

    /// Linmem-adjacent segments whose packed layout BREAKS adjacency (seg_0's
    /// length is not 4-aligned, so the pack inserts padding the linear memory
    /// doesn't have): a span crossing the boundary reads pad zeros instead of
    /// the next segment's bytes — RED.
    #[test]
    fn span_red_on_padding_shifted_crossing() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x100,
                bytes: vec![1, 2, 3], // len 3 → packed pads to 4
            },
            // Linmem-adjacent at 0x103; packed at offset 4 (shifted by 1).
            DataSegment {
                linmem_off: 0x103,
                bytes: vec![5, 6, 7, 8],
            },
        ];
        let (offs, blob) = mixed_pack(&segs);
        let packed = PackedInit {
            seg_packed_off: &offs,
            bytes: &blob,
        };
        let r = resolve_owner(&segs, 0x101, true).unwrap();
        assert_eq!(r.seg_index, 0);
        match validate_reloc_resolutions_spanned(&segs, &[r], &packed) {
            Verdict::Mismatch(m) => {
                // +2 = 0x103: runtime owns seg_1's first byte (5); the pack
                // serves its own pad byte (0).
                assert_eq!(m[0].span_byte, 2);
                assert_eq!(m[0].access_addr, 0x103);
                assert_eq!(m[0].served, 0, "the pack serves 4-align padding");
                assert_eq!(m[0].runtime, 5);
            }
            Verdict::Consistent => panic!("VACUOUS: padding-shifted crossing accepted"),
        }
    }

    /// The unknown-width tolerance: a reloc near the end of a SPARSE segment
    /// (no segment covers the bytes beyond it) must stay GREEN — the span
    /// bytes are implicit-zero linear memory and the common shape is a narrow
    /// access. This is the documented residue, not a bug.
    #[test]
    fn span_green_on_sparse_tail() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x100,
                bytes: vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
            },
            // Far away; between them is implicit-zero linmem.
            DataSegment {
                linmem_off: 0x400,
                bytes: vec![0xFF; 4],
            },
        ];
        let (offs, blob) = mixed_pack(&segs);
        let packed = PackedInit {
            seg_packed_off: &offs,
            bytes: &blob,
        };
        // Last word of seg_0: the conservative 8-byte span runs past the end
        // into uncovered linmem — skipped, not flagged.
        let r = resolve_owner(&segs, 0x108, true).unwrap();
        assert_eq!(r.seg_index, 0);
        assert_eq!(
            validate_reloc_resolutions_spanned(&segs, &[r], &packed),
            Verdict::Consistent,
            "uncovered span bytes are implicit-zero linmem — must not false-red"
        );
    }

    /// A span that escapes the init region entirely (into the globals slots /
    /// past the blob) while the runtime address IS segment-covered: RED — the
    /// pack cannot serve that byte at all. Shape: the LAST-declared segment is
    /// shorter than an earlier one at the same base, so bytes beyond its end
    /// are runtime-owned by the earlier segment but packed nowhere after it.
    #[test]
    fn span_red_on_init_region_escape() {
        let segs = vec![
            DataSegment {
                linmem_off: 0x100,
                bytes: vec![0x11; 8], // covers [0x100, 0x108)
            },
            DataSegment {
                linmem_off: 0x100,
                bytes: vec![0x22; 4], // last-declared owner of [0x100, 0x104)
            },
        ];
        let (offs, blob) = mixed_pack(&segs);
        assert_eq!(blob.len(), 12, "seg_1 is the final packed segment");
        let packed = PackedInit {
            seg_packed_off: &offs,
            bytes: &blob,
        };
        // 0x102 is owned by seg_1 (last); its span bytes +2/+3 (0x104/0x105)
        // are runtime-owned by seg_0 (0x11) but lie past seg_1's packed end =
        // past the whole init region.
        let r = resolve_owner(&segs, 0x102, true).unwrap();
        assert_eq!(r.seg_index, 1);
        match validate_reloc_resolutions_spanned(&segs, &[r], &packed) {
            Verdict::Mismatch(m) => {
                assert_eq!(m[0].span_byte, 2);
                assert_eq!(m[0].access_addr, 0x104);
                assert_eq!(m[0].runtime, 0x11);
            }
            Verdict::Consistent => panic!("VACUOUS: init-region escape accepted"),
        }
    }

    /// The blob-fill pin at the addend byte: segments and resolution are
    /// phase-1-green, but the SHIPPED blob was corrupted at the served
    /// position — the spanned validator must flag it at span byte 0 (phase 1
    /// reads segment bytes and cannot see it).
    #[test]
    fn span_red_on_blob_fill_corruption_at_addend_byte() {
        let segs = vec![DataSegment {
            linmem_off: 0x100,
            bytes: vec![1, 2, 3, 4],
        }];
        let (offs, mut blob) = mixed_pack(&segs);
        let r = resolve_owner(&segs, 0x102, true).unwrap();
        assert_eq!(
            validate_reloc_resolutions(&segs, std::slice::from_ref(&r)),
            Verdict::Consistent,
            "phase 1 (segment bytes) cannot see a blob-fill bug"
        );
        blob[2] = 0xEE; // corrupt the byte the reloc actually serves
        let packed = PackedInit {
            seg_packed_off: &offs,
            bytes: &blob,
        };
        match validate_reloc_resolutions_spanned(&segs, std::slice::from_ref(&r), &packed) {
            Verdict::Mismatch(m) => {
                assert_eq!(m[0].span_byte, 0);
                assert_eq!(m[0].served, 0xEE);
                assert_eq!(m[0].runtime, 3);
            }
            Verdict::Consistent => panic!("VACUOUS: corrupted shipped blob accepted"),
        }
    }

    /// ROM-image RED-FIRST (self-contained class, phase 1's `resolve_owner`
    /// pattern — the overwrite policy is an ARGUMENT): on an overlapping
    /// module the SAME dense-image validator must be RED on the first-wins
    /// pack (`last_wins = false`, the synthetic miscompile) and GREEN on the
    /// declaration-order pack (`last_wins = true`, WASM instantiation
    /// semantics). Green on both would be vacuous.
    #[test]
    fn rom_image_red_on_first_wins_green_on_last_wins() {
        let segs = overlapping_segments();
        let wrong = pack_rom_image(&segs, false);
        match validate_served_image(&segs, &wrong) {
            ImageVerdict::Mismatch(m) => {
                // The classic #757 byte: offset 8 must be seg_2's 'u', but the
                // first-wins image left seg_0's 0xAA there.
                let at8 = m.iter().find(|x| x.addr == 0x100008).expect("addr 8");
                assert_eq!(at8.served, 0xAA);
                assert_eq!(at8.runtime, b'u');
            }
            ImageVerdict::Consistent => {
                panic!("VACUOUS: dense-image validator accepted a first-wins pack")
            }
        }
        let right = pack_rom_image(&segs, true);
        assert_eq!(
            validate_served_image(&segs, &right),
            ImageVerdict::Consistent,
            "declaration-order (later-wins) pack must validate"
        );
    }

    /// A dense image with initializer garbage in an uncovered GAP is a
    /// mismatch (runtime linmem is zero there), and a truncated image whose
    /// missing tail is all-zero at runtime is fine (zeroed RAM serves it).
    #[test]
    fn rom_image_gap_garbage_red_zero_tail_green() {
        let segs = vec![
            DataSegment {
                linmem_off: 0,
                bytes: vec![1, 2],
            },
            DataSegment {
                linmem_off: 8,
                bytes: vec![0, 0, 0, 0],
            },
        ];
        // Garbage at uncovered addr 4.
        let mut img = pack_rom_image(&segs, true);
        img[4] = 0xCC;
        assert!(matches!(
            validate_served_image(&segs, &img),
            ImageVerdict::Mismatch(_)
        ));
        // Image truncated to the nonzero prefix: the all-zero tail (gap +
        // zero segment) is served by zeroed RAM — consistent.
        assert_eq!(
            validate_served_image(&segs, &[1, 2]),
            ImageVerdict::Consistent
        );
    }

    /// RISC-V single-base shape: the object ships NO initializer image
    /// (`image = &[]`, zeroed RAM serves everything). Nonzero segment bytes
    /// are un-served (RED, the silent initializer-drop); an all-zero segment
    /// — or an earlier nonzero byte OVERWRITTEN to zero by a later segment —
    /// is served correctly by zeroed RAM (GREEN). The overwrite case keeps
    /// this non-vacuous as a later-wins check, not a "any nonzero data" grep.
    #[test]
    fn zero_served_image_red_on_nonzero_green_on_zeroed() {
        let nonzero = vec![DataSegment {
            linmem_off: 16,
            bytes: vec![1, 2, 3, 4],
        }];
        match validate_served_image(&nonzero, &[]) {
            ImageVerdict::Mismatch(m) => {
                assert_eq!(m[0].addr, 16);
                assert_eq!(m[0].served, 0);
                assert_eq!(m[0].runtime, 1);
            }
            ImageVerdict::Consistent => panic!("VACUOUS: dropped nonzero initializer accepted"),
        }
        let zeroed = vec![
            DataSegment {
                linmem_off: 16,
                bytes: vec![1, 2, 3, 4],
            },
            // Later segment overwrites the nonzero bytes with zeros: the
            // runtime image is all-zero, so zeroed RAM serves it correctly.
            DataSegment {
                linmem_off: 16,
                bytes: vec![0, 0, 0, 0],
            },
        ];
        assert_eq!(
            validate_served_image(&zeroed, &[]),
            ImageVerdict::Consistent
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
