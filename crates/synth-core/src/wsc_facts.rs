//! `wsc.facts` custom-section ingestion — VCR-PERF-002 / #494 **Phase 1**.
//!
//! loom (the PROVER, loom#231/loom#240) forwards invariants its Z3 translation
//! validator already discharges in a custom section named `wsc.facts` (sibling
//! of `wsc.transformation.attestation`), keyed by `(function index, value id)`.
//! synth is a CONDITIONAL optimizer: a later phase consumes each fact as a
//! premise behind a per-elision ordeal obligation (see
//! `docs/design/proof-carrying-specialization.md`). THIS module is ingestion
//! only — parse and represent; **no codegen path reads the result yet**, so
//! emitted bytes are unchanged by construction (frozen-safe).
//!
//! Binary contract: `docs/design/wsc-facts-encoding.md` (schema v1). The
//! normative fail-safe skew rule (loom#231 Q4) is implemented here:
//!
//! - missing section / unknown version / structurally unparseable section →
//!   NO facts (the whole section is ignored, never an error);
//! - unknown fact kind → that record is skipped via its length prefix;
//! - known kind whose body doesn't decode exactly → that record is dropped.
//!
//! Facts are optional accelerators: there is no error path out of this module.
//! [`parse_wsc_facts`] is total — it returns a (possibly empty) fact list for
//! every input.

/// Name of the custom section loom emits (loom#231).
pub const WSC_FACTS_SECTION_NAME: &str = "wsc.facts";

/// Schema version this parser understands. The version byte is FIRST in the
/// payload so any incompatible future layout is detected before a single
/// record is read (fail-safe skew: unknown version ⇒ whole section ignored).
pub const WSC_FACTS_SCHEMA_VERSION: u8 = 1;

/// One proven invariant forwarded by loom, keyed by `(function index, value
/// id)`. `value_id` is the 0-based index of the producing operator within the
/// function body's operator sequence — the same index space as
/// [`FunctionOps::ops`]/[`FunctionOps::op_offsets`] (loom#231 Q1; see the
/// encoding doc's "Value identification"). Phase 1 stores facts verbatim; an
/// out-of-range `value_id` is vacuous and a Phase-2 consumer must ignore it.
///
/// [`FunctionOps::ops`]: crate::wasm_decoder::FunctionOps::ops
/// [`FunctionOps::op_offsets`]: crate::wasm_decoder::FunctionOps::op_offsets
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WscFact {
    /// Full wasm function index (imported functions first, then local ones) —
    /// the same space as [`FunctionOps::index`].
    ///
    /// [`FunctionOps::index`]: crate::wasm_decoder::FunctionOps::index
    pub func_index: u32,
    /// 0-based producing-operator index within the function body (see above).
    pub value_id: u32,
    /// The invariant itself.
    pub kind: FactKind,
}

/// The fact kinds of encoding schema v1, in silicon-payoff order (the numbers
/// are the on-wire `kind` bytes; `0x00` is deliberately unassigned so a zeroed
/// buffer never parses as a fact).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FactKind {
    /// `0x01` — the value is within `[lo, hi]`, signed, inclusive both ends
    /// (drives the dead-clamp elision, the `gust_mix` shape).
    ValueRange { lo: i64, hi: i64 },
    /// `0x02` — the shift amount is `< bound` (bare `lsl/lsr`, no mask).
    ShiftBound { bound: u32 },
    /// `0x03` — the divisor is never zero (the `div/rem` trap guard is dead).
    DivisorNonZero,
    /// `0x04` — the address plus an `access_width`-byte access stays within
    /// linear-memory bounds (the bounds check is dead).
    InBoundsAccess { access_width: u32 },
    /// `0x05` — both `select` arms are safe to evaluate: branchless `IT`
    /// lowering is admissible (pairs with VCR-SEL-004).
    SelectTotality,
    /// `0x06` — this address and the one produced by `other_value_id` (same
    /// function) never alias: values may stay in registers across the store.
    MemoryDisjointness { other_value_id: u32 },
}

/// Result of parsing a `wsc.facts` payload: the facts plus the diagnostic
/// counters the decoder surfaces as WARNINGS (never errors — the rivet
/// `VCR-PERF-002` phase-1 criterion is "ignored with a diagnostic, never an
/// error"). `Default` is the missing-section value: no facts, nothing to
/// report.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WscFactsParse {
    /// The facts that decoded cleanly. Empty whenever `section_ignored` is set.
    pub facts: Vec<WscFact>,
    /// `Some(reason)` when the WHOLE section was ignored: unknown schema
    /// version or structural unparseability (truncated/overrun framing,
    /// trailing bytes). Facts already decoded are dropped too — an
    /// unparseable section is not trusted piecemeal.
    pub section_ignored: Option<String>,
    /// Records dropped individually while the section itself parsed: unknown
    /// fact kinds (a newer loom) and known kinds whose length-prefixed body
    /// was not exactly the v1 fields (an extended body). Emitter/consumer
    /// skew signal — worth a warning, never an error.
    pub records_skipped: u32,
}

/// Parse a `wsc.facts` custom-section payload (schema v1). TOTAL by design —
/// this is the fail-safe skew rule (loom#231 Q4) and there is deliberately no
/// `Result` in the signature: facts are optional accelerators, so no input can
/// produce an error that changes a compilation outcome.
///
/// Whole-section ignore (reported via [`WscFactsParse::section_ignored`]):
/// unknown schema version, truncated/overrun framing, count mismatch, or
/// trailing bytes after the last record. Per-record skip (counted in
/// [`WscFactsParse::records_skipped`], parsing continues): unknown fact kinds
/// and known kinds whose length-prefixed body doesn't decode to exactly the
/// expected fields.
pub fn parse_wsc_facts(payload: &[u8]) -> WscFactsParse {
    let mut out = WscFactsParse::default();
    if parse_wsc_facts_inner(payload, &mut out).is_none() {
        return WscFactsParse {
            facts: Vec::new(),
            section_ignored: Some(
                "unknown schema version or truncated/overrun record framing".to_string(),
            ),
            records_skipped: 0,
        };
    }
    out
}

/// Structural parse into `out`: `None` ⇒ the whole section is unparseable and
/// must be ignored entirely (including records already decoded into `out`).
fn parse_wsc_facts_inner(payload: &[u8], out: &mut WscFactsParse) -> Option<()> {
    let mut r = Reader::new(payload);
    if r.byte()? != WSC_FACTS_SCHEMA_VERSION {
        return None;
    }
    let count = r.leb_u32()?;
    for _ in 0..count {
        let kind = r.byte()?;
        let func_index = r.leb_u32()?;
        let value_id = r.leb_u32()?;
        let body_len = r.leb_u32()?;
        let body = r.bytes(body_len as usize)?;
        // Per-record tolerance: an unknown kind byte, or a known kind whose
        // body isn't exactly the expected fields (a newer emitter may have
        // extended it), drops THIS record only — the framing above already
        // consumed it, so the rest of the section still parses.
        match decode_body(kind, body) {
            Some(kind) => out.facts.push(WscFact {
                func_index,
                value_id,
                kind,
            }),
            None => out.records_skipped += 1,
        }
    }
    // Trailing bytes after the declared records ⇒ structurally unparseable.
    if !r.is_empty() {
        return None;
    }
    Some(())
}

/// Decode one record body. `None` ⇒ drop the record (unknown kind, or a body
/// that is not exactly the v1 fields for its kind).
fn decode_body(kind: u8, body: &[u8]) -> Option<FactKind> {
    let mut r = Reader::new(body);
    let fact = match kind {
        0x01 => FactKind::ValueRange {
            lo: r.leb_s64()?,
            hi: r.leb_s64()?,
        },
        0x02 => FactKind::ShiftBound {
            bound: r.leb_u32()?,
        },
        0x03 => FactKind::DivisorNonZero,
        0x04 => FactKind::InBoundsAccess {
            access_width: r.leb_u32()?,
        },
        0x05 => FactKind::SelectTotality,
        0x06 => FactKind::MemoryDisjointness {
            other_value_id: r.leb_u32()?,
        },
        _ => return None,
    };
    // Exact-body rule: trailing bytes mean an extended (newer) body — treat
    // like an unknown kind rather than half-reading it.
    if !r.is_empty() {
        return None;
    }
    Some(fact)
}

/// Minimal bounds-checked cursor with wasm-spec LEB128 readers. Hand-rolled
/// (~30 lines) rather than borrowing `wasmparser::BinaryReader` so this
/// contract cannot drift under a wasmparser major bump — the encoding doc is
/// the single source of truth.
struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    fn is_empty(&self) -> bool {
        self.pos >= self.data.len()
    }

    fn byte(&mut self) -> Option<u8> {
        let b = *self.data.get(self.pos)?;
        self.pos += 1;
        Some(b)
    }

    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(n)?;
        let s = self.data.get(self.pos..end)?;
        self.pos = end;
        Some(s)
    }

    /// Unsigned LEB128, max 5 bytes (wasm-spec `u32`).
    fn leb_u32(&mut self) -> Option<u32> {
        let mut result: u32 = 0;
        for shift in [0u32, 7, 14, 21, 28] {
            let b = self.byte()?;
            let low = u32::from(b & 0x7f);
            // Bits that would fall off the top make the encoding invalid.
            if low.checked_shl(shift)? >> shift != low {
                return None;
            }
            result |= low << shift;
            if b & 0x80 == 0 {
                return Some(result);
            }
        }
        None // continuation bit set on the 5th byte
    }

    /// Signed LEB128, max 10 bytes (wasm-spec `s64`).
    fn leb_s64(&mut self) -> Option<i64> {
        let mut result: i64 = 0;
        let mut shift: u32 = 0;
        loop {
            let b = self.byte()?;
            if shift >= 63 {
                // 10th byte: only 1 payload bit left. It must terminate and
                // must be a pure sign-extension byte (0x00 or 0x7f).
                if b & 0x80 != 0 || (b != 0x00 && b != 0x7f) {
                    return None;
                }
                if b == 0x7f {
                    result |= -1i64 << shift;
                }
                return Some(result);
            }
            result |= i64::from(b & 0x7f) << shift;
            shift += 7;
            if b & 0x80 == 0 {
                // Sign-extend from the last payload bit.
                if shift < 64 && b & 0x40 != 0 {
                    result |= -1i64 << shift;
                }
                return Some(result);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Facts-only view for the happy-path assertions; the skew tests assert
    /// the diagnostic fields explicitly.
    fn facts(payload: &[u8]) -> Vec<WscFact> {
        parse_wsc_facts(payload).facts
    }

    // ---- test-side encoder (mirrors docs/design/wsc-facts-encoding.md) ----

    fn leb_u32(mut v: u32, out: &mut Vec<u8>) {
        loop {
            let mut b = (v & 0x7f) as u8;
            v >>= 7;
            if v != 0 {
                b |= 0x80;
            }
            out.push(b);
            if v == 0 {
                return;
            }
        }
    }

    fn leb_s64(mut v: i64, out: &mut Vec<u8>) {
        loop {
            let mut b = (v & 0x7f) as u8;
            v >>= 7; // arithmetic shift
            let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
            if !done {
                b |= 0x80;
            }
            out.push(b);
            if done {
                return;
            }
        }
    }

    fn record(kind: u8, func_index: u32, value_id: u32, body: &[u8]) -> Vec<u8> {
        let mut out = vec![kind];
        leb_u32(func_index, &mut out);
        leb_u32(value_id, &mut out);
        leb_u32(body.len() as u32, &mut out);
        out.extend_from_slice(body);
        out
    }

    fn section(version: u8, records: &[Vec<u8>]) -> Vec<u8> {
        let mut out = vec![version];
        leb_u32(records.len() as u32, &mut out);
        for r in records {
            out.extend_from_slice(r);
        }
        out
    }

    fn value_range_body(lo: i64, hi: i64) -> Vec<u8> {
        let mut b = Vec::new();
        leb_s64(lo, &mut b);
        leb_s64(hi, &mut b);
        b
    }

    // ---- well-formed sections: every v1 fact kind round-trips ----

    #[test]
    fn parses_value_range_494() {
        // The gust_mix premise: v ∈ [524, 1524] on (func 3, value 7).
        let s = section(1, &[record(0x01, 3, 7, &value_range_body(524, 1524))]);
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 3,
                value_id: 7,
                kind: FactKind::ValueRange { lo: 524, hi: 1524 },
            }]
        );
    }

    #[test]
    fn parses_negative_and_extreme_range_bounds_494() {
        let s = section(
            1,
            &[record(0x01, 0, 0, &value_range_body(i64::MIN, i64::MAX))],
        );
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 0,
                value_id: 0,
                kind: FactKind::ValueRange {
                    lo: i64::MIN,
                    hi: i64::MAX,
                },
            }]
        );
    }

    #[test]
    fn parses_shift_bound_494() {
        let mut body = Vec::new();
        leb_u32(32, &mut body);
        let s = section(1, &[record(0x02, 1, 4, &body)]);
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 1,
                value_id: 4,
                kind: FactKind::ShiftBound { bound: 32 },
            }]
        );
    }

    #[test]
    fn parses_divisor_nonzero_494() {
        let s = section(1, &[record(0x03, 2, 9, &[])]);
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 2,
                value_id: 9,
                kind: FactKind::DivisorNonZero,
            }]
        );
    }

    #[test]
    fn parses_in_bounds_access_494() {
        let mut body = Vec::new();
        leb_u32(4, &mut body);
        let s = section(1, &[record(0x04, 5, 11, &body)]);
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 5,
                value_id: 11,
                kind: FactKind::InBoundsAccess { access_width: 4 },
            }]
        );
    }

    #[test]
    fn parses_select_totality_494() {
        let s = section(1, &[record(0x05, 6, 13, &[])]);
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 6,
                value_id: 13,
                kind: FactKind::SelectTotality,
            }]
        );
    }

    #[test]
    fn parses_memory_disjointness_494() {
        let mut body = Vec::new();
        leb_u32(21, &mut body);
        let s = section(1, &[record(0x06, 7, 17, &body)]);
        assert_eq!(
            facts(&s),
            vec![WscFact {
                func_index: 7,
                value_id: 17,
                kind: FactKind::MemoryDisjointness { other_value_id: 21 },
            }]
        );
    }

    #[test]
    fn parses_multiple_facts_in_order_494() {
        let s = section(
            1,
            &[
                record(0x01, 0, 1, &value_range_body(-8, 8)),
                record(0x03, 0, 2, &[]),
            ],
        );
        let facts = facts(&s);
        assert_eq!(facts.len(), 2);
        assert_eq!(facts[0].kind, FactKind::ValueRange { lo: -8, hi: 8 });
        assert_eq!(facts[1].kind, FactKind::DivisorNonZero);
    }

    #[test]
    fn parses_empty_fact_list_494() {
        // A well-formed zero-fact section is NOT a skew condition: no facts,
        // no diagnostics.
        let parsed = parse_wsc_facts(&section(1, &[]));
        assert_eq!(parsed, WscFactsParse::default());
    }

    // ---- fail-safe skew rule: tolerance without any error path ----

    #[test]
    fn unknown_kind_is_skipped_others_kept_494() {
        // kind 0x2A from a future loom, length-prefixed body — skipped via the
        // prefix; the known records around it still parse.
        let s = section(
            1,
            &[
                record(0x03, 0, 1, &[]),
                record(0x2a, 0, 2, &[0xde, 0xad, 0xbe]),
                record(0x05, 0, 3, &[]),
            ],
        );
        let parsed = parse_wsc_facts(&s);
        assert_eq!(parsed.facts.len(), 2);
        assert_eq!(parsed.facts[0].kind, FactKind::DivisorNonZero);
        assert_eq!(parsed.facts[1].kind, FactKind::SelectTotality);
        // The skip is DIAGNOSED (skew signal), not a whole-section ignore.
        assert_eq!(parsed.records_skipped, 1);
        assert_eq!(parsed.section_ignored, None);
    }

    #[test]
    fn kind_zero_is_not_a_fact_494() {
        // 0x00 is deliberately unassigned (zeroed buffers must not parse).
        let s = section(1, &[record(0x00, 0, 0, &[])]);
        assert_eq!(facts(&s), vec![]);
    }

    #[test]
    fn extended_body_on_known_kind_drops_that_record_only_494() {
        // divisor-nonzero with a 2-byte body: a newer emitter extended it —
        // exact-body rule drops it, the neighbor survives.
        let s = section(
            1,
            &[record(0x03, 0, 1, &[0x01, 0x02]), record(0x05, 0, 2, &[])],
        );
        let facts = facts(&s);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].kind, FactKind::SelectTotality);
    }

    #[test]
    fn short_body_on_known_kind_drops_that_record_only_494() {
        // value-range with only `lo` present — the body under-decodes.
        let mut body = Vec::new();
        leb_s64(524, &mut body);
        let s = section(1, &[record(0x01, 0, 1, &body), record(0x03, 0, 2, &[])]);
        let facts = facts(&s);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].kind, FactKind::DivisorNonZero);
    }

    #[test]
    fn version_mismatch_ignores_whole_section_494() {
        for version in [0, 2, 0xff] {
            let parsed = parse_wsc_facts(&section(version, &[record(0x03, 0, 1, &[])]));
            assert_eq!(parsed.facts, vec![]);
            // Whole-section ignore is DIAGNOSED, never an error.
            assert!(parsed.section_ignored.is_some());
        }
    }

    #[test]
    fn empty_and_truncated_sections_ignored_494() {
        assert_eq!(facts(&[]), vec![]); // no version byte
        assert_eq!(facts(&[0x01]), vec![]); // no count
        // count says 1 record, no record bytes follow
        assert_eq!(facts(&[0x01, 0x01]), vec![]);
        // record framing truncated mid-header (kind present, indices missing)
        assert_eq!(facts(&[0x01, 0x01, 0x01]), vec![]);
    }

    #[test]
    fn body_len_overrun_ignores_whole_section_494() {
        // body_len = 200 but only 2 body bytes present — framing overrun, and
        // the earlier GOOD record is dropped too (unparseable ⇒ ignore whole).
        let good = record(0x03, 0, 1, &[]);
        let mut bad = vec![0x01];
        leb_u32(0, &mut bad);
        leb_u32(0, &mut bad);
        leb_u32(200, &mut bad);
        bad.extend_from_slice(&[0xaa, 0xbb]);
        let s = section(1, &[good, bad]);
        assert_eq!(facts(&s), vec![]);
    }

    #[test]
    fn trailing_bytes_after_records_ignore_whole_section_494() {
        let mut s = section(1, &[record(0x03, 0, 1, &[])]);
        s.push(0xff);
        assert_eq!(facts(&s), vec![]);
    }

    #[test]
    fn overlong_leb_ignores_whole_section_494() {
        // func_index as a 6-byte LEB (continuation on the 5th byte) — invalid
        // wasm-spec u32.
        let mut s = vec![0x01, 0x01, 0x03];
        s.extend_from_slice(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x00]); // func_index
        s.push(0x00); // value_id
        s.push(0x00); // body_len
        assert_eq!(facts(&s), vec![]);
    }

    #[test]
    fn garbage_is_ignored_never_panics_494() {
        // A few adversarial byte soups: total function, empty result.
        for garbage in [
            &[0xff_u8, 0xff, 0xff, 0xff][..],
            &[0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff][..],
            &[0x00, 0x00, 0x00][..],
        ] {
            assert_eq!(facts(garbage), vec![]);
        }
    }
}
