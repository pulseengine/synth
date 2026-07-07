# `wsc.facts` — binary encoding, schema v1 (VCR-PERF-002 / #494 Phase 1)

Status: **implemented (ingestion side)**. This is the concrete binary contract
for the `wsc.facts` custom section described in
`proof-carrying-specialization.md` ("The contract (what loom forwards)"). It
resolves loom#231 open questions 1 (keying / value identification) and 2
(binary encoding) on the consumer side; loom's emitter co-designs against this
document.

Parser: `crates/synth-core/src/wsc_facts.rs` (`parse_wsc_facts`), invoked from
`decode_wasm_module`'s custom-section arm, threaded into
`CompileConfig::wsc_facts` / `CompileConfig::current_func_facts`. Phase 1 has
**no consumer**: parsed facts change zero bytes of output by construction.

## Container

A standard wasm custom section (id 0) named exactly `wsc.facts`, a sibling of
`wsc.transformation.attestation`. If several `wsc.facts` sections appear, only
the **first** is honored (later duplicates are ignored — one prover, one
section).

## Fail-safe skew rule (normative, loom#231 Q4)

Facts are **optional accelerators** — there is NO error path from this section
that changes a compilation outcome. Every ignore/skip below is surfaced as a
stderr **warning** (the skew diagnostic; rivet VCR-PERF-002: "ignored with a
diagnostic, never an error"):

- missing section → no facts;
- unknown schema version → the whole section is ignored;
- structurally unparseable section (truncated framing, count overrun,
  body-length overrun) → the whole section is ignored, **including any facts
  already decoded** from it (an unparseable section is not trusted piecemeal);
- unknown fact kind → that record is skipped via its length prefix, the rest
  of the section is still consumed (forward-compatible: a newer loom may emit
  kinds an older synth does not know);
- known fact kind whose body does not decode to exactly the expected fields
  (short body, trailing bytes, over-long LEB) → that record alone is dropped
  (it is treated exactly like an unknown kind: a newer emitter may have
  extended the body).

The facts-absent compile is byte-identical to baseline by construction, and
Phase 1 keeps the facts-present compile byte-identical too (no consumer).

## Payload layout

All multi-byte integers are LEB128, exactly as in the wasm core spec:
`u32`/`u64` are unsigned LEB128 (at most 5/10 bytes), `s64` is signed LEB128
(at most 10 bytes).

```
payload := version:byte(=0x01)
           count:u32
           fact[count]

fact    := kind:byte
           func_index:u32          ; full wasm function index (imports first)
           value_id:u32            ; see "Value identification" below
           body_len:u32            ; length prefix — enables unknown-kind skip
           body:byte[body_len]
```

The version byte comes **first** so any future layout change is detectable
before a single record is read. `count` is the number of `fact` records; the
payload must contain exactly `count` well-framed records (extra trailing bytes
after the last record make the section structurally unparseable → ignored).

### Fact kinds (silicon-payoff order, per the design doc)

| kind | name | body | meaning (premise `P`) |
|---|---|---|---|
| `0x01` | value-range | `lo:s64 hi:s64` | the i32/i64 value ∈ `[lo, hi]` (signed, inclusive both ends) |
| `0x02` | shift-bound | `bound:u32` | the shift-amount value is `< bound` (e.g. 32 or 64 — bare `lsl/lsr`, no mask) |
| `0x03` | divisor-nonzero | (empty) | the divisor value is never 0 (the `div/rem` trap guard is dead) |
| `0x04` | in-bounds-access | `access_width:u32` | the address value plus an `access_width`-byte access stays within linear-memory bounds (the bounds check is dead) |
| `0x05` | select-totality | (empty) | both `select` arms are safe to evaluate — branchless `IT` lowering admissible (pairs with VCR-SEL-004) |
| `0x06` | memory-disjointness | `other_value_id:u32` | the address value and the address produced by `other_value_id` (same function) never alias — values may stay in registers across the store |
| other | — | skipped via `body_len` | unknown to this synth; ignored |

`0x00` is deliberately not assigned (a zeroed buffer never parses as a valid
fact kind).

### Value identification (loom#231 Q1)

`value_id` is the **0-based index of the producing operator within the
function body's code-section operator sequence** — the same index space as
synth's decoded `FunctionOps::ops` / `FunctionOps::op_offsets` (and hence the
`source_line` op-index the selector already tracks). "Producing operator"
means the wasm instruction whose result the fact constrains (for
divisor-nonzero: the instruction producing the divisor operand; for
in-bounds-access / memory-disjointness: the instruction producing the
address).

Rationale: this is the only identification both sides can compute without a
shared SSA numbering — loom emits post-optimization binaries, so its final
operator order IS what synth decodes; no id map has to travel alongside the
facts. A fact whose `value_id` is out of range for its function is vacuous
(names nothing) and any Phase-2 consumer must ignore it — Phase 1 stores it
as-is.

`func_index` is the full function index (imported functions first, then
locally defined), the same space as `FunctionOps::index`.

## Versioning

`version = 0x01` is this document. Any incompatible layout change bumps the
version byte; an old synth then ignores the whole section (fail-safe skew),
and a new synth may keep a v1 reader. Backward-compatible growth does **not**
need a bump: new fact kinds get new `kind` bytes, and extending an existing
kind's body is expressed as a NEW kind (bodies are fixed per kind — a longer
body on an existing kind is dropped per the skew rule above).

## Worked example

A single value-range fact `v ∈ [524, 1524]` on function 3, value 7 (the
`gust_mix` clamp premise):

```
01                 ; version 1
01                 ; count = 1
01                 ; kind = value-range
03                 ; func_index = 3
07                 ; value_id = 7
04                 ; body_len = 4
8c 04              ; lo = 524  (signed LEB128)
f4 0b              ; hi = 1524 (signed LEB128)
```

Wrapped in the custom section: `00 <section_size:u32> 09 "wsc.facts" <payload>`.

## Phasing recap

- **Phase 1 (this document + parser): ingestion only.** Facts land in
  `CompileConfig::wsc_facts` (whole-module table) and
  `CompileConfig::current_func_facts` (the compile driver filters per
  function, mirroring `func_params_i64`/`current_func_params_i64`). Zero
  codegen change; the integration gate proves a facts-carrying module
  compiles `.text`-byte-identical to the stripped module.
- **Phase 2+**: consumption per `proof-carrying-specialization.md` — every
  elision behind `SYNTH_FACT_SPEC` plus a per-elision ordeal obligation.
