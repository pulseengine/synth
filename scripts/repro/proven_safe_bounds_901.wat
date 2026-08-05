;; VCR-MEM-004 / #901 — the ProvenSafeBoundsChecker fixture.
;;
;; ONE function carrying BOTH halves of the safety contract, so a single
;; compiled binary demonstrates the whole thing:
;;
;;   PROVEN half   — `$base = 256 + (slot & 63) * 16` is entry-independently
;;                   within [256, 1264) for ANY runtime `$slot`, so every
;;                   access off `$base` is in-bounds against the declared
;;                   1-page (65536 B) minimum. This is exactly the verdict
;;                   scry's interval + known-bits domains produce
;;                   (`region_in_bounds`, scry FEAT-046). Five accesses.
;;
;;   NOT-PROVEN half — `$raw` is an unconstrained i32 parameter used directly
;;                   as an address. No analysis can bound it, so scry never
;;                   lists these sites. Three accesses. They MUST keep their
;;                   `--safety-bounds software` guard and MUST still trap when
;;                   driven out of the page — that is the "absence means NOT
;;                   PROVEN, never UNSAFE" property, executable.
;;
;; Under `--safety-bounds software` all EIGHT accesses carry the #752
;; wraparound-safe inline guard (SUB/CMP/BHS/UDF/CMP/BLS/UDF + the address
;; ADD — 16 B per site). With scry's verdicts covering only the five proven
;; sites, exactly five guards fall and exactly three remain.
;;
;; The record layout mirrors a scheduler task record (16 B each, base 256):
;;   state u8 @0 · prio u8 @1 · flags u16 @2 · deadline u32 @4 · budget u32 @8
;;
;; Operator indices (the `pc` key space — 0-based within the function body,
;; the wasmparser operator index space) are pinned in the comments below and
;; re-derived by the oracles, so a decoder drift is visible rather than silent.
;;
;; Oracles: crates/synth-cli/tests/proven_safe_bounds_901.rs (byte evidence +
;; the three fail-closed refusals) and
;; scripts/repro/proven_safe_bounds_901_differential.py (execution), both
;; CI-wired in the proven-safe-oracle job.
(module
  (memory (export "mem") 1)
  (func (export "probe") (param $slot i32) (param $raw i32) (result i32)
    (local $base i32)
    (local $acc i32)
    ;; ---- base = 256 + (slot & 63) * 16 : PROVABLY in [256, 1264) ----
    local.get $slot        ;; op 0
    i32.const 63           ;; op 1
    i32.and                ;; op 2
    i32.const 4            ;; op 3
    i32.shl                ;; op 4
    i32.const 256          ;; op 5
    i32.add                ;; op 6
    local.set $base        ;; op 7

    ;; ---- PROVEN accesses (5) ----
    local.get $base        ;; op 8
    i32.load8_u            ;; op 9   PROVEN  1 B
    local.get $base        ;; op 10
    i32.load8_u offset=1   ;; op 11  PROVEN  1 B
    i32.add                ;; op 12
    local.get $base        ;; op 13
    i32.load16_u offset=2  ;; op 14  PROVEN  2 B
    i32.add                ;; op 15
    local.get $base        ;; op 16
    i32.load offset=4      ;; op 17  PROVEN  4 B
    i32.add                ;; op 18
    local.set $acc         ;; op 19
    local.get $base        ;; op 20
    i32.const 2            ;; op 21
    i32.store8             ;; op 22  PROVEN  1 B  (state := 2, "polled")

    ;; ---- NOT-PROVEN accesses (3): `$raw` is unconstrained ----
    local.get $raw         ;; op 23
    i32.load               ;; op 24  NOT PROVEN 4 B — must still trap OOB
    local.get $acc         ;; op 25
    i32.add                ;; op 26
    local.set $acc         ;; op 27
    local.get $raw         ;; op 28
    i32.load8_u offset=3   ;; op 29  NOT PROVEN 1 B — must still trap OOB
    local.get $acc         ;; op 30
    i32.add                ;; op 31
    local.set $acc         ;; op 32
    local.get $raw         ;; op 33
    local.get $acc         ;; op 34
    i32.store offset=8     ;; op 35  NOT PROVEN 4 B — must still trap OOB

    local.get $acc))       ;; op 36 (+ implicit End = op 37)
