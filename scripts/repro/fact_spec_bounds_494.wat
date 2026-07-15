;; #494 bounds-elision × #390 guard_bool — the gust_poll-shaped fixture.
;;
;; One scheduler-poll round over a task-record array in linear memory:
;; records are 16 B each at base 256, indexed by $slot. Fields:
;;   state  u8  @0     prio   u8  @1     flags  u16 @2
;;   deadline u32 @4   budget u32 @8     ticks  u32 @12
;;
;; Under `--safety-bounds software` every one of the EIGHT accesses carries
;; the 4-instruction inline guard (ADD ip; CMP ip, r10; BLO +0; UDF #0 —
;; instruction_selector.rs `generate_*_with_bounds_check`). A `wsc.facts`
;; ValueRange premise `slot ∈ [0, 63]` (value_id 0 = the first `local.get`)
;; proves every access's last byte < 65536 (the declared 1-page minimum), so
;; all eight guards fall to
;;   UNSAT( P ∧ trap_mem_oob(zext64(index) + offset, size, 65536) )
;; — certificate-checked per site by the fact-spec pass (SYNTH_FACT_SPEC=1).
;;
;; Oracles: crates/synth-cli/tests/fact_spec_bounds_494.rs (byte evidence)
;; and scripts/repro/fact_spec_bounds_494_differential.py (four-way
;; execution differential), both CI-wired in the fact-spec-oracle job.
(module
  (memory (export "mem") 1)
  (func (export "poll") (param $slot i32) (result i32)
    (local $base i32)
    (local $acc i32)
    ;; base = 256 + slot*16
    local.get $slot        ;; op 0  <- ValueRange fact target (value_id 0)
    i32.const 4            ;; op 1
    i32.shl                ;; op 2
    i32.const 256          ;; op 3
    i32.add                ;; op 4
    local.set $base        ;; op 5
    ;; acc = state + prio + flags + deadline + budget
    local.get $base        ;; op 6
    i32.load8_u            ;; op 7   guarded byte load
    local.get $base        ;; op 8
    i32.load8_u offset=1   ;; op 9   guarded byte load
    i32.add                ;; op 10
    local.get $base        ;; op 11
    i32.load16_u offset=2  ;; op 12  guarded halfword load
    i32.add                ;; op 13
    local.get $base        ;; op 14
    i32.load offset=4      ;; op 15  guarded word load
    i32.add                ;; op 16
    local.get $base        ;; op 17
    i32.load offset=8      ;; op 18  guarded word load
    i32.add                ;; op 19
    local.set $acc         ;; op 20
    ;; ticks++
    local.get $base        ;; op 21
    local.get $base        ;; op 22
    i32.load offset=12     ;; op 23  guarded word load
    i32.const 1            ;; op 24
    i32.add                ;; op 25
    i32.store offset=12    ;; op 26  guarded word store
    ;; state := 2 (polled)
    local.get $base        ;; op 27
    i32.const 2            ;; op 28
    i32.store8             ;; op 29  guarded byte store
    local.get $acc))       ;; op 30 (+ implicit End = op 31)
