;; VCR-PERF-002 Phase 3+ (#494) — redundant-mask (narrowing) elision fixture.
;;
;; A representative dissolved DSP kernel: pack two lanes into one word,
;; `lo | (hi << 11)`. Each lane is masked with `& 0x7FF` (11 bits). When loom
;; proves both lanes are already in [0, 2047] (a wsc.facts ValueRange premise
;; appended by the differential harness), each `x & 0x7FF == x` — the masks are
;; provably the identity and synth deletes them. LLVM keeps them: a dissolved
;; primitive gives it no range on the params. 0x7FF is NOT a Thumb-2 modified
;; immediate and is NOT uxtb/uxth-foldable, so the flag-off baseline emits
;; `movw + and` per mask — an unambiguous 2-instruction-per-mask byte win.
;;
;; Value ids (0-based operator index within the body):
;;   0 = local.get $lo   ← fact target (lane bound)
;;   3 = local.get $hi   ← fact target (lane bound)
(module
  (func $gust_kernel (export "gust_kernel") (param $lo i32) (param $hi i32) (result i32)
    local.get $lo    ;; 0
    i32.const 0x7FF  ;; 1
    i32.and          ;; 2  lo & 0x7FF  (redundant under the proven bound)
    local.get $hi    ;; 3
    i32.const 0x7FF  ;; 4
    i32.and          ;; 5  hi & 0x7FF  (redundant under the proven bound)
    i32.const 11     ;; 6
    i32.shl          ;; 7  hi << 11
    i32.or))         ;; 8  lo | (hi << 11)
