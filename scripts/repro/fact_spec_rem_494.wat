;; VCR-PERF-002 Phase 3+ (#494) — constant-divisor rem_u IDENTITY elision.
;;
;; A representative embedded kernel: fold a raw channel reading into its
;; bucket index, `x rem_u 1000`. The divisor 1000 is a LITERAL i32.const, so
;; the `rem_u` cannot trap (traps only on divisor == 0; rem has no INT_MIN/-1
;; overflow). When loom proves the reading is already in [0, 999] (a wsc.facts
;; ValueRange premise appended by the differential harness), `x rem_u 1000 == x`
;; — the modulo is the identity and synth deletes the whole op, letting `x`
;; flow through.
;;
;; LLVM keeps it: a dissolved primitive gives clang no range on the param, so
;; `-Os` lowers `x % 1000` to the full reciprocal-multiply-subtract sequence
;; (movw + movt + umull + lsr + mov.w + mls = ~22 B on Thumb-2). synth-spec
;; emits a bare `bx lr` shape (the identity) — a large, ordeal-certified win
;; LLVM structurally cannot reach.
;;
;; Value ids (0-based operator index within the body):
;;   0 = local.get $x   ← fact target (reading bound)
(module
  (func $gust_scale (export "gust_scale") (param $x i32) (result i32)
    local.get $x     ;; 0
    i32.const 1000   ;; 1  literal divisor (≠0 ⇒ no trap)
    i32.rem_u))      ;; 2  x % 1000  (identity under the proven bound)
