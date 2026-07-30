;; #851 lane L3 — aarch64 `call_indirect` execution differential fixture.
;;
;; Shaped so all THREE WASM §4.4.8 traps are reachable from an exported entry
;; whose index is a PARAMETER (the realistic shape — and the one that needed
;; param homing to compile at all).
;;
;; TWO tables, because the emitted funcref region is CONTIGUOUS across tables:
;;
;;   region slot  0     1     2     3      4     5
;;   table 0      $add  $sub  $neg  NULL
;;   table 1                               $mul  $add
;;
;; That makes index 4 of TABLE 0 land on a slot that is fully valid — a real
;; `$bin` trampoline whose structural class id MATCHES what "bin" expects. So
;; the out-of-range trap can only come from the bounds guard: a lowering that
;; dropped it would happily CALL table 1's `$add` and return 13 where wasmtime
;; traps. Without a second table the type check masks a missing bounds guard
;; (past-the-end bytes read as class id 0, which mismatches anyway) and the
;; oracle would pass a genuinely unsound compiler.
;;
;; `$bin2` is a structurally-identical DUPLICATE of `$bin`: dispatching it at a
;; `$bin` function MUST succeed, because WASM type equality is structural. A
;; lowering that compared raw type INDICES would trap there — a trap where
;; wasmtime calls, the mirror-image bug that "just always trap" would hide.
(module
  (type $bin  (func (param i32 i32) (result i32)))
  (type $un   (func (param i32) (result i32)))
  (type $bin2 (func (param i32 i32) (result i32)))   ;; structurally == $bin
  (type $void (func))

  (table 4 funcref)                                   ;; table 0
  (table 2 funcref)                                   ;; table 1
  (elem (i32.const 0) $add $sub $neg)                  ;; table 0; slot 3 NULL
  (elem (table 1) (offset (i32.const 0)) func $mul $add)

  (func $add (type $bin) (i32.add (local.get 0) (local.get 1)))
  (func $sub (type $bin) (i32.sub (local.get 0) (local.get 1)))
  (func $neg (type $un)  (i32.sub (i32.const 0) (local.get 0)))
  ;; Table 1 slot 0 deliberately holds a DIFFERENT function than region slot 0,
  ;; so dropping the per-table base offset changes the RESULT (30 vs 13) rather
  ;; than silently agreeing.
  (func $mul (type $bin) (i32.mul (local.get 0) (local.get 1)))

  ;; Dispatch a BINARY callee through TABLE 0. Index from a parameter.
  ;;   idx 0/1 -> add/sub    idx 2 -> TYPE MISMATCH ($neg is unary)
  ;;   idx 3   -> NULL SLOT  idx >= 4 -> OUT OF RANGE (and idx 4/5 land on
  ;;                                     table 1's valid, type-matching slots)
  (func (export "bin") (param i32 i32 i32) (result i32)
    (call_indirect 0 (type $bin)
      (local.get 0) (local.get 1) (local.get 2)))

  ;; The DUPLICATE type: must behave EXACTLY like "bin" (structural equality).
  (func (export "bin_dup") (param i32 i32 i32) (result i32)
    (call_indirect 0 (type $bin2)
      (local.get 0) (local.get 1) (local.get 2)))

  ;; TABLE 1 — proves the per-table base offset is applied: index 0 here must
  ;; reach REGION slot 4 ($mul), not region slot 0 ($add). The contents differ
  ;; deliberately, so a dropped base offset returns 30-vs-13 instead of
  ;; agreeing by coincidence.
  (func (export "bin_t1") (param i32 i32 i32) (result i32)
    (call_indirect 1 (type $bin)
      (local.get 0) (local.get 1) (local.get 2)))

  ;; Dispatch a UNARY callee through table 0.
  ;;   idx 2 -> neg    idx 0/1 -> TYPE MISMATCH    idx 3 -> NULL    >=4 -> OOB
  (func (export "un") (param i32 i32) (result i32)
    (call_indirect 0 (type $un) (local.get 0) (local.get 1)))

  ;; A dispatch whose expected type matches NOTHING in either table: every
  ;; index must trap, including the in-range initialized ones.
  (func (export "novoid") (param i32)
    (call_indirect 0 (type $void) (local.get 0)))

  ;; The result of an indirect call feeds further arithmetic, so a dispatch that
  ;; returned the wrong register (or clobbered the value stack) is visible.
  (func (export "chained") (param i32) (result i32)
    (i32.mul
      (call_indirect 0 (type $bin) (i32.const 7) (i32.const 5) (local.get 0))
      (i32.const 3))))
