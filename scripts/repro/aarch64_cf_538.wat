;; #538 control-flow increment acceptance module — VOID-result blocks with
;; br / br_if, executed against wasmtime.
;;
;; The observable difference between a taken and a not-taken branch is a TRAP:
;; each function guards an `unreachable` with a `br_if`/`br`, so the branch
;; either skips the trap (returns a value) or falls into it (traps). That makes
;; both edges of every conditional branch executable and diff-able (a wrong
;; branch offset flips trap<->return and is caught).
(module
  ;; br_if: guard(cond, x) — if cond != 0, skip the trap and return x;
  ;; if cond == 0, fall into `unreachable` and TRAP.
  ;;   block            ;; void
  ;;     local.get cond
  ;;     br_if 0        ;; cond != 0 -> jump to block end (skip unreachable)
  ;;     unreachable    ;; cond == 0 -> trap
  ;;   end
  ;;   local.get x      ;; result
  (func (export "guard_brif") (param $cond i32) (param $x i32) (result i32)
    (block
      (local.get $cond)
      (br_if 0)
      (unreachable))
    (local.get $x))

  ;; Unconditional br 0: always skips the trap, always returns x. (A wrong
  ;; offset would land in the brk and trap for EVERY input — caught.)
  (func (export "always_br") (param $x i32) (result i32)
    (block
      (br 0)
      (unreachable))
    (local.get $x))

  ;; Nested blocks, br_if 1 to the OUTER end: if cond != 0 skip BOTH traps and
  ;; return x; if cond == 0 fall into the inner trap.
  ;;   block                 ;; outer
  ;;     block               ;; inner
  ;;       local.get cond
  ;;       br_if 1           ;; -> outer end
  ;;       unreachable       ;; inner trap
  ;;     end
  ;;     unreachable         ;; outer trap (unreachable if inner didn't trap)
  ;;   end
  ;;   local.get x
  (func (export "nested_brif1") (param $cond i32) (param $x i32) (result i32)
    (block
      (block
        (local.get $cond)
        (br_if 1)
        (unreachable))
      (unreachable))
    (local.get $x))

  ;; A block that guards a trap on the branch path, proving the value-stack
  ;; model survives a branch: if cond != 0 skip the trap; return a*b regardless
  ;; (the arithmetic sits AFTER the block, on the fall-through).
  (func (export "brif_then_mul") (param $cond i32) (param $a i64) (param $b i64) (result i64)
    (block
      (local.get $cond)
      (br_if 0)
      (unreachable))
    (local.get $a)
    (local.get $b)
    (i64.mul))

  ;; Straight-line control sanity: a bare block with no branch is transparent
  ;; (it just runs its body and falls through). add(a,b) after a bare block.
  (func (export "bare_block_add") (param $a i32) (param $b i32) (result i32)
    (block
      (nop))
    (local.get $a)
    (local.get $b)
    (i32.add))
)
