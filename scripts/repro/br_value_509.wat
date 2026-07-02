;; #509 — the DIRECT selector (so the SHIPPED `--relocatable` path) DROPPED the
;; CARRIED VALUE of a value-returning branch: a `br`/`br_if`/`br_table` that
;; targets a result-typed block and carries an operand returned the wrong value
;; (the carry was lost) for the dispatched/taken arm. wasmtime keeps it.
;;
;; FIXED by threading a blocktype-arity side-table (decoder
;; `FunctionOps::block_arity`, ordinal-keyed — `WasmOp::Block/Loop/If` stay
;; bare) into `select_with_stack`, which gives every branched-to result-typed
;; block a DESIGNATED RESULT REGISTER: each `br`/`br_if`/`br_table` edge emits
;; `mov R_res, carried` before its jump and the fall-through `End` reconciles
;; into the same register — the #313 if/else two-arm reconciliation generalized
;; to N forward edges. (NOT the #507 decline-to-direct shortcut, which cannot
;; tell a CARRIED result from an UNWOUND void-target value.)
;;
;; This is the discriminator: a value carried OVER A BRANCH was dropped, but a
;; branchless value-returning block (`ctrl`) was always correct — so the defect
;; was the branch value-carry, not result-typed blocks in general.
(module
  ;; value-returning br_table: the carried `i32.const 10` should reach whichever
  ;; result-typed block the selector dispatches to. sel 0 -> inner end (+1 then
  ;; +2 = carried+3); sel>=1 -> outer end (carried+2).
  (func (export "pick") (param i32) (result i32)
    (block (result i32)
      (block (result i32)
        (i32.const 10)
        (br_table 0 1 (local.get 0)))
      (i32.const 1)(i32.add))
    (i32.const 2)(i32.add))

  ;; value-returning br_if: taken (p != 0) -> block result is the carried 10;
  ;; not-taken (p == 0) -> 20.
  (func (export "pick_brif") (param i32) (result i32)
    (block (result i32)
      (i32.const 10)
      (br_if 0 (local.get 0))
      (drop)(i32.const 20)))

  ;; value-carrying plain br: `br 1` carries p+30 over BOTH nested result-typed
  ;; blocks (skipping the +1 on the inner fall-through arm). Always-taken edge:
  ;; result must be p+30 for every p.
  (func (export "pick_br") (param i32) (result i32)
    (block (result i32)
      (block (result i32)
        (local.get 0)(i32.const 30)(i32.add)
        (br 1))
      (i32.const 1)(i32.add)))

  ;; value-carrying br + a REAL fall-through edge into the same join: p != 0
  ;; takes the if-arm's `br 0` (carries 10), p == 0 falls through the block end
  ;; (carries p+40). Exercises both edge kinds into one designated join.
  (func (export "pick_br_fall") (param i32) (result i32)
    (block (result i32)
      (local.get 0)
      (if (then (i32.const 10) (br 1)))
      (local.get 0)(i32.const 40)(i32.add)))

  ;; CONTROL: a value-returning block with NO branch — the value flows straight
  ;; to the block end, so it is lowered correctly. Proves the defect is the
  ;; branch value-carry specifically (non-vacuity).
  (func (export "ctrl") (param i32) (result i32)
    (block (result i32) (local.get 0)(i32.const 5)(i32.add))))
