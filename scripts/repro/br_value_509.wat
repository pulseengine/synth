;; #509 — the DIRECT selector (so the SHIPPED `--relocatable` path) drops the
;; CARRIED VALUE of a value-returning branch: a `br`/`br_if`/`br_table` that
;; targets a result-typed block and carries an operand returns 0 (the value is
;; lost) for the dispatched/taken arm. wasmtime keeps it. The IR carries no
;; block-result arity (`WasmOp::Block` is a unit variant, the decoder tracks
;; none), so the selector cannot thread the carried value to the join — the real
;; fix needs block-arity threading + a result-register convention generalizing
;; the #313 if/else reconciliation (NOT the #507 decline-to-direct shortcut,
;; which cannot tell a CARRIED result from an UNWOUND void-target value).
;;
;; This is the discriminator: a value carried OVER A BRANCH is dropped, but a
;; branchless value-returning block (`ctrl`) is correct — so the defect is the
;; branch value-carry, not result-typed blocks in general.
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

  ;; CONTROL: a value-returning block with NO branch — the value flows straight
  ;; to the block end, so it is lowered correctly. Proves the defect is the
  ;; branch value-carry specifically (non-vacuity).
  (func (export "ctrl") (param i32) (result i32)
    (block (result i32) (local.get 0)(i32.const 5)(i32.add))))
