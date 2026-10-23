;; RQ-89-BRVALUE (#1215) — a value-carrying branch in an OPERAND position.
;; Executed by scripts/repro/brvalue_operand_1215_differential.py on three
;; legs (default, --no-optimize, --relocatable) against wasmtime.
;;
;; The first nine functions are the spec suite's own shapes, copied verbatim
;; but for the export name (prefixed with the spec file) so one module holds
;; them all and the `--relocatable` leg — which refuses the spec modules
;; whole, for reasons unrelated to #1215 (global initializers, #1052) — can
;; execute them too. The four `prop_*` functions are this lane's own: the
;; same mechanism reached through a construct whose `end` is itself
;; unreachable (a block nothing branches to, a loop, `return`, `unreachable`),
;; which the spec suite does not exercise.
(module
  ;; spec br.wast "nested-br_table-value-index", verbatim but for the export name
  (func (export "br.nested-br_table-value-index") (result i32)
    (i32.add
      (i32.const 1)
      (block (result i32)
        (drop (i32.const 2))
        (br_table 0 (i32.const 4) (br 0 (i32.const 8)))
        (i32.const 16)
      )
    )
  )
  ;; spec br_table.wast "nested-br_table-value", verbatim but for the export name
  (func (export "br_table.nested-br_table-value") (param i32) (result i32)
    (block (result i32)
      (i32.add
        (i32.const 1)
        (block (result i32)
          (drop (i32.const 2))
          (drop
            (block (result i32)
              (drop (i32.const 4))
              (br_table 0 (br_table 0 1 2 (i32.const 8) (local.get 0)) (i32.const 1))
              (i32.const 32)
            )
          )
          (i32.const 16)
        )
      )
    )
  )
  ;; spec br_table.wast "nested-br_table-value-index", verbatim but for the export name
  (func (export "br_table.nested-br_table-value-index") (param i32) (result i32)
    (block (result i32)
      (i32.add
        (i32.const 1)
        (block (result i32)
          (drop (i32.const 2))
          (br_table 0 (i32.const 4) (br_table 0 1 0 (i32.const 8) (local.get 0)))
          (i32.const 16)
        )
      )
    )
  )
  ;; spec br_if.wast "nested-br-value", verbatim but for the export name
  (func (export "br_if.nested-br-value") (param i32) (result i32)
    (i32.add
      (i32.const 1)
      (block (result i32)
        (drop (i32.const 2))
        (br 0
          (block (result i32)
            (drop (br_if 1 (i32.const 8) (local.get 0))) (i32.const 4)
          )
        )
        (i32.const 16)
      )
    )
  )
  ;; spec br_if.wast "nested-br_table-value", verbatim but for the export name
  (func (export "br_if.nested-br_table-value") (param i32) (result i32)
    (i32.add
      (i32.const 1)
      (block (result i32)
        (drop (i32.const 2))
        (br_table 0
          (block (result i32)
            (drop (br_if 1 (i32.const 8) (local.get 0))) (i32.const 4)
          )
          (i32.const 1)
        )
        (i32.const 16)
      )
    )
  )
  ;; spec br_if.wast "nested-br_table-value-index", verbatim but for the export name
  (func (export "br_if.nested-br_table-value-index") (param i32) (result i32)
    (i32.add
      (i32.const 1)
      (block (result i32)
        (drop (i32.const 2))
        (br_table 0
          (i32.const 4)
          (block (result i32)
            (drop (br_if 1 (i32.const 8) (local.get 0))) (i32.const 1)
          )
        )
        (i32.const 16)
      )
    )
  )
  ;; spec func.wast "break-br_table-nested-num", verbatim but for the export name
  (func (export "func.break-br_table-nested-num") (param i32) (result i32)
    (i32.add
      (block (result i32)
        (br_table 0 1 0 (i32.const 50) (local.get 0)) (i32.const 51)
      )
      (i32.const 2)
    )
  )
  ;; spec func.wast "break-br_table-num", verbatim but for the export name
  (func (export "func.break-br_table-num") (param i32) (result i32)
    (br_table 0 0 (i32.const 50) (local.get 0)) (i32.const 51)
  )
  ;; spec labels.wast "switch", verbatim but for the export name
  (func (export "labels.switch") (param i32) (result i32)
    (block $ret (result i32)
      (i32.mul (i32.const 10)
        (block $exit (result i32)
          (block $0
            (block $default
              (block $3
                (block $2
                  (block $1
                    (br_table $0 $1 $2 $3 $default (local.get 0))
                  ) ;; 1
                ) ;; 2
                (br $exit (i32.const 2))
              ) ;; 3
              (br $ret (i32.const 3))
            ) ;; default
          ) ;; 0
          (i32.const 5)
        )
      )
    )
  )
  ;; scripts/repro/rv32_br_value_931.wat's `carried` and `promoted`, verbatim
  ;; but for the export name. That fixture is executed only on RV32 in CI;
  ;; the RQ-89-BRVALUE byte census found the ARM legs' bytes moved, and on the
  ;; v0.88.0 binary `carried` returns 2 on all three ARM legs (wasmtime 6) —
  ;; the simplest form of this defect: the dead `(i32.const 0)` after the `br`
  ;; is what the trailing `i32.add` consumed in place of the outer 5.
  (func (export "repro931.carried") (result i32)
    (i32.const 5)
    (block $exit (result i32)
      (br $exit (i32.const 1))
      (i32.const 0))
    (i32.add))
  (func (export "repro931.promoted") (result i32)
    (local $x i32)
    (local.set $x (i32.const 7))
    (block $l (result i32) (br $l (local.get $x)) (i32.const 0))
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add))
  ;; lane fixtures: unreachability propagated out of an inner construct
  (func (export "prop_block") (param i32) (result i32)
    (i32.add (local.get 0)
      (block (result i32)
        (drop (block (result i32) (br 1 (i32.const 8)) (i32.const 5)))
        (i32.const 3))))
  (func (export "prop_loop") (param i32) (result i32)
    (i32.add (local.get 0)
      (block (result i32)
        (loop (br 1 (i32.const 8)))
        (i32.const 3))))
  (func (export "prop_return") (param i32) (result i32)
    (i32.add (local.get 0)
      (block (result i32)
        (br_if 0 (i32.const 7) (local.get 0))
        (drop (return (i32.const 40)))
        (i32.const 3))))
  (func (export "prop_unreachable") (param i32) (result i32)
    (i32.add (local.get 0)
      (block (result i32)
        (br_if 0 (i32.const 7) (local.get 0))
        (i32.add (unreachable) (i32.const 3)))))
)
