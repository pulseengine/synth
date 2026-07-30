;; #882 — RV32 br_table compare-chain lowering fixture.
;;
;; `dispatch` is gale's exact wdg_unlock shape: br_table { targets: [0, 1, 0],
;; default: 1 } — the last op standing between the wdg-thin driver and a
;; complete RV32 lowering. `dispatch3` covers three DISTINCT targets plus
;; default (the ARM #507 shape), so a wrong chain entry or a wrong default is
;; observable as a wrong return value, not just a shared-landing coincidence.
;;
;; Landings write through a local and fall to a common end (no mid-block
;; `return` — that is the separate #882 fixture-2 `Lend0` class).
;;
;; Semantics under test (WASM core): index i < len → targets[i]; any index
;; >= len (unsigned interpretation — "negative" i32s included) → default.
(module
  (memory 1)

  ;; gale wdg_unlock shape: targets [0, 1, 0], default 1.
  ;;   index 0 → depth 0 (inner)  → 10
  ;;   index 1 → depth 1 (outer)  → 20
  ;;   index 2 → depth 0 (inner)  → 10
  ;;   else    → depth 1 (outer)  → 20
  (func (export "dispatch") (param i32) (result i32)
    (local i32)
    (block $end
      (block $outer
        (block $inner
          local.get 0
          br_table $inner $outer $inner $outer
        )
        ;; depth-0 landing (index 0 or 2)
        i32.const 10
        local.set 1
        br $end
      )
      ;; depth-1 landing (index 1 or out-of-range)
      i32.const 20
      local.set 1
    )
    local.get 1)

  ;; three distinct targets: 0→10, 1→20, 2→30, out-of-range→30 (default).
  (func (export "dispatch3") (param i32) (result i32)
    (local i32)
    (block $end
      (block $b2
        (block $b1
          (block $b0
            local.get 0
            br_table $b0 $b1 $b2 $b2
          )
          i32.const 10
          local.set 1
          br $end
        )
        i32.const 20
        local.set 1
        br $end
      )
      i32.const 30
      local.set 1
    )
    local.get 1)

  ;; default DISTINCT from every table entry: 0→11, 1→22, out-of-range→33.
  ;; A lowering that folds the default into the last chain entry (or clamps
  ;; the index to the table instead of to default) fails here.
  (func (export "dispatch_default") (param i32) (result i32)
    (local i32)
    (block $end
      (block $bd
        (block $b1
          (block $b0
            local.get 0
            br_table $b0 $b1 $bd
          )
          i32.const 11
          local.set 1
          br $end
        )
        i32.const 22
        local.set 1
        br $end
      )
      i32.const 33
      local.set 1
    )
    local.get 1))
