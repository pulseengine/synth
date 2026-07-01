(module
  (memory 1)
  ;; #343 — `if (result i32)` with a value on BOTH arms. The then-arm computes
  ;; its result into a different register (t2, via `add`) than the else-arm
  ;; (t0, a bare const). Without result-register reconciliation at the join the
  ;; epilogue reads one fixed register, so one arm returns a stale value.
  ;;   pick(nonzero) = 1 + 2 = 3   (then-arm)
  ;;   pick(0)       = 20          (else-arm)
  (func (export "pick") (param i32) (result i32)
    (if (result i32) (local.get 0)
      (then (i32.add (i32.const 1) (i32.const 2)))
      (else (i32.const 20))))

  ;; A second shape: the else-arm is the one that lands in a higher register.
  ;;   pick2(nonzero) = 7               (then-arm)
  ;;   pick2(0)       = 100 + 200 = 300 (else-arm)
  (func (export "pick2") (param i32) (result i32)
    (if (result i32) (local.get 0)
      (then (i32.const 7))
      (else (i32.add (i32.const 100) (i32.const 200)))))

  ;; A value live ACROSS the if/else: `5` is pushed before the `if` and consumed
  ;; by `i32.add` after `end`. Guards the join split-index — the reconciliation
  ;; must merge only the arms' result (above the checkpoint), never the carried
  ;; value below it.
  ;;   pick3(nonzero) = 5 + 10 = 15  (then-arm)
  ;;   pick3(0)       = 5 + 20 = 25  (else-arm)
  (func (export "pick3") (param i32) (result i32)
    (i32.const 5)
    (if (result i32) (local.get 0)
      (then (i32.const 10))
      (else (i32.const 20)))
    (i32.add))
)
