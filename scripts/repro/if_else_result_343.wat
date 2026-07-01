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

  ;; #343 i64 — exercises the I64 arm of `reconcile_if_result` (the lo/hi pair
  ;; move and its documented no-cycle argument). Each arm lands its result in a
  ;; DIFFERENT register pair (then via i64.add, else a bare i64 const), and BOTH
  ;; halves are nonzero and differ between arms — so the join must emit BOTH the
  ;; lo and the hi `mv`, and a dropped hi-move would corrupt the top 32 bits
  ;; rather than hide behind a zero high half.
  ;;   pick64(nonzero) = 0x1_0000_0002 + 1 = 0x0000_0001_0000_0003  (then-arm)
  ;;   pick64(0)       =                     0x0000_0007_0000_0020  (else-arm)
  (func (export "pick64") (param i32) (result i64)
    (if (result i64) (local.get 0)
      (then (i64.add (i64.const 0x100000002) (i64.const 1)))
      (else (i64.const 0x700000020))))
)
