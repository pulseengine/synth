;; #851 — aarch64 non-param local support acceptance module.
;;
;; Every exported function uses at least one NON-PARAM local (a `(local ...)`
;; declaration beyond its params). Before #851 the aarch64 backend loud-declined
;; each of these (`local.get {i}: non-param locals not yet supported`); after,
;; they lower to a zero-initialized stack-slot frame with copy-semantics
;; get/set/tee. Each is diffed against wasmtime ground truth.
(module
  ;; Two non-param locals, both written then read and summed. 0 params.
  (func (export "two_locals_sum") (result i32)
    (local i32 i32)
    (local.set 0 (i32.const 5))
    (local.set 1 (i32.const 7))
    (i32.add (local.get 0) (local.get 1)))

  ;; A non-param local read BEFORE any write must default to 0 (WASM zero-init).
  ;; Returns param0 + local1(=0) == param0.
  (func (export "zero_init_read_first") (param i32) (result i32)
    (local i32)
    (i32.add (local.get 0) (local.get 1)))

  ;; THE aliasing case: get, set-same-index, get, add. Correct = old(0)+new(5)=5.
  ;; A read-by-reference model would give 5+5=10. 0 params, 1 local.
  (func (export "get_set_get_no_alias") (result i32)
    (local i32)
    (local.get 0)          ;; push local (0)
    (i32.const 5)
    (local.set 0)          ;; local := 5
    (local.get 0)          ;; push local (5)
    (i32.add))             ;; 0 + 5 = 5

  ;; local.tee: leaves the value on the stack AND stores it. tee 3 then double.
  (func (export "tee_double") (result i32)
    (local i32)
    (i32.const 3)
    (local.tee 0)          ;; local := 3, 3 stays on stack
    (local.get 0)          ;; reload 3
    (i32.add))             ;; 3 + 3 = 6

  ;; A local combined with a param, arithmetic over both.
  (func (export "param_plus_local") (param i32 i32) (result i32)
    (local i32)
    (local.set 2 (i32.mul (local.get 0) (local.get 1)))
    (i32.add (local.get 2) (i32.const 100)))

  ;; i64 non-param local — the 64-bit store/load must preserve the full width.
  (func (export "i64_local") (result i64)
    (local i64)
    (local.set 0 (i64.const 0x0123456789ABCDEF))
    (i64.add (local.get 0) (i64.const 1)))

  ;; Three locals, exercising the offset arithmetic and the 32-byte frame round.
  (func (export "three_locals") (result i32)
    (local i32 i32 i32)
    (local.set 0 (i32.const 10))
    (local.set 1 (i32.const 20))
    (local.set 2 (i32.const 30))
    (i32.add (i32.add (local.get 0) (local.get 1)) (local.get 2)))

  ;; Local threaded through a counter-like update (set then re-set).
  (func (export "reassign_local") (param i32) (result i32)
    (local i32)
    (local.set 1 (local.get 0))
    (local.set 1 (i32.add (local.get 1) (i32.const 1)))
    (local.set 1 (i32.mul (local.get 1) (i32.const 2)))
    (local.get 1))

  ;; Non-param local READ AND WRITTEN ACROSS a void block with an early `br_if`
  ;; out (#851 × #538-cf). SP is lowered once at prologue and the block never
  ;; touches it, so the single epilogue `add sp` at the outer `End` balances on
  ;; every path. param0 != 0 → br_if skips the second set → local = 1; param0 == 0
  ;; → falls through → local = 2. Returns the local.
  (func (export "local_across_block") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.const 1))
    (block
      (br_if 0 (local.get 0))          ;; if param0 != 0, jump to block end
      (local.set 1 (i32.const 2)))     ;; only runs when param0 == 0
    (local.get 1)))
