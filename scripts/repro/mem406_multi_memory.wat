;; #406 (VCR-MEM-002 phase 1) — two linear memories must be two DISTINCT
;; native regions.
;;
;; Pre-#406 synth dropped the memarg memory index at decode: every load/store
;; lowered to the ONE R11 base, so a store to memory $m1 silently clobbered
;; memory $m0 (store_both_read0 returned y instead of x), memory $m1's init
;; data never shipped, and memory.size/grow on $m1 read memory $m0's R10.
;;
;; Post-#406 (--relocatable): memory 0 keeps the runtime R11 base; memory 1 is
;; addressed via its own `__synth_wasm_data_1` region symbol (R_ARM_ABS32
;; literal pool), placed by the host linker/runtime — see
;; multi_memory_406_differential.py.
;;
;; Both memories are max==initial so memory.grow fails (-1) in wasmtime too,
;; matching synth's fixed-memory lowering. Sizes differ (1 vs 3 pages) so a
;; memory.size alias is observable.
(module
  (memory $m0 1 1)
  (memory $m1 3 3)
  (data (memory $m1) (i32.const 16) "\aa\bb\cc\dd\11\22\33\44")

  ;; The aliasing discriminator: store x to $m0[p], y to $m1[p], read back
  ;; $m0[p]. Correct: x. Pre-#406 (both stores on one base): y.
  (func (export "store_both_read0") (param $p i32) (param $x i32) (param $y i32) (result i32)
    (i32.store (local.get $p) (local.get $x))
    (i32.store $m1 (local.get $p) (local.get $y))
    (i32.load (local.get $p)))

  ;; Mirror: read back $m1[p]. Correct: y (and $m0[p] left = x).
  (func (export "store_both_read1") (param $p i32) (param $x i32) (param $y i32) (result i32)
    (i32.store (local.get $p) (local.get $x))
    (i32.store $m1 (local.get $p) (local.get $y))
    (i32.load $m1 (local.get $p)))

  ;; Init-data peeks on memory 1 (pre-#406 these segments were silently
  ;; DROPPED — memory 1 shipped uninitialized). Exercises the static memarg
  ;; offset (folded into the __synth_wasm_data_1 addend) + dynamic index.
  (func (export "peek1_8u") (param $i i32) (result i32)
    (i32.load8_u $m1 offset=16 (local.get $i)))
  (func (export "peek1_16u") (param $i i32) (result i32)
    (i32.load16_u $m1 offset=16 (local.get $i)))
  (func (export "peek1_32") (param $i i32) (result i32)
    (i32.load $m1 offset=16 (local.get $i)))

  ;; Sub-word store round-trips on memory 1 (sign + zero extends).
  (func (export "narrow1_8") (param $p i32) (param $v i32) (result i32)
    (i32.store8 $m1 (local.get $p) (local.get $v))
    (i32.load8_s $m1 (local.get $p)))
  (func (export "narrow1_16") (param $p i32) (param $v i32) (result i32)
    (i32.store16 $m1 (local.get $p) (local.get $v))
    (i32.load16_s $m1 (local.get $p)))

  ;; Per-memory size/grow. size0 = 1 (runtime R10), size1 = 3 (declared
  ;; constant — memory.grow always fails on this backend, so initial == size).
  (func (export "size0") (result i32) (memory.size $m0))
  (func (export "size1") (result i32) (memory.size $m1))
  (func (export "grow1") (param $n i32) (result i32)
    (memory.grow $m1 (local.get $n))))
