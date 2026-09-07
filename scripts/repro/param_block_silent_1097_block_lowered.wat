;; RQ-64-MVLOWER (#1093) — sub-shapes of `block (param ..)`, executed by the
;; #1097 oracle ONLY on a leg listed as LOWERED. One module per construct so
;; a still-declined construct can never block this one (#952). Every expected
;; value comes from wasmtime, live; nothing here is hand-pinned.
(module
  ;; two params: a taken br_if carries the TOP (3); fall-through subtracts.
  ;; wasmtime: bp2(nonzero) = 3, bp2(0) = 4.
  (func (export "bp2") (param i32) (result i32)
    (i32.const 7) (i32.const 3)
    (block (param i32 i32) (result i32)
      (local.get 0) (br_if 0)
      (i32.sub)))
  ;; an UNCONDITIONAL br to an OUTER param block, carrying the inner block's
  ;; result: nonzero -> inner br_if carries 7 to $i's end, then +42 = 49;
  ;; zero -> 7+1 = 8 is carried by `br $o` straight to the outer join.
  ;; (A `br` out of a nested VOID `if` cannot carry the param: wasm hides
  ;; operands below the if-frame's entry height — that shape needs an
  ;; `if (param ..)`, which is its own leg.)
  ;; wasmtime: bpu(nonzero) = 49, bpu(0) = 8.
  (func (export "bpu") (param i32) (result i32)
    (i32.const 7)
    (block $o (param i32) (result i32)
      (block $i (param i32) (result i32)
        (local.get 0) (br_if $i)
        (i32.const 1) (i32.add)
        (br $o))
      (i32.const 42) (i32.add)))
  ;; br_table into NESTED param blocks: index 0 -> inner end (then +1),
  ;; index 1 -> outer end (7 unchanged), anything else -> default = inner.
  ;; wasmtime: bpt(0) = 8, bpt(1) = 7, bpt(2) = 8, bpt(5) = 8.
  (func (export "bpt") (param i32) (result i32)
    (i32.const 7)
    (block $o (param i32) (result i32)
      (block $i (param i32) (result i32)
        (local.get 0) (br_table $i $o $i))
      (i32.const 1) (i32.add)))
  ;; a value BELOW the block params (100) must survive the edge and the
  ;; result-register landing. wasmtime: bpd(nonzero) = 107, bpd(0) = 149.
  (func (export "bpd") (param i32) (result i32)
    (i32.const 100) (i32.const 7)
    (block (param i32) (result i32)
      (local.get 0) (br_if 0)
      (i32.const 42) (i32.add))
    (i32.add)))
