;; #1097 — silent-miscompile shape 2: `block (param i32)` + br_if.
;; The br_if edge must carry the block param (7) to the join when taken;
;; the fall-through adds 42. wasmtime: bpb(nonzero) = 7, bpb(0) = 49.
(module
  (func (export "bpb") (param i32) (result i32)
    (i32.const 7)
    (block (param i32) (result i32)
      (local.get 0)
      (br_if 0)
      (i32.const 42)
      (i32.add))))
