;; #275 — self-contained `--cortex-m` call_indirect EXECUTION fixture (the
;; falcon shape: an export dispatches through a funcref table).
;;
;; Heterogeneous 5-slot table: slots 0/2 = (i32,i32)->i32 ($add/$sub), slot 1 =
;; (i32)->i32 ($ld), slots 3/4 null — so ONE image exercises every WASM Core
;; §4.4.8 outcome: matching dispatch (values), type mismatch (trap via the #676
;; type-id sidecar), null slot (trap, id 0), OOB index (trap, bounds guard).
;;
;; $ld reads LINEAR MEMORY (initialized by an active data segment, shipped via
;; the #758 flash ROM image): via1(x,1) = x + 42 proves the dispatched
;; function's R11 linmem addressing is INTACT — the funcref table lives in
;; flash, PC-relative, never overlapping the R11 linear-memory region (the
;; historical #717 collision read function "pointers" from linmem data).
(module
  (memory (export "memory") 1)
  (data (i32.const 0) "\2a\00\00\00") ;; linmem[0] = 42
  (type $bin (func (param i32 i32) (result i32)))
  (type $un  (func (param i32) (result i32)))
  (func $add (type $bin) (i32.add (local.get 0) (local.get 1)))
  (func $sub (type $bin) (i32.sub (local.get 0) (local.get 1)))
  (func $ld  (type $un)  (i32.add (local.get 0) (i32.load (i32.const 0))))
  ;; via2(x, idx): dispatch expecting the 2-arg type — x and 7 are the args.
  (func (export "via2") (param i32 i32) (result i32)
    (call_indirect (type $bin) (local.get 0) (i32.const 7) (local.get 1)))
  ;; via1(x, idx): dispatch expecting the 1-arg type.
  (func (export "via1") (param i32 i32) (result i32)
    (call_indirect (type $un) (local.get 0) (local.get 1)))
  (table 5 funcref) (elem (i32.const 0) $add $ld $sub))
