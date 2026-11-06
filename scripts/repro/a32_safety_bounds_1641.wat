;; #1641 — A32 `--safety-bounds software` fixture: every access is guarded.
;; Memory is one 64 KiB page; see a32_control_flow_1639_differential.py.
(module
  (memory 1)
  ;; plain load of a fresh (zeroed) page
  (func (export "ld") (param i32 i32) (result i32)
    (i32.load (local.get 0)))
  ;; store then reload through a static offset: the value round-trips iff
  ;; both accesses are in bounds; either OOB traps
  (func (export "rt") (param i32 i32) (result i32)
    (i32.store offset=4 (local.get 0) (local.get 1))
    (i32.load offset=4 (local.get 0)))
  ;; sub-word accesses inside a loop: sums n bytes written at 0..n-1
  (func (export "bytes") (param i32 i32) (result i32) (local i32 i32)
    (block
      (loop
        (br_if 1 (i32.ge_u (local.get 2) (local.get 0)))
        (i32.store8 (i32.add (local.get 1) (local.get 2)) (i32.add (local.get 2) (i32.const 7)))
        (local.set 3 (i32.add (local.get 3)
          (i32.load8_u (i32.add (local.get 1) (local.get 2)))))
        (local.set 2 (i32.add (local.get 2) (i32.const 1)))
        (br 0)))
    (local.get 3))
)
