;; #953 (SECURITY) — a module that declares ZERO pages of linear memory.
;;
;; Every address is out of bounds of a 0-byte memory, so under
;; `--safety-bounds software` every access must trap. wasmtime traps for all of
;; these; on v0.56.0 rv32 performed all of them, because the guard was baked at
;; 65532 — byte-for-byte the guard of a 1-page module.
;;
;; The address values below are chosen to straddle the invented bound rather
;; than to look adversarial: 0 is the friendliest possible address and was
;; accepted; 65528 is the last 4-byte-aligned address INSIDE the invented
;; 65532 bound and was accepted; 65536 is past it and was already trapping, so
;; it is the control that proves the guard existed at all and that the fixture
;; is not simply trapping on everything for an unrelated reason.
(module
  (memory 0)

  (func (export "ld") (param $a i32) (result i32)
    (i32.load (local.get $a)))

  ;; Stores emit the identical bound, so this is an out-of-bounds WRITE and not
  ;; only a read. Returns the value it stored so a trap is distinguishable from
  ;; a silent no-op.
  (func (export "st") (param $a i32) (result i32)
    (i32.store (local.get $a) (i32.const 42))
    (i32.const 42))

  ;; Sub-word accesses take a different guard path (width-adjusted bound), so
  ;; they are exercised too rather than assumed to follow the i32 case.
  (func (export "ld8") (param $a i32) (result i32)
    (i32.load8_u (local.get $a)))
)
