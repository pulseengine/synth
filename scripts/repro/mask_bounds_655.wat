;; #655 — RV32 emit_bounds_check masked the OPERAND before the static offset
;; was folded (the #651 class, RISC-V twin of ARM PR #654), and i64 accesses
;; carried no guard at all. Exercised by mask_bounds_655_riscv_differential.py
;; under `--safety-bounds mask` and `--safety-bounds software`.
;;
;; All static offsets stay <= 2047 so the module also compiles on pre-fix
;; synth (larger offsets fail loudly in offset_to_imm there); the huge-offset
;; case lives in mask_bounds_655_hugeoff.wat.
(module
  (memory 1) ;; 64 KiB — power of two, so mask mode is accepted

  ;; RED (offset escape): in-bound operand + static offset pushes the access
  ;; past the 64 KiB bound. Pre-fix: `and` the operand, then re-add 2044 in
  ;; the addressing mode -> reads/writes outside the memory window.
  (func (export "load_off_esc") (param i32) (result i32)
    (i32.load offset=2044 (local.get 0)))
  (func (export "store_off_esc") (param i32 i32)
    (i32.store offset=2044 (local.get 0) (local.get 1)))

  ;; RED (final-byte overhang): a word load starting in the last 3 bytes must
  ;; clamp to size-4 so the FINAL byte stays inside the bound.
  (func (export "load_word") (param i32) (result i32)
    (i32.load (local.get 0)))

  ;; Exactness guard: byte access at size-1 must be preserved exactly
  ;; (the ARM twin's latent size-vs-size-1 remap bug; RV32's mask was already
  ;; size-1 — this pins it).
  (func (export "load8") (param i32) (result i32)
    (i32.load8_u (local.get 0)))

  ;; RED (offset escape, halfword): ea == size wraps to 0 under mask
  ;; semantics; pre-fix it read one past the window.
  (func (export "load16_off") (param i32) (result i32)
    (i32.load16_u offset=254 (local.get 0)))

  ;; RED (i64 gap): i64 accesses had NO guard in Software and Mask modes.
  (func (export "load_i64_lo") (param i32) (result i32)
    (i32.wrap_i64 (i64.load (local.get 0))))
  (func (export "load_i64_hi") (param i32) (result i32)
    (i32.wrap_i64 (i64.shr_u (i64.load (local.get 0)) (i64.const 32))))
  (func (export "store_i64") (param i32 i32)
    (i64.store (local.get 0)
      (i64.or
        (i64.extend_i32_u (local.get 1))
        (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
)
