;; #655 companion — a static offset far beyond imm12. Mask mode folds the
;; offset into the masked effective address (residual access imm 0), so this
;; now COMPILES and is bounded exactly (u33 ADD-then-AND soundness); pre-fix
;; synth rejects it in offset_to_imm. Only compiled under
;; `--safety-bounds mask` by mask_bounds_655_riscv_differential.py.
(module
  (memory 1)
  (func (export "load_off_huge") (param i32) (result i32)
    (i32.load offset=0xffff0000 (local.get 0)))
)
