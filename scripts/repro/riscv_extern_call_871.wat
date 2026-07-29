;; #871 — gale-shaped thin-seam driver fixture: a core module importing the
;; two-function mmio seam (env::mmio_read32 / env::mmio_write32) and exporting
;; functions that use it. On ARM (--target cortex-m3 --relocatable) every
;; export lowers and the two imports appear as undefined symbols; on
;; `-b riscv` pre-fix every seam-using export was SKIPPED
;; ("external call without relocation table") — the #871 gap.
;;
;; Shapes are chosen so the RV32 v0.3.1 call convention (top-of-stack values
;; are exactly the callee's args; every call result is consumed) is
;; semantically exact — the execution differential runs them under unicorn
;; against wasmtime ground truth.
(module
  (import "env" "mmio_read32" (func $mmio_read32 (param i32) (result i32)))
  (import "env" "mmio_write32" (func $mmio_write32 (param i32 i32) (result i32)))
  ;; VOID import — the common driver-seam shape. Exercises the #871
  ;; func_result_counts path: a 0-result callee must push NOTHING (the legacy
  ;; phantom-a0 push corrupted every op after a void call).
  (import "env" "mmio_barrier" (func $mmio_barrier (param i32)))

  ;; read a register: one import call, arg straight from the param.
  (func (export "wdg_status") (param i32) (result i32)
    local.get 0
    call $mmio_read32)

  ;; write a constant: two args on the stack, result returned (consumed).
  (func (export "wdg_kick") (param i32) (result i32)
    local.get 0
    i32.const 0xA5
    call $mmio_write32)

  ;; read-modify-write through the seam: read result feeds the write value.
  (func (export "wdg_set_bit") (param i32 i32) (result i32)
    local.get 0
    local.get 0
    call $mmio_read32
    local.get 1
    i32.or
    call $mmio_write32)

  ;; two reads combined: both call results consumed by the add.
  (func (export "wdg_sum2") (param i32 i32) (result i32)
    local.get 0
    call $mmio_read32
    local.get 1
    call $mmio_read32
    i32.add)

  ;; void-import call followed by more work: no phantom result may remain on
  ;; the stack (the add must see exactly [local0, 5]).
  (func (export "wdg_flush") (param i32) (result i32)
    local.get 0
    call $mmio_barrier
    local.get 0
    i32.const 5
    i32.add)

  ;; import-free control: proves the non-seam path is untouched.
  (func (export "wdg_is_running") (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.and)

  ;; import-free arithmetic control.
  (func (export "wdg_lock") (param i32) (result i32)
    local.get 0
    i32.const 3
    i32.shl)
)
