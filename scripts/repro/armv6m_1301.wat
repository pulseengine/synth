;; RQ-91-ARMV6M (#1301): the cortex-m0 / cortex-m0plus fixture.
;; Three functions synth lowers entirely to ARMv6-M today (accepted, executed
;; against wasmtime) and one function per refusal class (each must decline
;; loudly, naming the class). See armv6m_1301_differential.py.
(module
 (func $inc (export "inc") (param i32) (result i32) (i32.add (local.get 0) (i32.const 1)))
 (func (export "sub3") (param i32 i32 i32) (result i32)
   (i32.sub (i32.sub (local.get 0) (local.get 1)) (local.get 2)))
 (func (export "ext8") (param i32) (result i32) (i32.extend8_s (local.get 0)))
 ;; --- refused: one per class ---
 (func (export "big") (param i32) (result i32) (i32.add (local.get 0) (i32.const 0x12345678)))
 (func (export "divu") (param i32 i32) (result i32) (i32.div_u (local.get 0) (local.get 1)))
 (func (export "lt") (param i32 i32) (result i32) (i32.lt_s (local.get 0) (local.get 1)))
 (func (export "callinc") (param i32) (result i32) (call $inc (call $inc (local.get 0))))
 (func (export "bits") (param i32 i32) (result i32)
   (i32.xor (i32.and (local.get 0) (local.get 1)) (i32.or (local.get 0) (i32.const 7))))
 (func (export "mul") (param i32 i32) (result i32) (i32.mul (local.get 0) (local.get 1)))
 (memory 1)
 (func (export "ld") (param i32) (result i32) (i32.load (local.get 0)))
)
