;; RQ-63-A64STACK — call shapes with LIVE VALUES BELOW the callee's arguments
;; on the value stack. Every one of these declined on aarch64 before v0.63
;; ("value stack holds N entries but needs exactly M (call clobbers
;; caller-saved temps below the args)"). The imported `clobber_add` is defined
;; by the harness and OVERWRITES every value-stack temp (x9..x15, v16..v23)
;; before returning a+b, so a missing reload is a wrong value, never a lucky
;; pass. Expected values come from wasmtime, never from this file.
(module
  (type $t1 (func (param i32) (result i32)))
  (import "env" "clobber_add" (func $clobber_add (param i32 i32) (result i32)))
  (memory 1)
  (table 1 funcref)
  (elem (i32.const 0) $inc7)
  (func $inc7 (type $t1) (i32.add (local.get 0) (i32.const 7)))
  (func $sub (param i32 i32) (result i32) (i32.sub (local.get 0) (local.get 1)))
  (func $dbl64 (param i64) (result i64) (i64.add (local.get 0) (local.get 0)))

  ;; 1. one GP value below a LOCAL direct call: a + inc7(b)
  (func (export "below_local") (param i32 i32) (result i32)
    (i32.add (local.get 0) (call $inc7 (local.get 1))))

  ;; 2. one GP value below an IMPORT call whose body clobbers every temp
  (func (export "below_import") (param i32 i32) (result i32)
    (i32.add (local.get 0) (call $clobber_add (local.get 1) (i32.const 100))))

  ;; 3. a call as the SECOND argument of a call: sub(a, clobber_add(b, 1))
  (func (export "nested_arg") (param i32 i32) (result i32)
    (call $sub (local.get 0) (call $clobber_add (local.get 1) (i32.const 1))))

  ;; 4. the first call's result survives the second call
  (func (export "two_calls") (param i32 i32) (result i32)
    (call $sub (call $clobber_add (local.get 0) (i32.const 1))
               (call $clobber_add (local.get 1) (i32.const 2))))

  ;; 5. THREE values below (odd count: the spill area pads to 32 bytes)
  (func (export "deep3") (param i32 i32 i32) (result i32)
    (i32.add (local.get 0)
      (i32.mul (local.get 1)
        (i32.sub (local.get 2) (call $clobber_add (local.get 0) (local.get 1))))))

  ;; 6. an i64 below the call: the spill is 64 bits wide
  (func (export "below_i64") (param i64 i64) (result i64)
    (i64.add (local.get 0) (call $dbl64 (local.get 1))))

  ;; 7. an f64 below the call: spilled through the FP file (str d / ldr d)
  (func (export "below_fp") (param i32) (result i32)
    (i32.trunc_f64_s
      (f64.add (f64.const 2.5)
               (f64.convert_i32_s (call $clobber_add (local.get 0) (i32.const 1))))))

  ;; 8. the store ADDRESS sits below the stored call result; read it back
  (func (export "store_below") (param i32 i32) (result i32)
    (i32.store (local.get 0) (call $clobber_add (local.get 1) (i32.const 3)))
    (i32.load (local.get 0)))

  ;; 9. a value below a call_indirect's args (the table index sits above them)
  (func (export "below_indirect") (param i32 i32 i32) (result i32)
    (i32.add (local.get 0)
             (call_indirect (type $t1) (local.get 1) (local.get 2))))

  ;; 10. the call inside a value-carrying block, the live value OUTSIDE it
  (func (export "below_block") (param i32 i32) (result i32)
    (i32.add (local.get 0)
      (block (result i32) (call $clobber_add (local.get 1) (i32.const 5)))))
)
