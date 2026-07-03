;; #503 — the i64 STACK-PARAM sub-case (the remainder after v0.15.x lifted the
;; >8-scalar cap): any 64-bit (i64/f64) param that AAPCS passes on the STACK
;; used to be declined ("#518/#503: an i64/f64 param is AAPCS-passed past R3"),
;; dropping falcon's func_58/func_163/func_164-class helpers from the ELF.
;;
;; The fix makes the incoming-param homing width-aware end to end
;; (`aapcs_param_layout`): a wide param past R3 gets an 8-byte-aligned NSAA
;; slot read via `I64Ldr [sp, #frame+24+nsaa]`, and — the found-along-the-way
;; #503-adjacent bug — an i32 param that a PRECEDING wide param pushed onto
;; the stack (AAPCS C.5: once any arg goes to the stack, NCRN=4, no backfill)
;; is now also read from its stack slot instead of a wrong register.
;;
;; Shapes (each export names the AAPCS placement it exercises):
;;   s_mix    (i32 i32 i32 i32 i64)      p4 = i64 @ [nsaa 0]   (issue #503 repro)
;;   s_align  (i32 i32 i32 i32 i32 i64)  p5 = i64 @ [nsaa 8]   (4-byte hole: NSAA
;;                                        rounds 4 -> 8 for the wide slot)
;;   s_p3     (i32 i32 i32 i64)          p3 = i64 @ [nsaa 0]   (even-align spills
;;                                        it with only 4 declared params)
;;   s_nar    (i64 i32 i32 i32)          p3 = i32 @ [nsaa 0]   (narrow-after-wide:
;;                                        p0=R0:R1, p1=R2, p2=R3, p3=stack — the
;;                                        pre-fix code read p3 from R3 = p2)
;;   s_call   (i32 i32 i32 i32 i64)      wide STACK param in a has-call function
;;                                        (lives in the caller's frame, so it
;;                                        survives the BL without a param slot)
;;   s_wr     (i32 i32 i32 i32 i64)      local.set/get round-trip on the wide
;;                                        stack param's slot (I64Str + I64Ldr)
;;   s_i32    (i32)                      control: untouched narrow path
;;
;; Differential oracle: scripts/repro/i64_stack_param_503_differential.py
;; (wasmtime ground truth vs unicorn on BOTH the direct/--relocatable and the
;; default/optimized-with-fallback paths).
(module
  (func $helper (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 5)))

  ;; the literal shape from issue #503's mix.wat
  (func (export "s_mix") (param i32 i32 i32 i32 i64) (result i64)
    (i64.add (local.get 4) (i64.extend_i32_u (local.get 0))))

  ;; NSAA 8-byte alignment: p4 (i32) sits at [sp,#0], p5 (i64) at [sp,#8]
  (func (export "s_align") (param i32 i32 i32 i32 i32 i64) (result i64)
    (i64.sub (local.get 5) (i64.extend_i32_u (local.get 4))))

  ;; 4 declared params, but the even-aligned pair does not fit: p3 -> stack
  (func (export "s_p3") (param i32 i32 i32 i64) (result i64)
    (i64.xor (local.get 3) (i64.extend_i32_u (local.get 2))))

  ;; narrow-after-wide: p3 is an i32 ON THE STACK (NCRN=4 after the p0 pair
  ;; and p1/p2 take R2/R3). Pre-fix this MIScompiled (read as R3 = p2).
  (func (export "s_nar") (param i64 i32 i32 i32) (result i32)
    (i32.sub (local.get 3) (local.get 2)))

  ;; wide stack param + a call: the caller-frame slot needs no call-spill
  (func (export "s_call") (param i32 i32 i32 i32 i64) (result i64)
    (i64.add
      (local.get 4)
      (i64.extend_i32_u (call $helper (local.get 1)))))

  ;; write-then-read the wide stack param's slot (I64Str/I64Ldr round trip)
  (func (export "s_wr") (param i32 i32 i32 i32 i64) (result i64)
    (local.set 4 (i64.add (local.get 4) (i64.const 0x100000001)))
    (local.get 4))

  ;; control: plain i32 param, byte-identical path
  (func (export "s_i32") (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 3))))
