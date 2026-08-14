;; #851 — aarch64 PARAM HOMING acceptance module (RQ-57-A64PARAM).
;;
;; Every exported function WRITES one of its own parameters (`local.set` or
;; `local.tee` on an index < num_params). Before this increment the aarch64
;; selector loud-declined that in a LEAF function ("local.set {i}: writing a
;; PARAMETER is not yet supported for aarch64"), because a param lived only in
;; its incoming AAPCS64 argument register and was pushed onto the value stack
;; BY REFERENCE — so writing it could clobber a value already stacked. Only the
;; NON-LEAF path homed params (v0.54 lane L3, to survive a `bl`), which is why
;; `param_write_across_call` below is the one case that already compiled.
;;
;; After the increment every param a function writes gets an 8-byte stack slot
;; filled from its argument register in the prologue, `local.get` LOADS a fresh
;; copy, and `local.set`/`local.tee` STORE — the same copy-semantics slot model
;; the non-param locals already used. Each result is diffed against wasmtime.
(module
  ;; --- the headline ALIASING case -----------------------------------------
  ;; get, set-same-index, get, add. Correct = old(p) + 5. A by-reference model
  ;; (the pre-fix shape, had it not declined) writes 5 into the register the
  ;; first `local.get` already pushed and yields 5 + 5 = 10 for EVERY p.
  (func (export "get_set_get_param_no_alias") (param i32) (result i32)
    (local.get 0)          ;; push the INCOMING param
    (i32.const 5)
    (local.set 0)          ;; param := 5
    (local.get 0)          ;; push 5
    (i32.add))             ;; old(p) + 5

  ;; local.tee on a param: the value must be left on the stack AND be durable.
  ;; Correct = old(p) + 20. A by-reference model gives 10 + 10 + 10 = 30.
  (func (export "tee_param_no_alias") (param i32) (result i32)
    (local.get 0)          ;; push the INCOMING param
    (i32.const 10)
    (local.tee 0)          ;; param := 10, 10 stays on the stack
    (i32.add)              ;; old(p) + 10
    (local.get 0)          ;; reload 10 from the home slot
    (i32.add))             ;; old(p) + 20

  ;; local.tee as the sole producer of the result (tee's stack value is used
  ;; directly, never reloaded). Correct = 100 - p.
  (func (export "tee_param_result") (param i32) (result i32)
    (local.tee 0 (i32.sub (i32.const 100) (local.get 0))))

  ;; --- the canonical real shape: a loop counter held in a PARAM ------------
  ;; sum 1..p, decrementing the param itself. Exercises a slot store/load
  ;; across a back-edge inside a leaf frame.
  (func (export "param_countdown_sum") (param i32) (result i32)
    (local i32)                                        ;; acc, zero-init
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 0)))
        (local.set 1 (i32.add (local.get 1) (local.get 0)))
        (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
        (br 0)))
    (local.get 1))

  ;; --- param write on BOTH arms of an if/else (SP balance on every path) ---
  (func (export "param_write_if_else") (param i32) (result i32)
    (if (local.get 0)
      (then (local.set 0 (i32.const 111)))
      (else (local.set 0 (i32.const 222))))
    (local.get 0))

  ;; --- offset arithmetic: write the LAST of three params, read all three ---
  ;; Correct = p0 + p1 + p0*p1.
  (func (export "write_last_of_three") (param i32 i32 i32) (result i32)
    (local.set 2 (i32.mul (local.get 0) (local.get 1)))
    (i32.add (i32.add (local.get 0) (local.get 1)) (local.get 2)))

  ;; --- the classic swap: two param writes through a scratch local ----------
  ;; Correct = p1 - p0 (a lowering that aliased either home would give 0).
  (func (export "swap_two_params") (param i32 i32) (result i32)
    (local i32)
    (local.set 2 (local.get 0))
    (local.set 0 (local.get 1))
    (local.set 1 (local.get 2))
    (i32.sub (local.get 0) (local.get 1)))

  ;; --- param write COEXISTING with a non-param local -----------------------
  ;; The homed frame now covers index 0..2, so the non-param local (index 2)
  ;; moved from slot 0 to slot 2 — its zero-init and its offset must both still
  ;; be right. Local 2 is READ BEFORE it is written, so a lost zero-init shows.
  ;; Correct = p0 + p1 + 9.
  (func (export "mixed_param_and_local") (param i32 i32) (result i32)
    (local i32)
    (local.set 0 (i32.add (local.get 0) (local.get 2)))  ;; p0 + 0
    (local.set 2 (i32.const 9))
    (i32.add (i32.add (local.get 0) (local.get 1)) (local.get 2)))

  ;; --- i64: the home slot must preserve the FULL width ---------------------
  (func (export "i64_param_write") (param i64) (result i64)
    (local.set 0 (i64.add (local.get 0) (i64.const 0x0000000100000000)))
    (local.get 0))

  ;; --- mixed-width params: an i64 param written next to an i32 param -------
  ;; Correct = p0 * (u64)p1.
  (func (export "i64_i32_param_write") (param i64 i32) (result i64)
    (local.set 0 (i64.mul (local.get 0) (i64.extend_i32_u (local.get 1))))
    (local.get 0))

  ;; --- the #457 param-count INFERENCE miscompile ---------------------------
  ;; param 1 is written before it is read in LINEAR op order, but only
  ;; CONDITIONALLY. The aarch64 driver inferred a function's param count from
  ;; "which indices are READ FIRST" and capped it with the declared count, so
  ;; param 1 was reclassified as a NON-PARAM local and ZERO-INITIALIZED — and
  ;; the function compiled SILENTLY WRONG rather than declining: with p0 == 0
  ;; the `if` never runs and the result must be the INCOMING p1, but the
  ;; emitted code returned 0. MEASURED on c2f9d72 (before this increment):
  ;;   cond_write_param(0, 42): wasmtime=42 synth=0
  ;; The inference now uses the highest REFERENCED index (still capped by the
  ;; declared count), so param 1 is a param and gets homed from x1.
  (func (export "cond_write_param") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 5))))
    (local.get 1))

  ;; The same hazard one index further out, and with the write inside a LOOP
  ;; body that may execute zero times. Correct = p2 when p0 == 0.
  (func (export "cond_write_param_loop") (param i32 i32 i32) (result i32)
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 0)))
        (local.set 2 (i32.add (local.get 2) (local.get 1)))
        (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
        (br 0)))
    (local.get 2))

  ;; --- NON-LEAF regression guard -------------------------------------------
  ;; This shape already compiled (the v0.54 L3 non-leaf homing); it is here so
  ;; the widened homing predicate cannot regress it. The `call` is evaluated
  ;; with an EMPTY value stack on purpose — a live temp across a call is a
  ;; SEPARATE, still-live aarch64 decline ("value stack holds N entries but
  ;; needs exactly 0"), not something param homing addresses. Correct = 3*p + 1.
  (func $one (result i32) (i32.const 1))
  (func (export "param_write_across_call") (param i32) (result i32)
    (local.set 0 (i32.mul (local.get 0) (i32.const 3)))
    (i32.add (call $one) (local.get 0))))
