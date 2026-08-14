;; #970 — a CONDITIONALLY-written parameter must keep its incoming argument.
;;
;; `count_params` (the ARM/RISC-V backends' access-pattern param inference)
;; counts only local indices READ BEFORE WRITTEN in LINEAR op order. A parameter
;; written on ONE branch of an `if` is "written first" in that order, so it was
;; demoted to a non-param local — losing the fact that its incoming argument
;; value is still live on the OTHER path. The demoted local is not even
;; zero-initialized (its first access is a write, so the #457 read-before-write
;; zero-init skips it), so the fall-through path reads an UNINITIALIZED frame
;; slot on RISC-V.
;;
;; Every `cw_*` export below has its HIGHEST referenced local index written
;; before it is read in linear order — that is what makes the max-over-read-first
;; rule undercount. The `guard_*` exports are the shapes the fix must NOT change:
;; a genuine read-before-write NON-PARAM local still observes the wasm-mandated 0
;; (#457), and an unconditionally-written param is correct either way.
(module
  ;; Callees exist so a param write can be a CALL RESULT: on both ABIs the
  ;; argument registers are CALLER-saved, so the call clobbers the incoming
  ;; param register on the path that does NOT take the branch too.
  (func $mk99 (result i32) (i32.const 99))
  (func $twice (param i32) (result i32) (i32.add (local.get 0) (local.get 0)))

  ;; ── the conditional-write class ────────────────────────────────────────────
  ;; THE canonical shape. cond_write_param(0, 42) must be 42.
  (func (export "cond_write_param") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 5))))
    (local.get 1))

  ;; The same shape with the written value coming from a CALL. This is the ARM
  ;; instance: the merge-point store no longer happens to catch a live param
  ;; register, because `bl` clobbered it.
  (func (export "cw_call") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 1 (call $mk99))))
    (local.get 1))

  ;; A call that also PASSES an argument, so r0/a0 is written on the way in.
  (func (export "cw_call_arg") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 1 (call $twice (i32.const 21)))))
    (local.get 1))

  ;; `local.tee` instead of `local.set` — same demotion, different lowering arm.
  (func (export "cw_tee") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (drop (local.tee 1 (i32.const 5)))))
    (local.get 1))

  ;; The write is guarded by `br_if` out of a `block`, not by `if`.
  (func (export "cw_brif") (param i32 i32) (result i32)
    (block
      (br_if 0 (i32.eqz (local.get 0)))
      (local.set 1 (i32.const 5)))
    (local.get 1))

  ;; A loop that writes the param only while the counter is nonzero, so
  ;; count=0 leaves the incoming argument untouched.
  (func (export "cw_loop") (param i32 i32) (result i32)
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 0)))
        (local.set 1 (i32.add (local.get 1) (i32.const 1)))
        (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
        (br 0)))
    (local.get 1))

  ;; The highest index of THREE params is the conditionally-written one, and
  ;; the surviving params are summed so a wrong slot offset is visible too.
  (func (export "cw_last_of_three") (param i32 i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 2 (i32.const 5))))
    (i32.add (local.get 1) (local.get 2)))

  ;; SIX declared params: on ARM indices 4 and 5 are AAPCS STACK-passed, so this
  ;; also exercises the leniency the `min(referenced, declared)` bound widens —
  ;; index 5 must be read from the caller's frame, not from a zero-init local.
  (func (export "cw_high_param") (param i32 i32 i32 i32 i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 5 (i32.const 7))))
    (i32.add (local.get 4) (local.get 5)))

  ;; ── guards: shapes the fix must leave alone ────────────────────────────────
  ;; #457: a genuine read-before-write NON-PARAM local reads the wasm-mandated 0.
  ;; If the fix over-widened the param count this would read caller garbage.
  (func (export "guard_rbw_local") (param i32) (result i32)
    (local i32)
    (i32.add (local.get 0) (local.get 1)))

  ;; #457 again, with the non-param local as the HIGHEST index and a param
  ;; conditionally written below it.
  (func (export "guard_rbw_local_mixed") (param i32 i32) (result i32)
    (local i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 5))))
    (i32.add (local.get 1) (local.get 2)))

  ;; Both arms write the param: correct under either rule.
  (func (export "guard_both_arms") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 5)))
      (else (local.set 1 (i32.const 7))))
    (local.get 1))

  ;; Unconditional write before the read: the incoming value is genuinely dead.
  (func (export "guard_write_then_read") (param i32 i32) (result i32)
    (local.set 1 (i32.const 5))
    (i32.add (local.get 0) (local.get 1)))

  ;; Plain read-only params.
  (func (export "guard_plain_params") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1)))
)
