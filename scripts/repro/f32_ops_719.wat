(module
  ;; #719 phase-1b f32 residual fixture (thumb-2 hard-float). Covers the falcon
  ;; f32 op residual left after #708 (load + reinterpret):
  ;;   * f32.store            — the VFP-store twin of f32.load
  ;;   * f32.abs / f32.neg    — VABS.F32 / VNEG.F32 (sign-bit edits)
  ;;   * f32.copysign         — sign-bit splice (bit-exact ±0/NaN-sign/±inf)
  ;;   * f32 local.set/tee     — VFP home write-back
  ;;   * mixed f32/int params  — AAPCS-VFP independent register pools
  ;;
  ;; The scalar-math + store + tee fixtures use ALL-i32 signatures (values enter
  ;; and leave as i32 BITS via reinterpret), so they are single-register in/out
  ;; and need no mixed-param support to differentiate — bit-exact vs wasmtime.
  ;; The `mix*` fixtures use genuine f32 params to exercise the independent
  ;; AAPCS-VFP core/VFP argument pools.
  (memory 1)
  (export "mem" (memory 0))

  ;; ---- sign-family math, bits-in / bits-out -------------------------------
  (func (export "abs") (param i32) (result i32)
    local.get 0 f32.reinterpret_i32 f32.abs i32.reinterpret_f32)
  (func (export "neg") (param i32) (result i32)
    local.get 0 f32.reinterpret_i32 f32.neg i32.reinterpret_f32)
  ;; copysign(a, b) = |a| with sign of b. a=param0 (magnitude), b=param1 (sign).
  (func (export "copysign") (param i32 i32) (result i32)
    local.get 0 f32.reinterpret_i32
    local.get 1 f32.reinterpret_i32
    f32.copysign i32.reinterpret_f32)

  ;; ---- f32.store: store the reinterpreted bits at addr, oracle reads mem ----
  (func (export "store") (param i32 i32)
    local.get 0                          ;; address
    local.get 1 f32.reinterpret_i32      ;; f32 value (from bits)
    f32.store)

  ;; ---- f32 local.set / local.tee (non-param f32 local write-back) ----------
  ;; set: value -> local 1 -> read back (identity through a VFP home)
  (func (export "lset") (param i32) (result i32)
    (local f32)
    local.get 0 f32.reinterpret_i32
    local.set 1
    local.get 1 i32.reinterpret_f32)
  ;; tee: value -> (local 1 AND stack) -> abs of the tee'd value
  (func (export "ltee") (param i32) (result i32)
    (local f32)
    local.get 0 f32.reinterpret_i32
    local.tee 1
    f32.abs
    i32.reinterpret_f32)

  ;; ---- mixed f32/int parameter pools (AAPCS-VFP) ---------------------------
  ;; (i32 f32): i32->R0, f32->S0. Return bits(param0 + reinterpret(param1)).
  (func (export "mix_if") (param i32 f32) (result i32)
    local.get 0
    local.get 1 i32.reinterpret_f32
    i32.add)
  ;; (f32 i32): f32->S0, i32->R0 (NOT R1 — the pool-independence discriminator).
  (func (export "mix_fi") (param f32 i32) (result i32)
    local.get 0 i32.reinterpret_f32
    local.get 1
    i32.add)
  ;; genuine f32 store from an f32 param + i32 addr param (falcon's `store` shape).
  (func (export "mix_store") (param i32 f32)
    local.get 0
    local.get 1
    f32.store)
  ;; f32 arithmetic returning an f32 result via a mixed signature.
  ;; (i32 f32 f32) -> f32 : returns (p1 + p2), bits read back through S0.
  (func (export "mix_add") (param i32 f32 f32) (result f32)
    local.get 1
    local.get 2
    f32.add)

  ;; ---- #719 phase 2: f32 live ACROSS an integer call ------------------------
  ;; Helper with an INTEGER signature that uses VFP internally: its own f32
  ;; lowering allocates S0/S1, so a call to it GENUINELY clobbers the caller's
  ;; low S-registers -- the spill/reload differential is non-vacuous without any
  ;; host code. fhelp(bits) = bits(-f32(bits)).
  (func $fhelp (param i32) (result i32)
    local.get 0 f32.reinterpret_i32 f32.neg i32.reinterpret_f32)

  ;; f32 TEMP live across the call: x + f32(-x_bits reinterpreted back).
  ;; xcall(b) = bits(f32(b) + f32(fhelp(b))) = bits(x + (-x)).
  (func (export "xcall") (param i32) (result i32)
    local.get 0 f32.reinterpret_i32      ;; live f32 temp in an S-register
    local.get 0 call $fhelp              ;; integer call; callee clobbers S0/S1
    f32.reinterpret_i32
    f32.add
    i32.reinterpret_f32)

  ;; f32 PARAM HOME (S0) live across the call: read the param AFTER the bl.
  ;; xhome(x, b) = bits(x) + fhelp(b)  (f32 home read post-call, plus the
  ;; integer result -- proves BOTH register files survive).
  (func (export "xhome") (param f32 i32) (result i32)
    local.get 1 call $fhelp
    local.get 0 i32.reinterpret_f32
    i32.add)

  ;; MULTIPLE live f32 values across the call: a non-param f32 LOCAL home and
  ;; an f32 temp, both live across the bl.
  ;; xcall2(b) = bits(((-x) + (-x)) + |x|) where x = f32(b); local 1 = |x| home.
  (func (export "xcall2") (param i32) (result i32)
    (local f32)
    local.get 0 f32.reinterpret_i32 f32.abs
    local.set 1                          ;; f32 local home, live across the call
    local.get 0 f32.reinterpret_i32 f32.neg  ;; f32 temp, live across the call
    local.get 0 call $fhelp              ;; clobbers low S-registers
    f32.reinterpret_i32
    f32.add
    local.get 1
    f32.add
    i32.reinterpret_f32)

  ;; ---- #719 phase 2: float-signature callees DECLINE loudly -----------------
  ;; These callers must be SKIPPED (absent from the symtab), never miscompiled:
  ;; the callee's f32 result arrives in S0 / its f32 arg belongs in S0, which
  ;; this increment does not marshal at the call boundary.
  (func $retf (result f32) f32.const 1.5)
  (func (export "bad_ret_f32_call") (result i32)
    call $retf i32.reinterpret_f32)
  (func $takef (param f32) (result i32)
    local.get 0 i32.reinterpret_f32)
  (func (export "bad_f32_arg_call") (param i32) (result i32)
    local.get 0 f32.reinterpret_i32 call $takef))
