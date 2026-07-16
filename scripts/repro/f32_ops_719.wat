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
  ;; #538 m4: f32.sqrt un-dropped at decode (single VSQRT.F32; negative
  ;; operand => quiet NaN, never traps). Bits-in/bits-out like abs/neg, but
  ;; compared NaN-leniently (sqrt is ARITHMETIC: NaN payload not pinned).
  (func (export "sqrt") (param i32) (result i32)
    local.get 0 f32.reinterpret_i32 f32.sqrt i32.reinterpret_f32)
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

  ;; ---- GI-FPU-002 phase 3 (#369): copysign with a LIVE core value -----------
  ;; The pre-fix F32Copysign encoder staged the magnitude through R0 — with
  ;; f32 params (S0/S1) and no core params, the `i32.const 41` temp lands in
  ;; R0 and is LIVE across the copysign, so the old sequence returned
  ;; bits(copysign)+bits(copysign) instead of 41+bits(copysign). The rewrite
  ;; clobbers only R12 (reserved encoder scratch).
  (func (export "cs_live") (param f32 f32) (result i32)
    i32.const 41
    local.get 0
    local.get 1
    f32.copysign i32.reinterpret_f32
    i32.add)

  ;; ---- GI-FPU-002 phase 3 (#369): the f32 call boundary is MARSHALLED -------
  ;; Float-signature callees now LOWER: arguments move into the AAPCS-VFP
  ;; S0.. pool, results come out of S0. Every callee below does real VFP
  ;; arithmetic (it reads its S-register args and writes S0), so a caller that
  ;; passed an arg in a core register or read the result from R0 diverges at
  ;; the VALUE level — non-vacuous rows.
  (func $retf (result f32) f32.const 1.5)
  (func $scale (param f32 f32) (result f32)
    local.get 0 local.get 1 f32.mul f32.const 1.5 f32.add)
  (func $addn (param f32 i32) (result f32)
    local.get 0 local.get 1 f32.convert_i32_s f32.add)

  ;; f32 RESULT out of S0: call_ret(a) = bits($retf() + f32(a)).
  (func (export "call_ret") (param i32) (result i32)
    call $retf
    local.get 0 f32.reinterpret_i32
    f32.add
    i32.reinterpret_f32)

  ;; f32 ARGS into S0/S1: call_args(a, b) = bits($scale(f32(a), f32(b))).
  (func (export "call_args") (param i32 i32) (result i32)
    local.get 0 f32.reinterpret_i32
    local.get 1 f32.reinterpret_i32
    call $scale
    i32.reinterpret_f32)

  ;; MIXED int+float args: the core pool skips the f32 (i32 arg -> R0, not R1).
  ;; call_mixed(n, xb) = bits($addn(f32(xb), n)).
  (func (export "call_mixed") (param i32 i32) (result i32)
    local.get 1 f32.reinterpret_i32
    local.get 0
    call $addn
    i32.reinterpret_f32)

  ;; OVERLAPPING sources: arg0's value is produced SECOND (lands in S1, must
  ;; move to S0) while arg1 lives in the S0 local home (must move to S1) — the
  ;; cross-swap exercises the two-phase frame staging, and the S0 home doubles
  ;; as a home-register argument source.
  (func (export "call_swap") (param i32 i32) (result i32)
    (local f32)
    local.get 1 f32.reinterpret_i32 local.set 2   ;; y -> S0 local home
    local.get 0 f32.reinterpret_i32               ;; x -> S1 temp
    local.get 2                                   ;; y (home S0)
    call $scale                                   ;; wants x in S0, y in S1
    i32.reinterpret_f32)

  ;; f32 LIVE ACROSS a float-signature call: the live temp must survive both
  ;; the callee's clobber AND the argument marshalling into its register.
  ;; call_live(a, b) = bits(f32(a) + $scale(f32(b), 2.0)).
  (func (export "call_live") (param i32 i32) (result i32)
    local.get 0 f32.reinterpret_i32               ;; live f32 across the call
    local.get 1 f32.reinterpret_i32
    f32.const 2.0
    call $scale
    f32.add
    i32.reinterpret_f32))
