(module
  ;; GI-FPU-002 phase 2 (#369) f64 fixture (thumb-2, cortex-m7dp ONLY — m4f is
  ;; single-precision and must honest-reject every f64 function).
  ;;
  ;; Values enter through linear memory (the harness writes the two 8-byte
  ;; operands at mem[0] / mem[8]) and leave through an f64.store at a
  ;; caller-chosen address — all-i32 signatures, so no f64 param/return
  ;; marshalling is needed to differentiate. Covers the phase-2 lowered set:
  ;;   f64.const, f64.promote_f32, add/sub/mul/div, abs/neg/sqrt, the six
  ;;   comparisons, f64.load, f64.store — and an f64 LIVE ACROSS an integer
  ;;   call (D0..D7 are caller-saved; preserved as aliased S-word pairs).
  (memory 1)
  (export "mem" (memory 0))

  ;; ---- f64.const -> f64.store (full 64-bit pattern materialization) --------
  (func (export "dconst") (param i32)
    local.get 0 f64.const 1.5 f64.store)
  (func (export "dconst_pi") (param i32)
    local.get 0 f64.const 3.141592653589793 f64.store)
  (func (export "dconst_nz") (param i32)
    local.get 0 f64.const -0.0 f64.store)

  ;; ---- f64.promote_f32 (falcon's 3-function blocker) ------------------------
  (func (export "dpromote") (param i32 i32)
    local.get 0
    local.get 1 f32.reinterpret_i32 f64.promote_f32
    f64.store)

  ;; ---- binary arithmetic: mem[0] OP mem[8] -> mem[addr] ---------------------
  (func (export "dadd") (param i32)
    local.get 0 (f64.add (f64.load (i32.const 0)) (f64.load (i32.const 8)))
    f64.store)
  (func (export "dsub") (param i32)
    local.get 0 (f64.sub (f64.load (i32.const 0)) (f64.load (i32.const 8)))
    f64.store)
  (func (export "dmul") (param i32)
    local.get 0 (f64.mul (f64.load (i32.const 0)) (f64.load (i32.const 8)))
    f64.store)
  (func (export "ddiv") (param i32)
    local.get 0 (f64.div (f64.load (i32.const 0)) (f64.load (i32.const 8)))
    f64.store)

  ;; ---- unary: OP(mem[0]) -> mem[addr] ---------------------------------------
  (func (export "dabs") (param i32)
    local.get 0 (f64.abs (f64.load (i32.const 0))) f64.store)
  (func (export "dneg") (param i32)
    local.get 0 (f64.neg (f64.load (i32.const 0))) f64.store)
  (func (export "dsqrt") (param i32)
    local.get 0 (f64.sqrt (f64.load (i32.const 0))) f64.store)

  ;; ---- the six comparisons: mem[0] CMP mem[8] -> i32 ------------------------
  (func (export "deq") (result i32)
    (f64.eq (f64.load (i32.const 0)) (f64.load (i32.const 8))))
  (func (export "dne") (result i32)
    (f64.ne (f64.load (i32.const 0)) (f64.load (i32.const 8))))
  (func (export "dlt") (result i32)
    (f64.lt (f64.load (i32.const 0)) (f64.load (i32.const 8))))
  (func (export "dle") (result i32)
    (f64.le (f64.load (i32.const 0)) (f64.load (i32.const 8))))
  (func (export "dgt") (result i32)
    (f64.gt (f64.load (i32.const 0)) (f64.load (i32.const 8))))
  (func (export "dge") (result i32)
    (f64.ge (f64.load (i32.const 0)) (f64.load (i32.const 8))))

  ;; ---- f64 live ACROSS an integer call --------------------------------------
  ;; $fhelp has an integer signature but uses VFP internally (allocates S0/S1
  ;; = the D0 alias), so the bl GENUINELY clobbers a live double unless the
  ;; caller spills/reloads it. dxcall(addr, b): mem[addr] = mem[0] +
  ;; promote(f32(fhelp(b))) where fhelp(b) = bits(-f32(b)).
  (func $fhelp (param i32) (result i32)
    local.get 0 f32.reinterpret_i32 f32.neg i32.reinterpret_f32)
  (func (export "dxcall") (param i32 i32)
    local.get 0
    i32.const 0 f64.load          ;; live f64 (D-register) across the call
    local.get 1 call $fhelp       ;; integer call; callee clobbers S0/S1 (=D0)
    f32.reinterpret_i32 f64.promote_f32
    f64.add
    f64.store)

  ;; ---- honest-decline shapes (must be ABSENT from the symtab) ---------------
  ;; f64 PARAM on a hard-float target: arrives in D0 (AAPCS-VFP); the legacy
  ;; i64-pair reading of R0:R1 would be a silent wrong-argument miscompile.
  (func (export "bad_dparam") (param f64 i32) (result i32)
    local.get 1)
  ;; call to an f64-RETURNING callee: the result arrives in D0, which the call
  ;; lowering does not marshal — the callee itself compiles (D0-homed return),
  ;; the CALLER must decline.
  (func $dret (result f64) f64.const 2.5)
  (func (export "bad_dret_call") (param i32)
    local.get 0 call $dret f64.store))
