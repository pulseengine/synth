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

  ;; ---- GI-FPU-002 phase 3 (#369): f64 PARAMS homed in D-registers -----------
  ;; dparam(f64 x, i32 addr): mem[addr] = x. x arrives in D0, addr in R0 (the
  ;; core walk SKIPS the D-homed f64) — the legacy i64-pair reading of R0:R1
  ;; would store garbage.
  (func (export "dparam") (param f64 i32)
    local.get 1 local.get 0 f64.store)

  ;; AAPCS-VFP BACK-FILL: (f32, f64, f32, i32) homes S0, D1(=S2:S3), S1, R0 —
  ;; the second f32 back-fills the S1 hole the f64's even-aligned pair skipped.
  ;; dparam_mix(a, b, c, addr): mem[addr] = promote(a) + b + promote(c).
  (func (export "dparam_mix") (param f32 f64 f32 i32)
    local.get 3
    local.get 0 f64.promote_f32
    local.get 1 f64.add
    local.get 2 f64.promote_f32 f64.add
    f64.store)

  ;; f64 PARAM HOME (D0 = S0:S1) live ACROSS an integer call whose callee
  ;; genuinely clobbers S0/S1. dparam_home(x, b, addr): mem[addr] =
  ;; promote(f32(fhelp(b))) + x  (x read AFTER the bl).
  (func (export "dparam_home") (param f64 i32 i32)
    local.get 2
    local.get 1 call $fhelp f32.reinterpret_i32 f64.promote_f32
    local.get 0 f64.add
    f64.store)

  ;; ---- GI-FPU-002 phase 3 (#369): f64 ARGS marshalled into D0/D1 ------------
  ;; $dscale does real double-precision arithmetic on BOTH its D-register args,
  ;; so passing either in a core pair (or in the wrong D-register) diverges.
  (func $dscale (param f64 f64) (result f64)
    local.get 0 local.get 1 f64.mul f64.const 2.5 f64.add)
  (func $dmix (param f64 i32) (result f64)
    local.get 0
    local.get 1 f32.reinterpret_i32 f64.promote_f32
    f64.add)

  ;; in-place sources: mem[0] -> D0, mem[8] -> D1 == the argument registers.
  (func (export "dcallargs") (param i32)
    local.get 0
    (f64.load (i32.const 0))
    (f64.load (i32.const 8))
    call $dscale
    f64.store)

  ;; CROSS-SWAPPED sources: y lives in the D0 local home, x is loaded into D1;
  ;; the call wants x in D0 and y in D1 — the two-phase frame staging must
  ;; swap them (and the D0 home doubles as a home-register argument source).
  (func (export "dcallswap") (param i32)
    (local f64)
    (local.set 1 (f64.load (i32.const 8)))  ;; y -> D0 local home
    local.get 0
    (f64.load (i32.const 0))                ;; x -> D1
    local.get 1                             ;; y (home D0)
    call $dscale                            ;; wants x in D0, y in D1
    f64.store)

  ;; MIXED int + f64 args: the core pool takes only the i32 (R0), the f64
  ;; goes to D0. dcallmix(addr, n): mem[addr] = $dmix(mem[0], n).
  (func (export "dcallmix") (param i32 i32)
    local.get 0
    (f64.load (i32.const 0))
    local.get 1
    call $dmix
    f64.store)

  ;; ---- GI-FPU-002 phase 3 (#369): f64 RESULT marshalled out of D0 -----------
  ;; The callee does real double-precision arithmetic (writes D0 and scratch),
  ;; so a caller that read the result from R0:R1 — or failed to spill its own
  ;; live double around the bl — diverges at the VALUE level.
  (func $dret (result f64)
    (f64.add (f64.load (i32.const 8)) (f64.const 2.5)))
  (func (export "dretcall") (param i32)
    local.get 0
    (f64.load (i32.const 0))        ;; live f64 (D-register) across the call
    call $dret                      ;; f64-returning callee: result in D0
    f64.add
    f64.store))
