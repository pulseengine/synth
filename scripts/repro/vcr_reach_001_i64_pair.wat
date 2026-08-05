(module
  (memory (export "memory") 1)

  ;; VCR-REACH-001 (VCR-DEC-001 increment 4, #242) — EXECUTION fixtures for the
  ;; i64 register-PAIR op model (`liveness::pair_effect`).
  ;;
  ;; The pass and BOTH dataflow validators consume that one definition, so
  ;; neither of them can catch an error IN it — the #872 lesson, and the reason
  ;; v0.53 and v0.54 each shipped a miscompile that both liveness-equation
  ;; instruments accepted. Only execution can. Each function below is built so a
  ;; specific WRONG model produces a WRONG VALUE, i.e. so the mutation matrix in
  ;; `vcr_dec_001_join_alloc_execution_differential.py` is non-vacuous.
  ;;
  ;; Every result is i32 so the harness can compare it in R0 alone; an i64 half
  ;; that must be right is folded down explicitly, never left to hide behind a
  ;; truncation.
  ;;
  ;; NO `(data …)` SEGMENT, deliberately. On this compile path
  ;; (`-b arm --target cortex-m4`, no `--cortex-m`) `.linear_memory` is emitted
  ;; SHT_NOBITS, so the emulator would start from zeroed memory while wasmtime
  ;; starts from the initialised image — every load would then differ for a
  ;; reason that has nothing to do with the allocator. The load fixtures SEED the
  ;; memory they read, inside the same call, so both engines observe the same
  ;; bytes by construction.

  ;; ---- (A) the shift-amount CLOBBER -------------------------------------
  ;;
  ;; `I64Shl`'s expansion opens with `AND rm_lo, rm_lo, #63` (an RMW of the
  ;; shift amount) and uses `rm_hi` as a pure scratch temp. `pair_effect` lists
  ;; BOTH as DEFS. Drop them and the model claims the shift amount survives the
  ;; shift — so the colourer may home a live value there, and the value is
  ;; silently destroyed.
  ;;
  ;; `$k` is deliberately kept LIVE ACROSS the shift (the `i64.xor` reads it
  ;; again) and deliberately NOT pre-masked: at `s = 100` the low half goes in as
  ;; 100 and comes out as `100 & 63 = 36`, so a model that thinks it survives is
  ;; off by a value the xor exposes. A pre-masked amount would make the `AND` a
  ;; no-op and this fixture would pass under the mutated model — vacuous
  ;; coverage that reads exactly like a green gate.
  ;;
  ;; Both sides of the expansion's internal `BPL` are driven by the caller
  ;; (`s < 32` and `s >= 32`): the shift distinctness constraints are
  ;; PATH-dependent, so a one-sided input set would never execute the arm whose
  ;; register the colourer moved.
  (func (export "shl_amt_live") (param $x i32) (param $s i32) (result i32)
    (local $k i64)
    (local.set $k (i64.extend_i32_s (local.get $s)))
    (i32.wrap_i64
      (i64.xor
        (i64.shl (i64.extend_i32_s (local.get $x)) (local.get $k))
        (local.get $k))))

  ;; The same shape reading the HIGH half of the result, so a mis-modelled
  ;; `rm_hi` (the pure temp clobber — the half a low-word-only check cannot see)
  ;; is observable too.
  (func (export "shl_amt_live_hi") (param $x i32) (param $s i32) (result i32)
    (local $k i64)
    (local.set $k (i64.extend_i32_s (local.get $s)))
    (i32.wrap_i64
      (i64.shr_u
        (i64.xor
          (i64.shl (i64.extend_i32_s (local.get $x)) (local.get $k))
          (local.get $k))
        (i64.const 32))))

  ;; `i64.shr_u`'s expansion writes `rd_lo` early instead of `rd_hi`, so its
  ;; distinctness set is the mirror image of `i64.shl`'s. Same live-amount trick.
  (func (export "shru_amt_live") (param $x i32) (param $s i32) (result i32)
    (local $k i64)
    (local.set $k (i64.extend_i32_s (local.get $s)))
    (i32.wrap_i64
      (i64.xor
        (i64.shr_u (i64.extend_i32_s (local.get $x)) (local.get $k))
        (local.get $k))))

  ;; ---- (B) the I64Ldr EARLY-CLOBBER --------------------------------------
  ;;
  ;; `I64Ldr` expands to `LDR rdlo,[base,#off]; LDR rdhi,[base,#off+4]`. The
  ;; SECOND load re-reads `base` AFTER the first has written `rdlo`, so the two
  ;; must be different registers — an obligation a defs/uses pair structurally
  ;; cannot state, carried by `pair_early_clobber` as an interference edge.
  ;;
  ;; `$a` is DEAD after the load, which is the whole point: ordinary liveness
  ;; then says `base` is free, and a plain interference graph will happily
  ;; coalesce `rdlo` onto it. A fixture whose address stayed live would be
  ;; forbidden by ordinary liveness alone and would prove nothing about the edge.
  ;;
  ;; BOTH halves are folded into the result — the low one directly, the high one
  ;; by storing the pair to a fixed scratch slot and reading its upper word back
  ;; with a plain 32-bit load. That is exact (no `shr_u`, whose high-half
  ;; destination lands on R8 here and trips the `i64-16bit-form-high-reg`
  ;; decline), and it puts the evidence in the compared memory window as well as
  ;; in R0. `$lo`/`$hi` are caller-supplied, so the loaded pair differs per input
  ;; instead of every case reading the same zeros.
  (func (export "ld_dead_base") (param $p i32) (param $lo i32) (param $hi i32)
        (result i32)
    (local $a i32)
    (local $v i64)
    (local.set $a (i32.and (local.get $p) (i32.const 0xF8)))
    (i32.store (local.get $a) (local.get $lo))
    (i32.store offset=4 (local.get $a) (local.get $hi))
    (local.set $v (i64.load (local.get $a)))
    (i64.store (i32.const 0x100) (local.get $v))
    (i32.xor (i32.wrap_i64 (local.get $v))
             (i32.load offset=4 (i32.const 0x100))))

  ;; The low half alone, with the address a computed temporary rather than a
  ;; local — a different colouring shape for the same obligation.
  (func (export "ld_dead_base_lo") (param $p i32) (param $lo i32) (result i32)
    (i32.store (i32.and (local.get $p) (i32.const 0xF8)) (local.get $lo))
    (i32.wrap_i64
      (i64.load (i32.and (local.get $p) (i32.const 0xF8)))))

  ;; ---- (C) store + round trip -------------------------------------------
  ;;
  ;; `I64Str`'s halves are SOURCES, not destinations — the one place a def/use
  ;; inversion in `rewrite_op` would be silent (a `d()` where a `u()` belongs).
  ;; Stored, then read back through a SEPARATE `I64Ldr`, so both the compared
  ;; memory window and the returned value carry the evidence.
  ;;
  ;; The stored pair is built with `i64.shl`/`i64.xor` rather than `i64.mul`:
  ;; `I64Mul` is NOT in `pair_effect`'s modeled set (a named next increment), so
  ;; it would decline the whole function and this case would gate nothing.
  (func (export "st_then_ld") (param $p i32) (param $v i32) (result i32)
    (local $a i32)
    (local.set $a (i32.and (local.get $p) (i32.const 0xF8)))
    (i64.store (local.get $a)
               (i64.xor (i64.extend_i32_s (local.get $v))
                        (i64.shl (i64.extend_i32_s (local.get $v))
                                 (i64.const 32))))
    (i32.wrap_i64
      (i64.xor (i64.load (local.get $a)) (i64.const 0x5A5A5A5A5A5A5A5A))))

  ;; ---- (D) the comparison chain ------------------------------------------
  ;;
  ;; `I64SetCond` reads all four halves and writes one boolean; on the ordered
  ;; arms `rd` is ALSO the discarded `SBCS` destination. Both branch directions
  ;; are driven by the caller, and the `i64.eq` arm (a different expansion, with
  ;; the `IT EQ; CMP` high-half chain) is exercised alongside `i64.lt_s`.
  (func (export "cmp64") (param $a i32) (param $b i32) (result i32)
    (i32.add
      (i64.lt_s (i64.extend_i32_s (local.get $a)) (i64.extend_i32_s (local.get $b)))
      (i32.mul
        (i32.const 2)
        (i64.eq (i64.extend_i32_s (local.get $a)) (i64.extend_i32_s (local.get $b))))))
)
