;; #916 — i64 zero-fill mis-encodes for a HIGH destination (R8-R12).
;;
;; The 16-bit `MOVS Rd,#imm8` (T1) has a THREE-bit Rd field. `reg_to_bits(R8)`
;; is 8, so `8 << 8 = 0x0800` and `0x2000 | 0x0800 = 0x2800` — the emitted
;; halfword is `CMP r0,#0`, not a move. The half that must be zeroed is NEVER
;; WRITTEN and keeps whatever the destination register held.
;;
;; Reachability was already established: `rv32_cmp_select_472.wat` at
;; `-b arm --target cortex-m4` emits `I64ShrU { rd_hi: R8, .. }` today, with an
;; allocator pool of R0-R8. It is unobservable THERE only because an
;; `I32WrapI64` discards the high half one instruction later — luck, not a
;; guarantee. This module removes the luck: every export KEEPS the half the
;; broken instruction was supposed to zero.
;;
;; * `shru_keep_high`  — i64.shr_u(x, n) for n >= 32 must have high half 0.
;;                       Returns the FULL i64, so a stale high half is visible.
;; * `shl_keep_low`    — i64.shl(x, n) for n >= 32 must have low half 0.
;; * `clz64` / `ctz64` — i64.clz/i64.ctz return i64; the high word is cleared
;;                       UNCONDITIONALLY (no `n >= 32` precondition), so these
;;                       were miscompiled for a high `rnhi` on every input.
;; * `extend_u64`      — i64.extend_i32_u clears the high word unconditionally.
;; * `pressure_shru`   — the same shr_u under enough live-pair pressure to push
;;                       the destination into the high half of the R0-R8 pool,
;;                       with four i32 params pinned in r0-r3 (#193/#204).
;;
;; Both shift amounts straddle 32 (the branch that selects the large-shift arm)
;; so the differential also exercises the `B .done` displacement, which had to
;; be widened when the zero-fill grew from 2 bytes to 4.
;;
;; Differential oracle:
;;   synth compile scripts/repro/i64_high_reg_zero_fill_916.wat -o /tmp/zf916.elf \
;;         --target cortex-m4 --relocatable --all-exports
;;   python scripts/repro/i64_high_reg_zero_fill_916_differential.py /tmp/zf916.elf
(module
  ;; i64.shr_u keeping the HIGH half. n is a runtime value so the n<32 / n>=32
  ;; branch is genuinely taken at run time, not folded.
  (func (export "shru_keep_high") (param i32) (result i64)
    i64.const 0xFEDCBA9876543210
    local.get 0
    i64.extend_i32_u
    i64.shr_u)

  ;; i64.shl keeping the LOW half.
  (func (export "shl_keep_low") (param i32) (result i64)
    i64.const 0xFEDCBA9876543210
    local.get 0
    i64.extend_i32_u
    i64.shl)

  ;; i64.shr_s — the control: its large-shift arm sign-fills with the 32-bit
  ;; ASR.W (4-bit Rd), so it was never defective. A regression here would mean
  ;; the fix damaged a neighbouring expansion.
  (func (export "shrs_keep_high") (param i32) (result i64)
    i64.const 0xFEDCBA9876543210
    local.get 0
    i64.extend_i32_u
    i64.shr_s)

  ;; i64.clz / i64.ctz — high word cleared unconditionally.
  (func (export "clz64") (param i32) (result i64)
    local.get 0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.clz)

  (func (export "ctz64") (param i32) (result i64)
    local.get 0
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.ctz)

  ;; i64.extend_i32_u — high word cleared unconditionally. Returned whole, so a
  ;; stale high half is visible.
  (func (export "extend_u64") (param i32) (result i64)
    local.get 0
    i64.extend_i32_u)

  ;; Pressure variant: four i32 params pinned in r0-r3 until their last read
  ;; plus several simultaneously-live i64 pairs, so the shift destination is
  ;; pushed toward the top of the R0-R8 allocator pool. The fold mixes
  ;; non-commutative ops so an operand-order or half-swap bug also shows.
  (func (export "pressure_shru") (param i32 i32 i32 i32) (result i64)
    i64.const 0x1111111111111111
    i64.const 0x2222222222222222
    i64.xor
    i64.const 0xFEDCBA9876543210
    local.get 0
    i64.extend_i32_u
    i64.shr_u
    i64.add
    local.get 1
    i64.extend_i32_u
    i64.sub
    i64.const 0x3333333333333333
    local.get 2
    i64.extend_i32_u
    i64.shl
    i64.xor
    local.get 3
    i64.extend_i32_u
    i64.add))
