;; VCR-RA-001 acceptance increment (#242) — i64 consecutive-PAIR exhaustion repro.
;;
;; The i64 sibling of high_pressure_i32.wat. Keeps 4 i64 constants
;; simultaneously live (4 register pairs = 8 regs; the deepest two spill via
;; the #171 pair-aware stack-spill loop) while all four i32 params are
;; reserved in r0-r3 until their last read (#193). At the first i64.add the
;; two popped operand pairs (r4-r7, extra_avoid) plus the four pinned param
;; registers leave only r8 free — no consecutive pair — and the operand stack
;; holds nothing register-resident left to spill, so pre-acceptance the
;; selector hard-failed with
;;   "register exhaustion: no consecutive pair of free registers for i64"
;; (stack spilling CANNOT recover this: the blockers are param home registers,
;; not stack values). With the param-backing retry the params are frame-backed
;; at entry (#204 machinery), freeing r0-r3, and the function compiles. The
;; fold mixes non-commutative ops (sub/xor) so an operand-order, reload, or
;; half-swap bug changes the result; the i64 result returns in r0:r1.
;;
;; Differential oracle:
;;   synth compile scripts/repro/high_pressure_i64.wat -o /tmp/hp64.elf \
;;         --target cortex-m4 --relocatable
;;   /tmp/armv/bin/python scripts/repro/high_pressure_i64_differential.py /tmp/hp64.elf
(module
  (func (export "high_pressure64") (param i32 i32 i32 i32) (result i64)
    i64.const 0x1111111111111111
    i64.const 0x2222222222222222
    i64.const 0x3333333333333333
    i64.const 0x4444444444444444
    i64.add   ;; <- pair exhaustion here pre-acceptance
    i64.sub
    i64.xor
    local.get 0
    i64.extend_i32_u
    i64.add
    local.get 1
    i64.extend_i32_u
    i64.sub
    local.get 2
    i64.extend_i32_u
    i64.xor
    local.get 3
    i64.extend_i32_u
    i64.add))
