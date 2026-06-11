;; VCR-RA-001 step 3b-lite (#242) — i32 register-pressure exhaustion repro.
;;
;; Keeps 10 i32 constants simultaneously live on the operand stack while both
;; params (r0/r1) are reserved until their last read: the R0–R8 pool (9 regs,
;; after the #212 R12 reserve) exhausts at the 8th const, and pre-3b the
;; selector hard-failed with
;;   "register exhaustion: all allocatable registers are live on the stack"
;; instead of spilling. With the spill-on-exhaustion retry the deepest stack
;; values spill to the frame's i64-spill area and reload on pop (#171
;; machinery), so the function compiles; the fold uses non-commutative ops
;; (sub/xor) so any operand-order or reload bug changes the result.
;;
;; Differential oracle:
;;   synth compile scripts/repro/high_pressure_i32.wat -o /tmp/hp.elf \
;;         --target cortex-m4 --relocatable
;;   /tmp/armv/bin/python scripts/repro/high_pressure_i32_differential.py /tmp/hp.elf
(module
  (func (export "high_pressure") (param i32 i32) (result i32)
    i32.const 3
    i32.const 5
    i32.const 7
    i32.const 11
    i32.const 13
    i32.const 17
    i32.const 19
    i32.const 23
    i32.const 29
    i32.const 31
    i32.mul   ;; 29*31
    i32.add   ;; 23 + 899
    i32.xor   ;; 19 ^ 922
    i32.add   ;; 17 + 937
    i32.sub   ;; 13 - 954
    i32.add   ;; 11 + (-941)
    i32.mul   ;; 7 * (-930)
    i32.xor   ;; 5 ^ (-6510)
    i32.sub   ;; 3 - (5 ^ -6510)
    local.get 0
    i32.add
    local.get 1
    i32.xor))
