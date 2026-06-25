;; perf repro (#472, epic #242): constant shift amounts on RV32.
;;
;; `i32.shl/shr_u/shr_s (value) (i32.const N)` lowers on RV32 as
;; `addi tmp, zero, N ; sll/srl/sra rd, value, tmp` — the amount is first
;; materialized into a register, then consumed by the register-form shift. RV32
;; has immediate shift forms `slli/srli/srai` that carry the amount in the
;; instruction, so folding a constant amount drops the `addi` (one instruction
;; per constant shift). The immediate-shift-fold lever does this fold.
;;
;; The fixture covers the cases the fold's masking must get right:
;;   * amount >= 32 (`shl33`): WASM shifts mod 32, the register `sll` masks
;;     `rs2[4:0]` in hardware — the fold must mask `shamt = N & 31` to match
;;     (33 -> 1).
;;   * negative amount (`shlneg`): `i32.const -1` -> mask 31.
;;   * a VARIABLE shift (`shlvar`): the amount is not a constant, so it must NOT
;;     fold — it stays a register `sll` and is byte-identical flag-off vs flag-on.
;;
;; Generic values — exhibits the pattern, tied to nothing real.
(module
  (memory 1)
  (export "memory" (memory 0))
  (func (export "shl8") (param i32) (result i32)
    (i32.shl (local.get 0) (i32.const 8)))
  (func (export "shru4") (param i32) (result i32)
    (i32.shr_u (local.get 0) (i32.const 4)))
  (func (export "shrs4") (param i32) (result i32)
    (i32.shr_s (local.get 0) (i32.const 4)))
  (func (export "shl33") (param i32) (result i32)      ;; amount >= 32 -> mask to 1
    (i32.shl (local.get 0) (i32.const 33)))
  (func (export "shlneg") (param i32) (result i32)     ;; amount -1 -> mask to 31
    (i32.shl (local.get 0) (i32.const -1)))
  (func (export "shlvar") (param i32) (param i32) (result i32)  ;; variable -> NOT folded
    (i32.shl (local.get 0) (local.get 1))))
