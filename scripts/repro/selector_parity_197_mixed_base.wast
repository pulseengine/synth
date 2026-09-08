;; RQ-65-PARITY (#197) — the MIXED-IMAGE linear-memory base witness.
;;
;; A self-contained image routes PER FUNCTION between the two shipped
;; selectors: `rd`/`wr`/`rd4` take the optimized path (absolute base
;; 0x2000_0100), `bt`/`bt_rd0` are diverted to the direct selector by their
;; br_table (`[R11, rN]`-relative). Before the startup seeded R11 with the
;; function-visible base, the two halves addressed wasm byte N at SRAM
;; addresses 0x100 apart: on main, `bt_rd0(0)` returned 0 where the optimized
;; `rd()` returned 42 from the SAME data segment, and `bt(0)` returned a stale
;; 0 after `wr(7)`. `--no-optimize` images could not see the data segment at
;; all (`rd()` = 0).
;;
;; Executed by scripts/repro/selector_parity_197_differential.py, which boots
;; the shipped Reset_Handler under unicorn — the register contract is what
;; synth emits, never a harness-side re-statement. Assertions run in order on
;; ONE instance (spec semantics).
(module
  (memory (export "memory") 1)
  (data (i32.const 0) "\2a\00\00\00")
  (func (export "rd") (result i32) i32.const 0 i32.load)
  (func (export "wr") (param i32) i32.const 4 local.get 0 i32.store)
  (func (export "rd4") (result i32) i32.const 4 i32.load)
  (func (export "bt") (param i32) (result i32)
    (block (block (block (local.get 0) (br_table 0 1 2))
      (i32.const 4) (i32.load) (return))
      (i32.const 11) (return))
    (i32.const 22))
  (func (export "bt_rd0") (param i32) (result i32)
    (block (block (block (local.get 0) (br_table 0 1 2))
      (i32.const 0) (i32.load) (return))
      (i32.const 11) (return))
    (i32.const 22))
)

(assert_return (invoke "rd") (i32.const 42))
(assert_return (invoke "bt_rd0" (i32.const 0)) (i32.const 42))
(invoke "wr" (i32.const 7))
(assert_return (invoke "rd4") (i32.const 7))
(assert_return (invoke "bt" (i32.const 0)) (i32.const 7))
(assert_return (invoke "bt" (i32.const 1)) (i32.const 11))
(assert_return (invoke "bt" (i32.const 2)) (i32.const 22))
(invoke "wr" (i32.const 99))
(assert_return (invoke "bt" (i32.const 0)) (i32.const 99))
(assert_return (invoke "rd4") (i32.const 99))
