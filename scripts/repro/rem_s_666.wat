;; #666 — rv32 i32.rem_s(INT_MIN, -1) spuriously trapped.
;;
;; WASM Core §4.3.2: irem_s(INT_MIN, -1) = 0, NO trap — only idiv_s traps on
;; the INT_MIN/-1 overflow. The rv32 selector shared div_s's INT_MIN/-1
;; ebreak guard with rem_s; RISC-V M-ext `rem` already returns 0 for the
;; overflow case, so the guard was pure over-trap. Twin of the ARM #633
;; fix-guard pin.
(module
  (func (export "rems") (param i32 i32) (result i32)
    (i32.rem_s (local.get 0) (local.get 1)))
  (func (export "divs") (param i32 i32) (result i32)
    (i32.div_s (local.get 0) (local.get 1))))
