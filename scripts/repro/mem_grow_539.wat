;; #539 — `memory.grow(0)` must return the CURRENT page count, not the
;; fixed-memory `-1` sentinel. Growing by zero pages can never fail (WASM Core
;; §4.4.7), so `memory.grow(0)` returns the current size; a guest doing
;; `if (memory.grow(0) < 0) trap;` (a legal "read/validate current size" idiom)
;; wrongly faulted because every `memory.grow` lowered to a constant -1.
;;
;; The fix folds the `i32.const 0; memory.grow` idiom to `memory.size`
;; (semantically identical) up front, which also surfaced + fixed a latent
;; optimized-path bug where `memory.size` returned BYTES (MOV R10) instead of
;; PAGES (LSR R10,#16). A non-zero delta keeps -1 (fixed memory genuinely cannot
;; grow).
(module
  (memory 3)
  ;; current size in pages — must be 3
  (func (export "sz") (result i32) (memory.size))
  ;; grow by 0 -> current size (3), NOT -1
  (func (export "grow0") (result i32) (memory.grow (i32.const 0)))
  ;; grow by >0 on fixed memory -> -1 (acceptable: cannot grow)
  (func (export "grow2") (result i32) (memory.grow (i32.const 2))))
