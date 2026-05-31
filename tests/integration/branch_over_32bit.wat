;; Regression fixture for #202: an `if` whose then-block contains a 32-bit
;; Thumb-2 instruction (movw+movt to materialize a >16-bit constant). The
;; BEQ that skips the then-block must target an instruction boundary, not the
;; middle of the 32-bit movw. Pre-#202 the branch encoded as `beq #0` and
;; landed mid-instruction → UsageFault on hardware.
(module
  (memory 1)
  (func (export "f") (param i32) (result i32)
    local.get 0
    if (result i32)
      i32.const 70000   ;; > 0xFFFF -> movw + movt (two 32-bit instructions)
    else
      i32.const 1
    end))
