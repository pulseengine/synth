(module
  ;; #739 companion: an SP global + 17-page memory but NO static/global access
  ;; in the code — the generated object carries no __synth_wasm_data /
  ;; __synth_globals relocation, so there is no native-pointer region and
  ;; nothing for --shadow-stack-size to shrink. Pre-fix this shape compiled
  ;; "green" with the flag SILENTLY ignored (and, on the #739 fixture, with
  ;; 1 MiB of statics dropped); post-fix it must refuse loudly.
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  (func (export "run") (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add))
