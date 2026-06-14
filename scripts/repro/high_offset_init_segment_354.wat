(module
  (memory (export "memory") 2)
  (global $sp (mut i32) (i32.const 65536))
  (data (i32.const 65536) "\00\00\00\00\00\00\00\00\f4\ff\ff\ff")
  (func (export "stack_push_decide") (result i32)
    ;; static address >= wasm_data_base (65536) -> __synth_wasm_data-relative
    i32.const 65544
    i32.load))
