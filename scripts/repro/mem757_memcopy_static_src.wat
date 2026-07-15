(module
  ;; #757 RED-FIRST repro attempt 2 — the actual gale MECHANISM: memmove
  ;; (`memory.copy`) whose SOURCE is a static pointer const `data_base + 0x20`
  ;; relocated by the native-pointer ABI, reached THROUGH a RawVec-grow `call`.
  ;;
  ;; Rust source shape: `dst.copy_from_slice(&STATIC_STR)` lowers to a
  ;; `memory.copy (dst_ptr, src_ptr=data_base+0x20, len)`. Under
  ;; --native-pointer-abi the `i32.const 0x100020` src pointer must relocate to
  ;; `__synth_wasm_data + 0x20`. If instead it folds/relocates to
  ;; `__synth_wasm_data + small` (e.g. the const-materialization path picks the
  ;; wrong addend), the copy reads the LOW consts [2,0,0,0,1,0,0].
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000):
  ;;   0x100000: \02\00\00\00 \01\00\00\00 ...   low consts, 0x00..0x1f
  ;;   0x100020: "gust:os up\n"                  the string at +0x20
  ;;   dst = 0x101000 (a clear .bss-ish region above the statics)
  ;;
  ;; Compile: --target cortex-m3 --native-pointer-abi --all-exports
  ;;          --relocatable --shadow-stack-size <B>
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  ;; ONE data segment: consts at 0x00..0x1f AND the string at +0x20 → the SAME
  ;; symbol, so the string source pointer has a NONZERO in-segment offset 0x20.
  (data (i32.const 1048576) "\02\00\00\00\01\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00gust:os up\n\00\00\00\00\00")
  ;; RawVec-grow: clobbers caller-saved, returns the dst base 0x101000
  (func $grow (param i32) (result i32)
    (local $x i32)
    (local.set $x (i32.const 0xdead))
    (i32.add (local.get 0) (local.get $x))
    drop
    (i32.const 1052672))  ;; 0x101000 dst base
  (func (export "copy_peek") (param i32) (result i32)
    (local $dst i32)
    (local.set $dst (call $grow (local.get 0)))
    ;; memmove: copy 11 bytes of the string (src = 0x100020) into dst (0x101000)
    (memory.copy
      (local.get $dst)          ;; dst = 0x101000
      (i32.const 1048608)       ;; src = data_base + 0x20 = 0x100020  (STATIC PTR)
      (i32.const 11))           ;; len = 11 (>= 9 → multi-chunk)
    ;; read dst byte (param 0) back
    (i32.load8_u (i32.add (local.get $dst) (local.get 0)))))
