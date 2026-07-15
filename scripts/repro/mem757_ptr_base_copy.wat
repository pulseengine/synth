(module
  ;; #757 RED-FIRST repro attempt 3 — the RawVec/memmove POINTER-BASE shape:
  ;; the copy source is a runtime pointer register holding `data_base`
  ;; (== wasm_data_base == 0x100000), and the string is read as `[base + 0x20]`
  ;; through small memarg offsets (the chunk offsets of a memmove loop). This is
  ;; the else-branch / small-offset path the six 0.43.0 controls never hit —
  ;; they all folded a LARGE static memarg (>= wasm_data_base) which routes to
  ;; the #746 arm. Here the memarg offsets are SMALL (0x20, 0x28) and the base
  ;; is a pointer, exactly like loom-inlined `Vec::extend_from_slice`.
  ;;
  ;; gale symptom: head reads `data_base + small` (the low consts
  ;; [2,0,0,0,1,0,0]) instead of `data_base + 0x20` — i.e. the +0x20 base
  ;; offset is dropped for the head chunk.
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000), ONE segment:
  ;;   0x100000: \02\00\00\00 \01\00\00\00 ...   low consts, 0x00..0x1f
  ;;   0x100020: "gust:os up\n"                  the string at +0x20
  ;;   dst = 0x101000
  ;;
  ;; Compile: --target cortex-m3 --native-pointer-abi --all-exports
  ;;          --relocatable --shadow-stack-size <B>
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  (data (i32.const 1048576) "\02\00\00\00\01\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00gust:os up\n\00\00\00\00\00")
  ;; RawVec-grow: clobbers caller-saved, returns dst base 0x101000
  (func $grow (param i32) (result i32)
    (local $x i32)
    (local.set $x (i32.const 0xdead))
    (i32.add (local.get 0) (local.get $x))
    drop
    (i32.const 1052672))  ;; 0x101000
  (func (export "copy_peek") (param i32) (result i32)
    (local $src i32)   ;; source POINTER (data_base), not a folded offset
    (local $dst i32)
    ;; src = data_base pointer 0x100000 (a runtime pointer register)
    (local.set $src (i32.const 1048576))
    (local.set $dst (call $grow (local.get 0)))
    ;; HEAD wide i64 from [src + 0x20] (the string), store to [dst + 0]
    (i64.store (local.get $dst) (i64.load offset=32 (local.get $src)))
    ;; TAIL bytes 8,9,10 from [src + 0x28..0x2a], store to [dst + 8..10]
    (i64.store8 offset=8 (local.get $dst) (i64.load8_u offset=40 (local.get $src)))
    (i64.store8 offset=9 (local.get $dst) (i64.load8_u offset=41 (local.get $src)))
    (i64.store8 offset=10 (local.get $dst) (i64.load8_u offset=42 (local.get $src)))
    ;; read dst byte (param 0) back
    (i32.load8_u (i32.add (local.get $dst) (local.get 0)))))
