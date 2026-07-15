(module
  ;; #757 RED-FIRST repro attempt 5 — gale's INLINED memmove shape. loom inlines
  ;; func_17 into the caller, so the source-relocation, the RawVec-grow `call`,
  ;; the head+tail chunks, AND register pressure / const-CSE all live in ONE
  ;; function. The head chunk routes through the #746 large-memarg arm
  ;; (offset >= wasm_data_base), the overlapping i32 tail through a small-offset
  ;; path — head and tail derive the source base DIFFERENTLY.
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000), ONE segment:
  ;;   0x100000: \02\00\00\00 \01\00\00\00 ...   low consts, 0x00..0x1f
  ;;   0x100020: "gust:os up\n"                  the string at +0x20
  ;;
  ;; RED signature: copy_peek(0)==0x02, copy_peek(4)==0x01 (head read
  ;; data_base + small = the low consts) while copy_peek(7..10) == " up\n".
  ;;
  ;; Compile: --target cortex-m3 --native-pointer-abi --all-exports
  ;;          --relocatable --shadow-stack-size <B>
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  (data (i32.const 1048576) "\02\00\00\00\01\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00gust:os up\n\00\00\00\00\00")
  (func $grow (param i32) (result i32)
    (local $x i32)
    (local.set $x (i32.const 0xdead))
    (i32.add (local.get 0) (local.get $x))
    drop
    (i32.const 1052672))  ;; dst 0x101000
  (func (export "copy_peek") (param i32) (result i32)
    (local $idx i32)   ;; dynamic index (0) — forces the #746 dynamic-index arm
    (local $dst i32)
    (local.set $idx (i32.const 0))
    (local.set $dst (call $grow (local.get 0)))
    ;; HEAD wide i64 from static source via LARGE memarg (#746 arm):
    ;;   source = __synth_wasm_data + 0x100020 + idx  (idx = 0)
    ;;   dest   = dst
    (i64.store (local.get $dst) (i64.load offset=1048608 (local.get $idx)))
    ;; overlapping i32 TAIL from static source at offset 0x100027 (bytes 7..10),
    ;; store to dst+7 — a DIFFERENT lowering path than the wide head.
    local.get $dst
    (i32.wrap_i64 (i64.load32_u offset=1048615 (local.get $idx)))
    i32.store offset=7
    ;; read dst byte (param 0) back
    (i32.load8_u (i32.add (local.get $dst) (local.get 0)))))
