(module
  ;; #757 RED-FIRST repro (v0.45 Lane 1) — the shape the six 0.43.0 controls
  ;; MISSED: the wide-head chunk-source addend miscomputation is MASKED unless
  ;; there is initialized data BELOW the copied string inside the SAME
  ;; `__synth_wasm_data` region.
  ;;
  ;; gale's mechanism-neutral 0.43.1 re-test: `.data` holds small consts at
  ;; offsets 0x00..0x1f AND the string "gust:os up\n" at 0x20. The copy reads
  ;; `data_base + small_offset` instead of `data_base + 0x20`, so output bytes
  ;; 0..6 come back as the LOW-offset const region = [2,0,0,0,1,0,0], while
  ;; bytes 7..10 (" up\n") are correct (the tail arm relocates right).
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000):
  ;;   0x100000: \02\00\00\00 \01\00\00\00 ...  small consts, 0x00..0x1f
  ;;   0x100020: "gust:os up\n"                 the string, at +0x20
  ;;
  ;; The head i64 chunk is copied from a STATIC source at data_base+0x20 through
  ;; the #746 i64 wide load/store arm, reached THROUGH a RawVec-grow `call`. If
  ;; the wide arm folds the wrong addend, copy_peek(0..6) returns the low consts.
  ;;
  ;; Compile: --target cortex-m3 --native-pointer-abi --all-exports
  ;;          --relocatable --shadow-stack-size <B>
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  ;; ONE data segment (gale's real topology): consts at 0x00..0x1f AND the
  ;; string "gust:os up\n" at +0x20, in the SAME `(data)` directive → the SAME
  ;; `__synth_wasm_seg_0` symbol. The string's in-segment offset is a NONZERO
  ;; 0x20. Two separate directives would give the string its own symbol with
  ;; addend 0, MASKING a zeroed/mangled chunk-source addend — that is exactly
  ;; why the six 0.43.0 controls stayed green. With one segment, a wrong head
  ;; addend of 0 reads seg_0+0 = [2,0,0,0,1,0,0] = gale's leaked bytes.
  (data (i32.const 1048576) "\02\00\00\00\01\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00gust:os up\n\00\00\00\00\00")
  ;; a callee that clobbers registers (grows a "vec": returns dst base)
  (func $grow (param i32) (result i32)
    (local $x i32)
    (local.set $x (i32.const 0xdead))
    (i32.add (local.get 0) (local.get $x))
    drop
    (i32.const 1048576))  ;; dst base 0x100000 (we overwrite the consts region,
                          ;; but copy_peek reads back the DEST, which must equal
                          ;; the STRING bytes if the copy sourced correctly)
  (func (export "copy_peek") (param i32) (result i32)
    (local $idx i32)
    (local $dst i32)
    (local.set $idx (i32.const 0))
    (local.set $dst (call $grow (local.get 0)))
    ;; HEAD wide i64 from static source at (idx) + static offset 0x100020 —
    ;; idx live across the call above. Dest 0x100000 (dst base, the LOW region).
    local.get $idx
    local.get $idx
    (i64.load offset=1048608)
    (i64.store offset=1048576)
    ;; TAIL bytes 8,9,10 (" up\n")
    (i64.store8 offset=1048584 (local.get $idx) (i64.load8_u offset=1048616 (local.get $idx)))
    (i64.store8 offset=1048585 (local.get $idx) (i64.load8_u offset=1048617 (local.get $idx)))
    (i64.store8 offset=1048586 (local.get $idx) (i64.load8_u offset=1048618 (local.get $idx)))
    ;; read byte (param 0) back from the DEST (0x100000)
    (i32.wrap_i64 (i64.load8_u offset=1048576 (local.get 0)))))
