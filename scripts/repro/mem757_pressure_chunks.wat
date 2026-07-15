(module
  ;; #757 RED-FIRST repro attempt 7 — HIGH REGISTER PRESSURE multi-chunk copy.
  ;; gale's func_17 lives in a 13-function module with real pressure; the six
  ;; prior fixtures were low-pressure. Here many i64 chunks are copied with many
  ;; live locals across the copy, forcing alloc_temp_or_spill / the #746 base
  ;; temp to genuinely spill BETWEEN the head and tail chunks. If a chunk's base
  ;; temp is spilled and the reload aliases a wrong slot, the head reads
  ;; `data_base + small`.
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000), ONE segment, 8 i64 chunks =
  ;; 64 bytes of distinct content at +0x20:
  ;;   0x100000: low consts 0x00..0x1f
  ;;   0x100020..0x10005f: 8 distinct i64 words
  ;;
  ;; Compile: --target cortex-m3 --native-pointer-abi --all-exports
  ;;          --relocatable --shadow-stack-size <B>
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  (data (i32.const 1048576)
    "\02\00\00\00\01\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00\11\11\11\11\11\11\11\11\22\22\22\22\22\22\22\22\33\33\33\33\33\33\33\33\44\44\44\44\44\44\44\44\55\55\55\55\55\55\55\55\66\66\66\66\66\66\66\66\77\77\77\77\77\77\77\77\88\88\88\88\88\88\88\88")
  (func $grow (param i32) (result i32)
    (local $x i32)
    (local.set $x (i32.const 0xdead))
    (i32.add (local.get 0) (local.get $x))
    drop
    (i32.const 1052672))  ;; dst 0x101000
  (func (export "copy_peek") (param i32) (result i32)
    (local $idx i32)
    (local $dst i32)
    (local $a i32) (local $b i32) (local $c i32) (local $d i32)
    (local.set $idx (i32.const 0))
    (local.set $dst (call $grow (local.get 0)))
    ;; keep many live values across the chunk copies to raise pressure
    (local.set $a (i32.add (local.get 0) (i32.const 1)))
    (local.set $b (i32.add (local.get 0) (i32.const 2)))
    (local.set $c (i32.add (local.get 0) (i32.const 3)))
    (local.set $d (i32.add (local.get 0) (i32.const 4)))
    ;; 8 i64 chunks from static [idx + 0x100020 + k*8] into dst, #746 wide arm
    (i64.store offset=0  (local.get $dst) (i64.load offset=1048608 (local.get $idx)))
    (i64.store offset=8  (local.get $dst) (i64.load offset=1048616 (local.get $idx)))
    (i64.store offset=16 (local.get $dst) (i64.load offset=1048624 (local.get $idx)))
    (i64.store offset=24 (local.get $dst) (i64.load offset=1048632 (local.get $idx)))
    (i64.store offset=32 (local.get $dst) (i64.load offset=1048640 (local.get $idx)))
    (i64.store offset=40 (local.get $dst) (i64.load offset=1048648 (local.get $idx)))
    (i64.store offset=48 (local.get $dst) (i64.load offset=1048656 (local.get $idx)))
    (i64.store offset=56 (local.get $dst) (i64.load offset=1048664 (local.get $idx)))
    ;; consume the pressure locals so they stay live across the copy
    (i32.add (i32.add (local.get $a) (local.get $b))
             (i32.add (local.get $c) (local.get $d)))
    drop
    ;; read dst byte (param 0) back
    (i32.load8_u (i32.add (local.get $dst) (local.get 0)))))
