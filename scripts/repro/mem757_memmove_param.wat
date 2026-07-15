(module
  ;; #757 RED-FIRST repro attempt 4 — gale's ACTUAL func_17 shape:
  ;;   run -> func_20 -> func_16 (RawVec-grow) -> func_17 (memmove(dst,src,len))
  ;; The memmove is a SEPARATE function taking (dst, src, len) as PARAMS; the
  ;; caller applies `+0x20` to the source before the call. The body is the
  ;; classic overlapping head-i64 + tail-i32 memmove (NOT the non-overlapping
  ;; i64 + 3×i8 the six controls used):
  ;;   head: i64.store(dst,   i64.load(src))        ;; dst[0..8]
  ;;   tail: i32.store off=7(dst, i32.load off=7(src)) ;; dst[7..11], fixes byte 7
  ;; Net for an 11-byte copy: bytes 0..6 from the HEAD source, 7..10 from the
  ;; TAIL source. gale: 0..6 WRONG (low consts), 7..10 RIGHT — head and tail
  ;; derive the source base DIFFERENTLY, so one is miscomputed.
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000), ONE segment:
  ;;   0x100000: \02\00\00\00 \01\00\00\00 ...   low consts, 0x00..0x1f
  ;;   0x100020: "gust:os up\n"                  the string at +0x20
  ;;
  ;; RED signature: copy_peek(0)==0x02, copy_peek(4)==0x01 (head read
  ;; data_base+0 = the low consts) while copy_peek(7..10) == " up\n".
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
  ;; func_17: overlapping head-i64 + tail-i32 memmove(dst, src, len)
  (func $memmove (param $dst i32) (param $src i32) (param $len i32)
    (local $t i32)
    ;; some register pressure so the base temps don't trivially survive
    (local.set $t (i32.add (local.get $len) (i32.const 3)))
    (local.set $t (i32.and (local.get $t) (i32.const -4)))
    ;; head: dst[0..8] = src[0..8]
    (i64.store (local.get $dst) (i64.load (local.get $src)))
    ;; tail: dst[7..11] = src[7..11]  (overlap fixes byte 7)
    (i32.store offset=7 (local.get $dst) (i32.load offset=7 (local.get $src))))
  (func (export "copy_peek") (param i32) (result i32)
    (local $dst i32)
    (local.set $dst (call $grow (local.get 0)))
    ;; caller applies +0x20 to the source (the &STATIC[0] pointer) and calls
    ;; the separate memmove — the +0x20 is applied HERE, not in func_17.
    (call $memmove
      (local.get $dst)
      (i32.add (i32.const 1048576) (i32.const 32))  ;; src = data_base + 0x20
      (i32.const 11))
    ;; read dst byte (param 0) back
    (i32.load8_u (i32.add (local.get $dst) (local.get 0)))))
