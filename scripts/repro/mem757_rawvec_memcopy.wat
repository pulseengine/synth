(module
  ;; #757 RED-FIRST repro attempt 6 — the RawVec call-graph shape on the RUNTIME
  ;; -OFFSET axis (not the addend axis the five prior fixtures verified). gale:
  ;;   run -> func_20 -> func_16 (RawVec-grow) -> func_17 (memmove)
  ;; The `&STATIC[0]` source pointer (data_base + 0x20) is computed, held in a
  ;; LOCAL ACROSS the RawVec-grow `call` (so it must spill/reload), THEN used as
  ;; the `memory.copy` source after the grow returns. If the reload picks a
  ;; stale slot or the source register is re-derived without the +0x20, the head
  ;; chunk reads `data_base + small` (the low consts) — gale's exact symptom.
  ;;
  ;; This is the axis the prior fixtures MISSED: they verified the link-time
  ;; relocation ADDEND (all correct, seg_0 + 0x20); this exercises the RUNTIME
  ;; source-pointer VALUE surviving the call, which is a different bug class.
  ;;
  ;; Layout (wasm_data_base = sp_init = 0x100000), ONE segment:
  ;;   0x100000: \02\00\00\00 \01\00\00\00 ...   low consts, 0x00..0x1f
  ;;   0x100020: "gust:os up\n"                  the string at +0x20
  ;;
  ;; RED signature: copy_peek(0)==0x02 / low-const bytes for the head; the tail
  ;; (bytes 7..10) reads " up\n" correctly.
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
    (local $src i32)
    (local $dst i32)
    (local $len i32)
    ;; source pointer &STATIC[0] = data_base + 0x20, computed BEFORE the grow
    (local.set $src (i32.add (i32.const 1048576) (i32.const 32)))
    (local.set $len (i32.const 11))
    ;; RawVec-grow — $src and $len are live ACROSS this call (must spill/reload)
    (local.set $dst (call $grow (local.get 0)))
    ;; memmove: copy from the reloaded $src into $dst
    (memory.copy (local.get $dst) (local.get $src) (local.get $len))
    ;; read dst byte (param 0) back
    (i32.load8_u (i32.add (local.get $dst) (local.get 0)))))
