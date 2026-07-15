(module
  ;; #757 CONTROL (NOT a repro): value-live-across-call static i64 copy is
  ;; CORRECT. This is one of six faithful reconstructions of gale's gust:os
  ;; v0.4.0 static-string copy shape, ALL of which compile CORRECTLY on 0.43.0
  ;; once the R_ARM_THM_CALL relocation is resolved in the differential harness
  ;; (see wide_static_copy_757_differential.py).
  ;;
  ;; The #757 triage hypothesis — "the per-chunk SOURCE ADDRESS relocation is
  ;; wrong for the HEAD chunk (addend uses the wrong chunk index)" — is
  ;; EMPIRICALLY FALSE for every shape reproducible from the issue text:
  ;;   * symmetric i64 head+tail, differing static memarg offsets
  ;;   * asymmetric i64 wide head + i64 narrow tail bytes
  ;;   * const-index and const-source-address chunks
  ;;   * the `memory.copy` opcode from a static source
  ;;   * a high-register-pressure loop copy
  ;;   * THIS one: the copy source/index LIVE ACROSS an internal call
  ;;     (gale's func_17 is reached through RawVec-grow func_16, a real `call`)
  ;; In all of them the emitted relocation addend AND the runtime base register
  ;; are correct, and execution matches wasmtime byte-for-byte.
  ;;
  ;; Kept as a REGRESSION CONTROL: the call-crossing shape (which the #746
  ;; single-load fixtures never exercised) copies "gust:os up\n" correctly.
  ;;
  ;; Compile: --target cortex-m3 --native-pointer-abi --all-exports
  ;;          --relocatable --shadow-stack-size <B>
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  (data (i32.const 1048608) "gust:os up\n\00\00\00\00\00")
  ;; a callee that clobbers registers (grows a "vec": returns dst base)
  (func $grow (param i32) (result i32)
    (local $x i32)
    (local.set $x (i32.const 0xdead))
    (i32.add (local.get 0) (local.get $x))
    drop
    (i32.const 1048576))  ;; dst base 0x100000
  (func (export "copy_peek") (param i32) (result i32)
    (local $idx i32)
    (local $dst i32)
    ;; establish a live index, then call grow (clobbers caller-saved)
    (local.set $idx (i32.const 0))
    (local.set $dst (call $grow (local.get 0)))
    ;; HEAD wide i64 from static source at (idx) + static offset — idx live
    ;; across the call above
    local.get $idx
    local.get $idx
    (i64.load offset=1048608)
    (i64.store offset=1048576)
    ;; TAIL bytes 8,9,10
    (i64.store8 offset=1048584 (local.get $idx) (i64.load8_u offset=1048616 (local.get $idx)))
    (i64.store8 offset=1048585 (local.get $idx) (i64.load8_u offset=1048617 (local.get $idx)))
    (i64.store8 offset=1048586 (local.get $idx) (i64.load8_u offset=1048618 (local.get $idx)))
    (i32.wrap_i64 (i64.load8_u offset=1048576 (local.get 0)))))
