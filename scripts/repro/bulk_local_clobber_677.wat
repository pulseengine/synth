(module
  ;; #677 — memory.copy/memory.fill clobber a local dest/src/len operand that is
  ;; reused AFTER the op (the lowering mutated the popped register in place as
  ;; the loop pointer / byte buffer, with no scratch copy).
  (memory 1)
  (export "memory" (memory 0))

  ;; dst is a local, read back after the copy (issue reproducer 1).
  ;; wasmtime: i32.load([dst]) = the copied word. pre-fix synth: wild pointer.
  (func (export "cpy_dst") (param i32 i32) (result i32)
    (i32.store (i32.const 16) (i32.const 67305985))          ;; 0x04030201 at [16]
    (memory.copy (local.get 0) (i32.const 16) (local.get 1))
    (i32.load (local.get 0)))

  ;; memory.fill, dst is a local read back after (issue reproducer 2).
  (func (export "fil_dst") (param i32 i32) (result i32)
    (memory.fill (local.get 0) (i32.const 66) (local.get 1))
    (i32.load8_u (local.get 0)))

  ;; len operand reused after the copy (issue reproducer 3).
  ;; pre-fix synth returned the last byte copied (len recycled as byte buffer).
  (func (export "cpy_len") (param i32 i32) (result i32)
    (i32.store (i32.const 16) (i32.const 99))
    (memory.copy (i32.const 32) (i32.const 16) (local.get 1))
    (local.get 1))

  ;; src operand reused after the copy.
  (func (export "cpy_src") (param i32 i32) (result i32)
    (i32.store (i32.const 16) (i32.const 168496141))         ;; 0x0A0B0C0D at [16]
    (memory.copy (i32.const 64) (local.get 0) (local.get 1))
    (local.get 0))

  ;; control: const dest — unaffected pre-fix, isolates the local-operand bug.
  (func (export "cpy_const") (param i32 i32) (result i32)
    (i32.store (i32.const 16) (i32.const 67305985))
    (memory.copy (i32.const 32) (i32.const 16) (local.get 1))
    (i32.load (i32.const 32))))
