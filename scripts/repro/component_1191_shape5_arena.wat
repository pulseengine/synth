;; #1191 shape 5: a component whose core module imports env::__cabi_arena_realloc,
;; satisfied by a SECOND core module. On the self-contained Cortex-M path the
;; #418 arena binder reads the bytes BEFORE decode; without the CLI-level
;; refusal it rewrote the component and failed with a misleading
;; "#418 internal ... (bug)" error. wasmtime: g() = 64.
(component
  (core module $A
    (import "env" "__cabi_arena_realloc" (func $r (param i32 i32 i32 i32) (result i32)))
    (memory (export "memory") 1)
    (func (export "g") (result i32) (call $r (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 16))))
  (core module $E (func (export "__cabi_arena_realloc") (param i32 i32 i32 i32) (result i32) i32.const 64))
  (core instance $e (instantiate $E))
  (core instance $a (instantiate $A (with "env" (instance $e))))
  (func $g (result u32) (canon lift (core func $a "g")))
  (export "g" (func $g)))
