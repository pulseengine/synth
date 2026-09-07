;; RQ-64-ARM64LINUX — the arm64-Linux HOST-LIBRARY fixture.
;;
;; Shaped so that ONE object exercises every boundary a real host integration
;; crosses, because each is a separate way the "links into a normal static
;; library" claim can be false:
;;
;;   * host -> synth calls through AAPCS64 in BOTH register files and both
;;     widths (`add` w-regs, `mul64` x-regs, `f64_scale` d-regs);
;;   * synth -> host: `via_import` and `below_call` call the IMPORTED
;;     `env.host_add`, which becomes a GLOBAL SHN_UNDEF symbol the host
;;     linker binds to the harness's C definition (R_AARCH64_CALL26);
;;   * synth -> synth: `helper_chain` calls the NON-exported `$sub`
;;     (R_AARCH64_CALL26 resolved within the object);
;;   * linear memory through the `x28` precondition — `store_load` writes a
;;     word the HARNESS then reads back from its own buffer, and `load8u`
;;     reads a byte the harness wrote — so the base the embedder chose and
;;     the base synth used are checked against each other from BOTH sides;
;;   * globals: `bump` / `acc64` read-modify-write the synth-EMITTED `.data`
;;     region (`__synth_globals`, reached via `adrp`+`add :lo12:` — the linker
;;     must place `.data` and resolve R_AARCH64_ADR_PREL_PG_HI21 /
;;     ADD_ABS_LO12_NC), and the values PERSIST across calls;
;;   * `call_indirect` through the synth-emitted `.text` funcref table
;;     (`__synth_func_table`, R_AARCH64_JUMP26 trampolines);
;;   * `mem_size` — the declared-minimum constant (no size register on this
;;     backend; the bounds limit is an immediate).
;;
;; Every case is NON-TRAPPING on purpose: a WASM trap is `brk #0` here, which
;; on Linux is SIGTRAP and kills the harness process — trap delivery is the
;; embedder's business and is gated by the unicorn oracles, not by this one.
(module
  (import "env" "host_add" (func $host_add (param i32 i32) (result i32)))
  (memory (export "memory") 1)
  (global $counter (mut i32) (i32.const 41))
  (global $acc64   (mut i64) (i64.const 0x100000000))
  (type $bin (func (param i32 i32) (result i32)))
  (table 3 funcref)
  (elem (i32.const 0) $add $sub $mul)

  (func $add (export "add") (type $bin)
    (i32.add (local.get 0) (local.get 1)))
  (func $sub (type $bin)
    (i32.sub (local.get 0) (local.get 1)))
  (func $mul (type $bin)
    (i32.mul (local.get 0) (local.get 1)))

  (func (export "mul64") (param i64 i64) (result i64)
    (i64.mul (local.get 0) (local.get 1)))

  (func (export "f64_scale") (param f64 f64) (result f64)
    (f64.mul (local.get 0) (local.get 1)))

  ;; Store a word at a wasm address, read it back. The harness ALSO reads
  ;; `base + addr` from C afterwards.
  (func (export "store_load") (param i32 i32) (result i32)
    (i32.store (local.get 0) (local.get 1))
    (i32.load (local.get 0)))

  ;; Read a byte the HARNESS wrote at `base + addr` before the call.
  (func (export "load8u") (param i32) (result i32)
    (i32.load8_u (local.get 0)))

  (func (export "bump") (param i32) (result i32)
    (global.set $counter (i32.add (global.get $counter) (local.get 0)))
    (global.get $counter))

  (func (export "acc64") (param i64) (result i64)
    (global.set $acc64 (i64.add (global.get $acc64) (local.get 0)))
    (global.get $acc64))

  ;; dispatch(idx, a, b) = table[idx](a, b)
  (func (export "dispatch") (param i32 i32 i32) (result i32)
    (call_indirect (type $bin) (local.get 1) (local.get 2) (local.get 0)))

  (func (export "via_import") (param i32) (result i32)
    (call $host_add (local.get 0) (i32.const 1000)))

  ;; RQ-63-A64STACK shape: a value BELOW the import call's arguments.
  (func (export "below_call") (param i32 i32) (result i32)
    (i32.add (local.get 0) (call $host_add (local.get 1) (i32.const 3))))

  (func (export "helper_chain") (param i32) (result i32)
    (i32.add (call $sub (local.get 0) (i32.const 1)) (i32.const 100)))

  (func (export "mem_size") (result i32)
    (memory.size)))
