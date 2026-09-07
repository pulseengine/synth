;; RQ-64-MACHO — the Mach-O HOST-LIBRARY fixture: the SAME module as
;; RQ-64-ARM64LINUX's `arm64_linux_host_link_rq64.wat`, on purpose.
;;
;; The thesis under test is that the CONTAINER, not the ISA, is what keeps
;; synth output off macOS — so the module that arm64-Linux links and executes
;; (ld.lld, qemu-user, unicorn, a native arm64-Linux runner) is exactly the
;; module whose `--object-format macho` twin Apple's ld links and macOS runs
;; here. One module, two containers, the same instruction bytes (checked
;; byte-for-byte by `macho_host_link_rq64_differential.py`), the same values
;; on both operating systems. Keep the two files identical below this header;
;; a shape one needs and the other does not belongs in a third fixture.
;;
;; What ONE object exercises, each a separate way the claim can be false:
;;
;;   * host -> synth calls through the arm64 procedure-call standard in BOTH
;;     register files and both widths (`add` w-regs, `mul64` x-regs,
;;     `f64_scale` d-regs) — Apple's arm64 ABI agrees with AAPCS64 on all of
;;     them (it diverges only on variadics and >8-arg stack packing, which
;;     this backend declines);
;;   * synth -> host: `via_import` and `below_call` call the IMPORTED
;;     `env.host_add`, which becomes an undefined `_host_add` the host linker
;;     binds to the harness's C definition (ARM64_RELOC_BRANCH26);
;;   * synth -> synth: `helper_chain` calls the NON-exported `$sub`
;;     (BRANCH26 resolved within the object);
;;   * linear memory through the `x28` precondition — `store_load` writes a
;;     word the HARNESS then reads back from its own buffer, and `load8u`
;;     reads a byte the harness wrote — so the base the embedder chose and
;;     the base synth used are checked against each other from BOTH sides;
;;   * globals: `bump` / `acc64` read-modify-write the synth-EMITTED
;;     `__DATA,__data` region (`___synth_globals`, reached via `adrp`+`add`
;;     — the linker must place the section and resolve ARM64_RELOC_PAGE21 /
;;     PAGEOFF12), and the values PERSIST across calls;
;;   * `call_indirect` through the synth-emitted `__text` funcref table
;;     (`___synth_func_table`, BRANCH26 trampolines);
;;   * `mem_size` — the declared-minimum constant (no size register on this
;;     backend; the bounds limit is an immediate).
;;
;; Every case is NON-TRAPPING on purpose: a WASM trap is `brk #0` here, which
;; on Darwin is SIGTRAP and kills the harness process — trap delivery is the
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
