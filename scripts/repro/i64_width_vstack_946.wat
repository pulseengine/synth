;; #946 — i64-local width inference vs the stack-effect table (executed
;; miscompile, fixed in the RQ-58-WILDCARD lane).
;;
;; `infer_i64_locals` simulates a virtual stack of value widths; its per-op
;; effects came from `wasm_stack_effect`, which said `if`/`br_if`/`br_table`
;; have "no value stack effect" and let a `_ => (0, 0)` wildcard absorb
;; `memory.copy`/`memory.fill`, while `call` never popped its arguments. Each
;; is wrong: they all consume values. The stale width entry made a later
;; `local.set` of an i64 read an i32 width, so the local got a 4-byte slot and
;; a single-word store — the hi half silently dropped.
;;
;; Every export here computes (0x1_0000_0005 >> 32) via an i64 local whose
;; `local.set` sits just past one of the offending shapes, and must return 1.
;; Pre-fix (v0.58 tree, cortex-m4 --relocatable --no-optimize, unicorn vs
;; wasmtime): all four returned 32. The memory.copy/memory.fill shapes live in
;; i64_width_vstack_mem_946.wat (a memory section excludes a module from this
;; sweep's execution phase); the call_indirect shape is pinned at unit level
;; in crates/synth-synthesis/tests/i64_width_vstack_946.rs.
(module
  (func $g (param i32) (result i32)
    local.get 0)

  ;; br_if pops its condition.
  (func (export "f_brif") (result i32)
    (local $x i64)
    i64.const 0x100000005
    block
      i32.const 1
      br_if 0
    end
    local.set $x
    local.get $x
    i64.const 32
    i64.shr_u
    i32.wrap_i64)

  ;; if pops its condition.
  (func (export "f_if") (result i32)
    (local $x i64)
    i64.const 0x100000005
    i32.const 1
    if
      nop
    end
    local.set $x
    local.get $x
    i64.const 32
    i64.shr_u
    i32.wrap_i64)

  ;; br_table pops its index.
  (func (export "f_brtable") (result i32)
    (local $x i64)
    i64.const 0x100000005
    block
      block
        i32.const 1
        br_table 0 1
      end
    end
    local.set $x
    local.get $x
    i64.const 32
    i64.shr_u
    i32.wrap_i64)

  ;; call pops its arguments (one here) along with pushing its result.
  (func (export "f_callargs") (result i32)
    (local $x i64)
    i64.const 0x100000005
    i32.const 7
    call $g
    drop
    local.set $x
    local.get $x
    i64.const 32
    i64.shr_u
    i32.wrap_i64))
