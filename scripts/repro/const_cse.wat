;; VCR-RA const-CSE (#242) execution-oracle fixture.
;;
;; Each export materializes the SAME constant several times in a straight-line
;; segment — exactly the redundant-const-materialization pattern gale measured
;; on silicon (flat_flight: 61% of materializations redundant). With
;; SYNTH_CONST_CSE=1 the optimized path aliases the repeated const to the
;; register that already holds it and emits no second movw/movt. This harness
;; proves that aliasing is SEMANTICS-PRESERVING (result bit-identical to
;; wasmtime) across:
;;   - large3 : a >16-bit const (movw+movt) reused 3×
;;   - small3 : a <16-bit const (single mov) reused 3×
;;   - neg    : a negative const (sign-extended bit-pattern) reused 2×
;;   - mixed  : the same const interleaved with other consts/ops (xor/mul)
;;   - ctrl   : a const reused ACROSS an if/else — the cache must RESET at the
;;              control-flow boundary, so the post-merge use re-materializes;
;;              a stale alias here would read a register the other arm clobbered
;;   - spill12: 12 simultaneously-live locals each = param+100000 → forces real
;;              register spills; proves the const cache stays correct when the
;;              aliased register is itself spilled (STR is a use, not a def, so
;;              the cache entry survives the spill and still names the live value)
(module
  (func (export "large3") (param i32) (result i32)
    local.get 0 i32.const 100000 i32.add i32.const 100000 i32.add i32.const 100000 i32.add)

  (func (export "small3") (param i32) (result i32)
    local.get 0 i32.const 200 i32.add i32.const 200 i32.add i32.const 200 i32.add)

  (func (export "neg") (param i32) (result i32)
    local.get 0 i32.const -100000 i32.add i32.const -100000 i32.add)

  (func (export "mixed") (param i32) (result i32)
    local.get 0 i32.const 70000 i32.mul i32.const 70000 i32.add
    i32.const 12345 i32.xor i32.const 70000 i32.add)

  (func (export "ctrl") (param i32) (result i32)
    (local.get 0) (i32.const 50000) (i32.add)
    (local.get 0)
    (if (result i32) (then (i32.const 50000)) (else (i32.const 60000)))
    (i32.add)
    (i32.const 50000) (i32.add))

  (func (export "spill12") (param i32) (result i32)
    (local $v0 i32) (local $v1 i32) (local $v2 i32) (local $v3 i32)
    (local $v4 i32) (local $v5 i32) (local $v6 i32) (local $v7 i32)
    (local $v8 i32) (local $v9 i32) (local $v10 i32) (local $v11 i32)
    (local.set $v0 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v1 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v2 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v3 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v4 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v5 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v6 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v7 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v8 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v9 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v10 (i32.add (local.get 0) (i32.const 100000)))
    (local.set $v11 (i32.add (local.get 0) (i32.const 100000)))
    (local.get $v0) (local.get $v1) (i32.add) (local.get $v2) (i32.add)
    (local.get $v3) (i32.add) (local.get $v4) (i32.add) (local.get $v5) (i32.add)
    (local.get $v6) (i32.add) (local.get $v7) (i32.add) (local.get $v8) (i32.add)
    (local.get $v9) (i32.add) (local.get $v10) (i32.add) (local.get $v11) (i32.add)
    (i32.const 100000) (i32.add)))
