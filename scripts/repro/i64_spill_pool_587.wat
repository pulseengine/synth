;; #587 — DIRECT-PATH i64 spill-slot POOL exhaustion (falcon func_60/func_73).
;;
;; The direct selector's pair allocator (#171/#325) spills deep i64 values to a
;; fixed frame pool of I64_SPILL_SLOTS = 8 slots. Twenty simultaneously-live
;; i64 constants need ~16 slots at peak (the R0-R8 pool holds 4 pairs), so the
;; pool exhausted and the whole function loud-skipped:
;;   "register exhaustion: i64 spill-slot pool exhausted — function too
;;    complex for current register allocator"
;;
;; The fix adds a `pool-grow` rung to the backend's exhaustion-recovery ladder:
;; when (and only when) an attempt fails with the slot-pool message, selection
;; reruns with the pool sized from a conservative operand-stack-depth bound
;; (`max_depth_bound`), so the frame grows only for functions that previously
;; did not compile at all — everything that compiled yesterday keeps its
;; 8-slot frame byte-identically.
;;
;; The fold mixes non-commutative ops (sub/xor) so a slot-collision, reload,
;; or half-swap bug changes the result; distinct byte patterns in every
;; constant make lo/hi swaps and wrong-slot reloads visible. hp2 folds from
;; the other end (deepest value consumed LAST) so slots stay live to the end.
;;
;; Differential oracle: scripts/repro/i64_spill_pool_587_differential.py
;; (wasmtime ground truth vs unicorn, direct/--relocatable and default paths).
(module
  (func (export "hp20") (param i32) (result i64)
    i64.const 0x0101010102020202
    i64.const 0x0303030304040404
    i64.const 0x0505050506060606
    i64.const 0x0707070708080808
    i64.const 0x090909090a0a0a0a
    i64.const 0x0b0b0b0b0c0c0c0c
    i64.const 0x0d0d0d0d0e0e0e0e
    i64.const 0x0f0f0f0f10101010
    i64.const 0x1111111112121212
    i64.const 0x1313131314141414
    i64.const 0x1515151516161616
    i64.const 0x1717171718181818
    i64.const 0x191919191a1a1a1a
    i64.const 0x1b1b1b1b1c1c1c1c
    i64.const 0x1d1d1d1d1e1e1e1e
    i64.const 0x1f1f1f1f20202020
    i64.const 0x2121212122222222
    i64.const 0x2323232324242424
    i64.const 0x2525252526262626
    i64.const 0x2727272728282828
    i64.add
    i64.sub
    i64.xor
    i64.add
    i64.sub
    i64.xor
    i64.add
    i64.sub
    i64.xor
    i64.add
    i64.sub
    i64.xor
    i64.add
    i64.sub
    i64.xor
    i64.add
    i64.sub
    i64.xor
    i64.add
    local.get 0
    i64.extend_i32_u
    i64.xor))
