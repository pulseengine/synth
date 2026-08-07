;; VCR-A64-CF-001 (#851) — aarch64 `br_table` + VALUE-CARRYING block/loop/if.
;;
;; Every function here compiled to NOTHING on `-b aarch64` before v0.55 L6:
;; `br_table` had no selector arm at all, and any `(result T)` frame was
;; loud-declined for want of result-register reconciliation. The cases are
;; chosen so a WRONG BRANCH DESTINATION or a wrong reconciliation register
;; changes the RESULT, not merely the schedule — a harness that only checked
;; "it compiled" would be vacuous.
(module
  (memory 1)

  ;; ---- br_table: the index lattice ------------------------------------
  ;; Classic dense switch. Index 0/1/2 pick distinct constants; ANY other
  ;; index (including the huge unsigned values the "negative" i32s denote)
  ;; falls to the default arm. The at-bound (3) and over-bound cases are what
  ;; a signed compare or an off-by-one chain would get wrong.
  (func (export "switch3") (param i32) (result i32)
    (block $d
      (block $c2
        (block $c1
          (block $c0
            (br_table $c0 $c1 $c2 $d (local.get 0)))
          (return (i32.const 100)))
        (return (i32.const 200)))
      (return (i32.const 300)))
    (i32.const 999))

  ;; Default-ONLY table (zero targets): every index must reach the default.
  ;; The degenerate chain — a bare `b` with no compare at all.
  (func (export "default_only") (param i32) (result i32)
    (block $d
      (br_table $d (local.get 0)))
    (i32.const 42))

  ;; DUPLICATE depths in one table: entries 0 and 2 share a destination.
  ;; A chain that de-duplicated or reordered compares would break the
  ;; index->arm mapping.
  (func (export "dup_targets") (param i32) (result i32)
    (block $d
      (block $b
        (block $a
          (br_table $a $b $a $d (local.get 0)))
        (return (i32.const 11)))
      (return (i32.const 22)))
    (i32.const 33))

  ;; MIXED destinations in ONE table, DEFAULT = the backward edge. Depth 1 is
  ;; the enclosing LOOP header (BACKWARD, resolved eagerly to a negative
  ;; offset) and depth 0 a block END (FORWARD, patched at `end`). A lowering
  ;; that assumed one direction emits a wrong offset for the other. The trip
  ;; count is data-dependent, so a wrong offset changes the result.
  (func (export "table_loop_default_back") (param i32) (result i32)
    (local $n i32) (local $steps i32)
    (local.set $n (local.get 0))
    (block $out
      (loop $again
        (local.set $steps (i32.add (local.get $steps) (i32.const 1)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        ;; index 0 -> $out (exit); anything else -> default $again (loop).
        (br_table $out $again (i32.gt_s (local.get $n) (i32.const 0)))))
    (local.get $steps))

  ;; Same, but TARGET 0 is the backward edge — the `cbz` form of the chain's
  ;; first entry, resolved eagerly against the loop header.
  (func (export "table_loop_target0_back") (param i32) (result i32)
    (local $n i32) (local $steps i32)
    (local.set $n (local.get 0))
    (block $out
      (loop $again
        (local.set $steps (i32.add (local.get $steps) (i32.const 1)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        ;; index 0 -> $again (loop); index 1 -> default $out (exit).
        (br_table $again $out (i32.le_s (local.get $n) (i32.const 0)))))
    (local.get $steps))

  ;; A table at exactly BR_TABLE_MAX_TARGETS (16 targets + default) — the
  ;; boundary the >16 decline is measured against. It must LOWER and be right
  ;; on every arm, including the last compare in the chain.
  (func (export "switch16") (param i32) (result i32)
    (block $d
     (block $p15 (block $p14 (block $p13 (block $p12
     (block $p11 (block $p10 (block $p9  (block $p8
     (block $p7  (block $p6  (block $p5  (block $p4
     (block $p3  (block $p2  (block $p1  (block $p0
       (br_table $p0 $p1 $p2 $p3 $p4 $p5 $p6 $p7 $p8 $p9
                 $p10 $p11 $p12 $p13 $p14 $p15 $d (local.get 0)))
       (return (i32.const 0)))  (return (i32.const 1)))
       (return (i32.const 2)))  (return (i32.const 3)))
       (return (i32.const 4)))  (return (i32.const 5)))
       (return (i32.const 6)))  (return (i32.const 7)))
       (return (i32.const 8)))  (return (i32.const 9)))
       (return (i32.const 10))) (return (i32.const 11)))
       (return (i32.const 12))) (return (i32.const 13)))
       (return (i32.const 14))) (return (i32.const 15)))
    (i32.const -1))

  ;; br_table guarding a TRAP: index 0 falls into `unreachable`. A dispatch
  ;; that landed on the wrong arm would return a value where wasmtime traps.
  (func (export "table_trap") (param i32) (result i32)
    (block $ok
      (block $bad
        (br_table $bad $ok $ok (local.get 0)))
      (unreachable))
    (i32.const 7))

  ;; ---- value-carrying block / if / loop --------------------------------
  ;; TWO edges into one join: the `br_if` edge carries `a`, the fall-through
  ;; carries `b`. Both must land in the SAME register or the result is
  ;; path-dependent — the exact defect the old decline was protecting.
  (func (export "block_two_edges") (param i32 i32 i32) (result i32)
    (i32.add
      (block (result i32)
        (br_if 0 (local.get 1) (local.get 0))
        (drop)
        (local.get 2))
      (i32.const 1000)))

  ;; A value-carrying block whose branch comes from a NESTED frame (depth 1),
  ;; so the reconciliation must target the OUTER frame's register.
  (func (export "block_nested_br") (param i32 i32) (result i32)
    (block (result i32)
      (block
        (br_if 0 (i32.eqz (local.get 0)))
        (br 1 (local.get 1)))
      (i32.const -5)))

  ;; Value-producing if/else: the then-arm deposits at `else`, the else-arm at
  ;; `end`. Both arms must reach the join in one register.
  (func (export "if_value") (param i32 i32 i32) (result i32)
    (if (result i32) (local.get 0)
      (then (i32.mul (local.get 1) (i32.const 3)))
      (else (i32.sub (local.get 2) (i32.const 7)))))

  ;; VALUE-CARRYING LOOP — the soundness-critical shape. A `br` to a loop
  ;; label targets the HEADER and carries the loop's PARAMETERS (none here),
  ;; NOT its result. An implementation that reconciled on the back-edge would
  ;; stamp a garbage value into the result register every iteration; here the
  ;; loop runs a data-dependent number of times before falling through with
  ;; its value, so that bug changes the RESULT.
  (func (export "loop_value") (param i32) (result i32)
    (local $i i32) (local $acc i32)
    (loop (result i32)
      (local.set $acc (i32.add (local.get $acc) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if 0 (i32.lt_u (local.get $i) (local.get 0)))
      (i32.mul (local.get $acc) (i32.const 2))))

  ;; A value-carrying block nested INSIDE a value-carrying loop: two live
  ;; reservations at once, which is where a single shared slot register would
  ;; collide.
  (func (export "nested_value_frames") (param i32) (result i32)
    (local $i i32) (local $acc i32)
    (loop (result i32)
      (local.set $acc
        (i32.add (local.get $acc)
          (block (result i32)
            (br_if 0 (i32.const 1) (i32.and (local.get $i) (i32.const 1)))
            (drop)
            (i32.const 10))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if 0 (i32.lt_u (local.get $i) (local.get 0)))
      (local.get $acc)))

  ;; i64 result through the reconciliation register (the `mov x` width claim).
  (func (export "block_i64") (param i32 i64 i64) (result i64)
    (block (result i64)
      (br_if 0 (local.get 1) (local.get 0))
      (drop)
      (local.get 2)))

  ;; f64 result through the reconciliation register (`fmov d`). The FP file is
  ;; reserved separately, and the f32 case below proves the 64-bit move keeps
  ;; a single-precision pattern intact.
  (func (export "block_f64") (param i32 f64 f64) (result f64)
    (block (result f64)
      (br_if 0 (local.get 1) (local.get 0))
      (drop)
      (local.get 2)))

  (func (export "block_f32") (param i32 f32 f32) (result f32)
    (block (result f32)
      (br_if 0 (local.get 1) (local.get 0))
      (drop)
      (local.get 2)))

  ;; A value-carrying block whose reconciled value came from LINEAR MEMORY,
  ;; so the slot register must not collide with the address/base temps.
  (func (export "block_from_memory") (param i32) (result i32)
    (i32.store (i32.const 16) (i32.const 0x5A5A))
    (i32.store (i32.const 32) (i32.const 0x1234))
    (block (result i32)
      (br_if 0 (i32.load (i32.const 16)) (local.get 0))
      (drop)
      (i32.load (i32.const 32))))

  ;; A value-carrying block reached ONLY through the branch (the fall-through
  ;; is `unreachable`) — proves the join reads the branch's deposit and that a
  ;; dead fall-through does not corrupt it.
  (func (export "block_branch_only") (param i32) (result i32)
    (block (result i32)
      (br_if 0 (i32.const 77) (local.get 0))
      (unreachable)))

  ;; ---- a CALL inside a value-carrying frame ----------------------------
  ;; The one soundness claim in `reconcile_into` that nothing else here
  ;; executes: `bl` CLOBBERS the caller-saved x9..x15 pool the reconciliation
  ;; slot lives in. The claim is that this is harmless, because a branch that
  ;; deposited into the slot has ALREADY transferred control — so on any path
  ;; that reaches the `bl`, the slot's value is dead and the fall-through
  ;; re-writes it. Cond nonzero takes the branch (the `bl` never runs and the
  ;; deposited 7 must survive); cond zero runs the call (the clobber must be
  ;; invisible). These shapes also force the HOMED-PARAM path (non-leaf +
  ;; reads a param), which no other value-carrying case here touches.
  (func $three (result i32) (i32.const 3))

  (func (export "block_over_call") (param i32) (result i32)
    (block (result i32)
      (br_if 0 (i32.const 7) (local.get 0))
      (drop)
      (call $three)))

  ;; Same property across the `else` deposit rather than the `end` one.
  (func (export "if_value_over_call") (param i32) (result i32)
    (if (result i32) (local.get 0)
      (then (i32.const 7))
      (else (call $three)))))
