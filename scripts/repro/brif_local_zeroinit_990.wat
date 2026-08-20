;; #990 — a plain NON-PARAM local written on only ONE arm of a `br_if` is
;; never zero-initialised: the merge point reads whatever was on the stack
;; below SP (information disclosure).
;;
;; WHY THE EXISTING ZERO-INIT DOES NOT RESCUE IT (#970's own finding): the
;; #457 zero-init fires only for locals whose FIRST access in LINEAR op order
;; is a READ. Here the first access is the WRITE — but the write sits on a
;; conditionally-skipped path, so "write before read in op order" is not
;; "write before read in EXECUTION order". The classifier must count a write
;; as settling the local only where the write DOMINATES the read.
;;
;; Every `bl_*` export is a shape where the defining write does NOT dominate
;; the merge-point read (br_if / if-without-else / one-armed if-else /
;; br_table / an i64 sibling). Every `guard_*` export is a shape the fix must
;; NOT change semantically: straight-line write-then-read (stays
;; zero-init-free and byte-identical), genuine read-before-write (#457,
;; already zeroed), and dominated-but-conservatively-rezeroed shapes.
(module
  ;; THE #990 shape, verbatim from the issue: the local is written only on the
  ;; br_if-NOT-taken path; the merge point reads it. x < 0 skips the write and
  ;; must observe the wasm-mandated 0.
  (func (export "bl_brif") (param i32) (result i32)
    (local i32)
    (block
      (br_if 0 (i32.lt_s (local.get 0) (i32.const 0)))
      (local.set 1 (i32.const 10)))
    (local.get 1))

  ;; Same class through `if` WITHOUT an else: param 0 == 0 skips the only write.
  (func (export "bl_if_no_else") (param i32) (result i32)
    (local i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 7))))
    (local.get 1))

  ;; if/else where EACH arm writes a DIFFERENT local: exactly one of the two
  ;; is unwritten on every execution, so the sum leaks on every input.
  (func (export "bl_if_else_one_arm") (param i32) (result i32)
    (local i32 i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 7)))
      (else (local.set 2 (i32.const 9))))
    (i32.add (local.get 1) (local.get 2)))

  ;; br_table sibling: index 0 lands on the writing arm, anything else jumps
  ;; straight to the merge and must read 0.
  (func (export "bl_br_table") (param i32) (result i32)
    (local i32)
    (block
      (block
        (br_table 0 1 (local.get 0)))
      (local.set 1 (i32.const 21)))
    (local.get 1))

  ;; i64 sibling of the #990 shape: BOTH words of the 8-byte slot must read 0
  ;; on the skipping path (a half-zeroed slot would leak one word).
  (func (export "bl_brif_i64") (param i32) (result i64)
    (local i64)
    (block
      (br_if 0 (i32.lt_s (local.get 0) (i32.const 0)))
      (local.set 1 (i64.const 0x1122334455667788)))
    (local.get 1))

  ;; ── guards: shapes the fix must leave semantically alone ──────────────────
  ;; Straight-line depth-0 write-then-read: the write dominates, no zero-init
  ;; now, none after (this is the byte-identity shape for the common case).
  (func (export "guard_straightline") (param i32) (result i32)
    (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (local.get 1))

  ;; #457: genuine read-before-write — already zero-inited; must keep reading 0.
  (func (export "guard_rbw") (param i32) (result i32)
    (local i32)
    (i32.add (local.get 0) (local.get 1)))

  ;; Both arms write the SAME local before the read: correct under either
  ;; rule (the conservative fix may add a dead zero-init; the value is
  ;; unconditionally overwritten either way).
  (func (export "guard_both_arms") (param i32) (result i32)
    (local i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 5)))
      (else (local.set 1 (i32.const 7))))
    (local.get 1))

  ;; Write and read INSIDE the same block, write first: dominated (straight
  ;; line within the block), and read again after the block — the set always
  ;; executed, so the fix's conservative extra zero-init is dead.
  (func (export "guard_same_block") (param i32) (result i32)
    (local i32)
    (block
      (local.set 1 (i32.add (local.get 0) (i32.const 5)))
      (drop (local.get 1)))
    (local.get 1))

  ;; #970's own canonical PARAM shape, inline: a conditionally-written
  ;; PARAMETER keeps its incoming argument (params are NOT zero-initialised).
  ;; The fix must not misclassify a param as a zero-init local.
  (func (export "guard_cond_param_970") (param i32 i32) (result i32)
    (if (local.get 0)
      (then (local.set 1 (i32.const 5))))
    (local.get 1))

  ;; A loop whose body reads the accumulator before its first linear write:
  ;; already rbw under the old rule (the in-loop read precedes the set in op
  ;; order), so it is zeroed today and must stay zeroed.
  (func (export "guard_loop_acc") (param i32) (result i32)
    (local i32 i32)
    (local.set 2 (local.get 0))
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 2)))
        (local.set 1 (i32.add (local.get 1) (i32.const 2)))
        (local.set 2 (i32.sub (local.get 2) (i32.const 1)))
        (br 0)))
    (local.get 1))
)
