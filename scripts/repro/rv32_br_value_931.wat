(module
  (memory 1)

  ;; ── #931 as filed ────────────────────────────────────────────────────────
  ;; `br` out of a value-producing `block`. The branch computed its value into
  ;; one register and jumped to the merge; the merge read the FALLTHROUGH
  ;; register, so the block yielded the not-taken path's value. Exit 0, silent.
  ;;   simple() = 1     (pre-fix: 0)
  (func (export "simple") (result i32)
    (block $exit (result i32)
      (br $exit (i32.const 1))
      (i32.const 0)))

  ;; The same shape with a computed (not constant) branch value, so the two
  ;; edges land in registers that differ for a reason other than allocation
  ;; order.
  ;;   computed(n) = n + 10
  (func (export "computed") (param i32) (result i32)
    (block $exit (result i32)
      (br $exit (i32.add (local.get 0) (i32.const 10)))
      (i32.const 0)))

  ;; ── The canonical-register hazard the fix must NOT introduce ─────────────
  ;; `br $l (local.get $x)` donates the value's register to the frame as its
  ;; canonical result register, and the frame's `end` writes that register on
  ;; the fallthrough path. If the donated register is a PROMOTED local's
  ;; (#472 local promotion is default-on for RV32), that write clobbers `$x`
  ;; itself — and every later read of `$x` returns the fallthrough value.
  ;;
  ;; `$x` must be read enough times for promotion to repay the callee-saved
  ;; prologue (5 reads did not — verify with `llvm-objdump` that `$x` has no
  ;; `lw ..(sp)`), and read AFTER the block so a clobber is observable rather
  ;; than dead.
  ;;   promoted() = 7 * 13 = 91   (a clobber shows up as 0: the fallthrough
  ;;   writes 0 into $x's register, so the block result AND every later read
  ;;   of $x become 0)
  (func (export "promoted") (result i32)
    (local $x i32)
    (local.set $x (i32.const 7))
    (block $l (result i32) (br $l (local.get $x)) (i32.const 0))
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add)
    (local.get $x) (i32.add))

  ;; ── br_if: the value must reach the merge on the TAKEN edge, and the
  ;; not-taken path must keep running with the value still on the stack ─────
  ;;   brif(nonzero) = 11     (taken — the br_if's value)
  ;;   brif(0)       = 22     (not taken — falls through to the tail)
  (func (export "brif") (param i32) (result i32)
    (block $exit (result i32)
      (drop (br_if $exit (i32.const 11) (local.get 0)))
      (i32.const 22)))

  ;; ── Two value-carrying edges into ONE frame ──────────────────────────────
  ;; The first edge fixes the canonical registers; the second must MOVE into
  ;; them rather than leave its value where it computed it.
  ;;   two_edges(0) = 100 | two_edges(1) = 200 | two_edges(other) = 300
  (func (export "two_edges") (param i32) (result i32)
    (block $exit (result i32)
      (block $b
        (br_if $b (local.get 0))
        (br $exit (i32.const 100)))
      (if (i32.eq (local.get 0) (i32.const 1))
        (then (br $exit (i32.const 200))))
      (i32.const 300)))

  ;; ── i64 result: BOTH halves must be reconciled ───────────────────────────
  ;; A dropped hi-move corrupts the top 32 bits rather than hiding behind a
  ;; zero high half, so both halves are nonzero and differ between the edges.
  ;;   br64() = 0x0000_0009_0000_0005
  (func (export "br64") (result i64)
    (block $exit (result i64)
      (br $exit (i64.add (i64.const 0x900000004) (i64.const 1)))
      (i64.const 0x100000002)))

  ;; ── A value live ACROSS the block ────────────────────────────────────────
  ;; `5` is pushed before the block and consumed after `end`. The truncation
  ;; the fix performs at the `br` must lower the vstack to the frame's OWN
  ;; checkpoint and no further — dropping the carried `5` would corrupt the
  ;; surrounding expression instead of the block's result.
  ;;   carried() = 5 + 1 = 6
  (func (export "carried") (result i32)
    (i32.const 5)
    (block $exit (result i32)
      (br $exit (i32.const 1))
      (i32.const 0))
    (i32.add))

  ;; ── Control-flow-only `br` (arity 0) ─────────────────────────────────────
  ;; Carries nothing, so the fix must leave it byte-identical and working.
  ;;   cfonly(nonzero) = 1 | cfonly(0) = 2
  (func (export "cfonly") (param i32) (result i32)
    (local $r i32)
    (local.set $r (i32.const 2))
    (block $exit
      (br_if $exit (i32.eqz (local.get 0)))
      (local.set $r (i32.const 1)))
    (local.get $r))

  ;; ── #930's shape, on RV32 ────────────────────────────────────────────────
  ;; A `br_if` out of an enclosing block from inside an `if`, whose VALUE
  ;; operand is itself a block that branches. Filed against thumb-2; RV32
  ;; happened to compile it correctly (both edges landed in the same register),
  ;; so this pins that it stays correct rather than staying lucky.
  ;;   nested() = 1
  (func (export "nested") (result i32)
    (block $l0 (result i32)
      (if (i32.const 1)
        (then
          (drop
            (br_if $l0
              (block $l1 (result i32) (br $l1 (i32.const 1)))
              (i32.const 1)))))
      (i32.const 0)))

  ;; ── `br 1`: a value-carrying branch to an OUTER frame ────────────────────
  ;; The truncation may only lower the vstack to the INNERMOST open frame's
  ;; checkpoint — each frame in between still owes its own `end` a split at
  ;; its own checkpoint.
  ;;   outer(nonzero) = 42 | outer(0) = 7
  (func (export "outer") (param i32) (result i32)
    (block $a (result i32)
      (block $b
        (br_if $b (i32.eqz (local.get 0)))
        (br $a (i32.const 42)))
      (i32.const 7)))
)
