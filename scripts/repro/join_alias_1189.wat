;; #1189 — if/else JOIN register aliasing a local's HOME register.
;;
;; Every export is a CALL-FREE function whose params are register-homed on the
;; ARM direct selector (R0..R3 by AAPCS). The then-arm of an `if (result)`
;; pushes a `local.get` of a register-homed local UNCOPIED (the home register
;; itself), so the #313 join `mov R_then, R_else` on the else path writes the
;; LOCAL. A later `local.get` of that local then reads the join value.
;;
;; The "clean" shapes are here too, so the oracle pins what does NOT reach the
;; class as firmly as what does: a narrow blast radius is a result.
;;
;; Every function's wrong-answer vector takes the ELSE path and re-reads the
;; local after the join; the then-path vector is the "correct by accident"
;; control (the join mov is a no-op there because R_then already holds the
;; value).
(module
  ;; --- reaches the class on the ARM direct selector (measured WRONG on main)
  ;; ir0: the issue's repro. ir0(0) = 9 + 0 = 9; main returned 18.
  (func (export "ir0") (param i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 0)) (else (i32.const 9)))
    (local.get 0) i32.add)
  ;; ir1..ir3: the aliased local homed in R1, R2, R3.
  (func (export "ir1") (param i32 i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 1)) (else (i32.const 9)))
    (local.get 1) i32.add)
  (func (export "ir2") (param i32 i32 i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 2)) (else (i32.const 9)))
    (local.get 2) i32.add)
  (func (export "ir3") (param i32 i32 i32 i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 3)) (else (i32.const 9)))
    (local.get 3) i32.add)
  ;; iboth: BOTH arms are homes — the join `mov r0, r1` copies local 1 INTO
  ;; local 0.
  (func (export "iboth") (param i32 i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 0)) (else (local.get 1)))
    (local.get 0) i32.add (local.get 1) i32.add)
  ;; isets: the else-arm WRITES the local, then the join overwrites that write.
  (func (export "isets") (param i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 0))
        (else (local.set 0 (i32.const 5)) (i32.const 9)))
    (local.get 0) i32.add)
  ;; inest: two joins, the inner one inside the outer then-arm — both alias.
  (func (export "inest") (param i32 i32) (result i32)
    (if (result i32) (local.get 0)
      (then (if (result i32) (local.get 1) (then (local.get 0)) (else (i32.const 7))))
      (else (i32.const 9)))
    (local.get 0) i32.add)
  ;; (i64p — the i64 pair form — lives in join_alias_1189_i64.wat: RV32
  ;; declines an i64 PARAM (#312) and #952 would fail the whole module.)
  ;; bif: the if sits inside a block — the block adds nothing, the if join is
  ;; the same join.
  (func (export "bif") (param i32) (result i32)
    (block (result i32)
      (if (result i32) (local.get 0) (then (local.get 0)) (else (i32.const 9))))
    (local.get 0) i32.add)
  ;; iloop: the if inside a loop body (after the back-edge).
  (func (export "iloop") (param i32 i32) (result i32)
    (loop (result i32)
      (local.set 1 (i32.sub (local.get 1) (i32.const 1)))
      (br_if 0 (local.get 1))
      (if (result i32) (local.get 0) (then (local.get 0)) (else (i32.const 9)))
      (local.get 0) i32.add))

  ;; --- does NOT reach the class (measured MATCH on main, pinned as such)
  ;; iloc: a NON-PARAM local. Promotion needs every access at control-flow
  ;; depth 0, so a then-arm read is never promoted: frame slot -> fresh temp.
  (func (export "iloc") (param i32) (result i32) (local i32)
    (local.set 1 (i32.add (local.get 0) (i32.const 3)))
    (if (result i32) (local.get 0) (then (local.get 1)) (else (i32.const 9)))
    (local.get 1) i32.add)
  ;; ielse: only the ELSE arm reads the home — `mov R_then, R_home` reads it.
  (func (export "ielse") (param i32) (result i32)
    (if (result i32) (local.get 0) (then (i32.const 9)) (else (local.get 0)))
    (local.get 0) i32.add)
  ;; idead: the local is never re-read after the join — the clobber is of a
  ;; dead value.
  (func (export "idead") (param i32) (result i32)
    (if (result i32) (local.get 0) (then (local.get 0)) (else (i32.const 9))))
  ;; itee: a then-arm `local.tee` pushes the tee'd TEMP, not the home.
  (func (export "itee") (param i32) (result i32)
    (if (result i32) (local.get 0) (then (i32.const 4) (local.tee 0)) (else (i32.const 9)))
    (local.get 0) i32.add)
  ;; bbrif / bfall: the #509 block join lands in a FRESH designated result
  ;; register; the home is only ever a SOURCE.
  (func (export "bbrif") (param i32) (result i32)
    (block (result i32) (local.get 0) (local.get 0) (br_if 0) (drop) (i32.const 9))
    (local.get 0) i32.add)
  (func (export "bfall") (param i32) (result i32)
    (block (result i32) (i32.const 9) (local.get 0) (br_if 0) (drop) (local.get 0))
    (local.get 0) i32.add)
  ;; lres: a `loop (result)` has no join — its label carries params, not
  ;; results.
  (func (export "lres") (param i32 i32) (result i32)
    (loop (result i32)
      (local.set 1 (i32.sub (local.get 1) (i32.const 1)))
      (br_if 0 (local.get 1))
      (local.get 0))
    (local.get 0) i32.add))
