;; #472 — RV32 i32 local-promotion lever (VCR-RA, port of the ARM #390/#457/#458
;; lever). Leaf functions with non-parameter i32 locals promoted into callee-
;; saved s-registers (s8/s9/s10) under SYNTH_RV_LOCAL_PROMO. Both the flag-on and
;; flag-off codegen must match wasmtime; the flag-on build must be smaller.
;;
;; Exercised properties:
;;  - $accum: three heavily-read i32 locals → all promoted, many `lw`s freed
;;            (the size win). All accesses depth-0 straight-line.
;;  - $war_set / $war_tee: the get→…→set/tee→use WAR hazard — an earlier
;;            `local.get` of a promoted local must survive a later write to the
;;            SAME local. Proves `snapshot_aliases`. Without it these miscompile
;;            (the get reads the post-write value).
;;  - $rbw: a local read BEFORE its first write — relies on the wasm zero-init,
;;            emitted as `addi s_i, zero, 0` at entry (the #457 gotcha).
(module
  ;; Three promotable locals, each read many times at depth 0.
  ;; x = a+b, y = a-b, z = x*y ; result = 8*(x+y+z).
  (func $accum (export "accum") (param $a i32) (param $b i32) (result i32)
    (local $x i32) (local $y i32) (local $z i32)
    (local.set $x (i32.add (local.get $a) (local.get $b)))
    (local.set $y (i32.sub (local.get $a) (local.get $b)))
    (local.set $z (i32.mul (local.get $x) (local.get $y)))
    (local.get $x) (local.get $y) (i32.add)
    (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add)
    (local.get $x) (i32.add) (local.get $y) (i32.add) (local.get $z) (i32.add))

  ;; WAR via local.set: push old x, then set x, then use old x.
  ;; returns old_x + new_x = a + 100.
  (func $war_set (export "war_set") (param $a i32) (result i32)
    (local $x i32)
    (local.set $x (local.get $a))   ;; x = a
    (local.get $x)                  ;; push OLD x (= a)
    (local.set $x (i32.const 100))  ;; x = 100  — must snapshot the pushed old x
    (local.get $x)                  ;; push NEW x (= 100)
    (i32.add))                      ;; a + 100

  ;; WAR via local.tee: read old x, then tee x, then use old x and the tee value.
  ;; returns old_x + (tee_val + new_x) = a + (100 + 100) = a + 200.
  (func $war_tee (export "war_tee") (param $a i32) (result i32)
    (local $x i32)
    (local.set $x (local.get $a))       ;; x = a
    (i32.add
      (local.get $x)                    ;; OLD x (= a) — must survive the tee below
      (i32.add
        (local.tee $x (i32.const 100))  ;; x = 100, leaves 100 on stack (snapshot old x)
        (local.get $x))))               ;; NEW x (= 100)  → 100 + 100

  ;; Read-before-write: x is read (as 0) before its first write. Promoted with a
  ;; prologue zero-init. x = 0 + a = a ; result = x + x = 2a.
  (func $rbw (export "rbw") (param $a i32) (result i32)
    (local $x i32)
    (local.set $x (i32.add (local.get $x) (local.get $a)))  ;; first access to x is a READ
    (i32.add (local.get $x) (local.get $x)))
)
