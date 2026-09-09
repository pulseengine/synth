;; #1226 red-first fixture (RQ-65-ALIASCLASS corpus sweep, self-test phase).
;;
;; Two modules, the spec-suite shape the issue was found on. The defect is
;; NOT the merge: the synth-cli `.wast` driver path returns `Vec::new()` for
;; every declared-width table ("WAST fixture suite is i32-only"), so on ANY
;; `.wast` an i64 param whose width body inference cannot recover is homed as
;; i32 — `second3` (`local.get 1` of an i64 param, never set) compiles to
;; `mov r0, r1` (homes=2) here and to `mov r0, r2; mov r1, r3` (homes=4) from
;; the identical text as a `.wat`. The corpus sweep derives that `.wat` (and a
;; single-module `.wast`) from THIS file's last module at run time and pins
;; `wast < wat` homes as KNOWN-OPEN; a fix makes them equal, the pin goes red,
;; and the fix flips it.
;;
;; `.wast`, deliberately: `scripts/repro/*.wat` is executed against wasmtime by
;; `arm_corpus_sweep_973.py`, and this module is a KNOWN miscompile.
(module
  (func (export "a") (param i32) (result i32) (local.get 0)))

(module
  (memory 1)
  (func (export "second3") (param i64 i64 i32) (result i64)
    (local.get 1))
  (func (export "checkRange") (param $from i64) (param $to i64) (param $expected i32) (result i64)
    (loop $cont
      (if (i64.eq (local.get $from) (local.get $to))
        (then (return (i64.const -1))))
      (if (i32.eq (i32.load8_u (i32.wrap_i64 (local.get $from))) (local.get $expected))
        (then (local.set $from (i64.add (local.get $from) (i64.const 1))) (br $cont))))
    (return (local.get $from))))
