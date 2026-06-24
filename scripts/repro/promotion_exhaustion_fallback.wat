;; Regression guard (#474): local promotion (default-on v0.14.0) must never be the
;; REASON a function fails to compile.
;;
;; Promotion pins eligible i32 locals into callee-saved r4-r8, halving the
;; operand-stack temp pool (temps drop from r4-r8+r0-r3 to just r0-r3). On a dense
;; function that tips register allocation past what it can recover, turning a
;; working compile into a hard "register exhaustion" failure (skipped function) --
;; observed on a real engine-control function: fine on v0.12.0, skipped on v0.14.0.
;;
;; This fixture reproduces it generically: 5 promotable i32 locals + a deep
;; right-leaning chain that keeps many products simultaneously live.
;;   * promotion ON  (v0.14.0 default) -- exhausts -> WAS skipped.
;;   * promotion OFF (SYNTH_NO_LOCAL_PROMOTE=1) -- compiles (frame-slot path).
;; The #474 fix runs the promotion-on ladder first (every function that compiles
;; today stays bit-identical) and, only if it still exhausts, falls back to the
;; promotion-off ladder automatically. With the fix this compiles, .text
;; byte-identical to the promotion-off build.
;;
;; Compile: --target cortex-m4 --relocatable --all-exports. Generic values.
(module
  (memory 1)
  (func (export "dense") (param $p i32) (result i32)
    (local $a i32)(local $b i32)(local $c i32)(local $d i32)(local $e i32)
    (local.set $a (i32.add (local.get $p) (i32.const 16)))
    (local.set $b (i32.add (local.get $p) (i32.const 32)))
    (local.set $c (i32.add (local.get $p) (i32.const 48)))
    (local.set $d (i32.add (local.get $p) (i32.const 64)))
    (local.set $e (i32.add (local.get $p) (i32.const 80)))
    (i32.add (i32.mul (local.get $a) (local.get $c)) (i32.add (i32.mul (local.get $e) (local.get $b)) (i32.add (i32.mul (local.get $d) (local.get $a)) (i32.add (i32.mul (local.get $c) (local.get $e)) (i32.add (i32.mul (local.get $b) (local.get $d)) (i32.add (i32.mul (local.get $a) (local.get $c)) (i32.add (i32.mul (local.get $e) (local.get $b)) (i32.add (i32.mul (local.get $d) (local.get $a)) (i32.add (i32.mul (local.get $c) (local.get $e)) (i32.add (i32.mul (local.get $b) (local.get $d)) (i32.add (i32.mul (local.get $a) (local.get $c)) (i32.add (i32.mul (local.get $e) (local.get $b)) (i32.add (i32.mul (local.get $d) (local.get $a)) (i32.add (i32.mul (local.get $c) (local.get $e)) (i32.add (i32.mul (local.get $b) (local.get $d)) (local.get $a))))))))))))))))
  ))
