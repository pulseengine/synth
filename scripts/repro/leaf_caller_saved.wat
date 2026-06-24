;; perf repro (VCR-RA-002, #428, epic #242): leaf-function prologue shrink.
;;
;; Local promotion (v0.14.0) homes eligible i32 locals in callee-saved r4..r8.
;; For a LEAF function that is the wrong pool: callee-saved regs must be
;; saved/restored (`push {r4-r8,lr}` / `pop {…,pc}` ~12 cyc of pure overhead),
;; whereas a leaf never calls, so caller-saved r1..r3 (minus params, minus r0
;; for the return value) are free homes that need NO prologue save. Promoting
;; into caller-saved first lets `shrink_callee_saved_saves` drop the callee-saved
;; push entirely.
;;
;; This fixture: 1 param + 3 promotable i32 locals (each written-before-read,
;; depth-0, >=2 reads), minimal operand-stack temp pressure. Flag-off homes
;; a,b,c -> r4,r5,r6 (push {r4-r6,lr}); flag-on (SYNTH_LEAF_CALLER_SAVED=1) homes
;; them -> r1,r2,r3 (no callee-saved push). Same result either way.
;;
;; Generic — neutral values, tied to nothing real.
(module
  (memory 1)
  (func (export "leaf3") (param $p i32) (result i32)
    (local $a i32) (local $b i32) (local $c i32)
    (local.set $a (i32.add (local.get $p) (i32.const 1)))
    (local.set $b (i32.add (local.get $a) (i32.const 2)))
    (local.set $c (i32.add (local.get $b) (i32.const 3)))
    (i32.add (i32.add (local.get $a) (local.get $b))
             (i32.add (local.get $c) (local.get $p)))))
