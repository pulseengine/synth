;; perf repro (VCR-RA-002, #390, epic #242): leaf-function prologue shrink —
;; dead-frame elimination.
;;
;; `compute_local_layout` reserves a frame slot (`sub sp,#N` / `add sp,#N`) for
;; every non-param wasm local it sees. Local promotion (v0.14.0) then homes the
;; eligible i32 locals in registers, so those frame bytes are NEVER accessed: a
;; dead `sub`/`add sp` pair (~2-3 cyc on a small leaf) that also touches SP and
;; thereby blocks `shrink_callee_saved_saves` (which declines on any SP def/use).
;; `elide_dead_frame` (SYNTH_DEAD_FRAME_ELIM=1) removes it when the body provably
;; never touches SP — saving the two instructions and restoring the SP-untouched
;; precondition the shrink pass needs.
;;
;; This fixture: 1 param + 3 promotable i32 locals (each written-before-read,
;; depth-0, >=2 reads), minimal operand-stack temp pressure. Promotion homes
;; a,b,c -> r4,r5,r6 and the layout reserves a dead 16-byte frame. Flag-off keeps
;; it (`sub sp,#16` ... `add sp,#16`, 36 B); flag-on elides it (28 B, -8 B = the
;; two 4-byte wide insns), byte-identical otherwise. leaf3(p) = 4*p + 10.
;;
;; NOTE: the push stays `{r4-r8,lr}` either way here — a,b,c are in callee-saved
;; r4,r5,r6 + scratch r7 = 4 saved regs, which `shrink_callee_saved_saves` pads
;; back up to the even-count `{r4-r8,lr}`. Trimming the push needs the locals OUT
;; of callee-saved (caller-saved leaf homing), tracked separately as #390.
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
