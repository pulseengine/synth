;; perf repro (#428, epic #242): a NON-LEAF thin forwarder pays a full
;; `push {r4-r8,lr}` + a dead `sub sp,#N` frame even though it forwards through one
;; call and touches no callee-saved register or stack slot of its own.
;;
;; The leaf-only prologue levers (`elide_dead_frame`, `shrink_callee_saved_saves`)
;; both decline on any function containing a call (`reg_effect` returns None on
;; `Bl`), so driver-class primitives keep the full frame + 6-register save-set.
;; The non-leaf variants prune both: a DIRECT call moves neither SP nor any
;; callee-saved register, so the dead frame comes out and the save-set shrinks to
;; the even-count `{r4,lr}` (which keeps SP 8-byte aligned at the call).
;;
;; The forwarders pass CONSTANT args (like gale's `uart_rx_fired` forwarding a
;; constant), so there is no param-backing `[sp]` traffic and the reserved frame
;; is dead — the case the lever targets. (A forwarder of a `local.get` would back
;; the param to the frame, keeping it live; that is out of scope and unaffected.)
;;
;;   `tick`     — pure forwarder: writes no callee-saved, dead frame → both fire.
;;   `tick_two` — two calls; holds the first result ACROSS the second call, so the
;;                allocator homes it in a callee-saved register the body writes →
;;                that register MUST stay saved (the shrink must not drop it).
;;
;; Generic values — exhibits the pattern, tied to nothing real.
(module
  (memory 1)
  (export "memory" (memory 0))
  (func $helper (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 100)))
  (func (export "tick") (result i32)
    (call $helper (i32.const 5)))
  (func (export "tick_two") (result i32)
    (i32.add (call $helper (i32.const 1)) (call $helper (i32.const 2)))))
