;; ABI-model evidence (#470, epic #242): intra-module callee-saved self-consistency.
;;
;; The optimized (non-relocatable) path is non-AAPCS BY DESIGN (arm_backend.rs:
;; "does not preserve caller-saved registers across calls"). `ir_to_arm` also
;; emits no callee-saved `push` and its temp pool prefers r4..r8, so an optimized
;; leaf clobbers callee-saved registers. This fixture shows that is HARMLESS
;; intra-module: the caller `a` holds its across-call value on the FRAME, not in a
;; callee-saved register, so the leaf's clobber corrupts nothing.
;;
;;   $b  — leaf: uses temps that land in r4..r8 (ir_to_arm CANDIDATES), no push.
;;   a   — call-containing -> declined to the direct selector -> spills $x to
;;         [sp] before `bl $b` and reloads after; pushes/pops {r4-r8,lr} for ITS
;;         caller. So `a` does not rely on $b preserving r4..r8.
;;
;; See optimized_path_abi_model.md. Generic — neutral values, tied to nothing real.
(module
  (memory 1)
  (func $b (param $p i32) (result i32)
    (i32.add (i32.mul (local.get $p) (i32.const 3)) (i32.const 7)))
  (func (export "a") (param $p i32) (result i32)
    (local $x i32)
    (local.set $x (i32.add (local.get $p) (i32.const 100)))
    (i32.add (call $b (local.get $p)) (local.get $x))))
