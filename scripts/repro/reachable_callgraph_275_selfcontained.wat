(module
  ;; #275 — the DIRECT reachable call graph on the SELF-CONTAINED --cortex-m
  ;; image. Only `entry` is exported; every helper below is NON-exported and is
  ;; reached ONLY through a static `call`. Pre-#235 the self-contained builder
  ;; emitted exports only, so these helpers were absent and `entry`'s BL had no
  ;; target — the image could not execute. This fixture makes the omission
  ;; observable at RUNTIME (a wrong numeric result), not just via `nm`.

  ;; leaf helper (func 0) — reached transitively (entry -> mid -> leaf)
  (func $leaf (param i32) (result i32)
    (i32.mul (local.get 0) (i32.const 7)))

  ;; mid helper (func 1) — reached from `entry`, and itself calls `leaf`
  (func $mid (param i32) (result i32)
    (i32.add (call $leaf (local.get 0)) (i32.const 3)))

  ;; a SECOND directly-reached helper (func 2) with a distinct constant, so a
  ;; single wrong BL target (mid vs add5) is caught, not laundered.
  (func $add5 (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 5)))

  ;; a NON-reachable dead helper (func 3) — must NOT be required for the image
  ;; to run; its presence/absence is irrelevant to correctness (reachability is
  ;; a closure, not "emit everything").
  (func $dead (param i32) (result i32)
    (i32.sub (local.get 0) (i32.const 999)))

  ;; exported entry (func 4): result = mid(x) + add5(x)
  ;;   = (x*7 + 3) + (x + 5) = 8*x + 8
  ;; A dropped/mispatched helper changes this for every non-degenerate x.
  (func (export "entry") (param i32) (result i32)
    (i32.add
      (call $mid  (local.get 0))
      (call $add5 (local.get 0)))))
