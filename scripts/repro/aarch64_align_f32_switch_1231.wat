;; RQ-66-UNWATCHED (#1231): `f32_align_switch` extracted verbatim from
;; tests/spec-testsuite/align.wast (module at line 458, function at line
;; 462) into its own single-module file.
;;
;; WHY THIS FIXTURE EXISTS RATHER THAN COMPILING align.wast DIRECTLY:
;; align.wast carries 25 top-level `(module ...)` forms, so the census
;; invocation (`synth compile align.wast -b aarch64 --all-exports`) takes the
;; #1225 multi-module MERGE path, which refuses the WHOLE FILE before any
;; per-function selection happens (module 23 carries an i64/f32/f64 result
;; the merge's i32-only signature tables cannot represent) — so align.wast's
;; contribution to the #1231 operand-class-confusion count is NOT visible on
;; that invocation at all. It only reproduces on the SINGLE-MODULE path,
;; which is what the real MVP-core census (#1017/#1225) takes for a .wast
;; whose module is extracted on its own — exactly what this fixture is.
;; The original issue's file-level table listed align.wast as contributing 1
;; function to this class; that table conflates the file-level census (which
;; cannot see this function at all) with the per-module census (which can) —
;; see the oracle docstring for the correction.
(module
  (memory 1)
  (func (export "f32_align_switch") (param i32) (result f32)
    (local f32 f32)
    (local.set 1 (f32.const 10.0))
    (block $4
      (block $2
        (block $1
          (block $default
            (block $0
              (br_table $0 $default $1 $2 $4 (local.get 0))
            ) ;; 0
            (f32.store (i32.const 0) (local.get 1))
            (local.set 2 (f32.load (i32.const 0)))
            (br $4)
          ) ;; default
          (f32.store align=1 (i32.const 0) (local.get 1))
          (local.set 2 (f32.load align=1 (i32.const 0)))
          (br $4)
        ) ;; 1
        (f32.store align=2 (i32.const 0) (local.get 1))
        (local.set 2 (f32.load align=2 (i32.const 0)))
        (br $4)
      ) ;; 2
      (f32.store align=4 (i32.const 0) (local.get 1))
      (local.set 2 (f32.load align=4 (i32.const 0)))
    ) ;; 4
    (local.get 2)
  )
)
