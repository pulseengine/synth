;; RQ-73-FALCONFIXTURE (#1318) — the shape behind 6 of the 7 declines in the
;; reporter's `opt.wasm`, reduced to one module and committed so the class is
;; reproducible IN THIS REPOSITORY rather than only from an issue attachment.
;;
;; PROVENANCE. #1318's `errors.zip` contains `opt.wasm` and `fused.wasm`, not
;; just logs. Measured at v0.72.0 with the reporter's own command line
;; (`--target cortex-m7 --relocatable --all-exports --embedder-data-init
;; --embedder-global-init`): `fused.wasm` rc=0 / 0 skipped, `opt.wasm` rc=1 /
;; 7 of 17 skipped — ONE `#1069` (the `controller@0.10.0#step` export) and SIX
;; `GI-FPU-002` (`func_4`, `func_5`, `func_8`, `func_10`, `func_11`,
;; `func_12`). Each of those six was extracted into its own module — stubbing
;; callees and adding the one mutable global where needed — and each still
;; declines with `GI-FPU-002`. All six contain a `block` with an f32 result.
;;
;; WHAT THIS FILE IS, AND IS NOT. The functions below are SYNTHESIZED minimal
;; shapes, not copies of the reporter's code: the smallest module carrying the
;; shape reproduces the same diagnostic, so committing a reduction keeps the
;; fixture readable and sidesteps redistributing someone else's module. Anyone
;; can recover the originals from the attachment with the method above; the
;; oracle's docstring records it.
;;
;; A HYPOTHESIS CHECKED AND DISCARDED, recorded so it is not re-tried:
;; `i32.reinterpret_f32` / `f32.reinterpret_i32` occur throughout `func_5`, but
;; a module containing ONLY those compiles cleanly on every backend. They are
;; not the trigger.
;;
;; WHY i32 AND i64 ARE HERE. They are the discriminating controls, and without
;; them this fixture would only show that something fails. i32 compiles on all
;; three backends; i64 declines on ARM with a NAMED message that says exactly
;; what is unsupported; f32/f64 decline with `GI-FPU-002`, whose text
;; ("an integer operation peeked an f32 (VFP) stack value — invalid wasm or an
;; unlowered float op reached the integer path") names the wrong subsystem and
;; reads as though the input might be malformed. It is not: every function here
;; is accepted and executed by wasmtime. That mismatch between the message and
;; the actual limitation is why six declines in a real flight-control module
;; were never connected to a known gap.
;;
;; NOTE ON THE RELATIONSHIP TO #509 / #1215, stated as measured and no further:
;; the SAME shape declines at i64 with the `#509` message and at f32 with an
;; integer-path message. Whether both raise sites reduce to one underlying
;; limitation has NOT been shown here, so no such claim is made.

(module
  ;; CONTROL — compiles on arm, riscv and aarch64. If this ever declines, the
  ;; oracle's whole discrimination is gone and it must be treated as vacuous.
  (func (export "vbr_i32") (param i32 i32) (result i32)
    (block (result i32)
      local.get 0
      local.get 1
      br_if 0
      i32.const 1
      i32.add))

  ;; ARM: declines with a NAMED, accurate message about the carried i64.
  (func (export "vbr_i64") (param i64 i32) (result i64)
    (block (result i64)
      local.get 0
      local.get 1
      br_if 0
      i64.const 1
      i64.add))

  ;; ARM: GI-FPU-002. This is the falcon shape.
  (func (export "vbr_f32") (param f32 i32) (result f32)
    (block (result f32)
      local.get 0
      local.get 1
      br_if 0
      f32.const 1
      f32.add))

  ;; ARM: GI-FPU-002 phase 2 (f64/D-register half of the same shape).
  (func (export "vbr_f64") (param f64 i32) (result f64)
    (block (result f64)
      local.get 0
      local.get 1
      br_if 0
      f64.const 1
      f64.add)))
