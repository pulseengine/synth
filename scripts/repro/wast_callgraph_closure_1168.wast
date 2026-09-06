;; #1168 — the reachable-callgraph closure on the .wast INPUT PATH.
;;
;; The helper chain is the shape of reachable_callgraph_275_selfcontained.wat
;; (the #275 EXECUTION fixture), delivered as a .wast with assert_return lines,
;; because THAT is the path that skipped the closure: `synth compile m.wast
;; --all-exports` compiled exports only, so `entry`'s three non-exported helpers
;; were absent and the object shipped with a dangling `func_N` at exit 0 on
;; ARM Thumb-2, A32 and RV32 - aarch64 refused only incidentally, #851/#1013.
;; spec_compile_census.py feeds .wast files, so every published census number
;; was measured on this path.
;;
;; Only `entry` is exported. leaf/mid/add5 are reached ONLY through static
;; `call`s; `dead` is unreachable and must stay OUT of the object - a closure,
;; not "emit everything". entry(x) = add5(mid(x)) = (7x+3)+5 = 7x+8, so a
;; dropped OR mis-patched helper changes the numeric result for every
;; non-degenerate x. The calls are NESTED rather than summed so the fixture
;; compiles on every backend today - aarch64's call value-stack discipline
;; (RQ-63-A64STACK) declines a call with a live value below its args.
;; Comments carry no parentheses on purpose: the harness extracts the module
;; form by paren matching to hand it to wasmtime.
(module
  (func $leaf (param i32) (result i32)
    (i32.mul (local.get 0) (i32.const 7)))
  (func $mid (param i32) (result i32)
    (i32.add (call $leaf (local.get 0)) (i32.const 3)))
  (func $add5 (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 5)))
  (func $dead (param i32) (result i32)
    (i32.sub (local.get 0) (i32.const 999)))
  (func (export "entry") (param i32) (result i32)
    (call $add5 (call $mid (local.get 0)))))
(assert_return (invoke "entry" (i32.const 0)) (i32.const 8))
(assert_return (invoke "entry" (i32.const 1)) (i32.const 15))
(assert_return (invoke "entry" (i32.const 5)) (i32.const 43))
(assert_return (invoke "entry" (i32.const 100)) (i32.const 708))
