;; RQ-59-GLOBALINIT (#1052): NONZERO global initializers — the value the
;; zeroed-scratch harness protocol could never distinguish from "dropped".
;;
;; The #643 fixture's initializers are all zero, and the sole relocatable-path
;; globals harness mapped a ZEROED region ("# zeroed globals table (inits are
;; 0)") — so an object that silently dropped every initializer was green for
;; that harness's entire existence. This fixture exists so the harness CAN
;; notice: 42 and 0x1122334455667788 are observable through plain global.get,
;; with no global.set anywhere (nothing re-establishes the values at runtime).
;;
;; The globals are also EXPORTED so the harness derives the ground-truth init
;; values from the module itself via wasmtime (served-image-vs-runtime-image,
;; the VCR-VER-003 shape) instead of hardcoding them twice.
(module
  (global $a (export "g_a") (mut i32) (i32.const 42))
  (global $b (export "g_b") (mut i64) (i64.const 0x1122334455667788))

  (func (export "get_a") (result i32) global.get $a)

  (func (export "get_b_lo") (result i32)
    (i32.wrap_i64 (global.get $b)))

  (func (export "get_b_hi") (result i32)
    (i32.wrap_i64 (i64.shr_u (global.get $b) (i64.const 32)))))
