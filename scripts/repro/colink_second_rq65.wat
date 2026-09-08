;; RQ-65-FUNCN (#1180) — the SECOND object of the host-library co-link
;; differential, shared by the arm64-Linux (ELF) and macOS (Mach-O) oracles.
;;
;; It is shaped to DEFINE every name synth invents that used to collide when
;; two synth aarch64 objects met in one link, so the leg cannot pass by
;; accident of the second module simply not having them:
;;
;;   * `func_1` — its first defined function is wasm index 1 (the import is
;;     index 0), exactly the label the fixture's `add` also carries; this is
;;     the pinned `duplicate symbol: func_1` of v0.64;
;;   * `__synth_globals` — a mutable global gives it its own `.data` region;
;;   * `__synth_func_table` — a funcref table + `call_indirect` gives it its
;;     own `.text`-resident table.
;;
;; All three are STB_LOCAL / non-`N_EXT` since RQ-65-FUNCN (planned once, in
;; `ObjectPlan`), so the pair links unaided; the exports below are GLOBAL and
;; the import binds to the SAME C `host_add` the fixture uses. No memory: the
;; fixture owns `x28`'s region and this object must not assume a second one.
;;
;; Every case is non-trapping (a trap is `brk #0`, which kills the harness).
(module
  (import "env" "host_add" (func $host_add (param i32 i32) (result i32)))
  (type $un (func (param i32) (result i32)))
  (global $acc (mut i32) (i32.const 1000))
  (table 2 funcref)
  (elem (i32.const 0) $triple $neg)

  ;; func_1 — NOT exported: only its in-object label names it.
  (func $triple (type $un)
    (i32.mul (local.get 0) (i32.const 3)))
  ;; func_2
  (func $neg (type $un)
    (i32.sub (i32.const 0) (local.get 0)))

  ;; synth -> host through the shared import.
  (func (export "g") (param i32) (result i32)
    (call $host_add (local.get 0) (i32.const 1)))

  ;; This object's OWN globals region, persisting across calls.
  (func (export "acc_b") (param i32) (result i32)
    (global.set $acc (i32.add (global.get $acc) (local.get 0)))
    (global.get $acc))

  ;; disp_b(idx, x) = table[idx](x) — this object's OWN funcref table.
  (func (export "disp_b") (param i32 i32) (result i32)
    (call_indirect (type $un) (local.get 1) (local.get 0)))

  ;; synth -> synth: CALL26 to the two LOCAL labels, resolved in-object even
  ;; though the other object defines the same `func_1`/`func_2`.
  (func (export "chain_b") (param i32) (result i32)
    (call $triple (call $neg (local.get 0)))))
