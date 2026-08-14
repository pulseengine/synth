;; #944 — compiler-introduced object-branch attribution fixture.
;;
;; Exercises every op family in the VERIFIED introduced-branch origin map
;; (synth_core::provenance::introduced_branch_origin), plus the `if` source
;; decision that #944 found mis-bucketed with the introduced branches:
;;
;;   bulk:    memory.fill -> 1 loop-bound branch   (bulk-memory-fill-loop)
;;            memory.copy -> 3 branches: overlap-direction test + forward and
;;                           backward copy-loop bounds (bulk-memory-copy-loop)
;;   divs:    i32.div_s   -> 3 branches: div-by-zero guard + INT_MIN/-1
;;                           overflow guard pair    (division-trap-guard)
;;   divu/rems/remu: 1 div-by-zero guard each      (division-trap-guard)
;;   decide:  if          -> 1 conditional branch, a SOURCE decision
;;                           (covered "If" entry, resolved: true)
;;
;; The gate (crates/synth-cli/tests/provenance_introduced_origin_944.rs) pins
;; the EXACT per-origin counts, so both widening the origin map without
;; verification and losing an attribution turn it red — and asserts the
;; module-wide unattributed count stays at its justified floor: 0.
(module
  (memory (export "memory") 1)
  (func (export "bulk") (param i32 i32 i32)
    local.get 0
    local.get 1
    local.get 2
    memory.fill
    local.get 0
    local.get 1
    local.get 2
    memory.copy)
  (func (export "divs") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.div_s)
  (func (export "divu") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.div_u)
  (func (export "rems") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.rem_s)
  (func (export "remu") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.rem_u)
  (func (export "decide") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.lt_s
    if (result i32)
      local.get 0
      local.get 1
      i32.add
    else
      local.get 1
    end)
)
