;; #543 Phase 2 — volatile DMA-window red→green oracle fixture.
;;
;; dma_window(v): four const-address linear-memory stores. Two land inside the
;; DMA window [0x100, 0x110) (`--volatile-segment 0x100:16`), two outside it.
;; Straight-line, every const address DISTINCT and single-use — exactly the
;; shape the #468 base-CSE / const-address-fold (`SYNTH_BASE_CSE=1`) optimizes
;; on the OPTIMIZED (non-`--relocatable`) path: hoist the linmem base into R11
;; once, fold each const address to `[R11,#imm]`, and drop the per-access
;; `movw/movt R12` base + `add` + address materialization.
;;
;; The behavior lattice pinned by volatile_segment_phase2_543.rs:
;;   - C  (no SYNTH_BASE_CSE, no ranges): verbatim per-access codegen;
;;   - A  (SYNTH_BASE_CSE, no ranges): all 4 stores fold — smallest .text;
;;   - P  (SYNTH_BASE_CSE + --volatile-segment 0x100:16): the 2 window stores
;;        keep their verbatim materialize-and-store codegen, the 2 outside
;;        still fold — strictly between A and C;
;;   - F  (SYNTH_BASE_CSE + a range covering all 4): base-CSE fully declines,
;;        byte-identical to C.
;;
;; Void on purpose: results are read back from linear memory (0x80/0x84 and
;; 0x100/0x104) by the unicorn-vs-wasmtime differential, and the stored $v
;; makes the window contents input-dependent. Addresses/values are neutral,
;; tied to nothing real. Consumed by
;; crates/synth-cli/tests/volatile_segment_phase2_543.rs and
;; scripts/repro/volatile_segment_543_differential.py.
(module
  (memory 1)
  (export "memory" (memory 0))
  (func (export "dma_window") (param $v i32)
    (i32.store (i32.const 0x100) (local.get $v))   ;; window
    (i32.store (i32.const 0x104) (i32.const 22))   ;; window
    (i32.store (i32.const 0x80)  (i32.const 33))   ;; outside
    (i32.store (i32.const 0x84)  (i32.const 44)))) ;; outside
