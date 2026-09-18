(module
  ;; RQ-70-NPA (#1331, cpetig, falcon-cascade) — a 20-line reduction of the shape
  ;; that skipped 4 of 6 EXPORTS on their module and emitted NO object at all.
  ;;
  ;; THE SHAPE: under `--native-pointer-abi`, an f32 load/store whose constant
  ;; memarg `offset` lands at or above the stack-pointer global's initializer
  ;; (the static-data base) with a DYNAMIC index. The i32 sub-word (#744) and
  ;; i64 (#746) arms have relocated this through `__synth_wasm_data` since #739;
  ;; the float arms declined loudly instead, which is why cpetig's `rate#tick`,
  ;; `attitude#tick`, `position#tick` and `ekf#estimate` were all skipped.
  ;;
  ;; WHY THE DECLINE WAS RIGHT, and why the fix is a relocation and not a bake:
  ;; the raw `[R11 + addr + #offset]` path materializes the linmem offset as an
  ;; un-relocated MOVW/MOVT immediate. That mis-addresses the moment the linker
  ;; places the region, and it is invisible to BOTH the #678
  ;; `--shadow-stack-size` down-shift and the post-link in-range oracle, because
  ;; each walks RELOCATIONS. Baking here would have been the #739 silent OOB.
  ;;
  ;; RED-FIRST BY CONSTRUCTION: compile with
  ;;   --target cortex-m7 --relocatable --all-exports --native-pointer-abi
  ;; Pre-fix both exports are skipped and the module fails via #952 with
  ;; "GI-FPU-002 phase 1b: f32.load from / f32.store to the static-data region
  ;; under the native-pointer ABI". Post-fix it emits an object whose f32
  ;; accesses carry a `__synth_wasm_data` relocation.
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))

  ;; f32 constants living ABOVE the SP init — the static-data region.
  (data (i32.const 1048584) "\00\00\80\3f\00\00\00\40")

  ;; A dynamic index (the param) plus a static-data memarg offset: exactly the
  ;; branch-3 form falcon's generated code emits, and the one that declined.
  (func (export "load_static_f32") (param i32) (result f32)
    local.get 0
    f32.load offset=1048584)

  (func (export "store_static_f32") (param i32) (param f32)
    local.get 0
    local.get 1
    f32.store offset=1048584)
)
