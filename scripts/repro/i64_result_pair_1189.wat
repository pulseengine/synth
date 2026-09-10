;; RQ-66-WATCHED (#1189) — the OPTIMIZED path's i64-result epilogue pair move.
;;
;; `ir_to_arm` lets an i64 result live in any register pair and, at the end
;; of the function, moves the halves into the AAPCS return pair R0:R1 —
;; `mov r1, <hi>` first (so a lo half sitting in R1 is not clobbered), then
;; `mov r0, <lo>`. The v0.65 mutation survey (RQ-65-MUTANTS) DELETED the
;; `mov r1, <hi>` and the whole named suite stayed green: eight self-contained
;; corpus objects lost the move (`const_body_791:c64`, the #916 shift/clz/ctz/
;; extend set, the #973 i64-cmp selects, `i64_divs_317:divs/rems`, the #615
;; extends and const, the #851 i64 local and ext32 shapes) and nothing
;; EXECUTED them — every existing i64 differential runs the RELOCATABLE
;; (direct-selector) object, whose epilogue is a different code path.
;;
;; Every export here returns i64 and takes ONLY i32 params (an i64 parameter
;; diverts the function to the direct selector via `has_wide_param`, which is
;; exactly the path that would NOT exercise this move). Shapes are the ones
;; the survey's changed-object list names, plus a few whose hi half is
;; computed rather than materialized.
(module
  (memory 1)
  (data (i32.const 64) "\10\32\54\76\98\ba\dc\fe")   ;; 0xfedcba9876543210 @64

  ;; the #791 shape: a bare i64 const (hi materialized in a callee-saved reg)
  (func (export "const64") (result i64) (i64.const 0x1122334455667788))
  (func (export "const64_neg") (result i64) (i64.const -2))

  ;; #615 / #851: extends of an i32 param
  (func (export "extend_s") (param i32) (result i64) local.get 0 i64.extend_i32_s)
  (func (export "extend_u") (param i32) (result i64) local.get 0 i64.extend_i32_u)

  ;; #916: shifts by a runtime count (both the n<32 and n>=32 arms)
  (func (export "shru") (param i32) (result i64)
    i64.const 0xFEDCBA9876543210 local.get 0 i64.extend_i32_u i64.shr_u)
  (func (export "shl") (param i32) (result i64)
    i64.const 0xFEDCBA9876543210 local.get 0 i64.extend_i32_u i64.shl)
  (func (export "shrs") (param i32) (result i64)
    i64.const 0xFEDCBA9876543210 local.get 0 i64.extend_i32_u i64.shr_s)
  (func (export "clz64") (param i32) (result i64) local.get 0 i64.extend_i32_u i64.clz)
  (func (export "ctz64") (param i32) (result i64) local.get 0 i64.extend_i32_u i64.ctz)
  (func (export "popcnt64") (param i32) (result i64) local.get 0 i64.extend_i32_s i64.popcnt)

  ;; arithmetic whose hi half is COMPUTED (carry / sign / product)
  (func (export "add64") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.add)
  (func (export "sub64") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.sub)
  (func (export "mul64") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.mul)
  (func (export "and64") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_s local.get 1 i64.extend_i32_u i64.and)
  (func (export "xor64") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_s i64.const 0x0F0F0F0F0F0F0F0F i64.xor)

  ;; #317: i64 div/rem (the software expansions)
  (func (export "divs") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_s local.get 1 i64.extend_i32_s i64.div_s)
  (func (export "rems") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_s local.get 1 i64.extend_i32_s i64.rem_s)
  (func (export "divu") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.div_u)

  ;; #973: an i64 select on an i32 condition
  (func (export "sel64") (param i32) (result i64)
    i64.const 0x0000000100000002 i64.const 0x7FFFFFFF80000000
    local.get 0 select)

  ;; #851: an i64 local set then returned
  (func (export "local64") (param i32) (result i64) (local i64)
    local.get 0 i64.extend_i32_s i64.const 40 i64.shl local.set 1
    local.get 1 i64.const 1 i64.or)

  ;; an i64 load (the data segment is what the ROM->RAM copy must deliver)
  (func (export "load64") (result i64) (i64.load (i32.const 64)))
  (func (export "load64_off") (param i32) (result i64) (i64.load offset=64 (local.get 0)))
)
