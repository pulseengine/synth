;; #382 (direct/relocatable path) — i64 load/store with a static offset > 0xFFF
;; (4095) must MATERIALIZE the offset, not skip the function.
;;
;; The direct selector (`--relocatable`, R11/fp = linear-memory base) lowers a
;; memory `i64.load`/`i64.store` to an `I64Ldr`/`I64Str` over
;; `reg_imm(R11, addr, offset)` = `R11 + addr + offset`. The encoder materializes
;; the effective base into `ip` (`ADD ip, base, index`) and accesses the two
;; halves at `[ip,#offset]` / `[ip,#offset+4]`. When `offset+4 > 0xFFF` the
;; imm12 form can't hold it, so `check_ldst_imm12` (#259) refused and the WHOLE
;; function was skipped. i32 (word/sub-word) already lowered via the #206/#372
;; offset_reg materialization; only i64 remained. Fix (arm_encoder
;; ::i64_effective_base): when `offset+4 > 0xFFF`, fold the offset into the base
;; too — `ADD ip, index, #offset; ADD ip, ip, base` — and access at `#0`/`#4`.
;;
;; Addresses are param-derived (dynamic) so issue-#95 const-address folding does
;; NOT apply — this exercises the register-offset (I64Ldr/I64Str) path. The
;; differential cross-addresses (store via offset=5000, read back ABSOLUTE at
;; addr+5000, and vice-versa) so a dropped offset is observable, not just a
;; self-consistent roundtrip. i32 cases are kept as a regression guard.
(module
  (memory (export "mem") 1)
  ;; --- i64 (the #382 direct-path fix) ---
  (func (export "store64_off") (param $a i32) (param $v i64)
    local.get $a local.get $v (i64.store offset=5000))
  (func (export "load64_off") (param $a i32) (result i64)
    local.get $a (i64.load offset=5000))
  (func (export "load64_abs") (param $a i32) (result i64)
    local.get $a (i64.load offset=0))
  ;; --- i32 (regression guard — already lowered via #206/#372) ---
  (func (export "store32_off") (param $a i32) (param $v i32)
    local.get $a local.get $v (i32.store offset=5000))
  (func (export "load32_off") (param $a i32) (result i32)
    local.get $a (i32.load offset=5000))
  (func (export "load32_abs") (param $a i32) (result i32)
    local.get $a (i32.load offset=0)))
