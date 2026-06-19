;; #382 — load/store with a static offset > 0xFFF (4095) must MATERIALIZE the
;; offset, not skip the function. The optimized (non-relocatable) path lowers a
;; memory access to `MOVW/MOVT R12,#base; ADD R12,R12,Raddr; LDR/STR [R12,#off]`.
;; When `off > 0xFFF` the encoder's check_ldst_imm12 (#259) REFUSES the imm12
;; form (it never silently masks to off&0xFFF), so the whole function was
;; dropped. Fix (optimizer_bridge::fold_mem_offset): fold the large constant
;; offset into the compile-time-constant base — `(base+off)+addr == base+addr+off`
;; — keeping the access immediate at #0 with zero added instructions.
;; Surfaced by the gust kernel (a large static struct field store lands beyond
;; the 12-bit imm range).
;;
;; The differential proves the offset is actually APPLIED (not dropped) by
;; cross-addressing: store via offset=5000 and read the SAME byte back via an
;; absolute load at addr+5000 (and the symmetric load-offset case). Addresses are
;; param-derived (dynamic) so issue-#95 const-address folding does not apply.
(module
  (memory 1)
  ;; word
  (func (export "store_off") (param $a i32) (param $v i32)
    local.get $a local.get $v (i32.store offset=5000))
  (func (export "load_abs") (param $a i32) (result i32)
    local.get $a (i32.load offset=0))
  (func (export "load_off") (param $a i32) (result i32)
    local.get $a (i32.load offset=5000))
  ;; half-word (sub-word path)
  (func (export "store_h_off") (param $a i32) (param $v i32)
    local.get $a local.get $v (i32.store16 offset=5000))
  (func (export "load_hu_abs") (param $a i32) (result i32)
    local.get $a (i32.load16_u offset=0)))
