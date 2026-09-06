;; RQ-63-ARMI64OFF (#1165) — load/store STATIC OFFSETS straddling the ARM
;; immediate-field boundaries, on BOTH ARM ISAs.
;;
;; The v0.62 reach census (RQ-62-REACH) ran `synth compile -b arm --all-exports
;; --relocatable` with NO `--target`, which resolves to the Arm32 (A32) ISA —
;; NOT Thumb-2. Its top ARM blocker, "i64 load/store offset N out of the A32
;; imm12 range" (46 of 110 core declines), is therefore the A32 encoder's
;; `I64Ldr`/`I64Str` arm, which never received #382's Thumb-2 large-offset
;; materialization. Worse, on the same target the A32 WORD and SUB-WORD
;; immediate arms did not decline at all: `encode_mem_addr` masked the offset
;; `& 0xFFF` (LDR/STR/LDRB/STRB) and the halfword/signed arms masked `& 0xFF`,
;; so `i32.load offset=5000` silently read `[ip, #904]` and `i32.load16_u
;; offset=256` read `[ip, #0]` — a wrong address with exit 0. And on Thumb-2,
;; `i64_effective_base` CLAMPED a memarg >= 2^31 (negative after the
;; selector's `as i32` cast) to 0, dropping the offset the i32 form of the same
;; memarg materializes in full.
;;
;; Ladder per form (below / AT the field maximum / one above / far above /
;; needs MOVT / >= 2^31):
;;   i64 pair   — A32 pair folds off <= 4091 (high half at +4 must stay in
;;                imm12); 4092 is the straddle (low half fits, high does not),
;;                4095 the imm12 maximum for the low half, 4096 both out.
;;   i32 word   — imm12: 4095 at, 4096 above.
;;   halfword   — A32 LDRH/STRH/LDRSH imm8 (imm4H:imm4L): 255 at, 256 above.
;;   signed byte — A32 LDRSB is the imm8 form: 255 at, 256 above.
;;   byte       — A32 LDRB/STRB are imm12 forms: 4095 at, 4096 above.
;;
;; Every offset access is CROSS-ADDRESSED by the differential: a value stored
;; through `offset=K` is read back ABSOLUTELY at `addr+K`, and an `offset=K`
;; load reads a value written absolutely — so a dropped, masked or clamped
;; offset is observable, never a self-consistent round trip. Addresses are
;; param-derived (dynamic) so the const-address folds do not apply; this is the
;; register-offset path the census exercised.
(module
  (memory (export "mem") 2)   ;; 128 KiB: offset 70000 + every addr stays inside

  ;; ---- i64 pair -----------------------------------------------------------
  (func (export "ld64_4088") (param $a i32) (result i64) local.get $a (i64.load offset=4088))
  (func (export "ld64_4091") (param $a i32) (result i64) local.get $a (i64.load offset=4091))
  (func (export "ld64_4092") (param $a i32) (result i64) local.get $a (i64.load offset=4092))
  (func (export "ld64_4095") (param $a i32) (result i64) local.get $a (i64.load offset=4095))
  (func (export "ld64_4096") (param $a i32) (result i64) local.get $a (i64.load offset=4096))
  (func (export "ld64_5000") (param $a i32) (result i64) local.get $a (i64.load offset=5000))
  (func (export "ld64_70000") (param $a i32) (result i64) local.get $a (i64.load offset=70000))
  (func (export "ld64_fffffff8") (param $a i32) (result i64) local.get $a (i64.load offset=0xfffffff8))
  (func (export "st64_4088") (param $a i32) (param $v i64) local.get $a local.get $v (i64.store offset=4088))
  (func (export "st64_4092") (param $a i32) (param $v i64) local.get $a local.get $v (i64.store offset=4092))
  (func (export "st64_4096") (param $a i32) (param $v i64) local.get $a local.get $v (i64.store offset=4096))
  (func (export "st64_70000") (param $a i32) (param $v i64) local.get $a local.get $v (i64.store offset=70000))
  (func (export "st64_fffffff8") (param $a i32) (param $v i64) local.get $a local.get $v (i64.store offset=0xfffffff8))
  (func (export "ld64_abs") (param $a i32) (result i64) local.get $a (i64.load))
  (func (export "st64_abs") (param $a i32) (param $v i64) local.get $a local.get $v (i64.store))

  ;; ---- i32 word (A32 imm12) ------------------------------------------------
  (func (export "ld32_4095") (param $a i32) (result i32) local.get $a (i32.load offset=4095))
  (func (export "ld32_4096") (param $a i32) (result i32) local.get $a (i32.load offset=4096))
  (func (export "ld32_5000") (param $a i32) (result i32) local.get $a (i32.load offset=5000))
  (func (export "ld32_fffffff8") (param $a i32) (result i32) local.get $a (i32.load offset=0xfffffff8))
  (func (export "st32_4095") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store offset=4095))
  (func (export "st32_4096") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store offset=4096))
  (func (export "st32_fffffff8") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store offset=0xfffffff8))
  (func (export "ld32_abs") (param $a i32) (result i32) local.get $a (i32.load))
  (func (export "st32_abs") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store))

  ;; ---- halfword (A32 imm8 forms: LDRH / LDRSH / STRH) ---------------------
  (func (export "ld16u_255") (param $a i32) (result i32) local.get $a (i32.load16_u offset=255))
  (func (export "ld16u_256") (param $a i32) (result i32) local.get $a (i32.load16_u offset=256))
  (func (export "ld16s_256") (param $a i32) (result i32) local.get $a (i32.load16_s offset=256))
  (func (export "ld16u_5000") (param $a i32) (result i32) local.get $a (i32.load16_u offset=5000))
  (func (export "st16_255") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store16 offset=255))
  (func (export "st16_256") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store16 offset=256))
  (func (export "ld16u_abs") (param $a i32) (result i32) local.get $a (i32.load16_u))
  (func (export "st16_abs") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store16))

  ;; ---- signed byte (A32 imm8 form: LDRSB) ---------------------------------
  (func (export "ld8s_255") (param $a i32) (result i32) local.get $a (i32.load8_s offset=255))
  (func (export "ld8s_256") (param $a i32) (result i32) local.get $a (i32.load8_s offset=256))

  ;; ---- byte (A32 imm12 forms: LDRB / STRB) --------------------------------
  (func (export "ld8u_4095") (param $a i32) (result i32) local.get $a (i32.load8_u offset=4095))
  (func (export "ld8u_4096") (param $a i32) (result i32) local.get $a (i32.load8_u offset=4096))
  (func (export "st8_4096") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store8 offset=4096))
  (func (export "ld8u_abs") (param $a i32) (result i32) local.get $a (i32.load8_u))
  (func (export "st8_abs") (param $a i32) (param $v i32) local.get $a local.get $v (i32.store8))
)
