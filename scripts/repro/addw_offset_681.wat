;; #681 — dynamic-address load/store with static offset 0x100..=0xFFF.
;;
;; `encode_thumb32_add_imm` packed the RAW offset into the T3 ADD.W
;; ThumbExpandImm field. That field is a MODIFIED immediate, correct only for
;; imm <= 0xFF: ThumbExpandImm(0x100) = 0, ThumbExpandImm(0x200) = 0,
;; ThumbExpandImm(0x400) = 0x8000_0000. Every dynamic-base access with a
;; static offset in [256, 4095] silently computed a WRONG address — and in
;; --safety-bounds software the guard (correct T4 ADDW) checked the intended
;; address while the access used the mis-encoded one (bounds bypass).
;;
;; Differential: scripts/repro/addw_offset_681_differential.py (wasmtime is
;; ground truth; unicorn runs synth's Thumb-2 with R11 = linear-memory base).
(module
  (memory (export "mem") 1)

  ;; Store distinct sentinels at base+{0,256,512,1020,1024,4092}, read them
  ;; all back and sum. Pre-fix, the 256/512/1024 stores land at base+0
  ;; (clobbering each other) and the 1024 access faults 2 GiB past the base.
  (func (export "probe") (param i32) (result i32)
    local.get 0 i32.const 111 i32.store
    local.get 0 i32.const 0x1111 i32.store offset=256
    local.get 0 i32.const 0x2222 i32.store offset=512
    local.get 0 i32.const 0x3333 i32.store offset=1020
    local.get 0 i32.const 0x4444 i32.store offset=1024
    local.get 0 i32.const 0x5555 i32.store offset=4092
    local.get 0 i32.load
    local.get 0 i32.load offset=256
    i32.add
    local.get 0 i32.load offset=512
    i32.add
    local.get 0 i32.load offset=1020
    i32.add
    local.get 0 i32.load offset=1024
    i32.add
    local.get 0 i32.load offset=4092
    i32.add)

  ;; gale's exact #681 repro: the offset=512 store must not clobber base+0.
  ;; Pre-fix returns 4660; correct result is 111.
  (func (export "clobber") (param i32) (result i32)
    local.get 0 i32.const 111 i32.store
    local.get 0 i32.const 4660 i32.store offset=512
    local.get 0 i32.load)

  ;; Sub-word paths (i8/i16) with big static offsets — same helper, scalar
  ;; sub-word arms.
  (func (export "subword") (param i32) (result i32)
    local.get 0 i32.const 0xAB i32.store8 offset=257
    local.get 0 i32.const 0xBEEF i32.store16 offset=770
    local.get 0 i32.load8_u offset=257
    local.get 0 i32.load16_u offset=770
    i32.add)

  ;; i64 path (i64_effective_base): store/load a 64-bit value at base+768.
  (func (export "wide") (param i32) (result i32)
    local.get 0 i64.const 0x1122334455667788 i64.store offset=768
    local.get 0 i64.load offset=768
    i32.wrap_i64
    local.get 0 i64.load offset=768
    i64.const 32
    i64.shr_u
    i32.wrap_i64
    i32.add))
