(module
  ;; #746 (the #739 residual): meld-fused shared-memory geometry — 17-page
  ;; (1088 KiB) linear memory, one __stack_pointer global init 0x100000
  ;; (1 MiB), and statics ABOVE sp_init (meld `--memory shared` places a
  ;; fused component's data above the shared SP).
  ;;
  ;; The access shape is gale's gust:os `log.line` bulk-copy one: a DYNAMIC
  ;; index in a register plus a STATIC-REGION memarg offset on a WIDE (i64)
  ;; load/store. #744 relocated the i32 sub-word arms; the i64 wide + narrow
  ;; arms still LOUD-DECLINED ("#739: i64.load ... not yet relocated"), so
  ;; the emit function was skipped and the node unlinkable. Post-#746 they
  ;; relocate: base = `__synth_wasm_data + offset` (reloc-visible to the
  ;; #678 `--shadow-stack-size` rebase) + dynamic index.
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  ;; An initialized (data) segment ABOVE sp_init at 0x100020 (the "log
  ;; message that correctly lives in .data") — read via i64 narrow loads.
  (data (i32.const 1048608) "\11\22\33\44\55\66\77\88")
  ;; BSS static above sp_init at 0x100010: store an i64 computed from the
  ;; dynamic index through the dynamic-index + static-offset shape, then
  ;; read it back. run64lo/run64hi return the low/high word.
  (func (export "run64lo") (param i32) (result i32)
    local.get 0
    local.get 0
    i64.extend_i32_u
    i64.const 0x1122334455667788
    i64.add
    i64.store offset=1048592
    local.get 0
    i64.load offset=1048592
    i32.wrap_i64)
  (func (export "run64hi") (param i32) (result i32)
    local.get 0
    local.get 0
    i64.extend_i32_u
    i64.const 0x55667788AABBCCDD
    i64.add
    i64.store offset=1048592
    local.get 0
    i64.load offset=1048592
    i64.const 32
    i64.shr_u
    i32.wrap_i64)
  ;; i64 NARROW stores + loads through a BSS static at 0x100018: store32
  ;; then read back with zero- and sign-extending narrow loads.
  (func (export "narrow32") (param i32) (result i32)
    local.get 0
    i64.const 0x0102030485868788
    i64.store32 offset=1048600
    local.get 0
    i64.load32_u offset=1048600
    i32.wrap_i64)
  (func (export "narrow16s") (param i32) (result i32)
    local.get 0
    i64.const 0xF9E8
    i64.store16 offset=1048600
    local.get 0
    i64.load16_s offset=1048600
    i32.wrap_i64)
  (func (export "narrow8") (param i32) (result i32)
    local.get 0
    i64.const 0xAB
    i64.store8 offset=1048600
    local.get 0
    i64.load8_u offset=1048600
    i32.wrap_i64)
  ;; Byte reads from the initialized (data) segment above sp_init through the
  ;; i64 narrow-load arm (retargeted to __synth_wasm_seg_0 by the ELF builder).
  (func (export "peek_data8") (param i32) (result i32)
    local.get 0
    i64.load8_u offset=1048608
    i32.wrap_i64)
  (func (export "peek_data16s") (param i32) (result i32)
    local.get 0
    i64.load16_s offset=1048608
    i32.wrap_i64))
