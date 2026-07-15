(module
  ;; #406/#739-cluster coverage WIDENER — multi-chunk / multi-segment static
  ;; data across BOTH the self-contained (`--cortex-m`, no --relocatable) and
  ;; the --relocatable object paths. Segments live at VARIED offsets, including
  ;; ones that straddle an internal 4 KiB page boundary and one placed near the
  ;; top of a two-page linear memory (approaching the globals-table boundary the
  ;; self-contained image lays out just above linmem). Single memory only —
  ;; multi-memory self-contained is a loud decline (#406), so this exercises the
  ;; static-data machinery both paths share.
  ;;
  ;; NOTE: this WIDENS coverage. It does NOT close #757 (blocked on the
  ;; reporter's reduced module). If any case diverges from wasmtime that is a
  ;; real find to report loudly, not to paper over.
  (memory (export "mem") 2)  ;; 2 pages = 128 KiB — room for a high segment

  ;; --- chunk A: small segment low in memory (word + high word) ---
  (data (i32.const 0x40) "\11\22\33\44\55\66\77\88")           ;; @0x40

  ;; --- chunk B: unaligned start, straddles a 4 KiB internal page boundary ---
  ;; starts at 0x0FFE, so bytes land at 0x0FFE..0x1005 — across the 0x1000 line.
  (data (i32.const 0x0FFE) "\a1\b2\c3\d4\e5\f6\07\18")          ;; @0x0FFE (straddles 0x1000)

  ;; --- chunk C: overlapping pair — later segment wins (in-order semantics) ---
  (data (i32.const 0x200) "\de\ad\be\ef")                       ;; @0x200
  (data (i32.const 0x203) "\99\aa")                             ;; @0x203 overwrites 0x203..0x204

  ;; --- chunk D: HIGH segment near the top of page 1 (0x1FF0), approaching the
  ;; end of the 2-page reservation where the globals table is laid out just
  ;; above linmem in the self-contained image. Wide + narrow reads. ---
  (data (i32.const 0x1FF0) "\ca\fe\ba\be\0d\f0\ad\8b")          ;; @0x1FF0

  ;; --- chunk E: a long (multi-word) segment to force a multi-word copy loop ---
  (data (i32.const 0x800)
    "\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f\10\11\12\13\14\15\16\17\18\19\1a\1b\1c\1d\1e\1f\20")

  ;; ---- reads ----
  (func (export "a_lo")  (result i32) (i32.load (i32.const 0x40)))    ;; 0x44332211
  (func (export "a_hi")  (result i32) (i32.load (i32.const 0x44)))    ;; 0x88776655

  ;; chunk B: read the word that straddles the page line (bytes 0x0FFE..0x1001)
  (func (export "b_straddle") (result i32) (i32.load (i32.const 0x0FFE)))  ;; 0xd4c3b2a1
  (func (export "b_after")    (result i32) (i32.load (i32.const 0x1002)))  ;; 0x1807f6e5

  ;; chunk C overlap: byte @0x203 is 0x99 (later segment), @0x200 word head.
  (func (export "c_head") (result i32) (i32.load8_u (i32.const 0x200)))    ;; 0xde
  (func (export "c_ovl")  (result i32) (i32.load8_u (i32.const 0x203)))    ;; 0x99

  ;; chunk D high segment (word + a byte mid-segment)
  (func (export "d_lo")  (result i32) (i32.load (i32.const 0x1FF0)))       ;; 0xbebafeca
  (func (export "d_hi")  (result i32) (i32.load (i32.const 0x1FF4)))       ;; 0x8badf00d
  (func (export "d_byte") (result i32) (i32.load8_u (i32.const 0x1FF6)))   ;; 0xba

  ;; chunk E: read three interior words of the long segment
  (func (export "e_0")  (result i32) (i32.load (i32.const 0x800)))         ;; 0x04030201
  (func (export "e_16") (result i32) (i32.load (i32.const 0x810)))         ;; 0x14131211
  (func (export "e_28") (result i32) (i32.load (i32.const 0x81c)))         ;; 0x201f1e1d

  ;; a load from a region NO segment initializes: must be zero
  (func (export "gap") (result i32) (i32.load (i32.const 0x1800)))         ;; 0
)
