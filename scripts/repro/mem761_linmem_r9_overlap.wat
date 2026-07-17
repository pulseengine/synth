;; #761: self-contained --cortex-m full-page linmem view overlaps the R9 globals
;; table at the top of SRAM.
;;
;; Geometry (pre-fix): R11 startup linmem base = 0x2000_0000; functions address
;; linear memory at optimized_linmem_base = 0x2000_0100 (0x100 above R11, #687).
;; The R9 globals table is placed at linmem_base + memory_size = 0x2000_0000 +
;; 0x10000 = 0x2001_0000. A function's store to wasm memory offset 0xFF00 lands
;; at 0x2000_0100 + 0xFF00 = 0x2001_0000 — EXACTLY the R9 globals table slot 0.
;;
;; So storing a sentinel to mem[0xFF00] aliases global 0. Each probe reads a
;; global it did NOT store into, so the ONLY way its return can be the sentinel
;; is the overlap alias. Probes are stateless w.r.t. each other (each stores a
;; distinct global-slot cell and returns a different, untouched global).
(module
  (memory 1)
  (global $g0 (mut i32) (i32.const 0xABCD))
  (global $g1 (mut i32) (i32.const 0x1234))

  ;; RED case: store the sentinel at mem offset 0xFF00, then return global 0.
  ;; g0 is never explicitly set here, so wasmtime returns 0xABCD. Pre-fix synth
  ;; returns the sentinel because 0xFF00 aliases g0's slot at 0x2001_0000.
  (func $overlap_probe (result i32)
    (i32.store (i32.const 0xFF00) (i32.const 0xDEADBEEF))
    (global.get $g0))

  ;; Regression witness: store the sentinel at mem offset 0, return global 1.
  ;; Offset 0 is far below the globals table before AND after the fix, so this
  ;; is 0x1234 either way — proves the fix doesn't perturb non-overlapping code.
  (func $disjoint_probe (result i32)
    (i32.store (i32.const 0x0000) (i32.const 0xDEADBEEF))
    (global.get $g1))

  ;; Store-lands-in-linmem witness: store the sentinel at mem[0xFF00] and read
  ;; it BACK from mem[0xFF00]. After the fix the store lands in REAL linear
  ;; memory (not the globals table), so this reads 0xDEADBEEF — confirming the
  ;; top of the page is now genuine linmem, not aliased to R9.
  (func $mem_ff00_probe (result i32)
    (i32.store (i32.const 0xFF00) (i32.const 0xDEADBEEF))
    (i32.load (i32.const 0xFF00)))

  (export "overlap_probe" (func $overlap_probe))
  (export "disjoint_probe" (func $disjoint_probe))
  (export "mem_ff00_probe" (func $mem_ff00_probe)))
