;; VCR-RA uxth/uxtb fold validation (#428, #242). `movw #0xffff; and` (and #0xff)
;; for a 16/8-bit mask folds to `uxth`/`uxtb`, dropping the dead movw. Enough live
;; masks that they land in scratch r2-r8 (not the r0/r1 result regs the conservative
;; dead-analysis must keep), so the fold actually fires. Result identical flag-off
;; vs flag-on vs wasmtime.  pack(a,b,c) = ((a&0xffff)<<8) ^ (b&0xffff) ^ (c&0xff)
(module
  (memory 1)
  (func (export "pack") (param $a i32) (param $b i32) (param $c i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.shl (i32.and (local.get $a) (i32.const 65535)) (i32.const 8))
        (i32.and (local.get $b) (i32.const 65535)))
      (i32.and (local.get $c) (i32.const 255)))))
