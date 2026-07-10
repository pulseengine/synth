;; #687 — stack-layout oracle fixture.
;;
;; `set_canary` plants a magic word at 8 consecutive linmem words near the TOP
;; of the 64KB linear memory (wasm addresses 0xF000..0xF01C — high enough that
;; a top-of-SRAM stack sweeps them long before it exits SRAM). `get_canary(i)`
;; reads word i back. `recurse(n)` recurses n deep — each activation pushes a
;; frame, so a large n drives SP down through whatever lies below the stack:
;; under --stack-layout=high that is the globals table + linear memory (the
;; canaries corrupt SILENTLY before any fault); under --stack-layout=low the
;; stack bottom is the SRAM start, so the first errant push faults BEFORE any
;; linmem byte changes. `add` is the in-budget control.
;;
;; set_canary/get_canary are straight-line const-address memory ops (the
;; OPTIMIZED selector path — they exercise the #687-shifted absolute linmem
;; base); recurse contains a local call (declined to the DIRECT selector,
;; which is what pushes real AAPCS frames).
(module
  (memory (export "memory") 1)

  (func (export "set_canary")
    (i32.store (i32.const 0xF000) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF004) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF008) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF00C) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF010) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF014) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF018) (i32.const 0xC0DECAFE))
    (i32.store (i32.const 0xF01C) (i32.const 0xC0DECAFE)))

  (func (export "get_canary") (param i32) (result i32)
    (i32.load (i32.add (i32.const 0xF000)
                       (i32.mul (local.get 0) (i32.const 4)))))

  (func $recurse (export "recurse") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (i32.const 0))
      (else (i32.add (i32.const 1)
                     (call $recurse (i32.sub (local.get 0) (i32.const 1)))))))

  (func (export "add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
