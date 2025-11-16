;; LED Blink Example for ARM Cortex-M (nRF52840)
;; This demonstrates a minimal embedded WebAssembly program
;; that would be synthesized to ARM assembly

(module
  ;; Memory for peripheral access and stack
  (memory (export "memory") 1)

  ;; GPIO peripheral base address (nRF52840)
  ;; P0 base: 0x50000000
  ;; P0.OUT register offset: 0x504
  (global $GPIO_P0_OUT (mut i32) (i32.const 0x50000504))
  (global $GPIO_P0_OUTSET (mut i32) (i32.const 0x50000508))
  (global $GPIO_P0_OUTCLR (mut i32) (i32.const 0x5000050C))
  (global $GPIO_P0_DIR (mut i32) (i32.const 0x50000514))

  ;; LED pin (P0.13 on nRF52840-DK)
  (global $LED_PIN (mut i32) (i32.const 13))

  ;; Delay constant (cycles)
  (global $DELAY_COUNT (mut i32) (i32.const 1000000))

  ;; Initialize GPIO for LED output
  (func $gpio_init
    (local $pin_mask i32)
    (local $dir_reg i32)

    ;; Calculate pin mask: 1 << LED_PIN
    (local.set $pin_mask
      (i32.shl
        (i32.const 1)
        (global.get $LED_PIN)
      )
    )

    ;; Read current DIR register
    (local.set $dir_reg
      (i32.load (global.get $GPIO_P0_DIR))
    )

    ;; Set pin as output: DIR |= pin_mask
    (i32.store
      (global.get $GPIO_P0_DIR)
      (i32.or
        (local.get $dir_reg)
        (local.get $pin_mask)
      )
    )
  )

  ;; Turn LED on
  (func $led_on
    (local $pin_mask i32)

    ;; Calculate pin mask
    (local.set $pin_mask
      (i32.shl
        (i32.const 1)
        (global.get $LED_PIN)
      )
    )

    ;; Set pin high: OUTSET = pin_mask
    (i32.store
      (global.get $GPIO_P0_OUTSET)
      (local.get $pin_mask)
    )
  )

  ;; Turn LED off
  (func $led_off
    (local $pin_mask i32)

    ;; Calculate pin mask
    (local.set $pin_mask
      (i32.shl
        (i32.const 1)
        (global.get $LED_PIN)
      )
    )

    ;; Set pin low: OUTCLR = pin_mask
    (i32.store
      (global.get $GPIO_P0_OUTCLR)
      (local.get $pin_mask)
    )
  )

  ;; Delay function (busy wait)
  (func $delay
    (local $counter i32)

    ;; Initialize counter
    (local.set $counter (global.get $DELAY_COUNT))

    ;; Busy wait loop
    (block $break
      (loop $continue
        ;; Decrement counter
        (local.set $counter
          (i32.sub (local.get $counter) (i32.const 1))
        )

        ;; Break if counter reaches zero
        (br_if $break
          (i32.eqz (local.get $counter))
        )

        ;; Continue loop
        (br $continue)
      )
    )
  )

  ;; Main blink loop
  (func (export "blink_loop")
    ;; Initialize GPIO
    (call $gpio_init)

    ;; Infinite blink loop
    (block $break
      (loop $continue
        ;; Turn LED on
        (call $led_on)

        ;; Delay
        (call $delay)

        ;; Turn LED off
        (call $led_off)

        ;; Delay
        (call $delay)

        ;; Continue forever
        (br $continue)
      )
    )
  )

  ;; Entry point (called from startup code)
  (func (export "main") (result i32)
    (call $blink_loop)
    (i32.const 0)
  )
)
