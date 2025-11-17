;; LED Blink Example in WebAssembly Text Format
;; Demonstrates GPIO toggle for embedded ARM target

(module
  ;; Memory for peripheral registers (minimum 1 page = 64KB)
  (memory (export "memory") 1)

  ;; GPIO register addresses (STM32-like)
  ;; Base address: 0x40020000 (GPIOA)
  ;; MODER offset: 0x00
  ;; ODR offset: 0x14
  ;; BSRR offset: 0x18

  ;; Initialize GPIO pin as output
  ;; Sets PA5 (LED pin) to output mode
  (func $gpio_init
    (local $gpioa_moder i32)
    (local $value i32)

    ;; GPIOA MODER register address
    (local.set $gpioa_moder (i32.const 0x40020000))

    ;; Read current MODER value
    (local.set $value (i32.load (local.get $gpioa_moder)))

    ;; Clear mode bits for pin 5 (bits 10-11)
    (local.set $value
      (i32.and
        (local.get $value)
        (i32.const 0xFFFFF3FF)))  ;; Clear bits 10-11

    ;; Set pin 5 to output mode (01)
    (local.set $value
      (i32.or
        (local.get $value)
        (i32.const 0x00000400)))  ;; Set bit 10

    ;; Write back to MODER
    (i32.store (local.get $gpioa_moder) (local.get $value))
  )

  ;; Turn LED on
  ;; Sets PA5 high using BSRR register
  (func $led_on
    (local $gpioa_bsrr i32)

    ;; GPIOA BSRR register
    (local.set $gpioa_bsrr (i32.const 0x40020018))

    ;; Set pin 5 (bit 5 in lower halfword sets the pin)
    (i32.store (local.get $gpioa_bsrr) (i32.const 0x00000020))
  )

  ;; Turn LED off
  ;; Resets PA5 low using BSRR register
  (func $led_off
    (local $gpioa_bsrr i32)

    ;; GPIOA BSRR register
    (local.set $gpioa_bsrr (i32.const 0x40020018))

    ;; Reset pin 5 (bit 21 in upper halfword resets the pin)
    (i32.store (local.get $gpioa_bsrr) (i32.const 0x00200000))
  )

  ;; Simple delay loop
  ;; Delays for approximately count iterations
  (func $delay (param $count i32)
    (local $i i32)
    (local.set $i (i32.const 0))

    (block $break
      (loop $continue
        ;; Check if i < count
        (br_if $break
          (i32.ge_u (local.get $i) (local.get $param 0)))

        ;; Increment i
        (local.set $i
          (i32.add (local.get $i) (i32.const 1)))

        ;; Continue loop
        (br $continue)
      )
    )
  )

  ;; Main blink loop
  ;; Continuously toggles LED with delay
  (func (export "main")
    ;; Initialize GPIO
    (call $gpio_init)

    ;; Infinite blink loop
    (block $exit
      (loop $blink
        ;; Turn LED on
        (call $led_on)

        ;; Delay
        (call $delay (i32.const 500000))

        ;; Turn LED off
        (call $led_off)

        ;; Delay
        (call $delay (i32.const 500000))

        ;; Continue blinking
        (br $blink)
      )
    )
  )
)
