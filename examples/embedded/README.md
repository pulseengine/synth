# LED Blink Example

This example demonstrates a minimal embedded application written in WebAssembly Text format that controls an LED on the nRF52840 development board.

## Hardware Target

- **Board**: nRF52840-DK
- **MCU**: nRF52840 (ARM Cortex-M4F)
- **LED**: P0.13 (LED1 on the dev board)

## Example Overview

The `led_blink.wat` file contains a complete LED blink program that:

1. **Initializes GPIO**: Configures P0.13 as an output pin
2. **Controls LED**: Turns the LED on and off using memory-mapped I/O
3. **Delays**: Implements a busy-wait delay loop
4. **Loops Forever**: Continuously blinks the LED

## WebAssembly Features Demonstrated

### Memory-Mapped I/O
```wasm
(global $GPIO_P0_OUT (mut i32) (i32.const 0x50000504))
(i32.store (global.get $GPIO_P0_OUT) (local.get $value))
```

### Bit Manipulation
```wasm
;; Calculate pin mask: 1 << pin_number
(i32.shl (i32.const 1) (global.get $LED_PIN))
```

### Control Flow
```wasm
(block $break
  (loop $continue
    ;; ... work ...
    (br_if $break (condition))
    (br $continue)
  )
)
```

## Synthesis Pipeline

To synthesize this WebAssembly module to ARM assembly:

### Step 1: Compile WAT to WASM
```bash
wat2wasm led_blink.wat -o led_blink.wasm
```

### Step 2: Transpile to C (using w2c2)
```bash
w2c2 led_blink.wasm led_blink.c
```

### Step 3: Generate Support Files (using Synth)
```bash
synth synthesize \
  --target nrf52840 \
  --wasm led_blink.wasm \
  --output build/
```

This generates:
- `startup.c` - ARM Cortex-M startup code
- `linker.ld` - Linker script for nRF52840
- `mpu_init.c` - MPU configuration (optional)

### Step 4: Compile with ARM GCC
```bash
arm-none-eabi-gcc \
  -mcpu=cortex-m4 \
  -mthumb \
  -mfloat-abi=hard \
  -mfpu=fpv4-sp-d16 \
  -O2 \
  -T build/linker.ld \
  -o build/led_blink.elf \
  build/startup.c \
  led_blink.c
```

### Step 5: Generate Binary
```bash
arm-none-eabi-objcopy -O binary build/led_blink.elf build/led_blink.bin
```

### Step 6: Flash to Device
```bash
nrfjprog --program build/led_blink.bin --chiperase --verify
nrfjprog --reset
```

## Optimization Opportunities

The synthesis pipeline can apply these optimizations:

### 1. Strength Reduction
```wasm
;; Original: multiply by power of 2
(i32.mul (local.get $x) (i32.const 4))

;; Optimized: shift left
(i32.shl (local.get $x) (i32.const 2))
```

### 2. Instruction Fusion
```wasm
;; Original: separate shift and add
(i32.shl (local.get $base) (i32.const 2))
(i32.add (local.get $offset))

;; Optimized ARM: single instruction
ADD r0, r1, r2, LSL #2
```

### 3. Constant Folding
```wasm
;; Original: runtime calculation
(i32.shl (i32.const 1) (i32.const 13))

;; Optimized: compile-time constant
(i32.const 8192)
```

### 4. Dead Code Elimination
The synthesis engine can remove unused functions and dead branches.

## Memory Layout

For nRF52840 (1MB Flash, 256KB RAM):

```
Flash (0x00000000 - 0x000FFFFF):
  0x00000000: Vector Table (256 bytes)
  0x00000100: .text (code)
  0x000xxxxx: .rodata (constants)

RAM (0x20000000 - 0x2003FFFF):
  0x20000000: .data (initialized data)
  0x200xxxxx: .bss (zero-initialized)
  0x200xxxxx: .heap
  0x2003Fxxx: .stack
```

## Expected Performance

Based on w2c2 benchmarks and synthesis optimizations:

- **Code Size**: ~200-300 bytes (including startup code)
- **RAM Usage**: <1KB (mostly stack)
- **Performance**: ~90-95% of hand-written C
- **Blink Frequency**: ~1 Hz (with 1M cycle delay)

## Hardware Requirements

To run this example, you need:

1. nRF52840-DK development board
2. J-Link debugger (built into the DK)
3. nRF Command Line Tools
4. ARM GNU Toolchain

## Future Enhancements

Possible extensions to this example:

1. **PWM**: Use timer peripheral for precise delays
2. **Multiple LEDs**: Control all 4 LEDs on the DK
3. **Button Input**: Read button state and toggle LED
4. **Low Power**: Use WFI (Wait For Interrupt) instead of busy-wait
5. **UART**: Send debug messages over serial

## References

- nRF52840 Product Specification: https://infocenter.nordicsemi.com/pdf/nRF52840_PS_v1.2.pdf
- ARM Cortex-M4 Technical Reference: https://developer.arm.com/documentation/100166/0001
- WebAssembly Core Specification: https://webassembly.github.io/spec/core/
