# Anti-Pinch Window Controller

Safety-critical automotive example demonstrating Synth's value proposition for
ASIL-rated embedded systems. Inspired by the [OSxCAR anti-pinch
demonstration](https://osxcar.de/insights/demonstration/).

## Safety-Critical Use Case

Power window anti-pinch protection is an ISO 26262 ASIL-B function required in
all modern vehicles. The controller must:

1. **Detect obstructions** (fingers, limbs) by monitoring motor current
2. **Stop the motor within milliseconds** when a jam/pinch is detected
3. **Reverse the window** to release the trapped object
4. **Never produce a false negative** -- missing a real pinch causes injury

This maps directly to Synth's strengths:

| Concern | Synth Solution |
|---------|---------------|
| Compiler bugs cause incorrect jam detection | Formally verified compilation (Rocq proofs) |
| Floating-point non-determinism | Integer-only arithmetic (0.1% fixed-point) |
| Runtime overhead misses WCET deadlines | Zero-overhead native ARM Thumb-2 code |
| Memory corruption corrupts safety state | WASM linear memory model (bounds-checked) |
| Untraceable code transformations | Bidirectional WASM-to-ARM traceability |

## Architecture

```
                   +------------------+
  Current Sensor   |                  |   PWM Output
  (ADC, mA)  ---->|  anti_pinch.wat  |----> Motor Driver
                   |  (WASM module)   |     (H-bridge)
  Position Sensor  |                  |
  (Hall/encoder)-->|  compiled by     |   Jam Alert
                   |  Synth to ARM    |----> Dashboard
                   +------------------+
                          |
                    100Hz tick loop
```

### Control Flow (tick function)

```
1. Read motor current from memory
2. If jam already flagged -> return 0 (motor stopped)
3. Determine direction (closing/opening/stopped)
4. If closing AND current > threshold (debounced, 3 ticks):
   -> Set jam flag
   -> Set PWM = 0 (emergency stop)
   -> Return 0
5. Ramp PWM toward target (soft start/stop, 2%/tick)
6. Update position estimate (PWM-proportional)
7. If position == target -> stop motor
8. Return new PWM duty cycle
```

### Memory Layout

All state is in WASM linear memory (integer, 4-byte aligned):

| Offset | Field | Range | Description |
|--------|-------|-------|-------------|
| 0 | `window_position` | 0-1000 | Current position (0.0%-100.0%) |
| 4 | `motor_current_ma` | mA | Last sensor reading |
| 8 | `pwm_duty` | 0-1000 | Current PWM output (0.0%-100.0%) |
| 12 | `direction` | 0/1/2 | 0=stopped, 1=closing, 2=opening |
| 16 | `jam_detected` | 0/1 | Jam flag |
| 20 | `current_threshold_ma` | mA | Jam detection threshold (default: 800) |
| 24 | `target_position` | 0-1000 | Commanded position |
| 28 | `pwm_ramp_rate` | units/tick | Soft start/stop rate (default: 20 = 2.0%) |
| 32 | `consecutive_over` | count | Debounce counter |
| 36 | `jam_debounce_limit` | count | Ticks to confirm jam (default: 3) |

## ASPICE / STPA Mapping

### STPA Losses

- **L-1**: Bodily injury to vehicle occupant (finger/limb trapped by window)
- **L-2**: Vehicle fails safety certification (non-compliant anti-pinch)

### STPA Hazards

- **H-1**: Window continues closing when obstruction present
- **H-3**: Jam detection has false negative (current reading below threshold
  despite real obstruction)

### STPA Unsafe Control Actions

| Control Action | Not Providing | Providing Incorrectly | Too Late |
|---------------|---------------|----------------------|----------|
| Stop motor on jam | H-1: injury | N/A | H-1: injury if >100ms |
| Reverse window | L-1: prolonged pinch | H-3: false negative | L-1 |
| Current threshold check | H-1, H-3 | H-3: wrong threshold | H-1 |

### Synth Mitigations

- **Formal verification**: Compilation correctness proven in Rocq -- the
  threshold comparison in the WAT produces the same result in ARM
- **Deterministic execution**: Integer arithmetic, no floating-point rounding,
  bounded WCET for the tick function
- **Memory safety**: WASM linear memory prevents state corruption from adjacent
  components

## Project Structure

```
anti-pinch-controller/
+-- anti_pinch.wat       # WASM module (control logic source)
+-- CMakeLists.txt       # Zephyr build configuration
+-- prj.conf             # Zephyr project settings
+-- README.md            # This file
+-- src/
    +-- main.c           # Zephyr app (simulation + control loop)
    +-- anti_pinch.s     # ARM Thumb-2 assembly (reference implementation)
```

## Building

### Compile WAT to ELF (standalone verification)

```bash
# From repository root
cargo run -p synth-cli -- compile \
  examples/anti-pinch-controller/anti_pinch.wat \
  -o /tmp/antipinch.elf \
  --cortex-m --all-exports

# Disassemble to verify generated code
cargo run -p synth-cli -- disasm /tmp/antipinch.elf
```

### Build Zephyr firmware

```bash
export ZEPHYR_BASE=/path/to/zephyr

# Build for Cortex-M4 (e.g., STM32F4 Discovery)
west build -b stm32f4_disco examples/anti-pinch-controller

# Build for QEMU emulation
west build -b qemu_cortex_m3 examples/anti-pinch-controller
west build -t run
```

## Expected Output

```
===========================================================
  Anti-Pinch Window Controller
  Compiled by Synth (WebAssembly -> ARM Cortex-M)
===========================================================

Scenario: close window to 100%, jam at ~70%, then reopen

 Time  | Pos    | Current | PWM    | Dir   | Jam | Event
-------|--------|---------|--------|-------|-----|------
    0  |  0.0%  |    0 mA |  2.0%  | CLOSE |  no |
  100  | 10.5%  |  256 mA | 64.0%  | CLOSE |  no |
  200  | 25.2%  |  320 mA | 80.0%  | CLOSE |  no |
  ...
  700  | 70.0%  | 1200 mA |  0.0%  | STOP  | YES | << JAM DETECTED

  >> Anti-pinch activated! Window will reverse in 500ms.

  >> Reversing window (opening to 0%).

 1200  | 65.0%  |  320 mA | 80.0%  | OPEN  |  no |
  ...
 1800  |  0.0%  |    0 mA |  0.0%  | STOP  |  no |

===========================================================
  Demo complete -- anti-pinch safety function verified.
===========================================================
```

## Rivet Traceability

See `artifacts/anti-pinch-example.yaml` for full ASPICE traceability:

- **AP-001**: Anti-pinch controller WASM module (derives-from BR-001, BR-003)
- **AP-002**: Jam detection via current threshold (system-req)
- **AP-003**: Soft start/stop PWM ramping (system-req)
- **AP-VER-001**: Renode simulation test (sys-verification)

## License

Same as Synth project (see root LICENSE file).
