# Renode vs QEMU: Analysis for Synth Testing Infrastructure

## Executive Summary

**Recommendation: Use Renode as primary, keep QEMU as secondary option**

Renode is significantly better suited for Synth's embedded ARM testing needs due to its embedded-first design, better MCU support, and superior CI/CD integration.

## Comparison Matrix

| Feature | Renode | QEMU |
|---------|--------|------|
| **Cortex-M Support** | Excellent (M0, M3, M4, M33) | Limited (2 TI boards) |
| **STM32F407 Support** | Native (stm32f4_discovery.repl) | Partial |
| **nRF52840 Support** | Native | None |
| **Peripheral Modeling** | UART, SPI, I2C, GPIO, DMA, ADC | Basic |
| **Extensibility** | Text-based config + C# | Fork + C (no stable API) |
| **CI/CD Integration** | Native Robot Framework + GitHub Action | Manual setup |
| **ELF Loading** | `sysbus LoadELF @file.elf` | `-kernel file.elf` |
| **Multi-node Simulation** | Native (wireless, wired) | Limited |
| **Debugging** | GDB, function tracing, coverage | GDB |
| **Zephyr Integration** | Official support | Community |

## Synth Target Hardware Support

### STM32F407 Discovery (Primary Target)

**Renode:**
- Built-in platform: `platforms/boards/stm32f4_discovery-kit.repl`
- Official script: `scripts/single-node/stm32f4_discovery.resc`
- Peripherals: UART, GPIO, DMA, timers, etc.

**QEMU:**
- `stm32f4-discovery` machine available but limited peripheral support

### nRF52840 (Secondary Target)

**Renode:**
- Full support including BLE simulation
- Zephyr demos work out-of-box

**QEMU:**
- No nRF52840 support

## CI/CD Integration

### Renode + GitHub Actions

```yaml
# .github/workflows/test.yml
name: Firmware Tests
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Build firmware
        run: cargo run -p synth-cli -- compile examples/wat/simple_add.wat -o test.elf

      - uses: antmicro/renode-test-action@v4
        with:
          renode-revision: 'master'
          tests-to-run: 'tests/renode/*.robot'
```

### Robot Framework Test Example

```robot
*** Settings ***
Library    String
Suite Setup    Setup
Suite Teardown    Teardown
Test Teardown    Test Teardown

*** Keywords ***
Setup
    Execute Command    mach create
    Execute Command    machine LoadPlatformDescription @platforms/boards/stm32f4_discovery-kit.repl

Test Teardown
    Execute Command    mach clear

*** Test Cases ***
Should Execute Add Function
    Execute Command    sysbus LoadELF @${CURDIR}/add.elf
    Execute Command    cpu Step 10
    ${r0}=    Execute Command    cpu GetRegisterUnsafe 0
    Should Be Equal As Integers    ${r0}    42    # Expected result
```

## Why Renode is Better for Synth

1. **Embedded-First Design**: Built specifically for MCU simulation, not retrofitted
2. **Our Target Boards**: Both STM32F407 and nRF52840 have native support
3. **CI Integration**: GitHub Action available, Robot Framework built-in
4. **Deterministic Testing**: Same simulation every time (no hardware variance)
5. **Pre-Silicon Development**: Can test before hardware available
6. **Google/TensorFlow Uses It**: Proven at scale for embedded testing

## Parallel Approach Recommendation

| Phase | Tool | Purpose |
|-------|------|---------|
| **Development** | Renode | Primary testing, CI/CD |
| **Validation** | Renode | Automated regression tests |
| **Backup** | QEMU | Alternative for specific scenarios |
| **Hardware** | Real boards | Final validation only |

### Rationale for Parallel (Not Either/Or)

1. **Renode Primary**: 95% of testing needs
   - Automated CI/CD
   - Function-level testing
   - Peripheral interaction testing

2. **QEMU Secondary**: Keep existing synth-qemu crate
   - Some users may prefer QEMU
   - QEMU has broader general awareness
   - Useful for quick ad-hoc testing

## Implementation Plan

### Phase 1: Renode Integration (Recommended)
1. Create `crates/synth-renode/` with Renode runner
2. Add Robot Framework test templates
3. Set up GitHub Action for CI
4. Create `.repl` file for Synth test harness

### Phase 2: Full ELF Generation (Required for Both)
1. Add vector table generation to ELF builder
2. Add startup code (reset handler, stack init)
3. Generate proper function prologue/epilogue
4. Wire up regalloc2 for correct register usage

### Phase 3: Test Suite
1. Create Robot Framework tests for each WASM operation
2. Add integration tests for WAT examples
3. Set up nightly CI runs

## Installation

### Renode
```bash
# macOS
brew install renode

# Linux (Debian/Ubuntu)
wget https://github.com/renode/renode/releases/download/v1.15.3/renode_1.15.3_amd64.deb
sudo dpkg -i renode_1.15.3_amd64.deb

# Or portable
wget https://github.com/renode/renode/releases/download/v1.15.3/renode-1.15.3.linux-portable.tar.gz
```

### QEMU (Existing)
```bash
# macOS
brew install qemu

# Linux
sudo apt install qemu-system-arm
```

## References

- [Renode Documentation](https://renode.readthedocs.io/)
- [Renode GitHub](https://github.com/renode/renode)
- [Cortex-M MCU Emulation with Renode](https://interrupt.memfault.com/blog/intro-to-renode)
- [Firmware Testing with Renode and GitHub Actions](https://interrupt.memfault.com/blog/test-automation-renode)
- [Renode GitHub Action](https://github.com/antmicro/renode-test-action)
- [STM32F4 Emulation with Renode](https://medium.com/@pc0is0me/getting-started-with-stm32f4-emulation-using-renode-f6cb158d27d1)
