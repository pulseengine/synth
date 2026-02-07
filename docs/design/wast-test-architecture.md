# WAST Test Architecture for Synth

## Overview

This document describes a future-proof architecture for running WebAssembly spec tests (WAST) against Synth-compiled ARM binaries on Renode.

## Requirements

### Immediate (Phase 1)
- Parse WAST files and extract test cases
- Compile WASM modules to ARM ELF via Synth
- Execute on Renode and verify `assert_return` results
- Support i32 arithmetic operations

### Near-term (Phase 2)
- `assert_trap` detection for div/rem by zero, overflow
- Control flow tests (block, loop, if, br)
- Multi-function modules

### Future (Phase 3+)
- Memory operations with bounds checking
- Table operations
- Call indirect with type checking
- SIMD operations
- Full spec conformance (~62,000 tests)

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                        synth-test                                │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐   │
│  │ WAST Parser  │  │ Test Runner  │  │  Renode Controller   │   │
│  │ (wast crate) │  │              │  │                      │   │
│  └──────┬───────┘  └──────┬───────┘  └──────────┬───────────┘   │
│         │                 │                      │               │
│         ▼                 ▼                      ▼               │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │                    Test Orchestrator                      │   │
│  │  - Compiles modules via Synth CLI                        │   │
│  │  - Manages Renode lifecycle                              │   │
│  │  - Executes tests and collects results                   │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                         Renode                                   │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐   │
│  │   Cortex-M   │  │  GDB Server  │  │   Telnet/Socket      │   │
│  │   Emulation  │  │  (port 3333) │  │   API (port 1234)    │   │
│  └──────────────┘  └──────────────┘  └──────────────────────┘   │
│                           │                      │               │
│                    ┌──────┴──────────────────────┘               │
│                    ▼                                             │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │                    CPU Hooks                              │   │
│  │  - Address hooks (function entry/exit)                   │   │
│  │  - Interrupt hooks (fault detection)                     │   │
│  │  - Watchpoints (memory access)                           │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

## Renode Control Options

### Option A: Telnet/Monitor API (Recommended for Phase 1-2)
```rust
// Connect to Renode monitor
let conn = TcpStream::connect("localhost:1234")?;

// Send commands
conn.write_all(b"mach create\n")?;
conn.write_all(b"machine LoadPlatformDescription @platform.repl\n")?;
conn.write_all(b"sysbus LoadELF @test.elf\n")?;

// Set registers and execute
conn.write_all(b"cpu SetRegisterUnsafe 0 5\n")?;  // arg0
conn.write_all(b"cpu SetRegisterUnsafe 1 3\n")?;  // arg1
conn.write_all(b"cpu PC 0x91\n")?;                 // function addr
conn.write_all(b"cpu Step 20\n")?;                 // execute

// Read result
conn.write_all(b"cpu GetRegisterUnsafe 0\n")?;
let result = read_response(&mut conn)?;
```

**Pros:**
- Simple text protocol
- No additional dependencies
- Works with any Renode version

**Cons:**
- String parsing required
- No structured error handling

### Option B: GDB Protocol (Recommended for trap detection)
```rust
// Connect via GDB remote protocol
let mut gdb = GdbConnection::connect("localhost:3333")?;

// Set breakpoint at function return
gdb.set_breakpoint(0x94)?;  // BX LR address

// Set registers
gdb.write_register(0, 5)?;  // r0 = 5
gdb.write_register(1, 3)?;  // r1 = 3
gdb.write_register(15, 0x91)?;  // pc = function

// Continue until breakpoint or signal
match gdb.continue_execution()? {
    StopReason::Breakpoint(_) => {
        let result = gdb.read_register(0)?;
        // assert_return: check result
    }
    StopReason::Signal(sig) => {
        // assert_trap: check signal type
        // SIGSEGV -> memory trap
        // SIGILL -> illegal instruction
        // SIGFPE -> arithmetic trap
    }
}
```

**Pros:**
- Structured protocol
- Trap detection via signals
- Breakpoint support
- Reverse execution support

**Cons:**
- More complex implementation
- Need GDB protocol library

### Option C: pyrenode3 (Future - when stable)
```python
from pyrenode3 import Emulation

e = Emulation()
e.load_repl("platform.repl")
e.machine0.sysbus.LoadELF("test.elf")

# Direct register access
e.machine0.cpu.SetRegisterUnsafe(0, 5)
e.machine0.cpu.SetRegisterUnsafe(1, 3)
e.machine0.cpu.PC = 0x91

# Add hook for trap detection
e.machine0.cpu.AddHookAtInterruptBegin(lambda: trap_detected())

# Execute
e.machine0.cpu.Step(20)
result = e.machine0.cpu.GetRegisterUnsafe(0)
```

**Pros:**
- Full API access
- Native Python integration
- Rich hook support

**Cons:**
- Still maturing
- Python dependency

## Trap Detection Strategy

### Phase 1: No trap detection
- Focus on `assert_return` tests only
- Skip `assert_trap` tests

### Phase 2: CPU Hook-based traps
```
# In Renode, set up hooks
cpu AddHookAtInterruptBegin "python handle_interrupt()"
cpu SetHookAtBlockEnd "python check_fault()"
```

For Cortex-M, traps manifest as:
- HardFault exception (vector 0x0C)
- UsageFault for div-by-zero (if enabled)
- MemManage for memory violations

### Phase 3: GDB signal-based traps
- Use GDB `continue` and catch stop reasons
- Map signals to WAST trap types:
  - `SIGFPE` → "integer divide by zero", "integer overflow"
  - `SIGSEGV` → "out of bounds memory access"
  - `SIGILL` → "unreachable", "invalid conversion"

## Test Execution Flow

```
For each WAST file:
  1. Parse WAST → extract modules and test cases

  2. For each module:
     a. Write WAT to temp file
     b. Compile: synth compile module.wat -o module.elf --cortex-m
     c. Extract function addresses from ELF symbol table

  3. Start Renode (once per test file)
     - Load platform
     - Load ELF
     - Set up hooks (if trap detection enabled)

  4. For each test case:
     a. Reset CPU state (PC, SP, registers)
     b. Set function arguments (r0-r3)
     c. Execute until return or trap
     d. Compare result or trap type
     e. Record pass/fail

  5. Generate report (JUnit XML, JSON, etc.)
```

## Performance Considerations

### Current (Robot Framework)
- ~1-2 seconds per test case
- Machine create/destroy overhead
- 62,400 tests → ~17-35 hours

### Optimized (Keep Renode running)
- ~10-50ms per test case (estimate)
- Reuse machine, just reset registers
- 62,400 tests → ~10-50 minutes

### Parallel execution
- Run multiple Renode instances
- Shard tests by file
- 8 cores → ~1-6 minutes

## Implementation Plan

### Phase 1: Telnet-based runner (Now)
1. Add Renode telnet client to `synth-test`
2. Implement test execution loop
3. Keep Robot as fallback/comparison

### Phase 2: GDB integration (When adding div/rem)
1. Add GDB remote protocol client
2. Implement trap detection
3. Map signals to WAST trap types

### Phase 3: Full conformance (Future)
1. Evaluate pyrenode3 stability
2. Add memory/table test support
3. Implement parallel execution
4. Target full spec conformance

## File Structure

```
crates/synth-test/
├── src/
│   ├── lib.rs           # WAST parsing, test case types
│   ├── main.rs          # CLI interface
│   ├── renode/
│   │   ├── mod.rs       # Renode controller trait
│   │   ├── telnet.rs    # Telnet/Monitor API client
│   │   ├── gdb.rs       # GDB remote protocol client
│   │   └── hooks.rs     # CPU hook management
│   ├── runner.rs        # Test execution orchestrator
│   └── report.rs        # Result formatting (JUnit, JSON)
├── tests/
│   └── integration.rs   # Self-tests
└── Cargo.toml
```

## Success Metrics

| Phase | Tests | Time Target | Trap Support |
|-------|-------|-------------|--------------|
| 1 | i32 arithmetic (~400) | <5 min | No |
| 2 | + control flow (~800) | <10 min | div/rem only |
| 3 | + memory (~2000) | <30 min | bounds check |
| 4 | Full spec (~62,000) | <1 hour | Full |

## References

- [Renode GDB docs](https://renode.readthedocs.io/en/latest/debugging/gdb.html)
- [Renode Python API](https://renode.readthedocs.io/en/latest/basic/using-python.html)
- [pyrenode3 announcement](https://antmicro.com/blog/2023/11/python-driven-automation-and-scripting-in-renode-with-pyrenode3/)
- [Renode reverse execution](https://renode.io/news/initial-support-for-reverse-execution-in-renode/)
- [WebAssembly test suite](https://github.com/WebAssembly/testsuite)
