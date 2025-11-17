# WebAssembly Component Model - Deep Research

## Executive Summary

The WebAssembly Component Model is a specification for building composable, interoperable WebAssembly modules with high-level interface types and strong isolation guarantees - perfect for embedded systems!

## Core Concepts

### 1. Components vs Modules

**Core Modules** (Traditional WASM):
- Low-level: only numbers (i32, i64, f32, f64)
- Linear memory model
- Import/export functions
- No built-in isolation

**Components** (Component Model):
- High-level types: strings, records, variants, lists
- Multiple memories for isolation
- Interface Types (WIT)
- Composition and linking
- **Perfect for embedded multi-app systems!**

### 2. WIT (WebAssembly Interface Types)

WIT is the IDL (Interface Definition Language) for components:

```wit
// Example: Sensor interface for embedded
package embedded:sensors@1.0.0;

/// Temperature sensor interface
interface temperature {
    /// Temperature reading in Celsius
    record reading {
        value: float32,
        timestamp: u64,
    }

    /// Read current temperature
    read: func() -> result<reading, error-code>;

    /// Calibrate sensor
    calibrate: func(offset: float32) -> result<_, error-code>;
}

/// Error codes
enum error-code {
    sensor-not-ready,
    out-of-range,
    calibration-failed,
}

world sensor-app {
    import temperature;
    export process-data: func(readings: list<reading>);
}
```

### 3. Canonical ABI

The Canonical ABI defines how high-level types are lowered to/lifted from core WASM:

**Lowering** (Component → Core):
```
Component Type          Core WASM
─────────────────────────────────
string                → (i32, i32) [ptr, len]
list<u8>              → (i32, i32) [ptr, len]
record { x: i32 }     → (i32) [flattened]
variant               → (i32, ...) [discriminant + payload]
```

**Lifting** (Core → Component):
- Validates UTF-8 for strings
- Checks bounds for lists
- Validates discriminants for variants

### 4. Multi-Memory Proposal

Components can have multiple linear memories:

```wasm
(component
  (core module $sensor
    (memory (export "mem") 1)  ;; 64KB for sensor
    ;; ... sensor code ...
  )

  (core module $processor
    (memory (export "mem") 4)  ;; 256KB for processing
    ;; ... processing code ...
  )

  ;; Memories are isolated!
)
```

**For Embedded Systems:**
- Each component gets its own memory
- Hardware MPU enforces isolation
- No cross-component memory corruption
- Safety without MMU!

## Component Binary Format

### Structure

```
Component :=
  magic version
  component-section*

component-section :=
  | core-module-section
  | core-instance-section
  | core-type-section
  | component-section
  | instance-section
  | alias-section
  | type-section
  | canon-section
  | start-section
  | import-section
  | export-section
```

### Example Component Binary

```wasm
(component
  ;; Import LED interface
  (import "led" (instance $led
    (export "on" (func))
    (export "off" (func))
  ))

  ;; Core module doing the work
  (core module $app
    (import "led" "on" (func $led-on))
    (import "led" "off" (func $led-off))

    (func (export "blink")
      (call $led-on)
      ;; delay
      (call $led-off)
    )
  )

  ;; Instantiate and export
  (core instance $app-inst (instantiate $app
    (with "led" (instance $led))
  ))

  (func (export "run") (canon lift
    (core func $app-inst "blink")
  ))
)
```

## Canonical ABI Details

### String Encoding

Components support multiple string encodings:

```rust
enum StringEncoding {
    UTF8,       // Default, most common
    UTF16,      // For Windows/Java interop
    Latin1,     // For ASCII/Latin1 data
}
```

**Lowering a string:**
```rust
fn lower_string(s: &str, encoding: StringEncoding, memory: &mut Memory, realloc: ReallocFunc) -> (i32, i32) {
    let bytes = match encoding {
        UTF8 => s.as_bytes(),
        UTF16 => encode_utf16(s),
        Latin1 => encode_latin1(s),
    };

    let ptr = realloc(0, 0, 1, bytes.len());
    memory.write(ptr, bytes);

    (ptr as i32, bytes.len() as i32)
}
```

### List Lowering/Lifting

```rust
fn lower_list<T>(list: &[T], memory: &mut Memory, lower_elem: impl Fn(&T) -> i32) -> (i32, i32) {
    let len = list.len();
    let ptr = realloc(0, 0, align_of::<T>(), len * size_of::<T>());

    for (i, elem) in list.iter().enumerate() {
        let elem_val = lower_elem(elem);
        memory.write_at(ptr + i * size_of::<T>(), elem_val);
    }

    (ptr as i32, len as i32)
}

fn lift_list<T>(ptr: i32, len: i32, memory: &Memory, lift_elem: impl Fn(i32) -> T) -> Vec<T> {
    let mut result = Vec::with_capacity(len as usize);

    for i in 0..len {
        let elem_ptr = ptr + i * size_of::<T>() as i32;
        let elem_val = memory.read_at(elem_ptr);
        result.push(lift_elem(elem_val));
    }

    result
}
```

### Record Flattening

Records are flattened into individual values when possible:

```wit
record point {
    x: s32,
    y: s32,
}
```

Lowered to: `(i32, i32)` - two separate values!

```wit
record complex {
    position: point,
    velocity: point,
    mass: float32,
}
```

Lowered to: `(i32, i32, i32, i32, f32)` - five values!

But if too many fields (>16), uses indirect passing via memory.

### Variant Encoding

```wit
variant result<T, E> {
    ok(T),
    err(E),
}
```

Lowered to: `(i32, ...)` where:
- First i32 is discriminant (0 = ok, 1 = err)
- Remaining values are the payload

```rust
fn lower_variant<T, E>(
    variant: Result<T, E>,
    lower_ok: impl Fn(T) -> Vec<i32>,
    lower_err: impl Fn(E) -> Vec<i32>,
) -> Vec<i32> {
    match variant {
        Ok(val) => {
            let mut result = vec![0]; // discriminant
            result.extend(lower_ok(val));
            result
        }
        Err(err) => {
            let mut result = vec![1]; // discriminant
            result.extend(lower_err(err));
            result
        }
    }
}
```

## Resource Types

Resources are handles with ownership semantics:

```wit
resource file {
    constructor(path: string);
    read: func() -> result<list<u8>, error-code>;
    write: func(data: list<u8>) -> result<_, error-code>;
}
```

Compiled to:

```wasm
;; Constructor
(func (export "[constructor]file") (param $path i32) (param $path-len i32) (result i32))

;; Methods take handle as first param
(func (export "[method]file.read") (param $handle i32) (result i32))
(func (export "[method]file.write") (param $handle i32) (param $data i32) (param $data-len i32) (result i32))

;; Destructor
(func (export "[destructor]file") (param $handle i32))
```

**Resource Handle Management:**
- Handle = u32 index into resource table
- Component owns the handle
- Automatic cleanup on drop
- Borrow checking enforced

## Embedded Systems Applications

### Use Case 1: Modular Sensor System

```wit
// sensor-interface.wit
package embedded:sensors;

interface temperature {
    read: func() -> float32;
}

interface humidity {
    read: func() -> float32;
}

interface display {
    show: func(temp: float32, humid: float32);
}

world weather-station {
    import temperature;
    import humidity;
    export display;
    export update: func();
}
```

**Benefits:**
- Each sensor in separate component
- Isolated memory (MPU-enforced)
- Hot-swappable sensors
- Type-safe interfaces

### Use Case 2: Secure Bootloader

```wit
// bootloader.wit
package embedded:bootloader;

interface firmware {
    resource image {
        constructor(data: list<u8>);
        verify: func() -> result<_, error-code>;
        install: func() -> result<_, error-code>;
    }
}

world secure-boot {
    import firmware;
    export boot: func() -> result<_, error-code>;
}
```

**Benefits:**
- Firmware in separate component
- Memory isolation prevents corruption
- Signature verification
- Secure state transitions

### Use Case 3: Multi-Application System

```wit
// app-framework.wit
package embedded:framework;

interface system {
    sleep: func(ms: u32);
    gpio-write: func(pin: u8, value: bool);
    gpio-read: func(pin: u8) -> bool;
}

world application {
    import system;
    export init: func();
    export run: func();
}
```

**Benefits:**
- Multiple apps on one MCU
- Each app isolated
- Shared system services
- No mutual interference

## Implementation Strategy for Synth

### Phase 1: WIT Parser (Weeks 1-2)

```rust
// crates/synth-wit/src/lib.rs
pub struct WitParser {
    lexer: Lexer,
    tokens: Vec<Token>,
}

pub enum WitItem {
    Interface(Interface),
    World(World),
    Type(TypeDef),
}

pub struct Interface {
    name: String,
    functions: Vec<Function>,
    types: Vec<TypeDef>,
}

pub struct Function {
    name: String,
    params: Vec<(String, Type)>,
    results: Vec<Type>,
}
```

### Phase 2: Canonical ABI (Weeks 3-4)

```rust
// crates/synth-abi/src/lib.rs
pub struct AbiLowering {
    memory: MemoryIndex,
    realloc: FuncIndex,
    encoding: StringEncoding,
}

impl AbiLowering {
    pub fn lower_string(&self, s: &str) -> (i32, i32);
    pub fn lower_list<T>(&self, list: &[T]) -> (i32, i32);
    pub fn lower_record(&self, record: &Record) -> Vec<i32>;
    pub fn lower_variant(&self, variant: &Variant) -> Vec<i32>;
}
```

### Phase 3: Component Linking (Weeks 5-6)

```rust
// crates/synth-linker/src/lib.rs
pub struct ComponentLinker {
    components: Vec<Component>,
    instances: HashMap<String, ComponentInstance>,
}

impl ComponentLinker {
    pub fn instantiate(&mut self, component: &Component) -> Result<InstanceId>;
    pub fn link(&mut self, imports: &[Import]) -> Result<()>;
    pub fn resolve_exports(&self, instance: InstanceId) -> &[Export];
}
```

### Phase 4: MPU Isolation (Weeks 7-8)

```rust
// crates/synth-backend/src/component_isolation.rs
pub struct ComponentIsolation {
    mpu: MPUAllocator,
    regions: HashMap<ComponentId, Vec<MPURegion>>,
}

impl ComponentIsolation {
    pub fn allocate_component(&mut self, component: &Component) -> Result<ComponentId>;
    pub fn configure_mpu(&self, component_id: ComponentId) -> Result<()>;
    pub fn enter_component(&self, component_id: ComponentId);
    pub fn exit_component(&self, component_id: ComponentId);
}
```

## Performance Considerations

### ABI Overhead

**String lowering:**
- Best case: ~10-20 cycles (short string, pre-allocated)
- Worst case: ~100+ cycles (allocation + encoding + copy)
- **Optimization:** String interning, pooled allocation

**List lowering:**
- O(n) copy operation
- Cache-friendly sequential writes
- **Optimization:** Zero-copy when possible

**Indirect parameter passing:**
- Extra memory round-trip
- ~5-10 cycles overhead
- **Optimization:** Register passing when < 4 params

### Memory Isolation Overhead

**MPU Configuration:**
- ~10-20 cycles per MPU region update
- Max 8 regions on Cortex-M4
- **Optimization:** Cache MPU configs, minimize switches

**Cross-Component Calls:**
- MPU reconfiguration
- Stack switching (if separate stacks)
- ~50-100 cycles total overhead
- **Optimization:** Batch calls, avoid chatty interfaces

## Security Benefits

### Memory Safety
- Each component has isolated memory
- MPU enforces at hardware level
- No pointer sharing between components
- Buffer overflows can't corrupt other components

### Type Safety
- Strong typing at component boundaries
- Runtime validation of ABI
- Invalid data rejected at boundary
- Prevents type confusion attacks

### Capability-Based Security
- Components only get what they import
- No ambient authority
- Explicit capability passing
- Principle of least privilege

## References

- [Component Model Specification](https://github.com/WebAssembly/component-model)
- [WIT Format](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md)
- [Canonical ABI](https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md)
- [wit-bindgen](https://github.com/bytecodealliance/wit-bindgen)
- [wasmtime Component Model](https://docs.wasmtime.dev/contributing-implementing-wasm-proposals-component-model.html)

## Next Steps for Synth

1. ✅ **Research completed** - This document
2. → **Implement WIT parser** - Parse interface definitions
3. → **Implement Canonical ABI** - Lower/lift high-level types
4. → **Multi-memory support** - Multiple isolated memory regions
5. → **Component linking** - Instantiate and compose components
6. → **MPU integration** - Hardware-enforced isolation
7. → **End-to-end example** - Multi-component embedded app
