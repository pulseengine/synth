# Portable Memory Architecture Design

**Goal:** A memory management layer that works across bare metal, Zephyr RTOS, and FreeRTOS while supporting WebAssembly multi-memory modules.

---

## Design Principles

1. **Platform Abstraction**: Single API, multiple backends
2. **Multi-Memory Native**: Design for N memories from the start
3. **Bounds Checking Flexibility**: Pluggable strategies (software, MPU, masking)
4. **Zero-Copy Where Possible**: Share memory between host and WASM when safe
5. **Deterministic Allocation**: No dynamic allocation after initialization (ASIL D)

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    WASM Module                                  │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                         │
│  │ Memory 0│  │ Memory 1│  │ Memory 2│  ...                    │
│  │ (heap)  │  │ (shared)│  │ (persist)│                        │
│  └────┬────┘  └────┬────┘  └────┬────┘                         │
└───────┼────────────┼────────────┼──────────────────────────────┘
        │            │            │
        ▼            ▼            ▼
┌─────────────────────────────────────────────────────────────────┐
│              Memory Manager (synth-memory crate)                │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  MemoryTable: [MemoryDescriptor; MAX_MEMORIES]           │  │
│  │    - base_addr: *mut u8                                  │  │
│  │    - size: u32                                           │  │
│  │    - max_pages: u32                                      │  │
│  │    - protection: ProtectionStrategy                      │  │
│  │    - flags: MemoryFlags (shared, persist, etc.)          │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │  Bounds Checker (trait-based)                             │ │
│  │    ├── SoftwareBoundsChecker                              │ │
│  │    ├── MaskingBoundsChecker (power-of-2)                  │ │
│  │    └── MpuBoundsChecker (platform-specific)               │ │
│  └───────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌─────────────────────────────────────────────────────────────────┐
│              Platform Abstraction Layer (PAL)                   │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │  Bare Metal │  │   Zephyr    │  │  FreeRTOS   │             │
│  │  (direct)   │  │ (mem domain)│  │ (MPU API)   │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Hardware (Cortex-M MPU)                      │
└─────────────────────────────────────────────────────────────────┘
```

---

## Core Data Structures

### Memory Descriptor

```rust
// crates/synth-memory/src/descriptor.rs

/// Maximum memories per module (WASM spec allows unlimited, we cap for embedded)
pub const MAX_MEMORIES: usize = 8;

/// Memory protection strategy
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ProtectionStrategy {
    /// No protection (trust WASM code)
    None,
    /// Software bounds check before each access
    Software,
    /// Address masking for power-of-2 sizes (~5% overhead)
    Masking,
    /// MPU guard regions (~0% overhead, uses hardware)
    Mpu { region_id: u8 },
}

/// Memory flags for special behaviors
bitflags::bitflags! {
    pub struct MemoryFlags: u32 {
        /// Memory is shared between threads
        const SHARED = 0b0001;
        /// Memory persists across module reloads
        const PERSISTENT = 0b0010;
        /// Memory is read-only after initialization
        const READONLY = 0b0100;
        /// Memory is exported to host
        const EXPORTED = 0b1000;
    }
}

/// Single memory instance descriptor
#[repr(C)]
pub struct MemoryDescriptor {
    /// Base address of this memory region
    pub base: *mut u8,
    /// Current size in bytes
    pub size: u32,
    /// Maximum size in bytes (for grow operations)
    pub max_size: u32,
    /// Current page count (size / 65536)
    pub pages: u32,
    /// Maximum pages (max_size / 65536)
    pub max_pages: u32,
    /// Protection strategy for this memory
    pub protection: ProtectionStrategy,
    /// Memory flags
    pub flags: MemoryFlags,
    /// Platform-specific data (MPU region, Zephyr partition, etc.)
    pub platform_data: usize,
}

/// Memory table for a module
#[repr(C)]
pub struct MemoryTable {
    /// Memory descriptors
    pub memories: [MemoryDescriptor; MAX_MEMORIES],
    /// Number of active memories
    pub count: u8,
}
```

### Bounds Checker Trait

```rust
// crates/synth-memory/src/bounds.rs

/// Bounds checking strategy (compile-time or runtime selectable)
pub trait BoundsChecker {
    /// Check if address + size is within memory bounds
    /// Returns adjusted address or triggers trap
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap>;

    /// Generate ARM instructions for inline bounds check
    /// Returns instruction bytes to insert before load/store
    fn generate_check_code(&self, memory_idx: u32) -> Vec<u8>;
}

/// Software bounds checking (portable, ~25-40% overhead)
pub struct SoftwareBoundsChecker;

impl BoundsChecker for SoftwareBoundsChecker {
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap> {
        let end = addr.checked_add(size).ok_or(Trap::OutOfBounds)?;
        if end > memory.size {
            return Err(Trap::OutOfBounds);
        }
        Ok(addr)
    }

    fn generate_check_code(&self, memory_idx: u32) -> Vec<u8> {
        // Generate: CMP addr, size; BHS trap_handler
        // ... ARM encoding here
        vec![]
    }
}

/// Address masking for power-of-2 memories (~5% overhead)
pub struct MaskingBoundsChecker {
    pub mask: u32,  // size - 1, e.g., 0xFFFF for 64KB
}

impl BoundsChecker for MaskingBoundsChecker {
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        // Masking always succeeds (wraps around)
        Ok(addr & self.mask)
    }

    fn generate_check_code(&self, _memory_idx: u32) -> Vec<u8> {
        // Generate: AND addr, addr, #mask (single instruction)
        vec![]
    }
}

/// MPU-based protection (near-zero overhead)
pub struct MpuBoundsChecker {
    pub region_id: u8,
}

impl BoundsChecker for MpuBoundsChecker {
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        // No software check needed - MPU handles it
        Ok(addr)
    }

    fn generate_check_code(&self, _memory_idx: u32) -> Vec<u8> {
        // No code needed - use LDRT/STRT for unprivileged access
        vec![]
    }
}
```

---

## Platform Abstraction Layer (PAL)

### Trait Definition

```rust
// crates/synth-memory/src/platform.rs

/// Platform-specific memory operations
pub trait MemoryPlatform {
    /// Allocate memory region with specified alignment
    fn allocate(&mut self, size: u32, align: u32) -> Result<*mut u8, AllocError>;

    /// Free memory region
    fn deallocate(&mut self, ptr: *mut u8, size: u32);

    /// Configure MPU region (if available)
    fn configure_mpu_region(
        &mut self,
        region_id: u8,
        base: *const u8,
        size: u32,
        access: MpuAccess,
    ) -> Result<(), MpuError>;

    /// Disable MPU region
    fn disable_mpu_region(&mut self, region_id: u8);

    /// Get number of available MPU regions
    fn available_mpu_regions(&self) -> u8;

    /// Handle memory fault (for trap conversion)
    fn handle_fault(&mut self, addr: u32) -> FaultAction;
}

/// MPU access permissions
pub enum MpuAccess {
    NoAccess,
    ReadOnly,
    ReadWrite,
    ReadExecute,
}

/// What to do on memory fault
pub enum FaultAction {
    /// Convert to WASM trap
    Trap(Trap),
    /// Continue execution (for debugging)
    Continue,
    /// Panic (unrecoverable)
    Panic,
}
```

### Bare Metal Implementation

```rust
// crates/synth-memory/src/platform/bare_metal.rs

/// Bare metal memory platform (direct hardware access)
pub struct BareMetalPlatform {
    /// Static memory pool
    pool: &'static mut [u8],
    /// Current allocation offset
    offset: usize,
    /// MPU configuration
    mpu_enabled: bool,
}

impl BareMetalPlatform {
    pub fn new(pool: &'static mut [u8]) -> Self {
        Self {
            pool,
            offset: 0,
            mpu_enabled: false,
        }
    }
}

impl MemoryPlatform for BareMetalPlatform {
    fn allocate(&mut self, size: u32, align: u32) -> Result<*mut u8, AllocError> {
        // Bump allocator - no deallocation
        let aligned_offset = (self.offset + align as usize - 1) & !(align as usize - 1);
        let end = aligned_offset + size as usize;

        if end > self.pool.len() {
            return Err(AllocError::OutOfMemory);
        }

        let ptr = unsafe { self.pool.as_mut_ptr().add(aligned_offset) };
        self.offset = end;
        Ok(ptr)
    }

    fn deallocate(&mut self, _ptr: *mut u8, _size: u32) {
        // Bump allocator doesn't support deallocation
        // This is intentional for deterministic embedded systems
    }

    fn configure_mpu_region(
        &mut self,
        region_id: u8,
        base: *const u8,
        size: u32,
        access: MpuAccess,
    ) -> Result<(), MpuError> {
        // Direct MPU register access for Cortex-M
        #[cfg(target_arch = "arm")]
        unsafe {
            const MPU_RNR: *mut u32 = 0xE000ED98 as *mut u32;   // Region Number Register
            const MPU_RBAR: *mut u32 = 0xE000ED9C as *mut u32;  // Region Base Address
            const MPU_RASR: *mut u32 = 0xE000EDA0 as *mut u32;  // Region Attribute and Size

            // Select region
            core::ptr::write_volatile(MPU_RNR, region_id as u32);

            // Set base address (must be aligned to size)
            core::ptr::write_volatile(MPU_RBAR, base as u32 & 0xFFFFFFE0);

            // Calculate size encoding (log2(size) - 1)
            let size_log2 = 31 - size.leading_zeros();
            let size_field = (size_log2 - 1) & 0x1F;

            // Build RASR: XN=0, AP[2:0]=access, TEX=0, S=1, C=1, B=0, SIZE, ENABLE
            let ap = match access {
                MpuAccess::NoAccess => 0b000,
                MpuAccess::ReadOnly => 0b110,
                MpuAccess::ReadWrite => 0b011,
                MpuAccess::ReadExecute => 0b110,
            };
            let rasr = (ap << 24) | (0b001 << 19) | (size_field << 1) | 1;

            core::ptr::write_volatile(MPU_RASR, rasr);
        }

        self.mpu_enabled = true;
        Ok(())
    }

    fn disable_mpu_region(&mut self, region_id: u8) {
        #[cfg(target_arch = "arm")]
        unsafe {
            const MPU_RNR: *mut u32 = 0xE000ED98 as *mut u32;
            const MPU_RASR: *mut u32 = 0xE000EDA0 as *mut u32;

            core::ptr::write_volatile(MPU_RNR, region_id as u32);
            core::ptr::write_volatile(MPU_RASR, 0); // Disable
        }
    }

    fn available_mpu_regions(&self) -> u8 {
        // Cortex-M4 has 8 regions, M7 has 16
        #[cfg(target_arch = "arm")]
        {
            const MPU_TYPE: *const u32 = 0xE000ED90 as *const u32;
            let mpu_type = unsafe { core::ptr::read_volatile(MPU_TYPE) };
            ((mpu_type >> 8) & 0xFF) as u8
        }
        #[cfg(not(target_arch = "arm"))]
        8 // Default for testing
    }

    fn handle_fault(&mut self, _addr: u32) -> FaultAction {
        FaultAction::Trap(Trap::OutOfBounds)
    }
}
```

### Zephyr Implementation

```rust
// crates/synth-memory/src/platform/zephyr.rs

/// Zephyr RTOS memory platform (uses Memory Domains)
pub struct ZephyrPlatform {
    /// Memory domain for WASM isolation
    domain: *mut z_mem_domain,
    /// Allocated partitions
    partitions: [Option<z_mem_partition>; MAX_MEMORIES],
}

impl ZephyrPlatform {
    pub fn new() -> Self {
        Self {
            domain: core::ptr::null_mut(),
            partitions: [None; MAX_MEMORIES],
        }
    }

    /// Initialize with a Zephyr memory domain
    pub fn init(&mut self, domain: *mut z_mem_domain) {
        self.domain = domain;
    }
}

impl MemoryPlatform for ZephyrPlatform {
    fn allocate(&mut self, size: u32, align: u32) -> Result<*mut u8, AllocError> {
        // Use Zephyr's k_aligned_alloc or static partition
        extern "C" {
            fn k_aligned_alloc(align: usize, size: usize) -> *mut core::ffi::c_void;
        }

        let ptr = unsafe { k_aligned_alloc(align as usize, size as usize) };
        if ptr.is_null() {
            return Err(AllocError::OutOfMemory);
        }
        Ok(ptr as *mut u8)
    }

    fn deallocate(&mut self, ptr: *mut u8, _size: u32) {
        extern "C" {
            fn k_free(ptr: *mut core::ffi::c_void);
        }
        unsafe { k_free(ptr as *mut core::ffi::c_void) };
    }

    fn configure_mpu_region(
        &mut self,
        region_id: u8,
        base: *const u8,
        size: u32,
        access: MpuAccess,
    ) -> Result<(), MpuError> {
        // Create Zephyr memory partition
        let attr = match access {
            MpuAccess::NoAccess => K_MEM_PARTITION_P_NA_U_NA,
            MpuAccess::ReadOnly => K_MEM_PARTITION_P_RO_U_RO,
            MpuAccess::ReadWrite => K_MEM_PARTITION_P_RW_U_RW,
            MpuAccess::ReadExecute => K_MEM_PARTITION_P_RX_U_RX,
        };

        let partition = z_mem_partition {
            start: base as usize,
            size: size as usize,
            attr,
        };

        // Add partition to domain
        extern "C" {
            fn k_mem_domain_add_partition(domain: *mut z_mem_domain, part: *mut z_mem_partition) -> i32;
        }

        self.partitions[region_id as usize] = Some(partition);
        let part_ptr = self.partitions[region_id as usize].as_mut().unwrap();

        let ret = unsafe { k_mem_domain_add_partition(self.domain, part_ptr) };
        if ret != 0 {
            return Err(MpuError::ConfigurationFailed);
        }

        Ok(())
    }

    fn disable_mpu_region(&mut self, region_id: u8) {
        if let Some(partition) = self.partitions[region_id as usize].take() {
            extern "C" {
                fn k_mem_domain_remove_partition(domain: *mut z_mem_domain, part: *mut z_mem_partition) -> i32;
            }

            let mut part = partition;
            unsafe { k_mem_domain_remove_partition(self.domain, &mut part) };
        }
    }

    fn available_mpu_regions(&self) -> u8 {
        // Zephyr manages this through CONFIG_MAX_DOMAIN_PARTITIONS
        #[cfg(feature = "zephyr")]
        {
            extern "C" {
                static CONFIG_MAX_DOMAIN_PARTITIONS: u8;
            }
            unsafe { CONFIG_MAX_DOMAIN_PARTITIONS }
        }
        #[cfg(not(feature = "zephyr"))]
        8
    }

    fn handle_fault(&mut self, _addr: u32) -> FaultAction {
        // Zephyr can handle this via its fault handler
        FaultAction::Trap(Trap::OutOfBounds)
    }
}
```

### FreeRTOS Implementation

```rust
// crates/synth-memory/src/platform/freertos.rs

/// FreeRTOS memory platform (uses MPU directly)
pub struct FreeRtosPlatform {
    /// Task handle for WASM execution
    task_handle: *mut TaskHandle_t,
    /// MPU region assignments
    regions: [bool; 8],
}

impl MemoryPlatform for FreeRtosPlatform {
    fn allocate(&mut self, size: u32, _align: u32) -> Result<*mut u8, AllocError> {
        extern "C" {
            fn pvPortMalloc(size: usize) -> *mut core::ffi::c_void;
        }

        let ptr = unsafe { pvPortMalloc(size as usize) };
        if ptr.is_null() {
            return Err(AllocError::OutOfMemory);
        }
        Ok(ptr as *mut u8)
    }

    fn deallocate(&mut self, ptr: *mut u8, _size: u32) {
        extern "C" {
            fn vPortFree(ptr: *mut core::ffi::c_void);
        }
        unsafe { vPortFree(ptr as *mut core::ffi::c_void) };
    }

    fn configure_mpu_region(
        &mut self,
        region_id: u8,
        base: *const u8,
        size: u32,
        access: MpuAccess,
    ) -> Result<(), MpuError> {
        // FreeRTOS provides vPortStoreTaskMPUSettings
        // We configure MPU directly and associate with task

        // Use FreeRTOS-MPU API if available, otherwise direct access
        #[cfg(feature = "freertos-mpu")]
        {
            extern "C" {
                fn xPortConfigureMPURegion(
                    region: u32,
                    base: u32,
                    size: u32,
                    access: u32,
                ) -> i32;
            }

            let access_bits = match access {
                MpuAccess::NoAccess => 0,
                MpuAccess::ReadOnly => portMPU_REGION_READ_ONLY,
                MpuAccess::ReadWrite => portMPU_REGION_READ_WRITE,
                MpuAccess::ReadExecute => portMPU_REGION_READ_ONLY | portMPU_REGION_EXECUTE,
            };

            let ret = unsafe { xPortConfigureMPURegion(region_id as u32, base as u32, size, access_bits) };
            if ret != pdTRUE {
                return Err(MpuError::ConfigurationFailed);
            }
        }

        self.regions[region_id as usize] = true;
        Ok(())
    }

    fn disable_mpu_region(&mut self, region_id: u8) {
        if self.regions[region_id as usize] {
            // Disable the region
            self.regions[region_id as usize] = false;
        }
    }

    fn available_mpu_regions(&self) -> u8 {
        self.regions.iter().filter(|&&used| !used).count() as u8
    }

    fn handle_fault(&mut self, _addr: u32) -> FaultAction {
        FaultAction::Trap(Trap::OutOfBounds)
    }
}
```

---

## Multi-Memory Code Generation

### Register Allocation for Multi-Memory

```
Memory 0: R11 (dedicated base register - most common)
Memory 1-7: Loaded from memory table on demand
```

### Instruction Selection

```rust
// In instruction_selector.rs

/// Generate load for multi-memory
fn generate_load(&mut self, memory_idx: u32, offset: u32, addr_reg: Reg, dest_reg: Reg) -> Vec<ArmOp> {
    let mut ops = Vec::new();

    match memory_idx {
        0 => {
            // Fast path: use dedicated R11
            ops.push(ArmOp::Ldr {
                rd: dest_reg,
                rn: Reg::R11,
                offset: addr_reg,
            });
        }
        _ => {
            // Slow path: load base from memory table
            // LDR R12, =MEMORY_TABLE
            // LDR R12, [R12, #(memory_idx * 8)]  ; Load base address
            // LDR dest, [R12, addr_reg]          ; Actual load
            ops.push(ArmOp::LoadLiteral {
                rd: Reg::R12,
                label: Label::MemoryTable,
            });
            ops.push(ArmOp::Ldr {
                rd: Reg::R12,
                rn: Reg::R12,
                offset: Reg::Imm((memory_idx * 8) as i32),
            });
            ops.push(ArmOp::Ldr {
                rd: dest_reg,
                rn: Reg::R12,
                offset: addr_reg,
            });
        }
    }

    // Add bounds checking based on strategy
    // (prepended or hardware-based)

    ops
}
```

---

## Multi-Memory Use Cases

### Use Case 1: Isolated Heap + Shared IPC Buffer

```wat
(module
  ;; Private heap for module-internal allocations
  (memory $heap 4)  ;; 256KB

  ;; Shared buffer for inter-module communication
  (memory $ipc 1)   ;; 64KB, exported
  (export "ipc_buffer" (memory $ipc))

  (func (export "allocate") (param $size i32) (result i32)
    ;; Allocate from private heap
    (memory.grow $heap (i32.const 1))
  )

  (func (export "send_message") (param $ptr i32) (param $len i32)
    ;; Copy from heap to IPC buffer
    (memory.copy $ipc $heap
      (i32.const 0)   ;; dst offset in $ipc
      (local.get $ptr) ;; src offset in $heap
      (local.get $len) ;; length
    )
  )
)
```

### Use Case 2: Persistent State + Working Memory

```wat
(module
  ;; Persistent state (survives module reloads)
  (memory $state 1)

  ;; Volatile working memory
  (memory $work 2)

  (func (export "checkpoint")
    ;; Save critical data to persistent memory
    (i32.store $state (i32.const 0)
      (i32.load $work (i32.const 0))
    )
  )
)
```

### Use Case 3: Thread-Local + Shared Memory

```wat
(module
  ;; Thread-local scratch space (no synchronization needed)
  (memory $local 1)

  ;; Shared memory (requires atomics)
  (memory $shared 4 4 shared)

  (func (export "atomic_increment") (result i32)
    ;; Atomic operation on shared memory
    (i32.atomic.rmw.add $shared (i32.const 0) (i32.const 1))
  )
)
```

---

## Memory Layout Strategy

### Per-Module Memory Map

```
For a module with 3 memories (heap=4 pages, ipc=1 page, state=1 page):

0x20000000 ┌─────────────────────┐
           │   Guard (no access) │  4KB
0x20001000 ├─────────────────────┤
           │   Memory 0 (heap)   │  256KB (4 × 64KB pages)
           │                     │
0x20041000 ├─────────────────────┤
           │   Guard (no access) │  4KB
0x20042000 ├─────────────────────┤
           │   Memory 1 (ipc)    │  64KB (1 page)
0x20052000 ├─────────────────────┤
           │   Guard (no access) │  4KB
0x20053000 ├─────────────────────┤
           │   Memory 2 (state)  │  64KB (1 page)
0x20063000 ├─────────────────────┤
           │   Guard (no access) │  4KB
0x20064000 └─────────────────────┘
           │   Stack (grows ↓)   │
0x20080000 └─────────────────────┘  (512KB total RAM example)
```

### MPU Region Allocation

With 8 MPU regions on Cortex-M4:

| Region | Purpose | Access |
|--------|---------|--------|
| 0 | Flash (code) | RX |
| 1 | Stack | RW |
| 2-7 | WASM memories (up to 6) | RW |

For more memories than regions: use software bounds checking for overflow.

---

## Initialization Sequence

```rust
/// Initialize memory for a WASM module
pub fn init_module_memory<P: MemoryPlatform>(
    platform: &mut P,
    memories: &[MemorySpec],
) -> Result<MemoryTable, MemoryError> {
    let mut table = MemoryTable::new();
    let available_mpu = platform.available_mpu_regions();
    let mut mpu_region = 2; // Start after flash and stack

    for (idx, spec) in memories.iter().enumerate() {
        let size = spec.initial_pages * WASM_PAGE_SIZE;
        let max_size = spec.max_pages.unwrap_or(spec.initial_pages) * WASM_PAGE_SIZE;

        // Allocate with guard regions
        let guard_size = 4096; // 4KB guards
        let total_size = size + 2 * guard_size;
        let base = platform.allocate(total_size, size)?; // Align to size for MPU

        // Configure protection
        let protection = if mpu_region < available_mpu && size.is_power_of_two() {
            // Use MPU
            platform.configure_mpu_region(
                mpu_region,
                unsafe { base.add(guard_size as usize) },
                size,
                MpuAccess::ReadWrite,
            )?;

            // Configure guards as no-access
            platform.configure_mpu_region(mpu_region + 1, base, guard_size, MpuAccess::NoAccess)?;

            let prot = ProtectionStrategy::Mpu { region_id: mpu_region };
            mpu_region += 2;
            prot
        } else if size.is_power_of_two() {
            // Use masking
            ProtectionStrategy::Masking
        } else {
            // Fall back to software
            ProtectionStrategy::Software
        };

        table.memories[idx] = MemoryDescriptor {
            base: unsafe { base.add(guard_size as usize) },
            size,
            max_size,
            pages: spec.initial_pages,
            max_pages: spec.max_pages.unwrap_or(spec.initial_pages),
            protection,
            flags: spec.flags,
            platform_data: 0,
        };
        table.count += 1;
    }

    Ok(table)
}
```

---

## References

- [WebAssembly Multi-Memory Proposal](https://github.com/WebAssembly/multi-memory)
- [OmniWasm MPU Sandboxing](http://www.runyupan.com/wp-content/uploads/2024/08/7-pan24owasm.pdf)
- [Zephyr Memory Domains](https://docs.zephyrproject.org/latest/kernel/usermode/memory_domain.html)
- [ARM Cortex-M MPU Guide](https://medium.com/@wadixtech/cortex-m3-mpu-91d8aa9c08e7)
- [FreeRTOS MPU Support](https://www.freertos.org/FreeRTOS-MPU-specific-functions.html)
