//! Target architecture specifications

use serde::{Deserialize, Serialize};

/// Target architecture for synthesis
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TargetArch {
    /// ARM Cortex-M series
    ARMCortexM(CortexMVariant),

    /// RISC-V
    RISCV(RISCVVariant),
}

/// ARM Cortex-M variants
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CortexMVariant {
    /// Cortex-M3 (ARMv7-M)
    M3,

    /// Cortex-M4 (ARMv7E-M)
    M4,

    /// Cortex-M4F (with FPU)
    M4F,

    /// Cortex-M7 (ARMv7E-M, high performance)
    M7,

    /// Cortex-M7 with double-precision FPU
    M7DP,

    /// Cortex-M33 (ARMv8-M Mainline with TrustZone)
    M33,

    /// Cortex-M55 (ARMv8.1-M with Helium MVE)
    M55,
}

/// RISC-V variants
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RISCVVariant {
    /// RV32I (32-bit integer)
    RV32I,

    /// RV32IMAC (32-bit with multiply, atomic, compressed)
    RV32IMAC,

    /// RV32GC (32-bit general-purpose with compressed)
    RV32GC,

    /// RV64I (64-bit integer)
    RV64I,

    /// RV64IMAC (64-bit with multiply, atomic, compressed)
    RV64IMAC,

    /// RV64GC (64-bit general-purpose with compressed)
    RV64GC,
}

/// Hardware capabilities
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HardwareCapabilities {
    /// Target architecture
    pub arch: TargetArch,

    /// Has Memory Protection Unit (MPU) for ARM
    pub has_mpu: bool,

    /// Number of MPU regions (typically 8 or 16)
    pub mpu_regions: u8,

    /// Has Physical Memory Protection (PMP) for RISC-V
    pub has_pmp: bool,

    /// Number of PMP entries (up to 16)
    pub pmp_entries: u8,

    /// Has Floating Point Unit
    pub has_fpu: bool,

    /// FPU precision
    pub fpu_precision: Option<FPUPrecision>,

    /// Has SIMD/vector extensions
    pub has_simd: bool,

    /// SIMD level
    pub simd_level: Option<SIMDLevel>,

    /// Can execute-in-place (XIP) from flash
    pub xip_capable: bool,

    /// Flash size in bytes
    pub flash_size: u64,

    /// RAM size in bytes
    pub ram_size: u64,
}

/// FPU precision
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FPUPrecision {
    /// Single precision (32-bit)
    Single,

    /// Double precision (64-bit)
    Double,
}

/// SIMD level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SIMDLevel {
    /// ARM Helium (MVE - M-Profile Vector Extension)
    Helium,

    /// RISC-V Vector Extension
    RISCVVector,

    /// WebAssembly SIMD (128-bit)
    WASMSIMD,
}

impl TargetArch {
    /// Get the target triple string (for compilation)
    pub fn target_triple(&self) -> &str {
        match self {
            TargetArch::ARMCortexM(variant) => match variant {
                CortexMVariant::M3 => "thumbv7m-none-eabi",
                CortexMVariant::M4 | CortexMVariant::M4F => "thumbv7em-none-eabi",
                CortexMVariant::M7 | CortexMVariant::M7DP => "thumbv7em-none-eabihf",
                CortexMVariant::M33 => "thumbv8m.main-none-eabi",
                CortexMVariant::M55 => "thumbv8.1m.main-none-eabi",
            },
            TargetArch::RISCV(variant) => match variant {
                RISCVVariant::RV32I | RISCVVariant::RV32IMAC | RISCVVariant::RV32GC => {
                    "riscv32imac-unknown-none-elf"
                }
                RISCVVariant::RV64I | RISCVVariant::RV64IMAC | RISCVVariant::RV64GC => {
                    "riscv64gc-unknown-none-elf"
                }
            },
        }
    }

    /// Get CPU name for compiler flags
    pub fn cpu_name(&self) -> &str {
        match self {
            TargetArch::ARMCortexM(variant) => match variant {
                CortexMVariant::M3 => "cortex-m3",
                CortexMVariant::M4 | CortexMVariant::M4F => "cortex-m4",
                CortexMVariant::M7 | CortexMVariant::M7DP => "cortex-m7",
                CortexMVariant::M33 => "cortex-m33",
                CortexMVariant::M55 => "cortex-m55",
            },
            TargetArch::RISCV(variant) => match variant {
                RISCVVariant::RV32I => "generic-rv32",
                RISCVVariant::RV32IMAC | RISCVVariant::RV32GC => "generic-rv32",
                RISCVVariant::RV64I => "generic-rv64",
                RISCVVariant::RV64IMAC | RISCVVariant::RV64GC => "generic-rv64",
            },
        }
    }

    /// Check if target has FPU
    pub fn has_hardware_fp(&self) -> bool {
        match self {
            TargetArch::ARMCortexM(variant) => matches!(
                variant,
                CortexMVariant::M4F
                    | CortexMVariant::M7
                    | CortexMVariant::M7DP
                    | CortexMVariant::M55
            ),
            TargetArch::RISCV(variant) => {
                matches!(variant, RISCVVariant::RV32GC | RISCVVariant::RV64GC)
            }
        }
    }
}

impl HardwareCapabilities {
    /// Create capabilities for a typical Cortex-M4F
    pub fn cortex_m4f_typical() -> Self {
        Self {
            arch: TargetArch::ARMCortexM(CortexMVariant::M4F),
            has_mpu: true,
            mpu_regions: 8,
            has_pmp: false,
            pmp_entries: 0,
            has_fpu: true,
            fpu_precision: Some(FPUPrecision::Single),
            has_simd: false,
            simd_level: None,
            xip_capable: true,
            flash_size: 1024 * 1024, // 1MB
            ram_size: 192 * 1024,    // 192KB
        }
    }

    /// Create capabilities for Nordic nRF52840
    pub fn nrf52840() -> Self {
        Self {
            arch: TargetArch::ARMCortexM(CortexMVariant::M4F),
            has_mpu: true,
            mpu_regions: 8,
            has_pmp: false,
            pmp_entries: 0,
            has_fpu: true,
            fpu_precision: Some(FPUPrecision::Single),
            has_simd: false,
            simd_level: None,
            xip_capable: true,
            flash_size: 1024 * 1024, // 1MB
            ram_size: 256 * 1024,    // 256KB
        }
    }

    /// Create capabilities for STM32F407
    pub fn stm32f407() -> Self {
        Self {
            arch: TargetArch::ARMCortexM(CortexMVariant::M4F),
            has_mpu: true,
            mpu_regions: 8,
            has_pmp: false,
            pmp_entries: 0,
            has_fpu: true,
            fpu_precision: Some(FPUPrecision::Single),
            has_simd: false,
            simd_level: None,
            xip_capable: true,
            flash_size: 1024 * 1024, // 1MB
            ram_size: 192 * 1024,    // 192KB (128KB + 64KB CCM)
        }
    }
}
