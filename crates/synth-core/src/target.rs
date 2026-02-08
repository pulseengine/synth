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

// ============================================================================
// Multi-backend target specification
// ============================================================================

/// Target architecture family (broader than CortexMVariant — spans all ARM + RISC-V)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArchFamily {
    ArmCortexM,
    ArmCortexR,
    ArmCortexA,
    RiscV,
}

/// ISA variant details — determines instruction encoding
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum IsaVariant {
    /// Cortex-M0 (v6-M, Thumb only)
    Thumb,
    /// Cortex-M3/M4/M7 (v7-M, Thumb-2)
    Thumb2,
    /// Cortex-R (v7-R, full ARM + Thumb-2)
    Arm32,
    /// Cortex-A53+ (v8-A)
    AArch64,
    /// RISC-V 32-bit with extension string (e.g. "imac")
    RiscV32 { extensions: String },
    /// RISC-V 64-bit with extension string
    RiscV64 { extensions: String },
}

/// Memory protection model
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum MemProtection {
    /// ARM MPU (Cortex-M, Cortex-R)
    Mpu { regions: u8 },
    /// ARM MMU (Cortex-A)
    Mmu,
    /// RISC-V Physical Memory Protection
    Pmp { entries: u8 },
    /// No hardware protection
    SoftwareOnly,
}

/// Full target specification for multi-backend compilation
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetSpec {
    /// Architecture family
    pub family: ArchFamily,
    /// LLVM-style triple (e.g. "thumbv7em-none-eabihf")
    pub triple: String,
    /// ISA variant details
    pub isa: IsaVariant,
    /// Memory protection model
    pub mem_protection: MemProtection,
}

impl TargetSpec {
    /// Cortex-M4 with 8 MPU regions (most common embedded target)
    pub fn cortex_m4() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7em-none-eabihf".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 8 },
        }
    }

    /// Cortex-M7 with 16 MPU regions
    pub fn cortex_m7() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7em-none-eabihf".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 16 },
        }
    }

    /// Cortex-R5 with 12 MPU regions
    pub fn cortex_r5() -> Self {
        Self {
            family: ArchFamily::ArmCortexR,
            triple: "armv7r-none-eabihf".to_string(),
            isa: IsaVariant::Arm32,
            mem_protection: MemProtection::Mpu { regions: 12 },
        }
    }

    /// Cortex-A53 with MMU
    pub fn cortex_a53() -> Self {
        Self {
            family: ArchFamily::ArmCortexA,
            triple: "aarch64-none-elf".to_string(),
            isa: IsaVariant::AArch64,
            mem_protection: MemProtection::Mmu,
        }
    }

    /// RISC-V RV32IMAC with 16 PMP entries
    pub fn riscv32imac() -> Self {
        Self {
            family: ArchFamily::RiscV,
            triple: "riscv32imac-unknown-none-elf".to_string(),
            isa: IsaVariant::RiscV32 {
                extensions: "imac".to_string(),
            },
            mem_protection: MemProtection::Pmp { entries: 16 },
        }
    }

    /// Parse from an LLVM triple or shorthand name
    pub fn from_triple(triple: &str) -> std::result::Result<Self, String> {
        match triple {
            "thumbv7em-none-eabihf" | "cortex-m4" => Ok(Self::cortex_m4()),
            "cortex-m7" => Ok(Self::cortex_m7()),
            "armv7r-none-eabihf" | "cortex-r5" => Ok(Self::cortex_r5()),
            "aarch64-none-elf" | "cortex-a53" => Ok(Self::cortex_a53()),
            "riscv32imac-unknown-none-elf" | "riscv32imac" => Ok(Self::riscv32imac()),
            _ => Err(format!("unknown target triple: {}", triple)),
        }
    }

    /// Whether this target uses Thumb-2 encoding (Cortex-M)
    pub fn is_thumb2(&self) -> bool {
        self.isa == IsaVariant::Thumb2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_target_spec_from_triple() {
        let spec = TargetSpec::from_triple("cortex-m4").unwrap();
        assert_eq!(spec.family, ArchFamily::ArmCortexM);
        assert!(spec.is_thumb2());
        assert_eq!(spec.mem_protection, MemProtection::Mpu { regions: 8 });
    }

    #[test]
    fn test_target_spec_unknown() {
        assert!(TargetSpec::from_triple("mips-unknown-none").is_err());
    }
}
