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

    /// Create capabilities for STM32H743 (Cortex-M7 with double-precision FPU)
    ///
    /// 16 MPU regions, 2MB Flash, 1MB RAM (DTCM + AXI SRAM + SRAM1-4).
    pub fn stm32h743() -> Self {
        Self {
            arch: TargetArch::ARMCortexM(CortexMVariant::M7DP),
            has_mpu: true,
            mpu_regions: 16,
            has_pmp: false,
            pmp_entries: 0,
            has_fpu: true,
            fpu_precision: Some(FPUPrecision::Double),
            has_simd: false,
            simd_level: None,
            xip_capable: true,
            flash_size: 2 * 1024 * 1024, // 2MB
            ram_size: 1024 * 1024,       // 1MB total
        }
    }

    /// Create capabilities for i.MX RT1062 (Cortex-M7 with single-precision FPU)
    ///
    /// Representative high-end M7 with 16 MPU regions, single-precision FPU,
    /// large OCRAM, and external XIP-capable QuadSPI Flash. Matches the
    /// configuration of safety-grade lockstepped M7 platforms used in
    /// industrial and embedded automotive contexts.
    pub fn imxrt1062() -> Self {
        Self {
            arch: TargetArch::ARMCortexM(CortexMVariant::M7),
            has_mpu: true,
            mpu_regions: 16,
            has_pmp: false,
            pmp_entries: 0,
            has_fpu: true,
            fpu_precision: Some(FPUPrecision::Single),
            has_simd: false,
            simd_level: None,
            xip_capable: true,
            flash_size: 8 * 1024 * 1024, // 8MB external QSPI flash (typical)
            ram_size: 1024 * 1024,       // 1MB OCRAM (FlexRAM 512KB + OCRAM 512KB)
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
    /// Floating-point unit capability (None = soft-float only)
    pub fpu: Option<FPUPrecision>,
}

// ============================================================================
// ISA feature gating — determines which instructions each variant supports
// ============================================================================

impl CortexMVariant {
    /// Returns whether this variant supports DSP instructions (SSAT, USAT, SMLAL, etc.)
    /// Only ARMv7E-M (Cortex-M4+) and above have DSP extensions.
    pub fn has_dsp(&self) -> bool {
        !matches!(self, Self::M3)
    }

    /// Returns whether this variant has a single-precision FPU
    pub fn has_single_precision_fpu(&self) -> bool {
        matches!(self, Self::M4F | Self::M7 | Self::M7DP | Self::M55)
    }

    /// Returns whether this variant has a double-precision FPU
    pub fn has_double_precision_fpu(&self) -> bool {
        matches!(self, Self::M7DP)
    }

    /// Returns whether this variant supports TrustZone security extensions
    pub fn has_trustzone(&self) -> bool {
        matches!(self, Self::M33 | Self::M55)
    }

    /// Returns whether this variant supports Helium MVE (M-Profile Vector Extension)
    pub fn has_helium(&self) -> bool {
        matches!(self, Self::M55)
    }
}

impl TargetSpec {
    /// Returns whether this target has a single-precision FPU
    pub fn has_single_precision_fpu(&self) -> bool {
        matches!(
            self.fpu,
            Some(FPUPrecision::Single) | Some(FPUPrecision::Double)
        )
    }

    /// Returns whether this target has a double-precision FPU
    pub fn has_double_precision_fpu(&self) -> bool {
        matches!(self.fpu, Some(FPUPrecision::Double))
    }
}

impl TargetSpec {
    /// Cortex-M3 (ARMv7-M, no FPU, 8 MPU regions)
    pub fn cortex_m3() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7m-none-eabi".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 8 },
            fpu: None,
        }
    }

    /// Cortex-M4 with 8 MPU regions (no FPU — M4 without F suffix)
    pub fn cortex_m4() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7em-none-eabi".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 8 },
            fpu: None,
        }
    }

    /// Cortex-M4F with single-precision FPU
    pub fn cortex_m4f() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7em-none-eabihf".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 8 },
            fpu: Some(FPUPrecision::Single),
        }
    }

    /// Cortex-M7 with single-precision FPU and 16 MPU regions
    pub fn cortex_m7() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7em-none-eabihf".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 16 },
            fpu: Some(FPUPrecision::Single),
        }
    }

    /// Cortex-M7 with double-precision FPU and 16 MPU regions
    pub fn cortex_m7dp() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv7em-none-eabihf".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 16 },
            fpu: Some(FPUPrecision::Double),
        }
    }

    /// Cortex-R5 with 12 MPU regions
    pub fn cortex_r5() -> Self {
        Self {
            family: ArchFamily::ArmCortexR,
            triple: "armv7r-none-eabihf".to_string(),
            isa: IsaVariant::Arm32,
            mem_protection: MemProtection::Mpu { regions: 12 },
            fpu: None,
        }
    }

    /// Cortex-A53 with MMU
    pub fn cortex_a53() -> Self {
        Self {
            family: ArchFamily::ArmCortexA,
            triple: "aarch64-none-elf".to_string(),
            isa: IsaVariant::AArch64,
            mem_protection: MemProtection::Mmu,
            fpu: None,
        }
    }

    /// RISC-V RV32IMAC with 16 PMP entries
    /// A bare-metal RV32 profile with the given ISA `extensions` string (e.g.
    /// `"imac"`, `"imc"`, `"im"`, `"i"`, `"gc"`). All RV32 variants share the
    /// PMP memory-protection model and have no hardware FPU in the base profile.
    pub fn riscv32(extensions: &str) -> Self {
        Self {
            family: ArchFamily::RiscV,
            triple: format!("riscv32{extensions}-unknown-none-elf"),
            isa: IsaVariant::RiscV32 {
                extensions: extensions.to_string(),
            },
            mem_protection: MemProtection::Pmp { entries: 16 },
            fpu: None,
        }
    }

    pub fn riscv32imac() -> Self {
        Self::riscv32("imac")
    }

    /// Cortex-M55 with Helium MVE, single-precision FPU, TrustZone
    pub fn cortex_m55() -> Self {
        Self {
            family: ArchFamily::ArmCortexM,
            triple: "thumbv8.1m.main-none-eabi".to_string(),
            isa: IsaVariant::Thumb2,
            mem_protection: MemProtection::Mpu { regions: 16 },
            fpu: Some(FPUPrecision::Single),
        }
    }

    /// Parse from an LLVM triple or shorthand name
    pub fn from_triple(triple: &str) -> std::result::Result<Self, String> {
        match triple {
            "thumbv7m-none-eabi" | "cortex-m3" => Ok(Self::cortex_m3()),
            "thumbv7em-none-eabi" | "cortex-m4" => Ok(Self::cortex_m4()),
            "thumbv7em-none-eabihf" | "cortex-m4f" => Ok(Self::cortex_m4f()),
            "cortex-m7" => Ok(Self::cortex_m7()),
            "cortex-m7dp" => Ok(Self::cortex_m7dp()),
            "thumbv8.1m.main-none-eabi" | "cortex-m55" => Ok(Self::cortex_m55()),
            "armv7r-none-eabihf" | "cortex-r5" => Ok(Self::cortex_r5()),
            "aarch64-none-elf" | "cortex-a53" => Ok(Self::cortex_a53()),
            // RV32 — accept the short ISA names that `riscv-runtime` and the
            // toolchains use (`rv32imac`, …) as well as the long LLVM triples.
            // The ESP32-C3 is RV32IMC (#218).
            "riscv32imac-unknown-none-elf" | "riscv32imac" | "rv32imac" => {
                Ok(Self::riscv32("imac"))
            }
            "riscv32imc" | "rv32imc" | "esp32c3" => Ok(Self::riscv32("imc")),
            "riscv32im" | "rv32im" => Ok(Self::riscv32("im")),
            "riscv32i" | "rv32i" => Ok(Self::riscv32("i")),
            "riscv32gc" | "rv32gc" => Ok(Self::riscv32("gc")),
            // Generic RV32 default → the broadly-supported imac profile.
            "riscv32" | "rv32" => Ok(Self::riscv32("imac")),
            _ => Err(format!(
                "unknown target triple: {triple}. Supported: \
                 cortex-m3, cortex-m4, cortex-m4f, cortex-m7, cortex-m7dp; \
                 rv32imac, rv32imc, rv32im, rv32i, rv32gc, esp32c3"
            )),
        }
    }

    /// Whether this target has a floating-point unit
    pub fn has_fpu(&self) -> bool {
        self.fpu.is_some()
    }

    /// Whether this target uses Thumb-2 encoding (Cortex-M)
    pub fn is_thumb2(&self) -> bool {
        self.isa == IsaVariant::Thumb2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// #218: the short RV32 ISA names (and the ESP32-C3 board alias) that
    /// `riscv-runtime` / the toolchains use must resolve to RISC-V target specs,
    /// not "unknown target triple", so `synth compile -b riscv -t rv32imac` is
    /// reachable.
    #[test]
    fn test_rv32_short_target_names_218() {
        for (name, ext) in [
            ("rv32imac", "imac"),
            ("rv32imc", "imc"),
            ("rv32im", "im"),
            ("rv32i", "i"),
            ("rv32gc", "gc"),
            ("esp32c3", "imc"),  // ESP32-C3 is RV32IMC
            ("riscv32", "imac"), // generic default
            ("riscv32imac", "imac"),
        ] {
            let spec = TargetSpec::from_triple(name)
                .unwrap_or_else(|e| panic!("RV32 target '{name}' must resolve: {e}"));
            assert_eq!(spec.family, ArchFamily::RiscV, "{name}");
            assert_eq!(
                spec.isa,
                IsaVariant::RiscV32 {
                    extensions: ext.to_string()
                },
                "{name}"
            );
        }
        // An unknown triple still errors, and now lists the RV32 options.
        let err = TargetSpec::from_triple("rv99zzz").unwrap_err();
        assert!(
            err.contains("rv32imac"),
            "error should list RV32 targets: {err}"
        );
    }

    #[test]
    fn test_target_spec_from_triple() {
        let spec = TargetSpec::from_triple("cortex-m4").unwrap();
        assert_eq!(spec.family, ArchFamily::ArmCortexM);
        assert!(spec.is_thumb2());
        assert_eq!(spec.mem_protection, MemProtection::Mpu { regions: 8 });
        assert!(!spec.has_fpu());
    }

    #[test]
    fn test_target_spec_unknown() {
        assert!(TargetSpec::from_triple("mips-unknown-none").is_err());
    }

    #[test]
    fn test_cortex_m3() {
        let spec = TargetSpec::from_triple("cortex-m3").unwrap();
        assert_eq!(spec.triple, "thumbv7m-none-eabi");
        assert!(!spec.has_fpu());
    }

    #[test]
    fn test_cortex_m4f() {
        let spec = TargetSpec::from_triple("cortex-m4f").unwrap();
        assert_eq!(spec.triple, "thumbv7em-none-eabihf");
        assert!(spec.has_fpu());
        assert_eq!(spec.fpu, Some(FPUPrecision::Single));
    }

    #[test]
    fn test_cortex_m7dp() {
        let spec = TargetSpec::from_triple("cortex-m7dp").unwrap();
        assert!(spec.has_fpu());
        assert_eq!(spec.fpu, Some(FPUPrecision::Double));
        assert_eq!(spec.mem_protection, MemProtection::Mpu { regions: 16 });
    }

    #[test]
    fn test_cortex_m7_has_fpu() {
        let spec = TargetSpec::cortex_m7();
        assert!(spec.has_fpu());
        assert_eq!(spec.fpu, Some(FPUPrecision::Single));
    }

    // ========================================================================
    // ISA feature gating tests
    // ========================================================================

    #[test]
    fn test_cortex_m3_isa_features() {
        let m3 = CortexMVariant::M3;
        assert!(!m3.has_dsp(), "M3 should not have DSP");
        assert!(!m3.has_single_precision_fpu(), "M3 should not have FPU");
        assert!(
            !m3.has_double_precision_fpu(),
            "M3 should not have double FPU"
        );
        assert!(!m3.has_trustzone(), "M3 should not have TrustZone");
        assert!(!m3.has_helium(), "M3 should not have Helium");
    }

    #[test]
    fn test_cortex_m4_isa_features() {
        let m4 = CortexMVariant::M4;
        assert!(m4.has_dsp(), "M4 should have DSP");
        assert!(
            !m4.has_single_precision_fpu(),
            "M4 (no F) should not have FPU"
        );
        assert!(
            !m4.has_double_precision_fpu(),
            "M4 should not have double FPU"
        );
    }

    #[test]
    fn test_cortex_m4f_isa_features() {
        let m4f = CortexMVariant::M4F;
        assert!(m4f.has_dsp(), "M4F should have DSP");
        assert!(
            m4f.has_single_precision_fpu(),
            "M4F should have single-precision FPU"
        );
        assert!(
            !m4f.has_double_precision_fpu(),
            "M4F should not have double FPU"
        );
    }

    #[test]
    fn test_cortex_m7dp_isa_features() {
        let m7dp = CortexMVariant::M7DP;
        assert!(m7dp.has_dsp(), "M7DP should have DSP");
        assert!(
            m7dp.has_single_precision_fpu(),
            "M7DP should have single-precision FPU"
        );
        assert!(
            m7dp.has_double_precision_fpu(),
            "M7DP should have double-precision FPU"
        );
    }

    #[test]
    fn test_cortex_m33_isa_features() {
        let m33 = CortexMVariant::M33;
        assert!(m33.has_dsp(), "M33 should have DSP");
        assert!(m33.has_trustzone(), "M33 should have TrustZone");
        assert!(!m33.has_helium(), "M33 should not have Helium");
    }

    #[test]
    fn test_cortex_m55_isa_features() {
        let m55 = CortexMVariant::M55;
        assert!(m55.has_dsp(), "M55 should have DSP");
        assert!(
            m55.has_single_precision_fpu(),
            "M55 should have single-precision FPU"
        );
        assert!(m55.has_trustzone(), "M55 should have TrustZone");
        assert!(m55.has_helium(), "M55 should have Helium");
    }

    #[test]
    fn test_target_spec_fpu_precision_queries() {
        let m3 = TargetSpec::cortex_m3();
        assert!(!m3.has_single_precision_fpu(), "M3 spec has no FPU");
        assert!(!m3.has_double_precision_fpu(), "M3 spec has no double FPU");

        let m4f = TargetSpec::cortex_m4f();
        assert!(m4f.has_single_precision_fpu(), "M4F spec has single FPU");
        assert!(
            !m4f.has_double_precision_fpu(),
            "M4F spec has no double FPU"
        );

        let m7dp = TargetSpec::cortex_m7dp();
        assert!(m7dp.has_single_precision_fpu(), "M7DP spec has single FPU");
        assert!(m7dp.has_double_precision_fpu(), "M7DP spec has double FPU");
    }

    #[test]
    fn test_cortex_m55_target_spec() {
        let m55 = TargetSpec::cortex_m55();
        assert_eq!(m55.family, ArchFamily::ArmCortexM);
        assert_eq!(m55.triple, "thumbv8.1m.main-none-eabi");
        assert!(m55.is_thumb2());
        assert!(m55.has_fpu());
        assert!(m55.has_single_precision_fpu());
        assert_eq!(m55.mem_protection, MemProtection::Mpu { regions: 16 });
    }

    #[test]
    fn test_cortex_m55_from_triple() {
        let m55 = TargetSpec::from_triple("cortex-m55").unwrap();
        assert_eq!(m55.triple, "thumbv8.1m.main-none-eabi");
        assert!(m55.has_fpu());

        let m55_triple = TargetSpec::from_triple("thumbv8.1m.main-none-eabi").unwrap();
        assert_eq!(m55_triple.triple, "thumbv8.1m.main-none-eabi");
    }

    // ========================================================================
    // M7 hardware constructor tests (PR #86 patch coverage)
    // ========================================================================

    #[test]
    fn test_imxrt1062_capabilities() {
        let caps = HardwareCapabilities::imxrt1062();
        assert_eq!(caps.arch, TargetArch::ARMCortexM(CortexMVariant::M7));
        assert!(caps.has_mpu, "i.MX RT1062 has an MPU");
        assert_eq!(caps.mpu_regions, 16, "M7 parts have 16 MPU regions");
        assert!(!caps.has_pmp, "ARM parts do not have PMP");
        assert_eq!(caps.pmp_entries, 0);
        assert!(caps.has_fpu, "i.MX RT1062 has FPU");
        assert_eq!(
            caps.fpu_precision,
            Some(FPUPrecision::Single),
            "i.MX RT1062 has single-precision FPU"
        );
        assert!(!caps.has_simd);
        assert!(caps.simd_level.is_none());
        assert!(caps.xip_capable);
        assert_eq!(caps.flash_size, 8 * 1024 * 1024, "8MB QSPI typical");
        assert_eq!(caps.ram_size, 1024 * 1024, "1MB OCRAM");
    }

    #[test]
    fn test_stm32h743_capabilities() {
        let caps = HardwareCapabilities::stm32h743();
        assert_eq!(caps.arch, TargetArch::ARMCortexM(CortexMVariant::M7DP));
        assert!(caps.has_mpu);
        assert_eq!(caps.mpu_regions, 16, "STM32H743 has 16 MPU regions");
        assert!(!caps.has_pmp);
        assert!(caps.has_fpu);
        assert_eq!(
            caps.fpu_precision,
            Some(FPUPrecision::Double),
            "STM32H743 has double-precision FPU"
        );
        assert_eq!(caps.flash_size, 2 * 1024 * 1024, "2MB Flash");
        assert_eq!(caps.ram_size, 1024 * 1024, "1MB RAM total");
        assert!(caps.xip_capable);
    }

    #[test]
    fn test_imxrt1062_arch_target_triple() {
        // imxrt1062 uses the M7 variant, which maps to thumbv7em-none-eabihf.
        let caps = HardwareCapabilities::imxrt1062();
        assert_eq!(caps.arch.target_triple(), "thumbv7em-none-eabihf");
        assert_eq!(caps.arch.cpu_name(), "cortex-m7");
        assert!(caps.arch.has_hardware_fp());
    }

    #[test]
    fn test_stm32h743_arch_target_triple() {
        // stm32h743 uses M7DP — same triple as M7 but flagged as double-precision.
        let caps = HardwareCapabilities::stm32h743();
        assert_eq!(caps.arch.target_triple(), "thumbv7em-none-eabihf");
        assert_eq!(caps.arch.cpu_name(), "cortex-m7");
        assert!(caps.arch.has_hardware_fp());
    }

    #[test]
    fn test_m7_hardware_capabilities_distinct_from_m4() {
        // Regression: M7 hardware must report 16 regions, M4 must report 8.
        // Previously the CLI's --hardware dispatch silently fell through to
        // a wrong default — this guards the constructor selection.
        let m4 = HardwareCapabilities::nrf52840();
        let m7 = HardwareCapabilities::imxrt1062();
        let m7dp = HardwareCapabilities::stm32h743();
        assert_eq!(m4.mpu_regions, 8);
        assert_eq!(m7.mpu_regions, 16);
        assert_eq!(m7dp.mpu_regions, 16);
        // M7DP must report Double, M7 must report Single, M4F must report Single.
        assert_eq!(m4.fpu_precision, Some(FPUPrecision::Single));
        assert_eq!(m7.fpu_precision, Some(FPUPrecision::Single));
        assert_eq!(m7dp.fpu_precision, Some(FPUPrecision::Double));
    }
}
