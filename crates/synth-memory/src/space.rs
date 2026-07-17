//! Platform space-consistency model (#77 — RAJA/Kokkos execution-space +
//! memory-space pattern).
//!
//! LLNL RAJA and Sandia Kokkos model *where code runs* (execution space) and
//! *where data lives* (memory space) as first-class concepts. Synth today
//! chooses a target's memory layout by informal convention (linker scripts +
//! `synth-memory` descriptors). This module gives ONE concrete slice of that
//! choice a *checked* property instead of a convention: the selected
//! execution space and the memory spaces it is asked to use must be mutually
//! consistent, and an inconsistent pairing is REJECTED (red-first) rather than
//! silently miscompiled.
//!
//! ## Scope (deliberately bounded, #77)
//!
//! This is NOT the full three-layer Platform Package from the issue. It
//! formalizes exactly two consistency invariants — the ones that turn a
//! "wrong config" from a runtime mystery into a compile-time `Err`:
//!
//! 1. **OS-mapping consistency.** A bare-metal execution space (no operating
//!    system underneath) cannot be paired with a memory space whose backing is
//!    an OS/host mapping (e.g. an `mmap`-backed Linux region). Conversely a
//!    hosted execution space cannot claim a physical on-chip space (Flash / TCM)
//!    that only exists on real silicon. This is the issue's own worked example
//!    ("a bare-metal target cannot request a Linux-only space").
//!
//! 2. **FPU-capability consistency.** A memory space may declare that it holds
//!    floating-point working data that requires hardware FP (a `RequiresFpu`
//!    flag). An execution space with `Fpu::None` cannot host such a space —
//!    the core has no FP unit to touch it.
//!
//! Geometry (linmem base vs globals region overlap, static-data addressing) is
//! deliberately OUT of scope here — that lives in `synth_core::static_data_addr`
//! (VCR-VER-003). This module owns only the *space-kind* consistency relation.
//!
//! The invariant is machine-checked by [`PlatformSpaces::validate`] and its
//! unit tests: a violating configuration returns [`SpaceError`], a consistent
//! one returns `Ok(())`.

#![allow(clippy::result_unit_err)]

/// Where compiled code executes — the *execution space* (Kokkos terminology).
///
/// The distinction that matters for consistency is whether an operating system
/// sits underneath (a hosted process) or whether this is bare silicon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionSpace {
    /// Bare-metal ARM Cortex-M core — no OS, physical memory map, MPU-based
    /// isolation. This is synth's primary deployment shape (i.MX RT1062,
    /// STM32H743, NUCLEO boards, qemu bare-metal).
    BareMetal {
        /// Which Cortex-M variant — gates FP and SIMD capability.
        core: CortexM,
    },
    /// Hosted process on an OS (Linux/desktop). Memory is virtual, spaces are
    /// OS mappings. This is the desktop test / `HostPlatform` shape.
    Hosted,
}

/// Cortex-M core variant — the capability axis relevant to space consistency
/// is the FPU. (SIMD/MPU are modeled elsewhere; this enum carries only what
/// the two invariants need.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CortexM {
    /// Cortex-M0 / M0+ — integer only, no FPU.
    M0,
    /// Cortex-M4F — single-precision FPv4 FPU.
    M4F,
    /// Cortex-M33 — single-precision FPU (FPv5), TrustZone.
    M33,
    /// Cortex-M55 — Helium (MVE) + double-precision FPU.
    M55,
}

impl CortexM {
    /// The FPU capability this core provides.
    pub const fn fpu(self) -> Fpu {
        match self {
            CortexM::M0 => Fpu::None,
            CortexM::M4F | CortexM::M33 => Fpu::Single,
            CortexM::M55 => Fpu::Double,
        }
    }
}

impl ExecutionSpace {
    /// Whether an operating system sits underneath this execution space.
    pub const fn is_os_hosted(self) -> bool {
        matches!(self, ExecutionSpace::Hosted)
    }

    /// The FPU capability available to code in this execution space. A hosted
    /// process is assumed to have hardware FP (host CPU); a bare-metal core's
    /// capability is dictated by its Cortex-M variant.
    pub const fn fpu(self) -> Fpu {
        match self {
            ExecutionSpace::BareMetal { core } => core.fpu(),
            ExecutionSpace::Hosted => Fpu::Double,
        }
    }
}

/// Hardware floating-point capability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fpu {
    /// No hardware FPU (integer-only core — soft-float only).
    None,
    /// Single-precision hardware FPU (FPv4/FPv5-SP).
    Single,
    /// Double-precision hardware FPU.
    Double,
}

/// The physical/logical backing of a memory space — this is the axis the
/// OS-mapping invariant checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryBacking {
    /// On-chip Flash / ROM — read-only at runtime, exists only on real
    /// silicon (or a bare-metal emulator). Physical.
    Flash,
    /// On-chip SRAM — read-write, physical.
    Sram,
    /// Tightly-Coupled Memory — fastest on-chip, physical.
    Tcm,
    /// External RAM (e.g. SDRAM over FMC) — physical, off-chip.
    ExternalRam,
    /// An OS/host mapping (e.g. `mmap`-backed region on Linux). Only exists
    /// under a hosted execution space.
    OsMapped,
}

impl MemoryBacking {
    /// Whether this backing is a physical on-silicon region (as opposed to an
    /// OS/host virtual mapping).
    pub const fn is_physical(self) -> bool {
        !matches!(self, MemoryBacking::OsMapped)
    }
}

/// A memory space: where a class of data lives (Kokkos terminology).
///
/// Only the fields the two consistency invariants need are modeled — the full
/// `{ base, size, latency, writeable }` descriptor from #77 is future work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemorySpace {
    /// A short stable identifier for diagnostics (e.g. "flash", "sram1",
    /// "extram", "host-heap").
    pub name: &'static str,
    /// The physical/logical backing — checked against the execution space.
    pub backing: MemoryBacking,
    /// Whether data placed in this space requires hardware floating-point to
    /// operate on (FP working set). Checked against the core's FPU.
    pub requires_fpu: bool,
}

impl MemorySpace {
    /// A physical on-chip space with no FP requirement.
    pub const fn physical(name: &'static str, backing: MemoryBacking) -> Self {
        Self {
            name,
            backing,
            requires_fpu: false,
        }
    }

    /// An OS-mapped (hosted) space with no FP requirement.
    pub const fn os_mapped(name: &'static str) -> Self {
        Self {
            name,
            backing: MemoryBacking::OsMapped,
            requires_fpu: false,
        }
    }

    /// Mark this space as holding an FP working set (requires hardware FPU).
    pub const fn with_fpu(mut self) -> Self {
        self.requires_fpu = true;
        self
    }
}

/// A rejected platform configuration — the machine reason the pairing is
/// inconsistent. Every variant names the offending space so the diagnostic is
/// actionable (#77 red-first).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpaceError {
    /// A bare-metal execution space was paired with an OS-mapped memory space.
    /// Bare metal has no OS to provide the mapping.
    BareMetalCannotUseOsSpace {
        /// Name of the offending OS-mapped space.
        space: &'static str,
    },
    /// A hosted execution space was paired with a physical on-silicon space
    /// (Flash/TCM/ExternalRam) that only exists on real hardware.
    HostedCannotUsePhysicalSpace {
        /// Name of the offending physical space.
        space: &'static str,
        /// The physical backing that is unavailable in a hosted process.
        backing: MemoryBacking,
    },
    /// A memory space requires hardware floating-point but the execution
    /// space's core has no FPU.
    FpuRequiredButAbsent {
        /// Name of the space that requires FP.
        space: &'static str,
    },
}

impl core::fmt::Display for SpaceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SpaceError::BareMetalCannotUseOsSpace { space } => write!(
                f,
                "#77 space-consistency: bare-metal execution space cannot use \
                 OS-mapped memory space '{space}' (no operating system provides \
                 the mapping on bare metal)"
            ),
            SpaceError::HostedCannotUsePhysicalSpace { space, backing } => write!(
                f,
                "#77 space-consistency: hosted execution space cannot use \
                 physical on-silicon memory space '{space}' (backing {backing:?} \
                 only exists on real hardware / a bare-metal emulator)"
            ),
            SpaceError::FpuRequiredButAbsent { space } => write!(
                f,
                "#77 space-consistency: memory space '{space}' requires hardware \
                 floating-point, but the execution space's core has no FPU"
            ),
        }
    }
}

/// A platform's selected execution space plus the memory spaces it will use.
///
/// [`validate`](PlatformSpaces::validate) is the checked invariant: it holds
/// (`Ok`) iff every memory space is consistent with the execution space.
#[derive(Debug, Clone)]
pub struct PlatformSpaces {
    /// Where code runs.
    pub execution: ExecutionSpace,
    /// Where data lives.
    pub memories: Vec<MemorySpace>,
}

impl PlatformSpaces {
    /// Construct a platform-spaces configuration.
    pub fn new(execution: ExecutionSpace, memories: Vec<MemorySpace>) -> Self {
        Self {
            execution,
            memories,
        }
    }

    /// The checked consistency invariant (#77).
    ///
    /// Returns `Ok(())` iff every memory space is consistent with the selected
    /// execution space under both invariants:
    ///
    /// 1. OS-mapping: bare metal ⇏ OS-mapped space; hosted ⇏ physical space.
    /// 2. FPU: an `Fpu::None` core cannot host an FP-requiring space.
    ///
    /// The FIRST inconsistent space (in declaration order) is reported so the
    /// diagnostic is deterministic.
    pub fn validate(&self) -> Result<(), SpaceError> {
        let os_hosted = self.execution.is_os_hosted();
        let fpu = self.execution.fpu();
        for m in &self.memories {
            // Invariant 1: OS-mapping consistency.
            if os_hosted {
                if m.backing.is_physical() {
                    return Err(SpaceError::HostedCannotUsePhysicalSpace {
                        space: m.name,
                        backing: m.backing,
                    });
                }
            } else if m.backing == MemoryBacking::OsMapped {
                return Err(SpaceError::BareMetalCannotUseOsSpace { space: m.name });
            }
            // Invariant 2: FPU-capability consistency.
            if m.requires_fpu && fpu == Fpu::None {
                return Err(SpaceError::FpuRequiredButAbsent { space: m.name });
            }
        }
        Ok(())
    }

    /// Convenience: `true` iff [`validate`](Self::validate) holds.
    pub fn is_consistent(&self) -> bool {
        self.validate().is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Cover target: STM32H743 (Cortex-M4F-class, on-chip Flash + SRAM + TCM).
    /// A well-formed bare-metal config is consistent.
    #[test]
    fn baremetal_physical_spaces_are_consistent() {
        let p = PlatformSpaces::new(
            ExecutionSpace::BareMetal { core: CortexM::M4F },
            vec![
                MemorySpace::physical("flash", MemoryBacking::Flash),
                MemorySpace::physical("sram1", MemoryBacking::Sram),
                MemorySpace::physical("dtcm", MemoryBacking::Tcm),
            ],
        );
        assert_eq!(p.validate(), Ok(()));
        assert!(p.is_consistent());
    }

    /// RED-FIRST (#77 invariant 1): a bare-metal core asking for an OS-mapped
    /// (Linux-only) space is REJECTED with the offending space named.
    #[test]
    fn baremetal_rejects_os_mapped_space() {
        let p = PlatformSpaces::new(
            ExecutionSpace::BareMetal { core: CortexM::M4F },
            vec![
                MemorySpace::physical("flash", MemoryBacking::Flash),
                MemorySpace::os_mapped("host-heap"),
            ],
        );
        assert_eq!(
            p.validate(),
            Err(SpaceError::BareMetalCannotUseOsSpace { space: "host-heap" })
        );
        assert!(!p.is_consistent());
        // Diagnostic is actionable (names the space).
        assert!(p.validate().unwrap_err().to_string().contains("host-heap"));
    }

    /// RED-FIRST (#77 invariant 1, other direction): a hosted process cannot
    /// claim a physical on-silicon space.
    #[test]
    fn hosted_rejects_physical_space() {
        let p = PlatformSpaces::new(
            ExecutionSpace::Hosted,
            vec![MemorySpace::physical("dtcm", MemoryBacking::Tcm)],
        );
        assert_eq!(
            p.validate(),
            Err(SpaceError::HostedCannotUsePhysicalSpace {
                space: "dtcm",
                backing: MemoryBacking::Tcm,
            })
        );
    }

    /// A hosted process with OS-mapped spaces is consistent.
    #[test]
    fn hosted_os_mapped_is_consistent() {
        let p = PlatformSpaces::new(
            ExecutionSpace::Hosted,
            vec![MemorySpace::os_mapped("host-heap")],
        );
        assert_eq!(p.validate(), Ok(()));
    }

    /// RED-FIRST (#77 invariant 2): an FP-requiring space on an FPU-less core
    /// (Cortex-M0) is REJECTED.
    #[test]
    fn fpu_required_but_core_has_none_is_rejected() {
        let p = PlatformSpaces::new(
            ExecutionSpace::BareMetal { core: CortexM::M0 },
            vec![MemorySpace::physical("sram1", MemoryBacking::Sram).with_fpu()],
        );
        assert_eq!(
            p.validate(),
            Err(SpaceError::FpuRequiredButAbsent { space: "sram1" })
        );
    }

    /// The same FP-requiring space on an M4F core (which has an FPU) IS
    /// consistent — the invariant is not vacuous in either direction.
    #[test]
    fn fpu_required_on_fpu_core_is_consistent() {
        let p = PlatformSpaces::new(
            ExecutionSpace::BareMetal { core: CortexM::M4F },
            vec![MemorySpace::physical("sram1", MemoryBacking::Sram).with_fpu()],
        );
        assert_eq!(p.validate(), Ok(()));
        assert_eq!(CortexM::M4F.fpu(), Fpu::Single);
        assert_eq!(CortexM::M0.fpu(), Fpu::None);
    }

    /// Determinism: the FIRST inconsistent space (declaration order) is the
    /// one reported.
    #[test]
    fn first_violation_is_reported() {
        let p = PlatformSpaces::new(
            ExecutionSpace::BareMetal { core: CortexM::M0 },
            vec![
                MemorySpace::os_mapped("first-bad"),
                MemorySpace::physical("sram1", MemoryBacking::Sram).with_fpu(),
            ],
        );
        assert_eq!(
            p.validate(),
            Err(SpaceError::BareMetalCannotUseOsSpace { space: "first-bad" })
        );
    }
}
