//! Bounds Checking Strategies
//!
//! Provides pluggable bounds checking for memory access safety.

use crate::{MemoryDescriptor, Trap};

/// Bounds checking strategy trait
///
/// Implementors provide different strategies for validating memory accesses.
pub trait BoundsChecker {
    /// Check if address + size is within memory bounds
    ///
    /// Returns the (possibly adjusted) address on success, or a trap on failure.
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap>;

    /// Get the overhead category for this checker
    fn overhead(&self) -> BoundsCheckOverhead;
}

/// Overhead category for bounds checking
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundsCheckOverhead {
    /// No overhead (unsafe or hardware-protected)
    Zero,
    /// Low overhead (~5%, e.g., address masking)
    Low,
    /// Medium overhead (~25%, e.g., software check with branch)
    Medium,
    /// High overhead (~40%, e.g., software check with call)
    High,
}

/// Software bounds checking (portable, ~25-40% overhead)
///
/// Performs an explicit comparison before each memory access.
/// This is the safest portable option.
#[derive(Debug, Clone, Copy, Default)]
pub struct SoftwareBoundsChecker;

impl BoundsChecker for SoftwareBoundsChecker {
    #[inline]
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap> {
        let end = addr.checked_add(size).ok_or(Trap::OutOfBounds)?;
        if end > memory.size {
            return Err(Trap::OutOfBounds);
        }
        Ok(addr)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Medium
    }
}

/// The set of `(func_index, pc)` access sites an external analysis PROVED
/// in-bounds — VCR-MEM-004 / #901, fed by scry's `safe-accesses.json`
/// (schema `scry/safe-accesses/v1`, scry#114).
///
/// `pc` is the 0-based **wasmparser operator index** within the function body,
/// the same index space synth's `op_offsets` side-table and the #494 per-site
/// elision marks are stated in.
///
/// **Absence means "not proven", NEVER "unsafe".** The verdict list is
/// non-exhaustive by contract, so a site this set does not contain must fall
/// back to a real check — see [`ProvenSafeBoundsChecker`]. That makes
/// [`ProvenSafeSites::default()`] (the empty set) the **fail-closed** value:
/// every refusal path — hash mismatch, malformed file, missing file —
/// produces it, and it degrades the whole module to [`SoftwareBoundsChecker`]
/// rather than to no checking.
///
/// Deliberately dep-free (this crate's entire dep list is `bitflags`): the
/// JSON ingestion, `module_sha256` verification and attestation live in
/// `synth_core::proven_safe`, which the compiler driver adapts into this
/// type. Same split as `synth-cli/src/shadow_budget.rs` keeping its decision
/// logic free of `scry_analyze_core` — and here it is forced, since
/// `synth-memory` is `publish = false` while `synth-cli` is published, so a
/// path dep is impossible without changing the published surface.
///
/// Uses `Vec` like the sibling [`codegen`] module does; this crate's
/// `no_std` cfg is aspirational today (`--no-default-features` does not build
/// for that reason, and did not before this type existed).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvenSafeSites {
    /// Sorted, de-duplicated `(func, pc)` pairs. Site counts per module are
    /// small, so a sorted `Vec` + binary search beats a hash set and keeps
    /// the attestation's iteration order deterministic.
    sites: Vec<(u32, u32)>,
}

impl ProvenSafeSites {
    /// The empty (fail-closed) set: nothing proven, everything checked.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record `(func, pc)` as proven in-bounds against the memory's
    /// **guaranteed minimum** size. Wasm memory only grows, so a verdict
    /// proven against the floor stays valid under `memory.grow`.
    pub fn insert(&mut self, func: u32, pc: u32) {
        if let Err(at) = self.sites.binary_search(&(func, pc)) {
            self.sites.insert(at, (func, pc));
        }
    }

    /// Is this exact site proven? The key is the PAIR — the same `pc` in a
    /// different function is a different site and is NOT proven.
    pub fn contains(&self, func: u32, pc: u32) -> bool {
        self.sites.binary_search(&(func, pc)).is_ok()
    }

    /// Number of proven sites.
    pub fn len(&self) -> usize {
        self.sites.len()
    }

    /// True when nothing is proven — the fail-closed state.
    pub fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    /// The proven sites of one function, in `pc` order. This is the per-site
    /// elision-mark vector the instruction selector consumes.
    pub fn pcs_for_func(&self, func: u32) -> Vec<u32> {
        self.sites
            .iter()
            .filter(|&&(f, _)| f == func)
            .map(|&(_, pc)| pc)
            .collect()
    }

    /// Every site, in `(func, pc)` order — the attestation's elision set.
    pub fn iter(&self) -> impl Iterator<Item = (u32, u32)> + '_ {
        self.sites.iter().copied()
    }
}

/// Bounds checking informed by an external proof (VCR-MEM-004 / #901).
///
/// One instance is a decision **for one access site**. A site scry proved
/// in-bounds needs no check at all ([`BoundsCheckOverhead::Zero`] — the whole
/// point: the ~25-40 % software-check tax goes to zero where the access is
/// proven); every other site delegates to [`SoftwareBoundsChecker`] unchanged,
/// because **absence from the verdict list means "not proven", never
/// "unsafe"**.
///
/// Build one with [`ProvenSafeBoundsChecker::for_site`]. The soundness of a
/// `proven` instance rests entirely on the verdicts having been bound to THIS
/// module (`module_sha256`) and to THIS memory floor (`memory_min_bytes`) —
/// both verified before the site set is built, both fail-closed. This type
/// deliberately offers no way to mark a site proven without a
/// [`ProvenSafeSites`] lookup, so a refused ingestion (empty set) can only
/// produce delegating checkers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProvenSafeBoundsChecker {
    /// Was THIS site proven in-bounds? `false` is the safe default.
    proven: bool,
}

impl ProvenSafeBoundsChecker {
    /// The checker for one access site: proven iff `sites` contains it.
    pub fn for_site(sites: &ProvenSafeSites, func: u32, pc: u32) -> Self {
        Self {
            proven: sites.contains(func, pc),
        }
    }

    /// The checker for a site with no verdict — delegates to
    /// [`SoftwareBoundsChecker`]. Also what every refusal path yields.
    pub fn not_proven() -> Self {
        Self { proven: false }
    }

    /// Was this site's check elided on a proof, rather than delegated?
    pub fn is_proven(&self) -> bool {
        self.proven
    }
}

impl Default for ProvenSafeBoundsChecker {
    /// Fail closed: an un-informed checker checks.
    fn default() -> Self {
        Self::not_proven()
    }
}

impl BoundsChecker for ProvenSafeBoundsChecker {
    #[inline]
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap> {
        if self.proven {
            // Proven in-bounds against the memory's guaranteed minimum: there
            // is no check to perform. This is the elision.
            return Ok(addr);
        }
        SoftwareBoundsChecker.check(memory, addr, size)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        if self.proven {
            BoundsCheckOverhead::Zero
        } else {
            SoftwareBoundsChecker.overhead()
        }
    }
}

/// Address masking for power-of-2 memories (~5% overhead)
///
/// Instead of checking bounds, mask the address to always be in range.
/// This only works when memory size is a power of 2.
///
/// **Warning**: This wraps out-of-bounds accesses instead of trapping!
/// Use only when security is less important than performance.
#[derive(Debug, Clone, Copy)]
pub struct MaskingBoundsChecker {
    /// Mask value (size - 1, e.g., 0xFFFF for 64KB)
    pub mask: u32,
}

impl MaskingBoundsChecker {
    /// Create a new masking bounds checker for a given size
    ///
    /// # Panics
    /// Panics if size is not a power of 2
    pub fn new(size: u32) -> Self {
        assert!(
            size.is_power_of_two(),
            "Size must be power of 2 for masking"
        );
        Self { mask: size - 1 }
    }

    /// Try to create a masking bounds checker
    ///
    /// Returns None if size is not a power of 2
    pub fn try_new(size: u32) -> Option<Self> {
        if size.is_power_of_two() {
            Some(Self { mask: size - 1 })
        } else {
            None
        }
    }
}

impl BoundsChecker for MaskingBoundsChecker {
    #[inline]
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        // Masking always "succeeds" by wrapping the address
        Ok(addr & self.mask)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Low
    }
}

/// No bounds checking (unsafe, ~0% overhead)
///
/// **Warning**: This provides no safety! Use only for:
/// - Trusted WASM modules
/// - When MPU provides hardware protection
/// - Performance testing
#[derive(Debug, Clone, Copy, Default)]
pub struct NoBoundsChecker;

impl BoundsChecker for NoBoundsChecker {
    #[inline]
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        Ok(addr)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Zero
    }
}

/// MPU-based bounds checking stub
///
/// The actual MPU configuration happens at memory initialization time.
/// At runtime, we rely on hardware faults for out-of-bounds access.
/// This checker is just a marker that MPU is in use.
#[derive(Debug, Clone, Copy)]
pub struct MpuBoundsChecker {
    /// The MPU region ID protecting this memory
    pub region_id: u8,
}

impl MpuBoundsChecker {
    pub fn new(region_id: u8) -> Self {
        Self { region_id }
    }
}

impl BoundsChecker for MpuBoundsChecker {
    #[inline]
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        // No software check - MPU handles it
        // Out-of-bounds access will trigger HardFault which we convert to trap
        Ok(addr)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Zero
    }
}

/// Code generation helpers for bounds checking
///
/// These functions generate ARM Thumb-2 instruction sequences for inline bounds checking.
pub mod codegen {
    /// Generate software bounds check instructions
    ///
    /// Generates: CMP Raddr, Rsize; BHS trap
    ///
    /// Returns (instructions, size_in_bytes)
    pub fn generate_software_check(
        addr_reg: u8,
        size_reg: u8,
        trap_label: u32,
    ) -> (Vec<u8>, usize) {
        let mut bytes = Vec::with_capacity(8);

        // CMP Raddr, Rsize (Thumb-2: compare registers)
        // Encoding: 0100 0010 10 Rm Rn => 0x4280 | (rm << 3) | rn
        let cmp = 0x4280u16 | ((size_reg as u16) << 3) | (addr_reg as u16);
        bytes.extend_from_slice(&cmp.to_le_bytes());

        // BHS (branch if higher or same, unsigned >=) to trap
        // Thumb-2: 0xD2xx where xx is signed offset/2
        // For now, we'll use a placeholder - actual offset depends on trap handler location
        let bhs = 0xD200u16 | ((trap_label as u16) & 0xFF);
        bytes.extend_from_slice(&bhs.to_le_bytes());

        (bytes, 4)
    }

    /// Generate address masking instruction
    ///
    /// Generates: AND Raddr, Raddr, #mask
    ///
    /// Returns (instructions, size_in_bytes)
    pub fn generate_masking(addr_reg: u8, mask: u32) -> (Vec<u8>, usize) {
        let mut bytes = Vec::with_capacity(4);

        // For masks that fit in Thumb-2 modified immediate:
        // AND Rd, Rn, #imm - Thumb-2 32-bit encoding
        // This is complex; for now, assume mask is loaded in a register

        // Simple version: AND Rd, Rm (Thumb-1)
        // This assumes mask is in a register. For real implementation,
        // we'd need to handle the full Thumb-2 immediate encoding.

        // Placeholder: BIC (bit clear) or AND immediate
        // For 64KB (0xFFFF mask), we can use: UXTH Rd, Rd (zero-extend halfword)
        if mask == 0xFFFF {
            // UXTH Rd, Rm: 1011 0010 10 Rm Rd
            let uxth = 0xB280u16 | ((addr_reg as u16) << 3) | (addr_reg as u16);
            bytes.extend_from_slice(&uxth.to_le_bytes());
            return (bytes, 2);
        }

        // Generic case: need full Thumb-2 AND immediate
        // For now, return empty (caller should use register-based masking)
        (bytes, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_descriptor(size: u32) -> MemoryDescriptor {
        MemoryDescriptor {
            base: core::ptr::null_mut(),
            size,
            max_size: size,
            pages: size / 65536,
            max_pages: size / 65536,
            protection: crate::ProtectionStrategy::Software,
            flags: crate::MemoryFlags::empty(),
            platform_data: 0,
        }
    }

    #[test]
    fn test_software_bounds_checker() {
        let checker = SoftwareBoundsChecker;
        let mem = make_test_descriptor(65536);

        // Valid access
        assert_eq!(checker.check(&mem, 0, 4), Ok(0));
        assert_eq!(checker.check(&mem, 65532, 4), Ok(65532));

        // Invalid access
        assert_eq!(checker.check(&mem, 65533, 4), Err(Trap::OutOfBounds));
        assert_eq!(checker.check(&mem, 65536, 1), Err(Trap::OutOfBounds));

        // Overflow check
        assert_eq!(checker.check(&mem, u32::MAX, 1), Err(Trap::OutOfBounds));
    }

    #[test]
    fn test_masking_bounds_checker() {
        let checker = MaskingBoundsChecker::new(65536);
        let mem = make_test_descriptor(65536);

        // Valid access - returns as-is
        assert_eq!(checker.check(&mem, 0, 4), Ok(0));
        assert_eq!(checker.check(&mem, 65532, 4), Ok(65532));

        // "Invalid" access - wraps around
        assert_eq!(checker.check(&mem, 65536, 4), Ok(0)); // Wraps to 0
        assert_eq!(checker.check(&mem, 65537, 4), Ok(1)); // Wraps to 1
        assert_eq!(checker.check(&mem, 0x20000, 4), Ok(0)); // Wraps to 0
    }

    #[test]
    fn test_masking_checker_requires_power_of_2() {
        assert!(MaskingBoundsChecker::try_new(65536).is_some());
        assert!(MaskingBoundsChecker::try_new(65535).is_none());
        assert!(MaskingBoundsChecker::try_new(100).is_none());
    }

    // ---- VCR-MEM-004 / #901: ProvenSafeBoundsChecker ------------------------

    /// PROPERTY 3 (the key is `(func, pc)`): a proven site is proven, and the
    /// SAME `pc` in a different function is not. A `pc`-only key would silently
    /// elide the wrong function's access.
    #[test]
    fn proven_safe_site_key_is_the_func_pc_pair_901() {
        let mut sites = ProvenSafeSites::new();
        sites.insert(4, 41);
        assert!(sites.contains(4, 41));
        assert!(
            !sites.contains(5, 41),
            "same pc, different func is NOT proven"
        );
        assert!(
            !sites.contains(4, 42),
            "same func, different pc is NOT proven"
        );
        // Insert is idempotent and keeps `(func, pc)` order (the attestation
        // iterates this).
        sites.insert(4, 41);
        sites.insert(0, 7);
        assert_eq!(sites.len(), 2);
        assert_eq!(sites.iter().collect::<Vec<_>>(), vec![(0, 7), (4, 41)]);
        assert_eq!(sites.pcs_for_func(4), vec![41]);
        assert_eq!(sites.pcs_for_func(9), Vec::<u32>::new());
    }

    /// PROPERTY 2 — ABSENCE MEANS "NOT PROVEN", NEVER "UNSAFE". A site missing
    /// from the verdict list must behave EXACTLY like `SoftwareBoundsChecker`
    /// over the whole matrix, including the overflow and boundary cases.
    #[test]
    fn absent_site_is_indistinguishable_from_the_software_checker_901() {
        let mut sites = ProvenSafeSites::new();
        sites.insert(0, 0); // some OTHER site is proven
        let mem = make_test_descriptor(65536);
        let absent = ProvenSafeBoundsChecker::for_site(&sites, 0, 1);
        let sw = SoftwareBoundsChecker;

        for (addr, size) in [
            (0u32, 4u32),
            (65532, 4),
            (65533, 4),
            (65536, 1),
            (u32::MAX, 1),
            (u32::MAX - 3, 4),
            (65535, 1),
        ] {
            assert_eq!(
                absent.check(&mem, addr, size),
                sw.check(&mem, addr, size),
                "absent site diverged from SoftwareBoundsChecker at ({addr}, {size})"
            );
        }
        // ...including the cost it advertises: an unproven site pays the check.
        assert_eq!(absent.overhead(), BoundsCheckOverhead::Medium);
        assert!(!absent.is_proven());
    }

    /// PROPERTY 1 — the FAIL-CLOSED value. Every refusal path (hash mismatch,
    /// malformed file, missing file, `memory_min_bytes` disagreement) produces
    /// the EMPTY site set, and an empty set must degrade the entire module to
    /// `SoftwareBoundsChecker` — never to no checking. Stated at the trait
    /// level here; the end-to-end refusal is gated in
    /// `synth-cli/tests/proven_safe_bounds_901.rs`.
    #[test]
    fn empty_site_set_checks_everything_901() {
        let refused = ProvenSafeSites::new(); // what a refusal yields
        assert!(refused.is_empty());
        let mem = make_test_descriptor(65536);
        let sw = SoftwareBoundsChecker;
        // Sweep a range of sites: not one of them may come back proven.
        for func in 0..4u32 {
            for pc in 0..8u32 {
                let c = ProvenSafeBoundsChecker::for_site(&refused, func, pc);
                assert!(!c.is_proven(), "refused ingestion produced a proven site");
                assert_eq!(c.overhead(), BoundsCheckOverhead::Medium);
                assert_eq!(c.check(&mem, 65536, 4), sw.check(&mem, 65536, 4));
                assert_eq!(c.check(&mem, 0, 4), sw.check(&mem, 0, 4));
            }
        }
        // The Default impl is the same fail-closed decision.
        assert!(!ProvenSafeBoundsChecker::default().is_proven());
        assert_eq!(
            ProvenSafeBoundsChecker::default().check(&mem, 65536, 4),
            Err(Trap::OutOfBounds)
        );
    }

    /// The elision itself: a proven site performs NO check (that is the point)
    /// and advertises `Zero` overhead. The address is returned unchanged even
    /// where the software checker would trap — which is exactly why the
    /// `module_sha256` + `memory_min_bytes` bindings must fail closed.
    #[test]
    fn proven_site_elides_the_check_entirely_901() {
        let mut sites = ProvenSafeSites::new();
        sites.insert(4, 41);
        let mem = make_test_descriptor(65536);
        let proven = ProvenSafeBoundsChecker::for_site(&sites, 4, 41);

        assert!(proven.is_proven());
        assert_eq!(proven.overhead(), BoundsCheckOverhead::Zero);
        assert_eq!(proven.check(&mem, 0, 4), Ok(0));
        assert_eq!(proven.check(&mem, 65532, 4), Ok(65532));
        // No check is performed — the proof, not the checker, is what keeps
        // this in bounds.
        assert_eq!(proven.check(&mem, 65536, 4), Ok(65536));
        assert_eq!(
            SoftwareBoundsChecker.check(&mem, 65536, 4),
            Err(Trap::OutOfBounds)
        );
    }

    #[test]
    fn test_no_bounds_checker() {
        let checker = NoBoundsChecker;
        let mem = make_test_descriptor(65536);

        // Always returns the address unchanged
        assert_eq!(checker.check(&mem, 0, 4), Ok(0));
        assert_eq!(checker.check(&mem, u32::MAX, 1), Ok(u32::MAX));
    }
}
