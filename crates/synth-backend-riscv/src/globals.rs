//! RQ-63-RVGLOBAL (#242, v0.63) — the RV32 WASM-globals substrate.
//!
//! # What ships, and why this shape
//!
//! Every DEFINED global gets a slot in a synth-EMITTED `.data` image named
//! [`GLOBALS_SYMBOL`] (`__synth_globals`), carrying the global's decoded
//! constant initializer. `global.get`/`global.set` reach a slot through
//! [`crate::riscv_op::RiscVOp::La`] — `lui`+`addi` against the symbol with
//! `R_RISCV_HI20`/`R_RISCV_LO12_I` — followed by an ordinary `lw`/`sw` at the
//! slot's constant offset. The linker places the region; the embedder's
//! standard C-runtime `.data` copy (synth's own `riscv-runtime` startup does
//! it) seeds it at reset.
//!
//! This is the aarch64 design (#851 lane L3) ported, and deliberately NOT the
//! ARM `--relocatable` one (R9 = globals base, embedder-loaded). The two
//! candidate RV32 shapes were weighed against the #275/#717 collision class:
//!
//! * A reserved base register (the R9 port) adds a SECOND ambient input the
//!   embedder must establish beside `s11`, and every existing RV32 harness
//!   would have to learn it. The ARM design exists because a Cortex-M image
//!   has no linker to consult; the RV32 object is ALWAYS host-linked ET_REL,
//!   exactly like aarch64, so a symbol costs two instructions and no register.
//! * The reloc-free "region past linear memory, `s11 + linmem_bytes + off`"
//!   shape (the parity ledger's earlier sketch) puts the globals INSIDE the
//!   address range an out-of-bounds linear-memory access reaches under the
//!   default `--safety-bounds none` envelope — a wasm store to
//!   `linmem_bytes + k` would silently corrupt global `k`. A linker-placed
//!   `.data` region has no such adjacency contract with linear memory.
//!
//! # Layout
//!
//! DENSE, width-summed, in declaration order — the #643 contract the ARM R9
//! table and `WasmGlobal::slot_bytes` already state: 4 bytes for i32/f32, 8
//! for i64/f64, 16 for v128, `global k` at `Σ widths[..k]`. An i64 slot is
//! two word accesses at `off` / `off + 4`; word alignment is all the paired
//! `lw`/`sw` needs, so the region is 4-aligned. (aarch64 chose uniform 8-byte
//! slots for its `ldr x` scaling; nothing outside a backend reads its own
//! region, so the layouts need not agree.)
//!
//! # Single producer
//!
//! [`slot_offsets`] is the ONE layout function: the selector prices a
//! `global.get` at `slot_offsets(&config.global_widths)[k]`, and
//! [`plan_image`] lays the initializer bytes out with the same call over the
//! same declared widths — so what the code addresses and what the object
//! ships cannot disagree (the #682 model↔selector drift class, closed by
//! construction — there is no second copy of the layout for a checker to
//! compare against).
//!
//! # What declines, loudly
//!
//! * an IMPORTED global (`op index < num_imported_globals`) — its value
//!   arrives at instantiation, which a synth-emitted region cannot bind
//!   (aarch64 declines these too); the selector refuses the access;
//! * a defined INTEGER global whose initializer is not a constant (`init:
//!   None` with `float_or_v128 == false`, e.g. `global.get` of an import) —
//!   [`plan_image`] refuses the whole region rather than seed a silently
//!   wrong 0, the #1052 class; float/v128 globals keep their zeroed slot
//!   because every access to them already loud-skips at decode
//!   (GI-FPU-001 / #680), so the dropped initializer is unobservable.

use synth_core::wasm_decoder::{GlobalInit, WasmGlobal};

/// The `.data` symbol naming the base of the emitted globals region.
pub const GLOBALS_SYMBOL: &str = "__synth_globals";

/// Dense byte offset of each defined global (index order), from the declared
/// slot widths. `slot_offsets(&[4, 4, 8, 4])` is `[0, 4, 8, 16]`.
pub fn slot_offsets(widths: &[u32]) -> Vec<u32> {
    let mut off = 0u32;
    widths
        .iter()
        .map(|w| {
            let here = off;
            off += w;
            here
        })
        .collect()
}

/// Total bytes of the region: the sum of the declared widths.
pub fn region_bytes(widths: &[u32]) -> u32 {
    widths.iter().sum()
}

/// Lay out the initializer image for the module's DEFINED globals.
///
/// Returns the empty image for a module with no defined globals (no region,
/// no symbol — byte-identical object). Refuses an integer global with a
/// non-constant initializer: see the module docs.
pub fn plan_image(globals: &[WasmGlobal]) -> Result<Vec<u8>, String> {
    // Defined globals in index order; the decoder pushes them that way, but
    // the layout must not depend on it.
    let mut ordered: Vec<&WasmGlobal> = globals.iter().collect();
    ordered.sort_by_key(|g| g.index);
    for (pos, g) in ordered.iter().enumerate() {
        if g.index as usize != pos {
            // MEASURED on the v0.63 corpus census: 6 components (loom
            // calculator/datetime/hello_rust_host/loom, kiln yolo_inference
            // debug/release) land here — each carries a global section in
            // MORE THAN ONE nested core module, and the decoder flattens
            // them into one list whose per-module indices restart at 0. A
            // `global.get 0` from the second module is then indistinguishable
            // from the first module's; one region cannot serve both. Refuse.
            return Err(format!(
                "global index space is not contiguous (position {pos} holds global {}) \
                 — this input declares globals in more than one nested core module \
                 (a component), whose per-module global indices the decoder flattens \
                 into one list; a single `{GLOBALS_SYMBOL}` region cannot tell them \
                 apart — refusing to lay out the globals region (RQ-63-RVGLOBAL)",
                g.index
            ));
        }
    }
    let widths: Vec<u32> = ordered.iter().map(|g| g.slot_bytes).collect();
    let offsets = slot_offsets(&widths);
    let mut image = vec![0u8; region_bytes(&widths) as usize];
    for (g, &off) in ordered.iter().zip(&offsets) {
        let slot = &mut image[off as usize..(off + g.slot_bytes) as usize];
        match g.init {
            Some(GlobalInit::I32(v)) => {
                let b = v.to_le_bytes();
                let n = b.len().min(slot.len());
                slot[..n].copy_from_slice(&b[..n]);
            }
            Some(GlobalInit::I64(v)) => {
                let b = v.to_le_bytes();
                let n = b.len().min(slot.len());
                slot[..n].copy_from_slice(&b[..n]);
            }
            // GI-FPU-001 (#369) / #680: the initializer is uncaptured AND every
            // access loud-skips at decode, so the zeroed slot is unobservable.
            None if g.float_or_v128 => {}
            None => {
                return Err(format!(
                    "global {} has a non-constant initializer (e.g. `global.get` of an \
                     imported global): its value is not statically known, so the emitted \
                     `{GLOBALS_SYMBOL}` image cannot carry it — refusing rather than seed \
                     a silently-wrong 0 (RQ-63-RVGLOBAL; the #1052 class). RV32 emits the \
                     globals region itself, so `--embedder-global-init` does not apply here.",
                    g.index
                ));
            }
        }
    }
    Ok(image)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn g(index: u32, init: Option<GlobalInit>, slot_bytes: u32, float: bool) -> WasmGlobal {
        WasmGlobal {
            index,
            init,
            mutable: true,
            slot_bytes,
            float_or_v128: float,
        }
    }

    #[test]
    fn dense_width_summed_offsets_643() {
        assert_eq!(slot_offsets(&[4, 4, 8, 4, 8, 4]), vec![0, 4, 8, 16, 20, 28]);
        assert_eq!(region_bytes(&[4, 4, 8, 4, 8, 4]), 32);
        assert!(slot_offsets(&[]).is_empty());
        assert_eq!(region_bytes(&[]), 0);
    }

    /// The fixture `scripts/repro/rv32_globals_1163.wat`: every initializer
    /// lands in ITS slot, both i64 words, sign preserved, zero-init zero.
    #[test]
    fn image_carries_every_initializer_in_its_slot() {
        let globals = vec![
            g(0, Some(GlobalInit::I32(7)), 4, false),
            g(1, Some(GlobalInit::I32(-123456)), 4, false),
            g(2, Some(GlobalInit::I64(0x1122334455667788)), 8, false),
            g(3, Some(GlobalInit::I32(0)), 4, false),
            g(4, Some(GlobalInit::I64(-1)), 8, false),
            g(5, Some(GlobalInit::I32(1024)), 4, false),
        ];
        let img = plan_image(&globals).unwrap();
        assert_eq!(img.len(), 32);
        let w = |off: usize| u32::from_le_bytes(img[off..off + 4].try_into().unwrap());
        assert_eq!(w(0), 7);
        assert_eq!(w(4) as i32, -123456);
        assert_eq!(w(8), 0x55667788, "i64 low word");
        assert_eq!(w(12), 0x11223344, "i64 high word (#649 class)");
        assert_eq!(w(16), 0);
        assert_eq!((w(20), w(24)), (0xFFFF_FFFF, 0xFFFF_FFFF));
        assert_eq!(w(28), 1024);
    }

    #[test]
    fn no_globals_means_no_region() {
        assert!(plan_image(&[]).unwrap().is_empty());
    }

    /// #1052 class: a non-constant INTEGER init is refused by name; a float
    /// global's uncaptured init is a zeroed slot (its access declines upstream).
    #[test]
    fn non_constant_integer_init_refuses_float_zeroes() {
        let err = plan_image(&[g(0, None, 4, false)]).unwrap_err();
        assert!(err.contains("non-constant initializer"), "{err}");
        assert!(err.contains("global 0"), "{err}");
        let img = plan_image(&[
            g(0, None, 8, true),
            g(1, Some(GlobalInit::I32(3)), 4, false),
        ])
        .unwrap();
        assert_eq!(img, vec![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0]);
    }

    #[test]
    fn non_contiguous_index_space_refuses() {
        let err = plan_image(&[g(1, Some(GlobalInit::I32(1)), 4, false)]).unwrap_err();
        assert!(err.contains("not contiguous"), "{err}");
    }
}
