//! Static-data addressing validation (VCR-VER-003, synth #777 / #757).
//!
//! The validator itself lives in [`synth_core::static_data_addr`] — it must run
//! on **every** compilation, and the shipping build is `--features riscv`, NOT
//! `verify`, so a check gated on this (optional) crate would stay dormant in
//! exactly the build that shipped #757 four times. It depends on nothing in
//! `synth-verify` (no ordeal, no `term`), so it belongs in `synth-core` where
//! the default compile path reaches it.
//!
//! This module re-exports it so the VCR-VER-003 name resolves under
//! `synth-verify` alongside the other translation-validation passes (it mirrors
//! VCR-VER-002's structure — a verdict enum + a per-compilation gate). See the
//! `synth-core` module for the full invariant and the non-vacuous discrimination
//! tests.

pub use synth_core::static_data_addr::{
    AddrMismatch, DataSegment, ImageMismatch, ImageVerdict, MAX_ACCESS_BYTES, PackedInit,
    RelocResolution, Verdict, image_extent, pack_rom_image, resolve_owner,
    validate_reloc_resolutions, validate_reloc_resolutions_spanned, validate_served_image,
};
