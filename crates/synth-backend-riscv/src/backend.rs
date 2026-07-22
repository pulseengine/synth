//! RISC-V `Backend` trait implementation — plumbs the selector + encoder + ELF
//! builder behind the same interface as `synth_backend::ArmBackend`.
//!
//! The skeleton supports a narrow subset of WASM (i32 arithmetic, params,
//! `local.get`/`local.set`). Full feature parity with the ARM backend is the
//! Track B2/B3/B4 deliverable.

use crate::elf_builder::{RiscVElfBuilder, RiscVElfFunction};
use crate::selector::{RvBoundsMode, SelectorOptions, select_with_params_i64};
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
    SafetyBounds,
};
use synth_core::target::{ArchFamily, IsaVariant, TargetSpec};
use synth_core::wasm_decoder::DecodedModule;
use synth_core::wasm_op::WasmOp;

pub struct RiscVBackend;

impl RiscVBackend {
    pub fn new() -> Self {
        Self
    }
}

impl Default for RiscVBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for RiscVBackend {
    fn name(&self) -> &str {
        "riscv"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            produces_elf: true,
            supports_rule_verification: false, // not yet — coming with B2 selector port
            supports_binary_verification: true,
            is_external: false,
        }
    }

    fn supported_targets(&self) -> Vec<TargetSpec> {
        vec![TargetSpec::riscv32imac()]
    }

    fn compile_module(
        &self,
        module: &DecodedModule,
        config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        ensure_supported_target(&config.target)?;

        let exports: Vec<_> = module
            .functions
            .iter()
            .filter(|f| f.export_name.is_some())
            .collect();

        if exports.is_empty() {
            return Err(BackendError::CompilationFailed(
                "no exported functions found".into(),
            ));
        }

        // Resolve the bounds-check mode once, using the module's first memory
        // (if any) to populate the size for Software/Mask modes.
        let mem_size = module
            .memories
            .first()
            .map(|m| m.initial_bytes())
            .unwrap_or(0);
        let opts = build_options(config, mem_size)?;

        let mut functions = Vec::new();
        let mut elf_funcs = Vec::new();
        for func in &exports {
            let name = func.export_name.clone().unwrap();
            // #457: THIS function's DECLARED param count (imports-first full
            // index) caps the access-pattern param inference, so a
            // read-before-write local gets a zero-inited frame slot instead of
            // an argument-register home. None when the driver supplied no
            // arg-count table (hand-built modules) — pure inference, as before.
            let declared_params = config.func_arg_counts.get(func.index as usize).copied();
            // Per-function i64/f64 PARAM mask (#518/#312 twin): feeds the
            // selector's honest i64-param loud-decline. Without it an i64 param
            // read by a `pop_any` consumer (e.g. `select`) was silently read as
            // a single i32 register (v0.50 Lane-7 soundness sweep).
            let declared_params_i64 = config.func_params_i64.get(func.index as usize).cloned();
            let func_config = if declared_params.is_some() || declared_params_i64.is_some() {
                Some(CompileConfig {
                    current_func_param_count: declared_params,
                    current_func_params_i64: declared_params_i64.unwrap_or_default(),
                    ..config.clone()
                })
            } else {
                None
            };
            let cfg = func_config.as_ref().unwrap_or(config);
            let compiled = compile_function_with_opts(&name, &func.ops, cfg, opts)?;
            elf_funcs.push(RiscVElfFunction {
                name: compiled.name.clone(),
                ops: compile_to_riscv_ops(&func.ops, cfg, opts, &compiled)?,
            });
            functions.push(compiled);
        }

        // #798: ship the module's active data segments as `.wasm_data` records
        // (declaration order — the startup's record-order copy preserves
        // later-wins), then READ BACK the emitted blob and validate the image
        // it serves against the declared segments. Empty segments ⇒ empty blob
        // ⇒ byte-identical object.
        let segments: Vec<synth_core::static_data_addr::DataSegment> = module
            .data_segments
            .iter()
            .map(|(off, d)| synth_core::static_data_addr::DataSegment {
                linmem_off: *off,
                bytes: d.clone(),
            })
            .collect();
        let wasm_data = synth_core::static_data_addr::pack_segment_records(&segments);
        let served = synth_core::static_data_addr::served_image_from_records(&wasm_data)
            .ok_or_else(|| {
                BackendError::CompilationFailed(
                    "VCR-VER-003 (#798): emitted .wasm_data records failed to parse back \
                     — this is a compiler bug in the record packing"
                        .into(),
                )
            })?;
        if let synth_core::static_data_addr::ImageVerdict::Mismatch(m) =
            synth_core::static_data_addr::validate_served_image(&segments, &served)
        {
            return Err(BackendError::CompilationFailed(format!(
                "VCR-VER-003 (#798): the shipped .wasm_data records serve {} byte(s) that \
                 disagree with the runtime linear-memory image (first: {}) — compiler bug \
                 in the record packing",
                m.len(),
                m[0].describe()
            )));
        }

        let builder = RiscVElfBuilder::new_relocatable();
        let elf = builder
            .build_with_data(&elf_funcs, &wasm_data)
            .map_err(|e| BackendError::CompilationFailed(format!("RISC-V ELF emit: {e}")))?;

        Ok(CompilationResult {
            functions,
            elf: Some(elf),
            backend_name: self.name().to_string(),
        })
    }

    fn compile_function(
        &self,
        name: &str,
        ops: &[WasmOp],
        config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        ensure_supported_target(&config.target)?;
        // No module context — default the memory size to 1 wasm page so that
        // Software/Mask modes can still synthesise the guard. Callers that
        // need a different size go through `compile_module`.
        let opts = build_options(config, 64 * 1024)?;
        compile_function_with_opts(name, ops, config, opts)
    }

    fn is_available(&self) -> bool {
        true
    }
}

/// Build `SelectorOptions` from the `CompileConfig`'s safety knobs.
///
/// Errors out (compile-time) when the user picks `SafetyBounds::Mask` with a
/// non-power-of-two memory size, per the design doc §3.1 path C.
fn build_options(config: &CompileConfig, mem_size: u32) -> Result<SelectorOptions, BackendError> {
    let bounds = match config.effective_safety_bounds() {
        SafetyBounds::None => RvBoundsMode::None,
        SafetyBounds::Mpu => RvBoundsMode::Pmp,
        SafetyBounds::Software => RvBoundsMode::Software { mem_size },
        SafetyBounds::Mask => {
            if mem_size == 0 || !mem_size.is_power_of_two() {
                return Err(BackendError::UnsupportedConfig(format!(
                    "--safety-bounds mask requires a power-of-two linear-memory size, got {} bytes — switch to --safety-bounds software for the deterministic check",
                    mem_size
                )));
            }
            RvBoundsMode::Mask { mask: mem_size - 1 }
        }
    };
    Ok(SelectorOptions {
        bounds,
        signed_div_overflow_trap: true,
    })
}

fn compile_function_with_opts(
    name: &str,
    ops: &[WasmOp],
    config: &CompileConfig,
    opts: SelectorOptions,
) -> Result<CompiledFunction, BackendError> {
    ensure_supported_target(&config.target)?;

    let num_params = effective_num_params(ops, config);
    // #312: pass the decoder's "returns i64" tables down so call-fed i64
    // locals get 8-byte frame slots and i64 call results the a0:a1 pair.
    // Plus the i64/f64 PARAM mask so an i64-param read hits the honest
    // loud-decline instead of a silent i32 misread (v0.50 Lane-7 sweep).
    let selection = select_with_params_i64(
        ops,
        num_params,
        opts,
        &config.func_ret_i64,
        &config.type_ret_i64,
        &config.current_func_params_i64,
    )
    .map_err(|e| BackendError::CompilationFailed(format!("RISC-V selector: {e}")))?;

    // VCR-RA-003 for RISC-V (#815, epic #242): UNCONDITIONAL per-compilation
    // register-allocation validation, the RV32 analogue of the ARM-only
    // `synth_synthesis::liveness::validate_final_allocation`. It proves — by
    // construction, on the EXACT emitted stream — that the allocation preserves
    // the two STRAIGHT-LINE invariants whose reference lives in the stream: (1)
    // callee-saved preservation (a written `s`-register saved+restored by the
    // prologue/epilogue) and (2) spill-slot non-aliasing (no live frame slot
    // overwritten before its reload). Runs on every RV32 compile in the DEFAULT
    // `--features riscv` build (NOT behind `--features verify`; a verify-gated
    // check would be dormant in the build that ships — the #757 / VCR-VER-003
    // lesson) and hard-errors on a VIOLATION. A `NotAttempted` verdict (a `Call`
    // — the ARM phase-2 across-call/across-join frontier, which has no RV CFG
    // machinery yet) is NON-FATAL: the two straight-line invariants still ran and
    // held; only the past-straight-line reasoning is declined (decline > guess).
    // Frozen-safe: it emits nothing, so RV32 `.text` is byte-identical.
    match crate::alloc_validator::validate_final_allocation_rv32(&selection.ops) {
        crate::alloc_validator::RaFinalVerdict::Violation(v) => {
            return Err(BackendError::CompilationFailed(format!(
                "VCR-RA-003 (RV32): register-allocation validation FAILED — {v:?}. \
                 The emitted stream violates a register-allocation invariant \
                 (callee-saved preservation / spill-slot non-aliasing); this is a \
                 compiler bug, not a program error. Refusing to emit a miscompiled \
                 object."
            )));
        }
        crate::alloc_validator::RaFinalVerdict::NotAttempted { reason } => {
            if std::env::var_os("SYNTH_RA003_VERBOSE").is_some() {
                eprintln!(
                    "VCR-RA-003 (RV32): past-straight-line validation NOT ATTEMPTED \
                     ({reason}) — callee-saved / spill-slot invariants held; \
                     across-call/across-join reasoning declined on this shape."
                );
            }
        }
        crate::alloc_validator::RaFinalVerdict::Consistent => {}
    }

    // Encode the function via the ELF builder's per-function pipeline so
    // we benefit from label resolution. We discard the ELF and keep the
    // raw bytes — that's what `CompiledFunction` carries.
    let elf_func = RiscVElfFunction {
        name: name.to_string(),
        ops: selection.ops,
    };
    let bytes = encode_function_bytes(&elf_func)?;

    Ok(CompiledFunction {
        name: name.to_string(),
        code: bytes,
        wasm_ops: ops.to_vec(),
        relocations: Vec::new(),
        // RISC-V DWARF `.debug_line` emission is a VCR-DBG-001 follow-up; no
        // source map produced yet (empty ⇒ the emitter skips this backend).
        line_map: Vec::new(),
        // VCR-DEC-003 (#396): provenance is ARM-only in v1 (empty ⇒ skipped).
        branch_map: Vec::new(),
        // #778: WCET cycle model is ARM(Thumb-2)-only in v1 (RISC-V has no
        // per-op cycle table yet) — no bound emitted for this backend.
        wcet: None,
        wcet_intermediate: None,
    })
}

fn ensure_supported_target(target: &TargetSpec) -> Result<(), BackendError> {
    if !matches!(target.family, ArchFamily::RiscV) {
        return Err(BackendError::UnsupportedConfig(format!(
            "RISC-V backend cannot compile for {:?}",
            target.family
        )));
    }
    if !matches!(
        target.isa,
        IsaVariant::RiscV32 { .. } | IsaVariant::RiscV64 { .. }
    ) {
        return Err(BackendError::UnsupportedConfig(format!(
            "RISC-V backend requires RiscV32/RiscV64 ISA, got {:?}",
            target.isa
        )));
    }
    Ok(())
}

/// Mirrors the ARM backend's parameter inference: walk the wasm and find
/// the highest LocalGet index that is read before being assigned.
fn count_params(wasm_ops: &[WasmOp]) -> u32 {
    let mut first_access: std::collections::HashMap<u32, bool> = std::collections::HashMap::new();
    for op in wasm_ops {
        match op {
            WasmOp::LocalGet(idx) => {
                first_access.entry(*idx).or_insert(true);
            }
            WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx) => {
                first_access.entry(*idx).or_insert(false);
            }
            _ => {}
        }
    }
    first_access
        .iter()
        .filter_map(|(&idx, &is_read_first)| if is_read_first { Some(idx + 1) } else { None })
        .max()
        .unwrap_or(0)
}

/// #457: cap the access-pattern param inference with the DECLARED count when
/// the driver supplied one. A read-before-write non-param local (which WASM
/// zero-initializes) is indistinguishable from a param to `count_params` — it
/// was homed in an argument register and read caller garbage instead of 0.
/// `min` (not a plain override) keeps every function whose inference is <= the
/// declared count byte-identical: the inference can only exceed the declared
/// count via a read-first local index >= it — exactly the read-before-write
/// locals. The selector zero-inits the reclassified locals' frame slots.
fn effective_num_params(ops: &[WasmOp], config: &CompileConfig) -> u32 {
    let inferred = count_params(ops);
    match config.current_func_param_count {
        Some(declared) => inferred.min(declared),
        None => inferred,
    }
}

/// Re-encode the selector's output to flat bytes — the same pipeline the ELF
/// builder uses, but exposed for `compile_function` (which doesn't return ELF).
fn encode_function_bytes(f: &RiscVElfFunction) -> Result<Vec<u8>, BackendError> {
    let builder = RiscVElfBuilder::new_relocatable();
    let elf = builder
        .build(std::slice::from_ref(f))
        .map_err(|e| BackendError::CompilationFailed(format!("RISC-V function emit: {e}")))?;

    // .text starts at offset 52 (ELF header). We need the bytes between header
    // and the next section. The simplest robust path: re-parse our own ELF.
    if elf.len() < 52 {
        return Err(BackendError::CompilationFailed(
            "ELF too small to contain header".into(),
        ));
    }
    // shoff is at bytes [32..36]
    let shoff = u32::from_le_bytes([elf[32], elf[33], elf[34], elf[35]]) as usize;
    // The first section header (after the null one) is .text at shoff + 40.
    // Pull sh_offset and sh_size for index 1.
    let text_shdr = shoff + 40;
    if elf.len() < text_shdr + 40 {
        return Err(BackendError::CompilationFailed(
            "section header table truncated".into(),
        ));
    }
    let sh_offset = u32::from_le_bytes([
        elf[text_shdr + 16],
        elf[text_shdr + 17],
        elf[text_shdr + 18],
        elf[text_shdr + 19],
    ]) as usize;
    let sh_size = u32::from_le_bytes([
        elf[text_shdr + 20],
        elf[text_shdr + 21],
        elf[text_shdr + 22],
        elf[text_shdr + 23],
    ]) as usize;
    Ok(elf[sh_offset..sh_offset + sh_size].to_vec())
}

/// Re-run the selector for a function whose `CompiledFunction` we already have.
/// We don't store the `RiscVOp` sequence in `CompiledFunction` to keep it
/// arch-neutral, so this re-derives it on demand for ELF emission.
fn compile_to_riscv_ops(
    ops: &[WasmOp],
    config: &CompileConfig,
    opts: SelectorOptions,
    _compiled: &CompiledFunction,
) -> Result<Vec<crate::riscv_op::RiscVOp>, BackendError> {
    let num_params = effective_num_params(ops, config);
    let selection = select_with_params_i64(
        ops,
        num_params,
        opts,
        &config.func_ret_i64,
        &config.type_ret_i64,
        &config.current_func_params_i64,
    )
    .map_err(|e| BackendError::CompilationFailed(format!("RISC-V selector: {e}")))?;
    Ok(selection.ops)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::register::Reg;
    use crate::riscv_op::RiscVOp;

    #[test]
    fn backend_name_and_caps() {
        let b = RiscVBackend::new();
        assert_eq!(b.name(), "riscv");
        let caps = b.capabilities();
        assert!(caps.produces_elf);
        assert!(!caps.is_external);
    }

    #[test]
    fn supported_targets_include_riscv32imac() {
        let b = RiscVBackend::new();
        let targets = b.supported_targets();
        assert!(
            targets
                .iter()
                .any(|t| matches!(t.family, ArchFamily::RiscV))
        );
    }

    #[test]
    fn rejects_arm_target() {
        let b = RiscVBackend::new();
        let cfg = CompileConfig {
            target: TargetSpec::cortex_m4f(),
            ..Default::default()
        };
        let r = b.compile_function("test", &[], &cfg);
        assert!(matches!(r, Err(BackendError::UnsupportedConfig(_))));
    }

    #[test]
    fn compiles_simple_add_to_bytes() {
        let b = RiscVBackend::new();
        let cfg = CompileConfig {
            target: TargetSpec::riscv32imac(),
            ..Default::default()
        };
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let f = b.compile_function("add", &ops, &cfg).unwrap();
        assert_eq!(f.name, "add");
        // Should have at least 5 instructions × 4 bytes = 20 bytes
        // (mv t0,a0; mv t1,a1; add t0,t0,t1; mv a0,t0; ret)
        assert!(f.code.len() >= 20, "code was {} bytes", f.code.len());
        // Last 4 bytes are the `jalr zero, 0(ra)` ret = 0x00008067
        let last = &f.code[f.code.len() - 4..];
        assert_eq!(
            u32::from_le_bytes([last[0], last[1], last[2], last[3]]),
            0x00008067
        );
    }

    #[test]
    fn count_params_basic() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(2),
            WasmOp::I32Add,
            WasmOp::I32Add,
        ];
        assert_eq!(count_params(&ops), 3);
    }

    #[test]
    fn count_params_local_set_first_excludes() {
        let ops = vec![
            WasmOp::LocalGet(0), // param
            WasmOp::LocalSet(1), // local var (set first)
            WasmOp::LocalGet(1), // re-read
        ];
        assert_eq!(count_params(&ops), 1);
    }

    /// #457: the declared param count caps the inference — a read-before-write
    /// local (inference: param) is reclassified onto the zero-inited frame
    /// path. `min`, not override: declared >= inferred changes nothing.
    #[test]
    fn effective_num_params_caps_inference_457() {
        let ops = vec![
            WasmOp::LocalGet(0), // param
            WasmOp::LocalGet(1), // read-before-write local → inference says param
            WasmOp::I32Add,
            WasmOp::End,
        ];
        assert_eq!(count_params(&ops), 2);
        let unknown = CompileConfig {
            target: TargetSpec::riscv32imac(),
            ..Default::default()
        };
        assert_eq!(effective_num_params(&ops, &unknown), 2);
        let declared = CompileConfig {
            current_func_param_count: Some(1),
            ..unknown.clone()
        };
        assert_eq!(effective_num_params(&ops, &declared), 1);
        let over_declared = CompileConfig {
            current_func_param_count: Some(4),
            ..unknown.clone()
        };
        assert_eq!(
            effective_num_params(&ops, &over_declared),
            2,
            "declared >= inferred keeps the inference (byte-identity)"
        );
    }

    #[test]
    fn manual_riscv_op_round_trip() {
        // Exercise compile_to_riscv_ops directly.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let dummy = CompiledFunction {
            name: "x".into(),
            code: Vec::new(),
            wasm_ops: ops.clone(),
            relocations: Vec::new(),
            line_map: Vec::new(),
            branch_map: Vec::new(),
            wcet: None,
            wcet_intermediate: None,
        };
        let cfg = CompileConfig {
            target: TargetSpec::riscv32imac(),
            ..Default::default()
        };
        let rv =
            compile_to_riscv_ops(&ops, &cfg, SelectorOptions::wasm_compliant(), &dummy).unwrap();
        // First two ops should move param regs into temporaries (immediate 0).
        assert!(matches!(
            rv[0],
            RiscVOp::Addi {
                rs1: Reg::A0,
                imm: 0,
                ..
            }
        ));
        assert!(matches!(
            rv[1],
            RiscVOp::Addi {
                rs1: Reg::A1,
                imm: 0,
                ..
            }
        ));
        // Third op is the actual ADD (registers vary with allocator policy).
        assert!(matches!(rv[2], RiscVOp::Add { .. }));
        // Final op is the function return.
        assert!(matches!(
            rv.last().unwrap(),
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            }
        ));
    }

    // ─── Phase 1 safety-bounds plumbing ────────────────────────────────

    #[test]
    fn build_options_default_is_none() {
        let cfg = CompileConfig::default();
        let opts = build_options(&cfg, 65536).unwrap();
        assert!(matches!(opts.bounds, RvBoundsMode::None));
        assert!(opts.signed_div_overflow_trap);
    }

    #[test]
    fn build_options_legacy_bounds_check_promotes_to_software() {
        let cfg = CompileConfig {
            bounds_check: true,
            ..Default::default()
        };
        let opts = build_options(&cfg, 65536).unwrap();
        assert!(matches!(
            opts.bounds,
            RvBoundsMode::Software { mem_size: 65536 }
        ));
    }

    #[test]
    fn build_options_safety_bounds_mpu_maps_to_pmp() {
        let cfg = CompileConfig {
            safety_bounds: SafetyBounds::Mpu,
            ..Default::default()
        };
        let opts = build_options(&cfg, 65536).unwrap();
        assert!(matches!(opts.bounds, RvBoundsMode::Pmp));
    }

    #[test]
    fn build_options_mask_requires_power_of_two() {
        let cfg = CompileConfig {
            safety_bounds: SafetyBounds::Mask,
            ..Default::default()
        };
        // 3000 bytes is not a power of two — should error.
        let err = build_options(&cfg, 3000).unwrap_err();
        assert!(matches!(err, BackendError::UnsupportedConfig(_)));

        // 65536 bytes is a power of two — should succeed.
        let opts = build_options(&cfg, 65536).unwrap();
        assert!(matches!(opts.bounds, RvBoundsMode::Mask { mask: 0xFFFF }));
    }

    #[test]
    fn compile_with_software_bounds_emits_bgeu_in_function_bytes() {
        // i32.load + safety-bounds software should produce a 32-bit instruction
        // whose lowest 7 bits == 0b1100011 (BRANCH opcode).
        let b = RiscVBackend::new();
        let cfg = CompileConfig {
            target: TargetSpec::riscv32imac(),
            safety_bounds: SafetyBounds::Software,
            ..Default::default()
        };
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        let f = b.compile_function("ldsafe", &ops, &cfg).unwrap();
        // Look for at least one branch-opcode (0x63) instruction in the bytes.
        let has_branch_opcode = f.code.chunks_exact(4).any(|w| (w[0] & 0x7F) == 0x63);
        assert!(
            has_branch_opcode,
            "expected at least one BRANCH-opcode (0x63) word in: {:?}",
            f.code
        );
    }
}
