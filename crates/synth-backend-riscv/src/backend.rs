//! RISC-V `Backend` trait implementation — plumbs the selector + encoder + ELF
//! builder behind the same interface as `synth_backend::ArmBackend`.
//!
//! The skeleton supports a narrow subset of WASM (i32 arithmetic, params,
//! `local.get`/`local.set`). Full feature parity with the ARM backend is the
//! Track B2/B3/B4 deliverable.

use crate::elf_builder::{RiscVElfBuilder, RiscVElfFunction};
use crate::selector::select_simple;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
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

        let mut functions = Vec::new();
        let mut elf_funcs = Vec::new();
        for func in &exports {
            let name = func.export_name.clone().unwrap();
            let compiled = self.compile_function(&name, &func.ops, config)?;
            elf_funcs.push(RiscVElfFunction {
                name: compiled.name.clone(),
                ops: compile_to_riscv_ops(&func.ops, &compiled)?,
            });
            functions.push(compiled);
        }

        let builder = RiscVElfBuilder::new_relocatable();
        let elf = builder
            .build(&elf_funcs)
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

        let num_params = count_params(ops);
        let selection = select_simple(ops, num_params)
            .map_err(|e| BackendError::CompilationFailed(format!("RISC-V selector: {e}")))?;

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
        })
    }

    fn is_available(&self) -> bool {
        true
    }
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
    _compiled: &CompiledFunction,
) -> Result<Vec<crate::riscv_op::RiscVOp>, BackendError> {
    let num_params = count_params(ops);
    let selection = select_simple(ops, num_params)
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
        };
        let rv = compile_to_riscv_ops(&ops, &dummy).unwrap();
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
}
