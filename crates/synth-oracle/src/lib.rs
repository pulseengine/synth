//! synth-oracle — the execution-oracle harness, in Rust.
//!
//! An oracle here runs one wasm export TWICE: on the reference interpreter
//! (kiln, [`reference`]) and as the machine code synth emitted for it, under
//! unicorn ([`emulate`]). [`compare`] turns the pair of outcomes into a
//! verdict. [`synth`] drives the compiler and reads function bytes from the
//! ELF symbol table.
//!
//! TEST INFRASTRUCTURE ONLY: `publish = false`, and never a dependency of
//! `synth-cli` or of any crate that ships. The engines are behind the `exec`
//! feature, so the default workspace build compiles only the value model,
//! the comparison matrix and the ELF driver.
//!
//! WHAT IS COMPARED by `run_case`: return values and trap-versus-return,
//! nothing else. Memory effects are not compared there, so it refuses a
//! module with a linear memory; the emulator refuses float signatures (on every core but
//! AArch64, where the AAPCS64 V-register convention is set up), calls and
//! multi-value results (see `emulate`).
//!
//! HOSTED objects (`hosted`, `run_hosted`): a module with function imports is
//! an `ET_REL` object the embedder links. `run_hosted` links it against host
//! stubs, maps linear memory where the test says, and runs a SEQUENCE of
//! calls on one image and on one kiln instance. There the comparison also
//! covers every host call (module, field, arguments, results, in order), and
//! memory effects are compared through what later calls in the sequence read.
//!
//! `run_case_env` (Refs #1254, #1724) (RV32) ALSO compares memory and calls: linear memory 0 is
//! mapped from the module's own initial image and compared BYTE FOR BYTE
//! after the call, and imported functions run as host stubs whose call trace
//! (name, arguments, results, order) must equal kiln's.

pub mod armv6m;
pub mod compare;
pub mod cycles;
pub mod probes;
pub mod record;
pub mod rv32_isa;
pub mod synth;
pub mod value;

#[cfg(feature = "exec")]
pub mod emulate;
#[cfg(feature = "exec")]
pub mod hosted;
#[cfg(feature = "exec")]
pub mod image;
#[cfg(feature = "exec")]
pub mod reference;

#[cfg(feature = "exec")]
pub use run_case::{
    Case, CaseError, HostedCase, env_for, run_case, run_case_env, run_hosted, run_sequence_env,
};

#[cfg(feature = "exec")]
mod run_case {
    use crate::compare::{EmuOutcome, RefOutcome, Verdict, verdict};
    use crate::emulate::{self, EmuConfig, EmuEnv, EmuError};
    use crate::reference::{self, HostCall, Imports, RefError};
    use crate::synth::CompiledObject;
    use crate::value::{
        FuncImport, WasmValue, export_signature, function_imports, has_linear_memory, memory_image,
    };

    /// One executed comparison.
    #[derive(Clone, Debug)]
    pub struct Case {
        pub export: String,
        pub args: Vec<WasmValue>,
        pub reference: RefOutcome,
        pub host_calls: Vec<HostCall>,
        pub emulator: EmuOutcome,
        pub verdict: Verdict,
    }

    #[derive(Clone, Debug)]
    pub enum CaseError {
        Signature(String),
        /// The module has a linear memory. Memory effects are not compared
        /// and no memory is mapped for the emulator, so it is refused rather
        /// than judged on return values alone.
        LinearMemory,
        Reference(RefError),
        Emulator(EmuError),
    }

    /// Run `export(args)` on kiln (with `fuel`) and on `obj` under `cfg`, and
    /// judge the pair.
    pub fn run_case(
        wasm: &[u8],
        obj: &CompiledObject,
        export: &str,
        args: &[WasmValue],
        fuel: u64,
        imports: &Imports,
        cfg: &EmuConfig,
    ) -> Result<Case, CaseError> {
        let sig = export_signature(wasm, export).map_err(CaseError::Signature)?;
        if has_linear_memory(wasm).map_err(CaseError::Signature)? {
            return Err(CaseError::LinearMemory);
        }
        let r = reference::run(wasm, export, args, fuel, imports).map_err(CaseError::Reference)?;
        let e = emulate::run(obj, export, &sig, args, cfg).map_err(CaseError::Emulator)?;
        Ok(Case {
            export: export.to_string(),
            args: args.to_vec(),
            verdict: verdict(&r.outcome, &e.outcome),
            reference: r.outcome,
            host_calls: r.calls,
            emulator: e.outcome,
        })
    }

    /// One step of a hosted sequence.
    #[derive(Clone, Debug)]
    pub struct HostedCase {
        pub export: String,
        pub args: Vec<WasmValue>,
        pub reference: RefOutcome,
        pub ref_calls: Vec<HostCall>,
        pub emulator: EmuOutcome,
        pub emu_calls: Vec<HostCall>,
        pub verdict: Verdict,
    }

    /// Run `steps` in order on ONE kiln instance and on ONE hosted image of
    /// `obj` (see [`crate::hosted`]), and judge every step.
    ///
    /// A step agrees only when the outcomes agree per the matrix AND the two
    /// engines made the same host calls in the same order. The sequence ends
    /// after the first step where either engine does not return values, so
    /// the result can be shorter than `steps`: a caller that requires every
    /// step must check the length.
    pub fn run_hosted(
        wasm: &[u8],
        obj: &CompiledObject,
        steps: &[(&str, &[WasmValue])],
        fuel: u64,
        imports: &Imports,
        cfg: &crate::hosted::HostConfig,
    ) -> Result<Vec<HostedCase>, CaseError> {
        let refs =
            reference::run_sequence(wasm, steps, fuel, imports).map_err(CaseError::Reference)?;
        let mut image =
            crate::hosted::Hosted::link(obj, wasm, imports, cfg).map_err(CaseError::Emulator)?;
        let mut cases = Vec::new();
        for ((export, args), r) in steps.iter().zip(refs) {
            let e = image.call(export, args).map_err(CaseError::Emulator)?;
            let mut v = verdict(&r.outcome, &e.outcome);
            if v.is_agree() && r.calls != e.calls {
                v = Verdict::Disagree(format!(
                    "host calls differ: reference {:?}, machine code {:?}",
                    r.calls, e.calls
                ));
            }
            let stop = !matches!(e.outcome, EmuOutcome::Values(_));
            cases.push(HostedCase {
                export: export.to_string(),
                args: args.to_vec(),
                reference: r.outcome,
                ref_calls: r.calls,
                emulator: e.outcome,
                emu_calls: e.calls,
                verdict: v,
            });
            if stop {
                break;
            }
        }
        Ok(cases)
    }

    /// The emulator environment for `wasm`: its memory image, and every
    /// function import served by `imports` under its FIELD name (the symbol
    /// synth's relocatable RV32 object calls).
    pub fn env_for(wasm: &[u8], imports: &Imports) -> Result<EmuEnv, CaseError> {
        let memory = memory_image(wasm).map_err(CaseError::Signature)?;
        let mut env = EmuEnv {
            memory,
            imports: Vec::new(),
        };
        for FuncImport { module, field, sig } in
            function_imports(wasm).map_err(CaseError::Signature)?
        {
            let f = imports.get(&module, &field).ok_or_else(|| {
                CaseError::Reference(RefError::UnresolvedImport {
                    module: module.clone(),
                    field: field.clone(),
                })
            })?;
            env.imports.push((field, sig, f.clone()));
        }
        Ok(env)
    }

    /// [`run_case`] for a module WITH a linear memory and/or imports (RV32):
    /// the verdict is on values or trap, AND on the final linear memory
    /// (byte-equal to kiln's), AND on the host-call trace (field, arguments
    /// and results, in order). Memory is compared after a trap too: a
    /// trapping access must not have written anything kiln did not.
    #[allow(clippy::too_many_arguments)]
    pub fn run_case_env(
        wasm: &[u8],
        obj: &CompiledObject,
        export: &str,
        args: &[WasmValue],
        fuel: u64,
        imports: &Imports,
        cfg: &EmuConfig,
        env: &EmuEnv,
    ) -> Result<Case, CaseError> {
        let sig = export_signature(wasm, export).map_err(CaseError::Signature)?;
        let r = reference::run(wasm, export, args, fuel, imports).map_err(CaseError::Reference)?;
        let e = emulate::run_env(obj, export, &sig, args, cfg, env).map_err(CaseError::Emulator)?;
        Ok(Case {
            export: export.to_string(),
            args: args.to_vec(),
            verdict: env_verdict(&r, &e),
            reference: r.outcome,
            host_calls: r.calls,
            emulator: e.outcome,
        })
    }

    /// [`run_case_env`] over a SEQUENCE (v0.92; RV32 and AArch64): `steps`
    /// run in order on ONE kiln instance, and on the emulator with each
    /// step's final linear memory carried into the next step's image, so a
    /// later call sees what an earlier one wrote. Every step is judged as in
    /// [`run_case_env`] — values or trap, host calls, and the WHOLE memory
    /// byte for byte, after a trap too.
    ///
    /// The sequence ends after the first step where either engine does not
    /// return values (kiln's instance is not usable past a trap), so the
    /// result can be shorter than `steps`: a caller that requires every step
    /// must check the length.
    pub fn run_sequence_env(
        wasm: &[u8],
        obj: &CompiledObject,
        steps: &[(&str, &[WasmValue])],
        fuel: u64,
        imports: &Imports,
        cfg: &EmuConfig,
    ) -> Result<Vec<Case>, CaseError> {
        let refs =
            reference::run_sequence(wasm, steps, fuel, imports).map_err(CaseError::Reference)?;
        let mut env = env_for(wasm, imports)?;
        let mut cases = Vec::new();
        for ((export, args), r) in steps.iter().zip(refs) {
            let sig = export_signature(wasm, export).map_err(CaseError::Signature)?;
            let e = emulate::run_env(obj, export, &sig, args, cfg, &env)
                .map_err(CaseError::Emulator)?;
            let v = env_verdict(&r, &e);
            let stop = !matches!(e.outcome, EmuOutcome::Values(_))
                || !matches!(r.outcome, RefOutcome::Values(_));
            env.memory = e.memory.clone();
            cases.push(Case {
                export: export.to_string(),
                args: args.to_vec(),
                verdict: v,
                reference: r.outcome,
                host_calls: r.calls,
                emulator: e.outcome,
            });
            if stop {
                break;
            }
        }
        Ok(cases)
    }

    /// The verdict of one environment step: the outcome matrix, then the
    /// host-call trace, then linear memory (length, then every byte).
    fn env_verdict(r: &reference::RefRun, e: &emulate::EmuRun) -> Verdict {
        let mut v = verdict(&r.outcome, &e.outcome);
        if v.is_agree() {
            let key = |c: &HostCall| (c.field.clone(), c.args.clone(), c.results.clone());
            let rk: Vec<_> = r.calls.iter().map(key).collect();
            let ek: Vec<_> = e.calls.iter().map(key).collect();
            if rk != ek {
                v = Verdict::Disagree(format!("host calls: reference {rk:?}, emulator {ek:?}"));
            } else if r.memory.as_ref().map(Vec::len) != e.memory.as_ref().map(Vec::len) {
                v = Verdict::Disagree(format!(
                    "memory size: reference {:?}, emulator {:?}",
                    r.memory.as_ref().map(Vec::len),
                    e.memory.as_ref().map(Vec::len)
                ));
            } else if let (Some(rm), Some(em)) = (&r.memory, &e.memory)
                && let Some(i) = rm.iter().zip(em).position(|(a, b)| a != b)
            {
                v = Verdict::Disagree(format!(
                    "memory differs first at {i:#x}: reference {:#04x}, emulator {:#04x}",
                    rm[i], em[i]
                ));
            }
        }
        v
    }
}
