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
//! WHAT IS COMPARED: return values and trap-versus-return, nothing else.
//! Memory effects are not compared, so `run_case` refuses a module with a
//! linear memory; the emulator refuses float signatures (on every core but
//! AArch64, where the AAPCS64 V-register convention is set up), calls and
//! multi-value results (see `emulate`).
//!
//! HOSTED objects (`hosted`, `run_hosted`): a module with function imports is
//! an `ET_REL` object the embedder links. `run_hosted` links it against host
//! stubs, maps linear memory where the test says, and runs a SEQUENCE of
//! calls on one image and on one kiln instance. There the comparison also
//! covers every host call (module, field, arguments, results, in order), and
//! memory effects are compared through what later calls in the sequence read.

pub mod armv6m;
pub mod compare;
pub mod cycles;
pub mod probes;
pub mod record;
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
pub use run_case::{Case, CaseError, HostedCase, run_case, run_hosted};

#[cfg(feature = "exec")]
mod run_case {
    use crate::compare::{EmuOutcome, RefOutcome, Verdict, verdict};
    use crate::emulate::{self, EmuConfig, EmuError};
    use crate::reference::{self, HostCall, Imports, RefError};
    use crate::synth::CompiledObject;
    use crate::value::{WasmValue, export_signature, has_linear_memory};

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
}
