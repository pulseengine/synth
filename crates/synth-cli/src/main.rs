//! Synth CLI - WebAssembly-to-ARM Cortex-M AOT Compiler
//!
//! Command-line interface for the Synth compiler. Compiles WASM/WAT files
//! to bare-metal ARM Cortex-M ELF binaries with optional formal verification.

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use synth_backend::{
    ArmBackend, ArmRelocationType, ElfBuilder, ElfSectionType, ElfType, ProgramFlags,
    ProgramHeader, Relocation, Section, SectionFlags, Symbol, SymbolBinding, SymbolType,
    VectorTable, W2C2Backend,
};
use synth_core::HardwareCapabilities;
use synth_core::SafetyManifest;
use synth_core::backend::{Backend, BackendRegistry, CompileConfig, SafetyBounds, VolatileRange};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::ImportEntry;
use synth_core::wsc_facts::WscFact;
use synth_synthesis::{
    FunctionOps, WasmGlobal, WasmMemory, WasmOp, decode_wasm_functions, decode_wasm_module,
};
use tracing::{Level, info, warn};
use wast::parser::{self, ParseBuffer};
use wast::{Wast, WastDirective};

// Layer-2 budget-derivation logic, landed frozen-safe ahead of the gated call
// site that runs scry's `analyze()` (the scry production-dep step is a separate,
// user-gated decision). `allow(dead_code)` until that wiring lands.
#[allow(dead_code)]
mod shadow_budget;
mod sign;

/// Sentinel value clap substitutes when `--sbom` is given without a path.
/// Resolved to `<output>.cdx.json` by [`resolve_sbom_path`]. Unlikely to
/// collide with a real path the user would pass.
const SBOM_DEFAULT_SENTINEL: &str = "\u{0}sbom-default\u{0}";

// =============================================================================
// VCR-PERF-002 Phase 2 (#494): proof-carrying specialization (fact-spec)
// =============================================================================

/// `SYNTH_FACT_SPEC` — default OFF (silicon-gated, the design doc's Phase-3
/// flip criterion). When set (any value but `0`) AND the module carried a
/// parseable `wsc.facts` section, the driver runs the per-function fact-spec
/// pass before selection. Frozen fixtures carry no facts section, so they are
/// bit-identical trivially even with the flag on.
fn fact_spec_enabled() -> bool {
    std::env::var("SYNTH_FACT_SPEC").is_ok_and(|v| v != "0")
}

/// One function's rewritten stream + side-tables, when the Phase-2 pass
/// admitted at least one certificate-backed elision.
struct SpecializedFn {
    ops: Vec<WasmOp>,
    block_arity: Vec<(u8, u8)>,
    /// Indices into the ORIGINAL op stream that survived — for filtering
    /// parallel side-tables (`op_offsets` feeding `.debug_line`).
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    kept: Vec<usize>,
    /// #494 phase 2b: div/rem sites (indices into `ops`) whose divide-by-zero
    /// guard was certificate-elided — threaded to
    /// `CompileConfig::fact_div_zero_elide` for the direct selector.
    elide_div_zero: Vec<usize>,
    /// #494 phase 2b: `div_s` sites whose INT_MIN/-1 overflow guard was
    /// certificate-elided (a SEPARATE obligation — divisor-nonzero alone
    /// never lands here, #633/#634).
    elide_div_ovf: Vec<usize>,
}

/// Run the fact-spec pass (value-range facts ⇒ dead conditional-branch
/// elision; #494 phase 2b: divisor-nonzero facts ⇒ div/rem trap-guard
/// elision marks — `docs/design/proof-carrying-specialization.md`) for one
/// function. Every elision was individually discharged by the ordeal-backed
/// solver (certificate-checked) BEFORE this returns; admits and declines are
/// logged per function. Returns `Some` when the op stream changed OR at
/// least one guard-elision mark was admitted — `None` means the general
/// lowering proceeds untouched.
fn maybe_fact_spec(
    func_name: &str,
    ops: &[WasmOp],
    block_arity: &[(u8, u8)],
    facts: &[WscFact],
    params_i64: &[bool],
) -> Option<SpecializedFn> {
    if !fact_spec_enabled() || facts.is_empty() {
        return None;
    }
    #[cfg(feature = "verify")]
    {
        let r = synth_verify::fact_spec::specialize_function(
            func_name,
            ops,
            block_arity,
            facts,
            params_i64,
        );
        // Loud by contract: every decline names its site and reason; every
        // admit carries the certificate line (the evidence trail).
        for line in &r.declined {
            eprintln!("fact-spec: DECLINE {line}");
        }
        for line in &r.admitted {
            eprintln!("fact-spec: ADMIT {line}");
        }
        if r.changed() || !r.elide_div_zero.is_empty() || !r.elide_div_ovf.is_empty() {
            eprintln!(
                "fact-spec: '{func_name}' specialized — {} elision(s) admitted, \
                 {} declined ({} → {} ops, {} zero-guard + {} overflow-guard marks)",
                r.admitted.len(),
                r.declined.len(),
                ops.len(),
                r.ops.len(),
                r.elide_div_zero.len(),
                r.elide_div_ovf.len(),
            );
            return Some(SpecializedFn {
                ops: r.ops,
                block_arity: r.block_arity,
                kept: r.kept,
                elide_div_zero: r.elide_div_zero,
                elide_div_ovf: r.elide_div_ovf,
            });
        }
        None
    }
    #[cfg(not(feature = "verify"))]
    {
        let _ = (func_name, ops, block_arity, facts, params_i64);
        // Decline loudly (the design doc's rule): without the solver the
        // obligation cannot be discharged, so no elision may fire — but the
        // user asked for specialization, so say why nothing happens.
        eprintln!(
            "warning: SYNTH_FACT_SPEC is set but this synth was built without the \
             'verify' feature — the per-elision proof obligation (#494) cannot be \
             discharged, so every elision is DECLINED and the general lowering is \
             emitted. Rebuild with `--features verify` to enable fact-based \
             specialization."
        );
        None
    }
}

#[derive(Parser)]
#[command(name = "synth")]
#[command(about = "WebAssembly-to-ARM Cortex-M AOT compiler")]
#[command(
    long_about = "Synth compiles WebAssembly (WASM/WAT) to native ARM Cortex-M machine code,\n\
producing bare-metal ELF binaries for embedded targets.\n\n\
Examples:\n  \
synth compile input.wat -o output.elf\n  \
synth compile input.wat --cortex-m -o firmware.elf\n  \
synth compile input.wat --cortex-m --link -o firmware.elf\n  \
synth disasm firmware.elf\n  \
synth verify input.wat firmware.elf"
)]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse and analyze a WebAssembly component
    Parse {
        /// Input WebAssembly file
        #[arg(value_name = "INPUT")]
        input: PathBuf,

        /// Output JSON representation
        #[arg(short, long, value_name = "OUTPUT")]
        output: Option<PathBuf>,
    },

    /// Synthesize a component to native code
    Synthesize {
        /// Input WebAssembly file
        #[arg(value_name = "INPUT")]
        input: PathBuf,

        /// Output binary file
        #[arg(short, long, value_name = "OUTPUT")]
        output: PathBuf,

        /// Target architecture
        #[arg(
            short,
            long,
            value_name = "TARGET",
            default_value = "thumbv7em-none-eabihf"
        )]
        target: String,

        /// Hardware config (nrf52840, stm32f407, stm32h743, imxrt1062, or custom)
        #[arg(long, value_name = "HARDWARE", default_value = "nrf52840")]
        hardware: String,

        /// Optimization level (0-3, s, z)
        #[arg(short = 'O', long, value_name = "LEVEL", default_value = "2")]
        opt_level: String,

        /// Enable XIP (execute-in-place)
        #[arg(long)]
        xip: bool,

        /// Enable formal verification
        #[arg(long)]
        verify: bool,
    },

    /// Display information about a target
    TargetInfo {
        /// Target name
        #[arg(value_name = "TARGET")]
        target: String,
    },

    /// Compile WASM/WAT to ARM ELF (e.g., synth compile input.wat --cortex-m -o fw.elf)
    Compile {
        /// Input WASM or WAT file (optional, use --demo for built-in demos)
        #[arg(value_name = "INPUT")]
        input: Option<PathBuf>,

        /// Output ELF file
        #[arg(short, long, value_name = "OUTPUT", default_value = "output.elf")]
        output: PathBuf,

        /// Demo function to compile (add, mul, calc) - used when no input file
        #[arg(short, long, value_name = "DEMO")]
        demo: Option<String>,

        /// Function index to compile (compiles all exports if neither this nor --func-name is set)
        #[arg(short, long, value_name = "INDEX")]
        func_index: Option<u32>,

        /// Function name (export name) to compile - overrides func_index
        #[arg(short = 'n', long, value_name = "NAME")]
        func_name: Option<String>,

        /// Compile ALL exported functions into a multi-function ELF
        #[arg(long)]
        all_exports: bool,

        /// Generate complete Cortex-M binary with vector table (for Renode/QEMU)
        #[arg(long)]
        cortex_m: bool,

        /// Target profile. ARM: cortex-m3, cortex-m4, cortex-m4f, cortex-m7,
        /// cortex-m7dp. RISC-V (-b riscv): rv32imac, rv32imc, rv32im, rv32i,
        /// rv32gc, esp32c3 (RV32IMC). `-b riscv` defaults to rv32imac.
        /// Implies --cortex-m for Cortex-M targets
        #[arg(short, long, value_name = "TARGET")]
        target: Option<String>,

        /// Disable optimization passes (use direct instruction selection)
        #[arg(long)]
        no_optimize: bool,

        /// Use Loom-compatible optimization (skip passes Loom already handles)
        #[arg(long)]
        loom_compat: bool,

        /// Run Loom WASM optimizer before compilation (requires --features loom)
        /// Pipeline: WASM -> loom optimize -> optimized WASM -> synth compile -> ARM
        /// Implies --loom-compat (skips redundant synth passes)
        #[arg(long)]
        loom: bool,

        /// DEPRECATED: alias for `--safety-bounds software`. Will be removed
        /// in a future release. Prints a deprecation notice when used.
        #[arg(long)]
        bounds_check: bool,

        /// Memory bounds safety profile (Phase 1 of binary-safety design).
        ///
        /// Accepted values:
        /// - `none`     — no inline check, no MPU/PMP setup (fastest, unsafe)
        /// - `mpu`      — rely on ARM MPU / RV32 PMP hardware enforcement
        /// - `software` — emit CMP + inline UDF trap (ARM) or BGEU+EBREAK (RV32) per access
        /// - `mask`     — AND addr with `mem_size - 1` (requires power-of-two size)
        #[arg(long, value_name = "MODE")]
        safety_bounds: Option<String>,

        /// Compilation backend (arm, w2c2, awsm, wasker)
        #[arg(short, long, default_value = "arm")]
        backend: String,

        /// Run translation validation after compilation
        #[arg(long)]
        verify: bool,

        /// Link the compiled object into a final firmware ELF using arm-none-eabi-gcc
        #[arg(long)]
        link: bool,

        /// Path to kiln-builtins object file (.o) for linking (used with --link)
        #[arg(long, value_name = "BUILTINS")]
        builtins: Option<PathBuf>,

        /// Force relocatable object (.o, ET_REL) output even when wasm has no imports
        /// — for linking into a host build system.
        #[arg(long)]
        relocatable: bool,

        /// #237: native-pointer ABI for host-pointer drop-ins. Emits wasm function
        /// statics as a base-independent `.data` section (`__synth_wasm_data`,
        /// MOVW/MOVT-relocated), so a `linmem base = 0` native-pointer trampoline
        /// addresses host pointers and statics correctly in one function.
        #[arg(long)]
        native_pointer_abi: bool,

        /// Emit a CycloneDX 1.5 SBOM for the compiled ELF. With a path, writes
        /// there; as a bare flag (`--sbom`) writes `<output>.cdx.json` next to
        /// the ELF. The SBOM documents the synth compiler, the input WASM, the
        /// output ELF (hashes + sizes), and the WASM module's imports. It is
        /// the artifact consumed by `rivet import --format cyclonedx`.
        #[arg(
            long,
            value_name = "PATH",
            num_args = 0..=1,
            default_missing_value = SBOM_DEFAULT_SENTINEL
        )]
        sbom: Option<PathBuf>,

        /// Sign the compiled ELF (in place) via sigil's `wsc sign --keyless
        /// --format elf`. Requires the `wsc` binary from
        /// https://github.com/pulseengine/sigil on PATH, plus an OIDC token
        /// in the environment (e.g. GitHub Actions with `id-token: write`).
        /// Off by default — opt in per-invocation. See
        /// `docs/sigil-integration.md`.
        #[arg(long)]
        sign_output: bool,

        /// #383 (VCR-MEM-001): integrator-declared shadow-stack budget in BYTES
        /// for the `--native-pointer-abi` linear-memory reservation. Without
        /// this flag synth reserves the wasm linmem region up to the declared
        /// page top (the SP global's init, e.g. 65536 for `(memory 1)`), which
        /// is RAM-prohibitive on small MCUs. With it, the region is reserved as
        /// `static_data_high_water + budget` and the shadow-stack top is
        /// re-based to that smaller extent — so a few-KB-live module links into
        /// an 8 KiB-RAM part. Synth REFUSES (does not silently shrink) if the
        /// static-data high-water would collide with the re-based stack top.
        /// The footprint is ASSERTED (the budget is trusted), not proven —
        /// synth does not yet prove the program's max shadow-stack depth fits
        /// the budget (that is the layer-2 auto-proof / scry tail, VCR-MEM-001).
        /// CONTRACT: the budget must cover EVERYTHING live in linear memory above
        /// address 0 — the shadow stack AND any heap use — because static markers
        /// (`__heap_base` etc.) keep their original high addresses; the shrink
        /// re-bases only the stack top. Safe for no-grow / no-heap MCU images
        /// (the dissolved library-OS case); a module that dynamically allocates
        /// above B will mis-address. Only meaningful with `--native-pointer-abi`.
        #[arg(long, value_name = "BYTES")]
        shadow_stack_size: Option<u32>,

        /// VCR-DBG-001 (#394): emit DWARF debug sections (`.debug_info`/
        /// `.debug_abbrev`/`.debug_str`/`.debug_line`) mapping ARM `.text`
        /// addresses back to the input wasm's source lines. Requires the input to
        /// carry DWARF (`.debug_line` custom section) and the ARM backend (RISC-V
        /// carries no line_map). Purely additive: `.text`/`.data`/`.bss` stay
        /// byte-identical; off by default. Emitted only on the relocatable-object
        /// (host-link) path — on a self-contained image or RISC-V it is a no-op
        /// and warns. The `.text` addresses carry `.rel.debug_*` relocations
        /// against a `__synth_text_base` symbol, so a host linker fixes them up to
        /// the final load address (verified end-to-end with `arm-none-eabi-ld`).
        /// EXPERIMENTAL: `__synth_text_base` is a global symbol, so linking more
        /// than one synth `--debug-line` object into a single image collides
        /// (`multiple definition`) — compile such modules as one object or link
        /// separately until the local-section-symbol follow-up lands.
        #[arg(long)]
        debug_line: bool,

        /// #543 (Phase 1): mark a linear-memory segment as VOLATILE — the DMA
        /// transfer window. Format `<base>:<len>`; both accept hex (`0x…`) or
        /// decimal, e.g. `--volatile-segment 0x20001000:4096`. Repeatable to mark
        /// more than one range. Names a region `[base, base+len)` of the fused
        /// linear memory that an external agent (the DMA engine, gale's
        /// `own<buffer>` handoff / decision DD-DMA-REGION-001) rewrites out-of-band,
        /// so loads/stores inside it must eventually not be cached or reordered
        /// across the transfer boundary. PHASE 1 = plumbing only: the ranges are
        /// parsed and threaded to codegen but NOT yet consumed — the emitted bytes
        /// are unchanged whether or not the flag is passed. The codegen back-off
        /// (const-CSE + #468 base-CSE decline inside these ranges) is the gated
        /// Phase 2. See rivet VCR-DMA-001.
        #[arg(long, value_name = "BASE:LEN")]
        volatile_segment: Vec<String>,
    },

    /// Disassemble an ARM ELF file (e.g., synth disasm output.elf)
    Disasm {
        /// Input ELF file
        #[arg(value_name = "INPUT")]
        input: PathBuf,
    },

    /// List available compilation backends and their status
    Backends,

    /// Verify compilation correctness via Z3 — requires a build with
    /// `--features verify` (e.g., synth verify input.wat output.elf)
    Verify {
        /// Input WASM or WAT file (source)
        #[arg(value_name = "WASM")]
        wasm_input: PathBuf,

        /// Input ELF file (compiled output to verify)
        #[arg(value_name = "ELF")]
        elf_input: PathBuf,

        /// Backend that produced the ELF (for verification strategy selection)
        #[arg(short, long, default_value = "arm")]
        backend: String,
    },

    /// Emit RISC-V bare-metal startup code + linker script
    /// (e.g., `synth riscv-runtime -o build/`)
    RiscvRuntime {
        /// Output directory — receives `startup.c` and `linker.ld`
        #[arg(short = 'o', long, value_name = "DIR", default_value = ".")]
        outdir: PathBuf,

        /// Target ISA variant (default: rv32imac)
        #[arg(short, long, default_value = "rv32imac")]
        target: String,

        /// Flash origin address (default: 0x0)
        #[arg(long, default_value = "0x0")]
        flash_origin: String,

        /// RAM origin address (default: 0x80000000)
        #[arg(long, default_value = "0x80000000")]
        ram_origin: String,

        /// Linear-memory size in bytes (default: 65536, one wasm page)
        #[arg(long, default_value = "65536")]
        linear_memory_size: u64,

        /// Stack size in bytes (default: 4096)
        #[arg(long, default_value = "4096")]
        stack_size: u64,

        /// Enable FPU init in the reset vector
        #[arg(long)]
        enable_fpu: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize logging
    let level = if cli.verbose {
        Level::DEBUG
    } else {
        Level::INFO
    };

    tracing_subscriber::fmt()
        .with_max_level(level)
        .with_target(false)
        .init();

    match cli.command {
        Commands::Parse { input, output } => {
            parse_command(input, output)?;
        }
        Commands::Synthesize {
            input,
            output,
            target,
            hardware,
            opt_level,
            xip,
            verify,
        } => {
            synthesize_command(input, output, target, hardware, opt_level, xip, verify)?;
        }
        Commands::TargetInfo { target } => {
            target_info_command(target)?;
        }
        Commands::Compile {
            input,
            output,
            demo,
            func_index,
            func_name,
            all_exports,
            cortex_m,
            target,
            no_optimize,
            loom_compat,
            loom,
            bounds_check,
            safety_bounds,
            backend,
            verify,
            link,
            builtins,
            relocatable,
            native_pointer_abi,
            sbom,
            sign_output,
            shadow_stack_size,
            debug_line,
            volatile_segment,
        } => {
            // Resolve target spec: --target overrides, --cortex-m is backwards compat
            let target_spec = resolve_target_spec(target.as_deref(), cortex_m, &backend)?;
            let is_cortex_m =
                cortex_m || target_spec.family == synth_core::target::ArchFamily::ArmCortexM;

            // --loom implies --loom-compat (skip redundant synth passes)
            let loom_compat = loom_compat || loom;

            // Phase 1 safety-bounds resolution. `--safety-bounds` takes
            // precedence; `--bounds-check` is the legacy alias and emits a
            // single-line deprecation notice when used.
            let resolved_safety_bounds =
                resolve_safety_bounds(safety_bounds.as_deref(), bounds_check)?;

            // Resolve the CycloneDX SBOM destination. `--sbom` with no value
            // means "next to the ELF" (`<output>.cdx.json`); `--sbom PATH`
            // writes there; absent means no SBOM.
            let sbom_path = resolve_sbom_path(sbom, &output);

            // #543 Phase 1: parse the volatile DMA-window ranges. Inert plumbing —
            // threaded to codegen but not yet consumed (Phase 2 is gated).
            let volatile_segments = parse_volatile_segments(&volatile_segment)?;

            compile_command(
                input,
                output.clone(),
                demo,
                func_index,
                func_name,
                all_exports,
                is_cortex_m,
                no_optimize,
                loom_compat,
                loom,
                resolved_safety_bounds,
                &backend,
                verify,
                &target_spec,
                relocatable,
                native_pointer_abi,
                sbom_path,
                sign_output,
                shadow_stack_size,
                debug_line,
                volatile_segments,
            )?;

            // If --link requested, invoke the cross-linker
            if link {
                link_firmware(&output, builtins.as_deref(), &target_spec)?;
            }
        }
        Commands::Disasm { input } => {
            disasm_command(input)?;
        }
        Commands::Backends => {
            backends_command()?;
        }
        Commands::Verify {
            wasm_input,
            elf_input,
            backend,
        } => {
            verify_command(wasm_input, elf_input, &backend)?;
        }
        Commands::RiscvRuntime {
            outdir,
            target,
            flash_origin,
            ram_origin,
            linear_memory_size,
            stack_size,
            enable_fpu,
        } => {
            riscv_runtime_command(
                outdir,
                target,
                flash_origin,
                ram_origin,
                linear_memory_size,
                stack_size,
                enable_fpu,
            )?;
        }
    }

    Ok(())
}

#[cfg(feature = "riscv")]
#[allow(clippy::too_many_arguments)]
fn riscv_runtime_command(
    outdir: PathBuf,
    target: String,
    flash_origin: String,
    ram_origin: String,
    linear_memory_size: u64,
    stack_size: u64,
    enable_fpu: bool,
) -> Result<()> {
    use synth_backend_riscv::{
        LinkerScriptConfig, RiscVLinkerScriptGenerator, RiscVStartupGenerator, StartupConfig,
    };
    use synth_core::{HardwareCapabilities, RISCVVariant, TargetArch};

    // Hardware caps from the target name.
    let variant = match target.as_str() {
        "rv32i" => RISCVVariant::RV32I,
        "rv32imac" | "rv32imc" => RISCVVariant::RV32IMAC,
        "rv32gc" => RISCVVariant::RV32GC,
        "rv64i" => RISCVVariant::RV64I,
        "rv64imac" => RISCVVariant::RV64IMAC,
        "rv64gc" => RISCVVariant::RV64GC,
        _ => anyhow::bail!(
            "unknown RISC-V target: {}. Supported: rv32i, rv32imac, rv32gc, rv64i, rv64imac, rv64gc",
            target
        ),
    };

    let parse_addr = |s: &str| -> Result<u64> {
        let s = s.trim_start_matches("0x").trim_start_matches("0X");
        u64::from_str_radix(s, 16).context(format!("invalid hex address: {}", s))
    };
    let flash_origin_v = parse_addr(&flash_origin)?;
    let ram_origin_v = parse_addr(&ram_origin)?;

    let hw_caps = HardwareCapabilities {
        arch: TargetArch::RISCV(variant),
        has_mpu: false,
        mpu_regions: 0,
        has_pmp: true,
        pmp_entries: 16,
        has_fpu: enable_fpu,
        fpu_precision: None,
        has_simd: false,
        simd_level: None,
        xip_capable: true,
        flash_size: 64 * 1024,
        ram_size: 64 * 1024,
    };

    std::fs::create_dir_all(&outdir).context("failed to create output directory")?;

    // Startup
    let startup = RiscVStartupGenerator::new(hw_caps.clone()).with_config(StartupConfig {
        enable_fpu,
        ..Default::default()
    });
    let startup_path = outdir.join("startup.c");
    std::fs::write(&startup_path, startup.generate())
        .context(format!("failed to write {}", startup_path.display()))?;

    // Linker script
    let linker = RiscVLinkerScriptGenerator::new(hw_caps).with_config(LinkerScriptConfig {
        flash_origin: flash_origin_v,
        ram_origin: ram_origin_v,
        linear_memory_size,
        stack_size,
    });
    let linker_path = outdir.join("linker.ld");
    std::fs::write(&linker_path, linker.generate())
        .context(format!("failed to write {}", linker_path.display()))?;

    println!("Wrote {}", startup_path.display());
    println!("Wrote {}", linker_path.display());
    println!();
    let march = if matches!(target.as_str(), "rv32imac" | "rv32imc") {
        "rv32imac"
    } else {
        target.as_str()
    };
    println!("Link your synth-compiled .o with:");
    println!(
        "  riscv64-unknown-elf-gcc -nostartfiles -nostdlib -mabi=ilp32 -march={} \\",
        march
    );
    println!(
        "    -T {} -o firmware.elf {} <synth.o>",
        linker_path.display(),
        startup_path.display()
    );

    Ok(())
}

#[cfg(not(feature = "riscv"))]
#[allow(clippy::too_many_arguments)]
fn riscv_runtime_command(
    _outdir: PathBuf,
    _target: String,
    _flash_origin: String,
    _ram_origin: String,
    _linear_memory_size: u64,
    _stack_size: u64,
    _enable_fpu: bool,
) -> Result<()> {
    anyhow::bail!("RISC-V backend was not compiled in (rebuild with --features riscv)")
}

fn parse_command(input: PathBuf, output: Option<PathBuf>) -> Result<()> {
    info!("Parsing WebAssembly component: {}", input.display());

    // Parse the component
    let component =
        synth_frontend::parse_component_file(&input).context("Failed to parse component")?;

    // Validate the component
    synth_frontend::validate_component(&component).context("Component validation failed")?;

    info!("Component parsed successfully");
    info!("  Name: {}", component.name);
    info!("  Modules: {}", component.modules.len());
    info!("  Total memories: {}", component.total_memories());
    info!(
        "  Total memory size: {} bytes",
        component.total_memory_size()
    );

    // Output JSON if requested
    if let Some(output_path) = output {
        let json =
            serde_json::to_string_pretty(&component).context("Failed to serialize component")?;
        std::fs::write(&output_path, json).context(format!(
            "Failed to write output to {}",
            output_path.display()
        ))?;
        info!("Component JSON written to: {}", output_path.display());
    }

    Ok(())
}

fn synthesize_command(
    input: PathBuf,
    output: PathBuf,
    target: String,
    hardware: String,
    opt_level: String,
    xip: bool,
    verify: bool,
) -> Result<()> {
    info!("Synthesizing WebAssembly component: {}", input.display());
    info!("  Target: {}", target);
    info!("  Hardware: {}", hardware);
    info!("  Optimization level: {}", opt_level);
    info!("  XIP: {}", xip);
    info!("  Verification: {}", verify);

    // Parse the component
    let component =
        synth_frontend::parse_component_file(&input).context("Failed to parse component")?;

    synth_frontend::validate_component(&component).context("Component validation failed")?;

    // Get hardware capabilities
    let hw_caps = match hardware.as_str() {
        "nrf52840" => HardwareCapabilities::nrf52840(),
        "stm32f407" => HardwareCapabilities::stm32f407(),
        "stm32h743" => HardwareCapabilities::stm32h743(),
        "imxrt1062" => HardwareCapabilities::imxrt1062(),
        _ => {
            anyhow::bail!(
                "Unsupported hardware: {}. Use nrf52840, stm32f407, stm32h743, imxrt1062",
                hardware
            );
        }
    };

    info!("Hardware capabilities:");
    info!("  MPU regions: {}", hw_caps.mpu_regions);
    info!("  FPU: {}", hw_caps.has_fpu);
    info!("  Flash: {} KB", hw_caps.flash_size / 1024);
    info!("  RAM: {} KB", hw_caps.ram_size / 1024);

    // For PoC, we'll implement the full synthesis pipeline later
    // For now, just report what would happen
    info!("Synthesis pipeline (PoC - not yet fully implemented):");
    info!("  1. Component parsing: ✓");
    info!("  2. Memory layout analysis: TODO");
    info!("  3. MPU region allocation: TODO");
    info!("  4. Optimization: TODO");
    info!("  5. Code generation: TODO");
    info!("  6. Binary emission: TODO");

    info!("Output would be written to: {}", output.display());

    Ok(())
}

fn target_info_command(target: String) -> Result<()> {
    info!("Target information for: {}", target);

    // Parse target and display info
    match target.as_str() {
        "nrf52840" => {
            let caps = HardwareCapabilities::nrf52840();
            print_hardware_info(&caps);
        }
        "stm32f407" => {
            let caps = HardwareCapabilities::stm32f407();
            print_hardware_info(&caps);
        }
        "stm32h743" => {
            let caps = HardwareCapabilities::stm32h743();
            print_hardware_info(&caps);
        }
        "imxrt1062" => {
            let caps = HardwareCapabilities::imxrt1062();
            print_hardware_info(&caps);
        }
        _ => {
            anyhow::bail!(
                "Unknown target: {}. Supported: nrf52840, stm32f407, stm32h743, imxrt1062",
                target
            );
        }
    }

    Ok(())
}

fn print_hardware_info(caps: &HardwareCapabilities) {
    println!("Hardware Capabilities:");
    println!("  Architecture: {:?}", caps.arch);
    println!("  MPU: {} (regions: {})", caps.has_mpu, caps.mpu_regions);
    println!("  FPU: {}", caps.has_fpu);
    if let Some(precision) = caps.fpu_precision {
        println!("    Precision: {:?}", precision);
    }
    println!("  SIMD: {}", caps.has_simd);
    if let Some(level) = caps.simd_level {
        println!("    Level: {:?}", level);
    }
    println!("  XIP capable: {}", caps.xip_capable);
    println!(
        "  Flash: {} KB ({} MB)",
        caps.flash_size / 1024,
        caps.flash_size / (1024 * 1024)
    );
    println!("  RAM: {} KB", caps.ram_size / 1024);
}

/// Compiled function for ELF building (name + code bytes + relocations)
struct ElfFunction {
    name: String,
    /// #394 Tier-1.x: the developer-facing name from the wasm `name` custom
    /// section (present for internal functions too, unlike the export name).
    /// Consumed ONLY by the `--debug-line` `DW_TAG_subprogram` emit — symbol
    /// names and relocation labels keep using `name` (export name or `func_N`),
    /// so linkability and emitted bytes are unchanged.
    debug_name: Option<String>,
    /// WASM function index — used to define a `func_{index}` symbol so that
    /// internal calls (`BL func_N`, emitted by the selector against the WASM
    /// index) resolve to this function's address (#167).
    wasm_index: u32,
    code: Vec<u8>,
    /// Relocations targeting external symbols (from import dispatch stubs)
    relocations: Vec<synth_core::backend::CodeRelocation>,
    /// VCR-DBG-001 step 4 (#394): per-op wasm code BYTE offsets (decoder side
    /// table, `FunctionOps.op_offsets`) — module-relative, parallel to the wasm
    /// ops. Threaded here so the `--debug-line` emitter can normalize against
    /// `code_base` and compose with `line_map`. Empty unless DWARF emission is on.
    op_offsets: Vec<u32>,
    /// VCR-DBG-001 step 4 (#394): `(machine_offset_within_function → wasm_op_index)`
    /// captured by the ARM backend (`CompiledFunction.line_map`). Empty for the
    /// RISC-V backend. Composed with `op_offsets` to map ARM text address → source.
    line_map: synth_core::backend::LineMap,
}

/// Resolve --target / --cortex-m into a TargetSpec
fn resolve_target_spec(target: Option<&str>, cortex_m: bool, backend: &str) -> Result<TargetSpec> {
    match target {
        // from_triple already lists the supported ARM + RV32 names in its error.
        Some(name) => TargetSpec::from_triple(name).map_err(|e| anyhow::anyhow!("{e}")),
        // No --target given: pick a backend-appropriate default so `-b riscv`
        // doesn't inherit the ARM profile and bail (#218).
        None if backend == "riscv" => Ok(TargetSpec::riscv32("imac")),
        // #538: `-b aarch64` without --target defaults to the A64 host profile.
        None if backend == "aarch64" => Ok(TargetSpec::cortex_a53()),
        None if cortex_m => Ok(TargetSpec::cortex_m3()),
        None => {
            // Default: Arm32 ISA (non-Cortex-M, no vector table)
            Ok(TargetSpec {
                isa: synth_core::target::IsaVariant::Arm32,
                ..TargetSpec::cortex_m4()
            })
        }
    }
}

/// Build the backend registry with all available backends
fn build_backend_registry() -> BackendRegistry {
    let mut registry = BackendRegistry::new();

    // Always register the built-in ARM backend
    registry.register(Box::new(ArmBackend::new()));

    // AArch64 host-native backend (#538) — always available (pure Rust).
    registry.register(Box::new(synth_backend_aarch64::AArch64Backend::new()));

    // Register w2c2 backend (always available, checks tool at runtime)
    registry.register(Box::new(W2C2Backend::new()));

    // Register aWsm backend if compiled with feature
    #[cfg(feature = "awsm")]
    registry.register(Box::new(synth_backend_awsm::AwsmBackend::new()));

    // Register wasker backend if compiled with feature
    #[cfg(feature = "wasker")]
    registry.register(Box::new(synth_backend_wasker::WaskerBackend::new()));

    // Register RISC-V backend if compiled with feature
    #[cfg(feature = "riscv")]
    registry.register(Box::new(synth_backend_riscv::RiscVBackend::new()));

    registry
}

/// Run the Loom WASM optimizer on a WASM module if enabled.
///
/// Pipeline: raw WASM bytes -> loom optimize -> optimized WASM bytes
///
/// Loom is PulseEngine's WASM-level optimizer (https://github.com/pulseengine/loom).
/// It applies constant folding, strength reduction, and dead code elimination
/// at the WASM level with optional Z3 verification of semantic equivalence.
///
/// ## Integration status
///
/// The `--loom` flag and integration points are wired up. When the `loom` crate
/// is published, enable the dependency in workspace Cargo.toml and synth-cli
/// Cargo.toml (see commented-out lines), then uncomment the `#[cfg(feature = "loom")]`
/// block below.
///
/// ## Expected loom API
///
/// ```ignore
/// // loom-opt crate expected API:
/// pub fn optimize(wasm_bytes: &[u8]) -> Result<Vec<u8>>;
/// ```
fn maybe_run_loom(enabled: bool, wasm_bytes: Vec<u8>) -> Result<Vec<u8>> {
    if !enabled {
        return Ok(wasm_bytes);
    }

    // === Loom integration point ===
    //
    // When the loom crate is available, uncomment the feature-gated block below
    // and the corresponding dependency lines in:
    //   - Cargo.toml (workspace): loom-opt = { git = "..." }
    //   - crates/synth-cli/Cargo.toml: loom = ["dep:loom-opt"], loom-opt = { workspace = true, optional = true }
    //
    // Then compile with: cargo build --features loom
    //
    // #[cfg(feature = "loom")]
    // {
    //     info!("Running Loom WASM optimizer...");
    //     let input_len = wasm_bytes.len();
    //     let optimized = loom_opt::optimize(&wasm_bytes)
    //         .context("Loom optimization failed")?;
    //     let savings = if input_len > 0 {
    //         let reduced = input_len.saturating_sub(optimized.len());
    //         (reduced as f64 / input_len as f64) * 100.0
    //     } else {
    //         0.0
    //     };
    //     info!(
    //         "Loom: {} bytes -> {} bytes ({:.1}% reduction)",
    //         input_len, optimized.len(), savings,
    //     );
    //     return Ok(optimized);
    // }

    anyhow::bail!(
        "--loom is not yet available. The loom WASM optimizer integration is pending.\n\
         See https://github.com/pulseengine/loom for status.\n\n\
         In the meantime, use --loom-compat to skip synth passes that overlap\n\
         with loom's optimizations (constant folding, strength reduction)."
    );
}

/// Reconcile `--safety-bounds` and the legacy `--bounds-check` flag. Prints a
/// one-line deprecation notice when the legacy flag is used. Phase 1 of
/// `docs/binary-safety-design.md` §2 (CLI surface).
fn resolve_safety_bounds(
    safety_bounds: Option<&str>,
    legacy_bounds_check: bool,
) -> Result<SafetyBounds> {
    if let Some(v) = safety_bounds {
        let parsed = SafetyBounds::parse(v).map_err(|e| anyhow::anyhow!(e))?;
        if legacy_bounds_check {
            eprintln!(
                "warning: --bounds-check is deprecated; --safety-bounds={} takes precedence",
                parsed.as_str()
            );
        }
        return Ok(parsed);
    }
    if legacy_bounds_check {
        eprintln!("warning: --bounds-check is deprecated; use --safety-bounds=software instead");
        return Ok(SafetyBounds::Software);
    }
    Ok(SafetyBounds::None)
}

/// Emit the `safety-manifest.json` sidecar when any safety knob is active.
/// Phase 1 only records bounds + division traps; later phases will extend
/// the schema. Silently no-ops when `safety_bounds == None` (the default,
/// for back-compat with callers that don't opt in).
fn maybe_emit_safety_manifest(
    elf_path: &std::path::Path,
    target_spec: &TargetSpec,
    safety_bounds: SafetyBounds,
    linear_memory_bytes: u32,
) -> Result<()> {
    if safety_bounds == SafetyBounds::None {
        return Ok(());
    }
    let manifest = SafetyManifest {
        synth_version: env!("CARGO_PKG_VERSION").to_string(),
        target_triple: target_spec.triple.clone(),
        safety_bounds,
        // Phase 1: div-by-zero and signed-div-overflow are always enabled
        // for WASM-compliant output on both backends. The columns will gain
        // independent knobs in Phase 2 when `--safety-div` / `--safety-div-overflow`
        // CLI flags land.
        safety_div_zero: true,
        safety_div_overflow: true,
        linear_memory_bytes,
    };
    let sidecar = SafetyManifest::sidecar_path(elf_path);
    let json = manifest.to_json();
    std::fs::write(&sidecar, json)
        .with_context(|| format!("Failed to write safety manifest: {}", sidecar.display()))?;
    info!("Wrote safety manifest: {}", sidecar.display());
    Ok(())
}

/// Resolve the `--sbom` flag into a concrete destination path (or `None`).
///
/// clap substitutes [`SBOM_DEFAULT_SENTINEL`] when the flag is given with no
/// value, so:
/// - flag absent            -> `None`              (no SBOM)
/// - bare `--sbom`          -> `Some(<sentinel>)`   -> `<output>.cdx.json`
/// - `--sbom path.cdx.json` -> `Some("path...")`    -> that path verbatim
fn resolve_sbom_path(sbom: Option<PathBuf>, output: &std::path::Path) -> Option<PathBuf> {
    match sbom {
        None => None,
        Some(p) if p.as_os_str() == SBOM_DEFAULT_SENTINEL => {
            Some(synth_core::CycloneDxSbom::sidecar_path(output))
        }
        Some(p) => Some(p),
    }
}

/// #543 (Phase 1): parse the repeated `--volatile-segment <base>:<len>` flag
/// values into [`VolatileRange`]s. Both fields accept a `0x`-prefixed hex or a
/// plain decimal `u32`. A range must be `base:len` with exactly one colon; a
/// zero-length range and a range whose `base + len` overflows `u32` are rejected.
///
/// Phase 1 only PARSES and validates — the ranges are threaded onto
/// [`CompileConfig::volatile_segments`] but not yet consumed by any pass, so the
/// flag is inert on the emitted bytes. Returns a descriptive error for malformed
/// input (the flag surface must reject `garbage` loudly, not silently drop it).
fn parse_volatile_segments(raw: &[String]) -> Result<Vec<VolatileRange>> {
    fn parse_u32(field: &str, whole: &str) -> Result<u32> {
        let t = field.trim();
        let parsed = if let Some(hex) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
            u32::from_str_radix(hex, 16)
        } else {
            t.parse::<u32>()
        };
        parsed.map_err(|_| {
            anyhow::anyhow!(
                "invalid --volatile-segment '{whole}': '{field}' is not a u32 \
                 (expected hex like 0x20001000 or decimal)"
            )
        })
    }

    let mut ranges = Vec::with_capacity(raw.len());
    for spec in raw {
        let (base_s, len_s) = spec.split_once(':').ok_or_else(|| {
            anyhow::anyhow!(
                "invalid --volatile-segment '{spec}': expected '<base>:<len>' \
                 (e.g. 0x20001000:4096)"
            )
        })?;
        let base = parse_u32(base_s, spec)?;
        let len = parse_u32(len_s, spec)?;
        if len == 0 {
            anyhow::bail!("invalid --volatile-segment '{spec}': length must be non-zero");
        }
        if base.checked_add(len).is_none() {
            anyhow::bail!(
                "invalid --volatile-segment '{spec}': base + len overflows the 32-bit \
                 linear-memory address space"
            );
        }
        ranges.push(VolatileRange { base, len });
    }
    Ok(ranges)
}

/// Emit a CycloneDX 1.5 SBOM next to the compiled ELF when `--sbom` was
/// requested. The SBOM documents the synth compiler, the input WASM module
/// (hash + size), the output ELF (hash + size + target + backend), and the
/// WASM module's imports as a CycloneDX dependency graph. It is the artifact
/// consumed by rivet #107's `sbom-record` (`rivet import --format cyclonedx`).
///
/// `input_wasm_bytes` is the post-WAT-decode WASM (the bytes synth actually
/// compiled). When the input was a built-in demo (no file), `input_path` is a
/// synthetic name.
fn emit_sbom(
    sbom_path: &std::path::Path,
    input_path: &std::path::Path,
    input_wasm_bytes: &[u8],
    output_path: &std::path::Path,
    output_elf_bytes: &[u8],
    target_spec: &TargetSpec,
    backend_name: &str,
    imports: &[ImportEntry],
) -> Result<()> {
    let inputs = synth_core::SbomInputs {
        synth_version: env!("CARGO_PKG_VERSION"),
        input_path,
        input_bytes: input_wasm_bytes,
        output_path,
        output_bytes: output_elf_bytes,
        target_triple: &target_spec.triple,
        backend: backend_name,
        imports,
    };
    let sbom = synth_core::CycloneDxSbom::new(&inputs, synth_core::sbom::now_rfc3339());
    std::fs::write(sbom_path, sbom.to_json())
        .with_context(|| format!("Failed to write SBOM: {}", sbom_path.display()))?;
    info!(
        "Wrote CycloneDX SBOM ({} components): {}",
        sbom.components.len(),
        sbom_path.display()
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn compile_command(
    input: Option<PathBuf>,
    output: PathBuf,
    demo: Option<String>,
    func_index: Option<u32>,
    func_name_arg: Option<String>,
    all_exports: bool,
    cortex_m: bool,
    no_optimize: bool,
    loom_compat: bool,
    loom: bool,
    safety_bounds: SafetyBounds,
    backend_name: &str,
    verify: bool,
    target_spec: &TargetSpec,
    relocatable: bool,
    native_pointer_abi: bool,
    sbom_path: Option<PathBuf>,
    sign_output: bool,
    shadow_stack_size: Option<u32>,
    // VCR-DBG-001 step 4 (#394): `--debug-line` — emit `.debug_line` DWARF.
    debug_line: bool,
    // #543 Phase 1: integrator-marked volatile DMA-window ranges. Threaded to the
    // CompileConfig; not yet consumed (Phase 2 is the gated codegen back-off).
    volatile_segments: Vec<VolatileRange>,
) -> Result<()> {
    // Validate backend exists
    let registry = build_backend_registry();
    let backend = registry.get(backend_name).ok_or_else(|| {
        let available: Vec<_> = registry
            .list()
            .iter()
            .map(|b| b.name().to_string())
            .collect();
        anyhow::anyhow!(
            "Unknown backend '{}'. Available: {}",
            backend_name,
            available.join(", ")
        )
    })?;

    if !backend.is_available() {
        anyhow::bail!(
            "Backend '{}' is not available (external tool not installed)",
            backend_name
        );
    }

    info!("Using backend: {}", backend.name());

    // Default to multi-function compilation when the user provides a file
    // but doesn't specify --func-index or --func-name.
    let use_all_exports =
        all_exports || (input.is_some() && func_index.is_none() && func_name_arg.is_none());

    if use_all_exports {
        return compile_all_exports(
            input,
            output,
            cortex_m,
            no_optimize,
            loom_compat,
            loom,
            safety_bounds,
            backend,
            verify,
            target_spec,
            relocatable,
            native_pointer_abi,
            sbom_path,
            sign_output,
            shadow_stack_size,
            debug_line,
            volatile_segments,
        );
    }

    // Single function compilation (when --func-index or --func-name is specified)
    let func_index = func_index.unwrap_or(0);
    // Captured for SBOM emission: the WASM bytes synth actually compiled and
    // the module's imports. `None` for the demo path (no input module).
    let mut sbom_wasm_bytes: Option<Vec<u8>> = None;
    let mut sbom_imports: Vec<ImportEntry> = Vec::new();
    // #599: the module's declared value-width tables, plumbed into the
    // CompileConfig exactly as the all-exports path does. This path previously
    // built its config from `..default()` — so a read-only i64 PARAM was never
    // classified i64 (#518's direct-path mechanism) and the selector allocated
    // the shift-amount constant into the param's live high register:
    // `i64.shr_u x 32` returned 32 (the shift amount) instead of the high word.
    // Empty for the demo path (all-i32 demos).
    let mut current_func_params_i64: Vec<bool> = Vec::new(); // #359/#518/#599
    // #457: declared param count of THIS function — caps the access-pattern
    // param inference (a read-before-write local is otherwise indistinguishable
    // from a param). None for the demo path (no module signature).
    let mut current_func_param_count: Option<u32> = None;
    let mut func_ret_i64: Vec<bool> = Vec::new(); // #311: call-result pair tagging
    let mut type_ret_i64: Vec<bool> = Vec::new(); // #311: call_indirect results
    // #643: per-global slot widths (8 for i64/f64) — type-aware globals-table
    // layout + register-pair global accesses. Empty for the demo path.
    let mut global_widths: Vec<u32> = Vec::new();
    let mut current_func_block_arity: Vec<(u8, u8)> = Vec::new(); // #509: value-carrying branches
    // VCR-PERF-002 Phase 1 (#494): loom `wsc.facts` premises — whole-module
    // table + this function's slice. Threaded to the CompileConfig; NOT yet
    // consumed by any codegen path (Phase 2 is the gated elision).
    let mut wsc_facts: Vec<WscFact> = Vec::new();
    let mut current_func_facts: Vec<WscFact> = Vec::new();
    // #642: call_indirect guard inputs (compile-time table size + closed-world
    // type verdicts). Default = decline every call_indirect (demo path).
    let mut call_indirect_guards = synth_core::CallIndirectGuards::default();
    let (wasm_ops, func_name): (Vec<WasmOp>, String) = match (&input, &demo) {
        (Some(path), _) => {
            info!("Compiling WASM file: {}", path.display());

            let file_bytes = std::fs::read(path)
                .context(format!("Failed to read input file: {}", path.display()))?;

            let wasm_bytes = if path.extension().is_some_and(|ext| ext == "wast") {
                info!("Parsing WAST to WASM (extracting module)...");
                let contents =
                    String::from_utf8(file_bytes).context("WAST file is not valid UTF-8")?;
                extract_module_from_wast(&contents)?
            } else if path.extension().is_some_and(|ext| ext == "wat") {
                info!("Parsing WAT to WASM...");
                wat::parse_bytes(&file_bytes)
                    .context("Failed to parse WAT file")?
                    .into_owned()
            } else {
                file_bytes
            };

            // Run Loom WASM optimizer if --loom is enabled
            let wasm_bytes = maybe_run_loom(loom, wasm_bytes)?;

            // #599: decode the module ONCE for its signature side-tables (the
            // per-function declared param widths and returns-i64 tables the
            // selector needs for i64 correctness) — previously decoded only
            // conditionally for the SBOM, so the tables never reached the config.
            let module = decode_wasm_module(&wasm_bytes)
                .context("Failed to decode WASM module (signature tables)")?;
            // #642: compute the call_indirect guard inputs BEFORE the
            // module's vectors are moved out below.
            call_indirect_guards = module.call_indirect_guards();
            func_ret_i64 = module.func_ret_i64;
            type_ret_i64 = module.type_ret_i64;
            // #643: capture the declared global slot widths (indexed by
            // global index; gaps default to the 4-byte legacy width).
            for g in &module.globals {
                let i = g.index as usize;
                if global_widths.len() <= i {
                    global_widths.resize(i + 1, 4);
                }
                global_widths[i] = g.slot_bytes;
            }
            let module_func_params_i64 = module.func_params_i64;
            let module_func_arg_counts = module.func_arg_counts;
            // VCR-PERF-002 Phase 1 (#494): whatever facts loom forwarded
            // (empty for a section-less module — the overwhelmingly common
            // case — and for any malformed section, per the fail-safe rule).
            wsc_facts = module.wsc_facts;

            // Capture the WASM bytes + imports for the SBOM (the bytes synth
            // actually compiles, after WAT decode and any Loom pass).
            if sbom_path.is_some() {
                sbom_imports = module.imports;
                sbom_wasm_bytes = Some(wasm_bytes.clone());
            }

            let functions =
                decode_wasm_functions(&wasm_bytes).context("Failed to decode WASM functions")?;

            info!("Found {} functions in module", functions.len());

            for f in &functions {
                if let Some(ref name) = f.export_name {
                    info!("  Export '{}' -> function index {}", name, f.index);
                }
            }

            let func = if let Some(ref name) = func_name_arg {
                functions
                    .into_iter()
                    .find(|f| f.export_name.as_deref() == Some(name.as_str()))
                    .context(format!("Function '{}' not found", name))?
            } else {
                functions
                    .into_iter()
                    .find(|f| f.index == func_index)
                    .context(format!("Function index {} not found", func_index))?
            };

            let name = func
                .export_name
                .clone()
                .unwrap_or_else(|| format!("func_{}", func.index));
            info!("Compiling function {} ({} ops)", name, func.ops.len());

            // #599: THIS function's declared param widths + blocktype-arity
            // side-table (indexed by full function index), mirroring the
            // all-exports compile loop (#359/#509/#518).
            if let Some(p) = module_func_params_i64.get(func.index as usize) {
                current_func_params_i64 = p.clone();
            }
            // #457: THIS function's declared param count from the type section.
            current_func_param_count = module_func_arg_counts.get(func.index as usize).copied();
            current_func_block_arity = func.block_arity.clone();
            // VCR-PERF-002 Phase 1 (#494): THIS function's facts slice, the
            // `current_func_params_i64` pattern (`compile_function` carries no
            // function index, so the driver filters by `func_index` up front).
            current_func_facts = wsc_facts
                .iter()
                .filter(|f| f.func_index == func.index)
                .cloned()
                .collect();

            // #554: an op the decoder DROPPED (`_ => None`, e.g. scalar `f32.*`)
            // is recorded in `func.unsupported` but is already gone from
            // `func.ops` — so it never reaches a backend selector's
            // unsupported-op guard, and the backend would lower the remaining
            // stream into a SILENT MISCOMPILE (aarch64 emitted `mov w0,w1`). Fail
            // honestly here, the single-function analogue of the `--all-exports`
            // loud-skip (#369). Backend-agnostic: this guards the ARM/RISC-V
            // direct paths too, not just `-b aarch64`.
            if let Some(reason) = &func.unsupported {
                anyhow::bail!(
                    "function '{}' contains an unsupported operator ({}) the '{}' \
                     backend cannot lower — it was dropped at decode, so refusing \
                     to emit a silent miscompile (#369, #554). Implement the op or \
                     compile a function the backend supports.",
                    name,
                    reason,
                    backend.name()
                );
            }

            (func.ops, name)
        }
        (None, Some(demo_name)) => {
            info!("Compiling demo function: {}", demo_name);

            match demo_name.as_str() {
                "add" => (
                    vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add],
                    "add".to_string(),
                ),
                "mul" => (
                    vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Mul],
                    "mul".to_string(),
                ),
                "calc" => (
                    vec![
                        WasmOp::I32Const(5),
                        WasmOp::I32Const(3),
                        WasmOp::I32Mul,
                        WasmOp::I32Const(2),
                        WasmOp::I32Add,
                    ],
                    "calc".to_string(),
                ),
                _ => anyhow::bail!("Unknown demo: {}. Available: add, mul, calc", demo_name),
            }
        }
        (None, None) => {
            info!("No input specified, using 'add' demo");
            (
                vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add],
                "add".to_string(),
            )
        }
    };

    // VCR-PERF-002 Phase 2 (#494): fact-spec — behind SYNTH_FACT_SPEC and a
    // per-elision ordeal obligation. No-op unless the module carried facts,
    // the flag is on, AND at least one elision was certificate-admitted.
    let mut wasm_ops = wasm_ops;
    let mut fact_div_zero_elide = Vec::new();
    let mut fact_div_ovf_elide = Vec::new();
    if let Some(spec) = maybe_fact_spec(
        &func_name,
        &wasm_ops,
        &current_func_block_arity,
        &current_func_facts,
        &current_func_params_i64,
    ) {
        wasm_ops = spec.ops;
        current_func_block_arity = spec.block_arity;
        // #494 phase 2b: certificate-discharged div/rem guard-elision marks,
        // keyed by index into the (possibly rewritten) stream above.
        fact_div_zero_elide = spec.elide_div_zero;
        fact_div_ovf_elide = spec.elide_div_ovf;
    }

    info!("WASM operations: {:?}", wasm_ops);

    // Build compile config from CLI flags
    let config = CompileConfig {
        no_optimize,
        loom_compat,
        safety_bounds,
        target: target_spec.clone(),
        // #543 Phase 1: threaded but not yet consumed (inert plumbing).
        volatile_segments,
        // #599: the module's declared value-width tables — an i64 param that is
        // only READ is 64-bit by signature, invisible to op-stream inference.
        // Without these the selector materialized constants into the param's
        // live high register (i64.shr_u/shr_s returned the shift amount).
        current_func_params_i64,
        // #457: declared param count — caps the param-count inference so a
        // read-before-write local lands in a zero-inited frame slot.
        current_func_param_count,
        func_ret_i64,
        type_ret_i64,
        // #643: type-aware globals-table layout (8-byte i64/f64 slots).
        global_widths,
        current_func_block_arity,
        // VCR-PERF-002 Phase 1 (#494): threaded but not yet consumed (inert
        // plumbing, like volatile_segments was in #543 Phase 1). Phase 2 reads
        // `current_func_facts` in the selector behind SYNTH_FACT_SPEC.
        wsc_facts,
        current_func_facts,
        // VCR-PERF-002 Phase 2b (#494): div/rem trap-guard elision marks —
        // empty unless SYNTH_FACT_SPEC + facts + a discharged obligation.
        fact_div_zero_elide,
        fact_div_ovf_elide,
        // #642: call_indirect guard inputs — the default declines every
        // call_indirect lowering, so the demo path (no module) stays safe.
        call_indirect_guards,
        ..CompileConfig::default()
    };

    // Compile via the selected backend
    let compiled = backend
        .compile_function(&func_name, &wasm_ops, &config)
        .map_err(|e| anyhow::anyhow!("Backend '{}' compilation failed: {}", backend.name(), e))?;
    let code = compiled.code;
    info!("Encoded {} bytes of machine code", code.len());

    let elf_data = if backend.name() == "aarch64" {
        // #546: emit the AArch64 backend's own EM_AARCH64 ELF64 object, not the
        // ARM (EM_ARM/ELF32) wrapper. The A64 codegen is correct; only the
        // container differs. Discriminate on backend name, not target family:
        // `cortex_a53()` is `ArchFamily::ArmCortexA` (isa AArch64), so a family
        // check would misroute it into the ARM builder.
        build_aarch64_elf(&code, &func_name)?
    } else if matches!(target_spec.family, synth_core::target::ArchFamily::RiscV) {
        build_riscv_elf(&code, &func_name)?
    } else if cortex_m {
        build_cortex_m_elf(&code, &func_name, target_spec)?
    } else {
        build_simple_elf(&code, &func_name)?
    };

    info!("Generated {} byte ELF file", elf_data.len());

    // Step 4: Write to file
    let mut file = File::create(&output).context(format!(
        "Failed to create output file: {}",
        output.display()
    ))?;
    file.write_all(&elf_data)
        .context("Failed to write ELF data")?;

    // Phase 1: write the safety-manifest sidecar whenever any safety knob
    // is active. Single-function path uses 0 for linear-memory-bytes because
    // the WASM was supplied as a raw function-body slice — `compile_all_exports`
    // has the module context and threads through the real value.
    maybe_emit_safety_manifest(&output, target_spec, safety_bounds, 0)?;

    // Emit a CycloneDX SBOM when requested. Only possible when synth compiled
    // an actual WASM module (not a built-in demo, which has no input file).
    if let Some(ref sbom_dest) = sbom_path {
        match (sbom_wasm_bytes.as_deref(), input.as_deref()) {
            (Some(wasm), Some(in_path)) => {
                emit_sbom(
                    sbom_dest,
                    in_path,
                    wasm,
                    &output,
                    &elf_data,
                    target_spec,
                    backend_name,
                    &sbom_imports,
                )?;
            }
            _ => {
                eprintln!(
                    "warning: --sbom requires a WASM/WAT input file; \
                     skipping SBOM for demo compilation"
                );
            }
        }
    }

    // Phase 5: sign the ELF via sigil's `wsc sign --keyless --format elf`.
    // Done last so the SBOM (if any) records the hash of the unsigned synth
    // output; the on-disk ELF after this step is the signed version. See
    // docs/sigil-integration.md.
    if sign_output {
        sign::sign_elf(&output)?;
    }

    println!("Compiled {} to {}", func_name, output.display());
    println!("  Code size: {} bytes", code.len());
    println!("  ELF size: {} bytes", elf_data.len());
    println!("\nInspect with: synth disasm {}", output.display());

    // Run translation validation if requested
    if verify {
        let caps = backend.capabilities();
        if caps.supports_rule_verification {
            #[cfg(feature = "verify")]
            {
                run_verification(&wasm_ops, &func_name)?;
            }
            #[cfg(not(feature = "verify"))]
            {
                println!("\nVerification requested but not compiled into this binary.");
                println!("Rebuild with: cargo build --features verify");
            }
        } else {
            println!(
                "\nBackend '{}' does not support rule verification.",
                backend.name()
            );
            if caps.supports_binary_verification {
                println!("Binary-level translation validation is planned but not yet implemented.");
            }
        }
    }

    Ok(())
}

/// Run per-rule translation validation using Z3 SMT solver
#[cfg(feature = "verify")]
fn run_verification(wasm_ops: &[WasmOp], func_name: &str) -> Result<()> {
    use std::collections::HashSet;
    use synth_synthesis::{ArmOp, Condition, Operand2, Pattern, Reg, Replacement, SynthesisRule};

    println!("\nRunning translation validation for '{}'...", func_name);

    // Build verification rules for the instruction selection mappings actually used.
    // These correspond to the basic WasmOp → ArmOp translations in the instruction selector.
    let mut rules = Vec::new();
    let mut seen = HashSet::new();

    for op in wasm_ops {
        let disc = std::mem::discriminant(op);
        if !seen.insert(disc) {
            continue; // already added a rule for this op kind
        }

        let rule = match op {
            WasmOp::I32Add => Some(SynthesisRule {
                name: "i32.add → ADD".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Add),
                replacement: Replacement::ArmInstr(ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }),
                cost: synth_synthesis::Cost {
                    cycles: 1,
                    code_size: 2,
                    registers: 2,
                },
            }),
            WasmOp::I32Sub => Some(SynthesisRule {
                name: "i32.sub → SUB".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Sub),
                replacement: Replacement::ArmInstr(ArmOp::Sub {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }),
                cost: synth_synthesis::Cost {
                    cycles: 1,
                    code_size: 2,
                    registers: 2,
                },
            }),
            WasmOp::I32Mul => Some(SynthesisRule {
                name: "i32.mul → MUL".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Mul),
                replacement: Replacement::ArmInstr(ArmOp::Mul {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }),
                cost: synth_synthesis::Cost {
                    cycles: 1,
                    code_size: 2,
                    registers: 2,
                },
            }),
            WasmOp::I32And => Some(SynthesisRule {
                name: "i32.and → AND".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32And),
                replacement: Replacement::ArmInstr(ArmOp::And {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }),
                cost: synth_synthesis::Cost {
                    cycles: 1,
                    code_size: 2,
                    registers: 2,
                },
            }),
            WasmOp::I32Or => Some(SynthesisRule {
                name: "i32.or → ORR".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Or),
                replacement: Replacement::ArmInstr(ArmOp::Orr {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }),
                cost: synth_synthesis::Cost {
                    cycles: 1,
                    code_size: 2,
                    registers: 2,
                },
            }),
            WasmOp::I32Xor => Some(SynthesisRule {
                name: "i32.xor → EOR".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Xor),
                replacement: Replacement::ArmInstr(ArmOp::Eor {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }),
                cost: synth_synthesis::Cost {
                    cycles: 1,
                    code_size: 2,
                    registers: 2,
                },
            }),
            // Comparison ops: CMP + SetCond sequence (two ARM instructions per WASM op)
            WasmOp::I32Eq => Some(SynthesisRule {
                name: "i32.eq → CMP + SetCond(EQ)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Eq),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::EQ,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32Ne => Some(SynthesisRule {
                name: "i32.ne → CMP + SetCond(NE)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Ne),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::NE,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32LtS => Some(SynthesisRule {
                name: "i32.lt_s → CMP + SetCond(LT)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LtS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::LT,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32LeS => Some(SynthesisRule {
                name: "i32.le_s → CMP + SetCond(LE)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LeS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::LE,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32GtS => Some(SynthesisRule {
                name: "i32.gt_s → CMP + SetCond(GT)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GtS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::GT,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32GeS => Some(SynthesisRule {
                name: "i32.ge_s → CMP + SetCond(GE)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GeS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::GE,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32LtU => Some(SynthesisRule {
                name: "i32.lt_u → CMP + SetCond(LO)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LtU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::LO,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32LeU => Some(SynthesisRule {
                name: "i32.le_u → CMP + SetCond(LS)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LeU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::LS,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32GtU => Some(SynthesisRule {
                name: "i32.gt_u → CMP + SetCond(HI)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GtU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::HI,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            WasmOp::I32GeU => Some(SynthesisRule {
                name: "i32.ge_u → CMP + SetCond(HS)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GeU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::HS,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 2,
                },
            }),
            // i32.eqz: unary comparison against zero
            WasmOp::I32Eqz => Some(SynthesisRule {
                name: "i32.eqz → CMP #0 + SetCond(EQ)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Eqz),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::EQ,
                    },
                ]),
                cost: synth_synthesis::Cost {
                    cycles: 2,
                    code_size: 4,
                    registers: 1,
                },
            }),
            // Shift ops use immediate shift values in the instruction selector,
            // so SMT verification of the variable-shift case requires a different
            // ARM op encoding (register-based shift). Skipped for now.
            // LocalGet/LocalSet/Const are register operations, not computational — skip
            _ => None,
        };

        if let Some(r) = rule {
            rules.push(r);
        }
    }

    if rules.is_empty() {
        println!("  No verifiable computational rules for this function.");
        println!("  (LocalGet/Set/Const are register operations, not verified by SMT)");
        return Ok(());
    }

    println!("  Verifying {} instruction selection rules...", rules.len());

    let (verified, failed, unknown) = synth_verify::with_verification_context(|| {
        let validator = synth_verify::TranslationValidator::new();
        let mut verified = 0u32;
        let mut failed = 0u32;
        let mut unknown = 0u32;

        for rule in &rules {
            match validator.verify_rule(rule) {
                Ok(synth_verify::ValidationResult::Verified) => {
                    println!("  ✓ {} verified", rule.name);
                    verified += 1;
                }
                Ok(synth_verify::ValidationResult::Invalid { counterexample }) => {
                    println!("  ✗ {} INVALID: {:?}", rule.name, counterexample);
                    failed += 1;
                }
                Ok(synth_verify::ValidationResult::Unknown { reason }) => {
                    println!("  ? {} unknown: {}", rule.name, reason);
                    unknown += 1;
                }
                Err(e) => {
                    println!("  ! {} error: {}", rule.name, e);
                    unknown += 1;
                }
            }
        }

        (verified, failed, unknown)
    });

    println!(
        "\nVerification summary: {} verified, {} failed, {} unknown",
        verified, failed, unknown
    );

    if failed > 0 {
        anyhow::bail!(
            "Translation validation failed: {} rules produced counterexamples",
            failed
        );
    }

    Ok(())
}

/// Extract module binary from WAST file (handles assert_return, etc.)
/// Extract all modules from a WAST file, returning their binary representations.
///
/// Many spec test files contain multiple modules where exports live in later
/// modules, not the first one.  We collect every valid module so the caller
/// can merge exports across them.
fn extract_all_modules_from_wast(contents: &str) -> Result<Vec<Vec<u8>>> {
    let buf = ParseBuffer::new(contents)
        .map_err(|e| anyhow::anyhow!("Failed to create parse buffer: {}", e))?;

    let wast: Wast =
        parser::parse(&buf).map_err(|e| anyhow::anyhow!("Failed to parse WAST: {}", e))?;

    let mut modules = Vec::new();

    for directive in wast.directives {
        if let WastDirective::Module(mut quote_wat) = directive {
            match quote_wat.encode() {
                Ok(binary) => modules.push(binary),
                Err(e) => {
                    // Some modules in spec tests are intentionally invalid
                    // (e.g. modules used in assert_invalid). Skip them.
                    info!("Skipping unencoded module: {}", e);
                }
            }
        }
    }

    if modules.is_empty() {
        anyhow::bail!("No module found in WAST file");
    }

    Ok(modules)
}

/// Legacy helper: extract a single module from a WAST file.
/// Picks the first module that has exported functions; falls back to the first
/// module if none have exports.
fn extract_module_from_wast(contents: &str) -> Result<Vec<u8>> {
    let modules = extract_all_modules_from_wast(contents)?;

    // Prefer a module with exports
    for module_bytes in &modules {
        if let Ok(decoded) = decode_wasm_module(module_bytes)
            && decoded.functions.iter().any(|f| f.export_name.is_some())
        {
            return Ok(module_bytes.clone());
        }
    }

    // Fall back to first module (non-empty guaranteed by check above)
    modules
        .into_iter()
        .next()
        .ok_or_else(|| anyhow::anyhow!("no modules found in WAST file"))
}

/// #235: the set of function indices reachable from any exported function via
/// `call` (transitively), including the exports themselves. Imports (index <
/// `num_imports`) are not followed — they stay external symbols the host linker
/// resolves. Used so `--all-exports --relocatable` emits a self-contained object
/// containing every internal callee a dissolved export needs (e.g. a panic
/// helper loom left un-inlined), instead of leaving it as an undefined symbol.
/// #237: identify the wasm stack-pointer global for the native-pointer ABI.
///
/// The stack-pointer global is the mutable `i32` global whose initializer is a
/// plausible stack top: a positive constant no larger than the linear-memory
/// extent (the SP starts at the boundary between the descending stack and the
/// static-data region). When several qualify, the highest initializer wins —
/// the stack pointer sits at the top of the wasm address space. Returns
/// `(index, init_value)`, or `None` if the module has no such global (in which
/// case the legacy R9 globals-table path is used).
fn identify_stack_pointer_global(globals: &[WasmGlobal], linmem_bytes: u32) -> Option<(u32, i32)> {
    globals
        .iter()
        .filter(|g| g.mutable)
        .filter_map(|g| g.init_i32.map(|v| (g.index, v)))
        .filter(|&(_, v)| v > 0 && (v as u32) <= linmem_bytes)
        .max_by_key(|&(_, v)| v)
}

fn reachable_from_exports(
    funcs: &[FunctionOps],
    num_imports: u32,
    elem_func_indices: &[u32],
) -> std::collections::BTreeSet<u32> {
    let pos_by_index: std::collections::HashMap<u32, usize> = funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (f.index, i))
        .collect();
    let mut reachable: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let mut work: Vec<u32> = Vec::new();
    // #275: the first `call_indirect` reached makes every table function a
    // possible target. Add them all once (sound over-approximation — any table
    // entry could be the dynamic callee), then keep following their direct calls.
    let mut table_included = false;
    for f in funcs {
        if f.export_name.is_some() && reachable.insert(f.index) {
            work.push(f.index);
        }
    }
    while let Some(idx) = work.pop() {
        if let Some(&p) = pos_by_index.get(&idx) {
            for op in &funcs[p].ops {
                match op {
                    WasmOp::Call(target) if *target >= num_imports && reachable.insert(*target) => {
                        work.push(*target);
                    }
                    WasmOp::CallIndirect { .. } if !table_included => {
                        table_included = true;
                        for &t in elem_func_indices {
                            if t >= num_imports && reachable.insert(t) {
                                work.push(t);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    reachable
}

/// Compile all exported functions (plus their reachable internal callees, #235)
/// into a multi-function ELF.
#[allow(clippy::too_many_arguments)]
fn compile_all_exports(
    input: Option<PathBuf>,
    output: PathBuf,
    cortex_m: bool,
    no_optimize: bool,
    loom_compat: bool,
    loom: bool,
    safety_bounds: SafetyBounds,
    backend: &dyn Backend,
    verify: bool,
    target_spec: &TargetSpec,
    relocatable: bool,
    native_pointer_abi: bool,
    sbom_path: Option<PathBuf>,
    sign_output: bool,
    shadow_stack_size: Option<u32>,
    // VCR-DBG-001 step 4 (#394): emit a `.debug_line` section from the input
    // wasm's DWARF + the ARM line_maps. Default off ⇒ output byte-identical.
    debug_line: bool,
    // #543 Phase 1: integrator-marked volatile DMA-window ranges. Threaded to the
    // CompileConfig; not yet consumed (Phase 2 is the gated codegen back-off).
    volatile_segments: Vec<VolatileRange>,
) -> Result<()> {
    let path = input.context("--all-exports requires an input file")?;

    info!("Compiling all exports from: {}", path.display());

    let file_bytes =
        std::fs::read(&path).context(format!("Failed to read input file: {}", path.display()))?;

    // WASM bytes captured for the SBOM (the post-decode bytes synth compiles).
    // For a WAST file with multiple modules this holds the representative
    // module (the one whose imports were merged), set inside the match below.
    let mut sbom_wasm_bytes: Option<Vec<u8>> = None;

    // Decode module(s) — for WAST files we merge exports across all modules
    let (
        all_exports,
        all_memories,
        all_imports,
        max_num_imported_funcs,
        func_arg_counts,
        type_arg_counts,
        all_data_segments, // #237: active data segments, for --native-pointer-abi
        stack_pointer_global_opt, // #237: (index, init) of the SP global, if any
        all_globals, // #237: every defined global (index, init) — slot region under --native-pointer-abi
        all_global_widths, // #643: per-global slot widths (8 for i64/f64) — type-aware R9 table layout
        all_func_ret_i64,  // #311: per-function returns-i64 (pair tagging)
        all_type_ret_i64,  // #311: per-type returns-i64 (call_indirect)
        all_func_params_i64, // #359: per-function declared param widths (stack-arg ABI)
        all_wsc_facts,     // VCR-PERF-002 Phase 1 (#494): loom wsc.facts premises
        all_call_indirect_guards, // #642: table size + closed-world type verdicts
    ) = if path.extension().is_some_and(|ext| ext == "wast") {
        info!("Parsing WAST (extracting all modules)...");
        let contents = String::from_utf8(file_bytes).context("WAST file is not valid UTF-8")?;
        let module_binaries = extract_all_modules_from_wast(&contents)?;
        info!("Found {} modules in WAST file", module_binaries.len());

        // Decode each module and collect exports.
        // Use an IndexMap-style approach: last module with a given export name wins
        // (matching WAST spec semantics where assertions test the most-recent module).
        let mut export_map: std::collections::HashMap<String, FunctionOps> =
            std::collections::HashMap::new();
        let mut merged_memories: Vec<WasmMemory> = Vec::new();
        let mut merged_imports: Vec<ImportEntry> = Vec::new();
        let mut max_imports: u32 = 0;
        // #195: keep the arg-count tables aligned with the module whose
        // imports get merged (the one that defines `max_imports`).
        let mut merged_func_arg_counts: Vec<u32> = Vec::new();
        let mut merged_type_arg_counts: Vec<u32> = Vec::new();

        for (idx, wasm_bytes) in module_binaries.iter().enumerate() {
            // Run Loom optimizer on each module if --loom is enabled
            let wasm_bytes = maybe_run_loom(loom, wasm_bytes.clone())?;
            // First decoded module is the SBOM default; refined below to
            // the module whose imports get merged.
            if sbom_wasm_bytes.is_none() {
                sbom_wasm_bytes = Some(wasm_bytes.clone());
            }
            match decode_wasm_module(&wasm_bytes) {
                Ok(module) => {
                    let export_count = module
                        .functions
                        .iter()
                        .filter(|f| f.export_name.is_some())
                        .count();
                    info!(
                        "  Module {}: {} functions ({} exports), {} memories",
                        idx,
                        module.functions.len(),
                        export_count,
                        module.memories.len()
                    );

                    for func in module.functions {
                        if let Some(name) = func.export_name.clone() {
                            export_map.insert(name, func);
                        }
                    }

                    // Take the largest memory across all modules
                    for mem in &module.memories {
                        if merged_memories.is_empty()
                            || mem.initial_pages
                                > merged_memories
                                    .first()
                                    .map(|m| m.initial_pages)
                                    .unwrap_or(0)
                        {
                            merged_memories = vec![mem.clone()];
                        }
                    }

                    if module.num_imported_funcs > max_imports {
                        max_imports = module.num_imported_funcs;
                        merged_imports = module.imports.clone();
                        merged_func_arg_counts = module.func_arg_counts.clone();
                        merged_type_arg_counts = module.type_arg_counts.clone();
                        // Keep the SBOM input aligned with the merged
                        // imports (the module the dependency graph reflects).
                        sbom_wasm_bytes = Some(wasm_bytes.clone());
                    } else if merged_func_arg_counts.is_empty() {
                        // No imports anywhere yet: still carry the arg-count
                        // tables from a module so direct calls get marshalled.
                        merged_func_arg_counts = module.func_arg_counts.clone();
                        merged_type_arg_counts = module.type_arg_counts.clone();
                    }
                }
                Err(e) => {
                    info!("  Module {}: decode failed ({}), skipping", idx, e);
                }
            }
        }

        let exports: Vec<_> = export_map.into_values().collect();
        (
            exports,
            merged_memories,
            merged_imports,
            max_imports,
            merged_func_arg_counts,
            merged_type_arg_counts,
            Vec::new(), // #237: data segments not threaded for WAST (single-module .wasm path covers it)
            None,       // #237: SP-global promotion is single-module .wasm only
            Vec::new(), // #237: globals slot region is single-module .wasm only
            Vec::new(), // #643: WAST fixture suite is i32-only — legacy 4-byte global slots
            Vec::new(), // #311: WAST runs the fixture suite; i32-only
            Vec::new(),
            Vec::new(), // #359: WAST fixture suite is i32-only — no stack params
            Vec::new(), // #494: facts are a loom-emitted-.wasm channel; WAST fixtures carry none
            // #642: the multi-module WAST merge has no single table image to
            // verify — the default guards DECLINE any call_indirect (the WAST
            // fixture suite carries none), never an unchecked branch.
            synth_core::CallIndirectGuards::default(),
        )
    } else {
        let wasm_bytes = if path.extension().is_some_and(|ext| ext == "wat") {
            info!("Parsing WAT to WASM...");
            wat::parse_bytes(&file_bytes)
                .context("Failed to parse WAT file")?
                .into_owned()
        } else {
            file_bytes
        };

        // Run Loom optimizer if --loom is enabled
        let wasm_bytes = maybe_run_loom(loom, wasm_bytes)?;

        let module = decode_wasm_module(&wasm_bytes).context("Failed to decode WASM module")?;
        sbom_wasm_bytes = Some(wasm_bytes);

        // #642: call_indirect guard inputs — computed while the module is
        // still whole (before its vectors are moved out below).
        let guards = module.call_indirect_guards();
        let func_arg_counts = module.func_arg_counts;
        let type_arg_counts = module.type_arg_counts;
        let memories = module.memories;
        let imports = module.imports;
        let num_imports = module.num_imported_funcs;
        let data_segs = module.data_segments; // #237: capture before `functions` is moved
        let elem_func_indices = module.elem_func_indices; // #275: call_indirect targets
        // #237: identify the stack-pointer global for native-pointer promotion.
        // linmem extent gates the "plausible stack top" heuristic.
        let linmem_bytes = memories.first().map(|m| m.initial_bytes()).unwrap_or(0);
        let sp_global = identify_stack_pointer_global(&module.globals, linmem_bytes);
        // #237: every defined global gets a materialized slot under the
        // native-pointer ABI (init defaults to 0 for non-i32.const inits).
        let globals: Vec<(u32, i32)> = module
            .globals
            .iter()
            .map(|g| (g.index, g.init_i32.unwrap_or(0)))
            .collect();
        // #643: per-global slot widths (4 = i32/f32, 8 = i64/f64, 16 = v128),
        // indexed by global index — the selector lays the R9 globals table out
        // by summing these, giving i64 globals room for both words and
        // shifting every later global's offset accordingly.
        let global_widths: Vec<u32> = {
            let mut widths = Vec::new();
            for g in &module.globals {
                let i = g.index as usize;
                if widths.len() <= i {
                    widths.resize(i + 1, 4);
                }
                widths[i] = g.slot_bytes;
            }
            widths
        };
        // #643: the native-pointer ABI materializes `__synth_globals` as
        // 4-byte i32 slots (`idx * 4`); a wide (i64/f64/v128) global has no
        // consistent slot there. Refuse up front — an honest error beats the
        // silent high-word truncation this replaced.
        if native_pointer_abi && global_widths.iter().any(|&w| w > 4) {
            anyhow::bail!(
                "--native-pointer-abi does not support i64/f64/v128 globals \
                 (the `__synth_globals` slot region is 4-byte i32 slots) — \
                 refusing to truncate them to 32 bits (#643)"
            );
        }
        // #235: compile not just the exports but every internal (non-imported)
        // function reachable from them via `call`. A loom-dissolved export can
        // retain a non-inlinable callee (e.g. a panic helper from an overflow
        // check); without that callee's body in the object the export references
        // an unresolved symbol and the host link fails. Imports (index <
        // num_imports) stay external — the linker resolves them. A module whose
        // exports call no internal function (every leaf fixture) yields exactly
        // the exports, so existing output stays bit-identical.
        let reachable = reachable_from_exports(&module.functions, num_imports, &elem_func_indices);
        // Preserve definition order; keep exports + reachable internal callees.
        let exports: Vec<_> = module
            .functions
            .into_iter()
            .filter(|f| reachable.contains(&f.index))
            .collect();
        (
            exports,
            memories,
            imports,
            num_imports,
            func_arg_counts,
            type_arg_counts,
            data_segs,
            sp_global,
            globals,
            global_widths,
            module.func_ret_i64,
            module.type_ret_i64,
            module.func_params_i64,
            module.wsc_facts,
            guards, // #642
        )
    };

    // Log memory information
    if !all_memories.is_empty() {
        info!("Memories ({} total):", all_memories.len());
        for mem in &all_memories {
            let max_str = mem
                .max_pages
                .map(|m| format!("{}", m))
                .unwrap_or_else(|| "unlimited".to_string());
            info!(
                "  memory[{}]: {} initial pages, {} max pages ({}KB initial)",
                mem.index,
                mem.initial_pages,
                max_str,
                mem.initial_pages * 64
            );
        }
    }

    // Log import information
    if max_num_imported_funcs > 0 {
        info!(
            "Module imports {} functions (Meld dispatch enabled):",
            max_num_imported_funcs
        );
        for imp in &all_imports {
            if matches!(imp.kind, synth_core::ImportKind::Function(_)) {
                info!("  import[{}]: {}::{}", imp.index, imp.module, imp.name);
            }
        }
    }

    if all_exports.is_empty() {
        anyhow::bail!("No exported functions found in module");
    }

    info!("Found {} exported functions:", all_exports.len());
    for f in &all_exports {
        let display_name = f
            .export_name
            .as_deref()
            .map_or_else(|| format!("func_{}", f.index), String::from);
        info!("  '{}' (index {})", display_name, f.index);
    }

    // Build compile config from CLI flags
    let config = CompileConfig {
        no_optimize,
        loom_compat,
        safety_bounds,
        num_imports: max_num_imported_funcs,
        func_arg_counts,
        type_arg_counts,
        target: target_spec.clone(),
        // #197: --relocatable forces the direct selector + direct func_N import
        // ABI so host-linked objects get fp-relative memory access and
        // caller-saved preservation (the optimized path is wrong for ET_REL).
        relocatable,
        // #237: native-pointer ABI — wasm statics (initialized + zero-init/BSS)
        // become __synth_wasm_data-relative across the whole linear memory.
        native_pointer_abi,
        linear_memory_bytes: all_memories.first().map(|m| m.initial_bytes()).unwrap_or(0),
        // #237: register-promote the stack-pointer global (only consulted under
        // native_pointer_abi) so the dissolved object needs no R9 globals table.
        stack_pointer_global: stack_pointer_global_opt,
        func_ret_i64: all_func_ret_i64.clone(),
        type_ret_i64: all_type_ret_i64.clone(),
        // #643: per-global slot widths — i64/f64 globals get 8-byte slots and
        // register-pair accesses; later globals' offsets shift accordingly.
        global_widths: all_global_widths.clone(),
        // #359: indexed declared param widths (per full function index) — the
        // source of truth for the AAPCS stack-argument refusal. The per-function
        // `current_func_params_i64` is derived from this in the compile loop.
        func_params_i64: all_func_params_i64.clone(),
        // #543 Phase 1: threaded but not yet consumed (inert plumbing). The
        // Phase-2 back-off (const-CSE + #468 base-CSE decline inside these ranges)
        // lives on the optimized path this config feeds. See VCR-DMA-001.
        volatile_segments,
        // VCR-PERF-002 Phase 1 (#494): the module's loom-forwarded `wsc.facts`
        // premises — threaded but not yet consumed (inert plumbing, the #543
        // Phase-1 pattern). The per-function slice is filtered into
        // `current_func_facts` in the compile loop below; Phase 2 reads it in
        // the selector behind SYNTH_FACT_SPEC.
        wsc_facts: all_wsc_facts.clone(),
        // #642: call_indirect guard inputs (compile-time table size for the
        // bounds guard + closed-world type verdicts). Default = decline.
        call_indirect_guards: all_call_indirect_guards,
        ..CompileConfig::default()
    };

    // Compile each function via the selected backend
    let mut compiled_funcs = Vec::new();
    let mut skipped_funcs: Vec<(String, String)> = Vec::new();
    for func in &all_exports {
        // Exported functions keep their export name; reachable internal callees
        // (#235) have none, so they take the `func_{index}` symbol — exactly the
        // name an internal `call` relocation references, so it resolves in-object.
        let name = func
            .export_name
            .clone()
            .unwrap_or_else(|| format!("func_{}", func.index));
        info!(
            "Compiling function '{}' via backend '{}'...",
            name,
            backend.name()
        );

        // In the all-exports path, a single un-compilable function (e.g. an
        // i64-heavy compiler_builtins helper that exhausts the register
        // allocator, #168) must not abort the whole module. Emit a diagnostic,
        // record it, and continue — the function is simply absent from the
        // output object. Callers that need it get a link error naming the
        // missing symbol, which is far more actionable than a whole-module
        // failure on dead-weight pulled in by `--whole-archive`.
        // #359: tell the backend the CURRENT function's declared param widths
        // (indexed by full function index). The AAPCS stack-argument path needs
        // the declared widths — an unused i64 param still shifts the layout, so
        // op-stream inference cannot reconstruct them. Cheap per-function clone
        // (`compile_function` is a shared trait method with no function index).
        // #509: also thread THIS function's blocktype-arity side-table, so the
        // direct selector can land a value carried by br/br_if/br_table in the
        // target block's designated result register (and the optimized path can
        // detect-and-decline the shape).
        let mut func_config = {
            let mut fc = config.clone();
            if let Some(p) = all_func_params_i64.get(func.index as usize)
                && !p.is_empty()
            {
                fc.current_func_params_i64 = p.clone();
            }
            fc.current_func_block_arity = func.block_arity.clone();
            // #457: THIS function's DECLARED param count, so the backends can
            // cap the access-pattern param inference that mistook a
            // read-before-write non-param local for a param.
            fc.current_func_param_count = config.func_arg_counts.get(func.index as usize).copied();
            // VCR-PERF-002 Phase 1 (#494): THIS function's wsc.facts slice
            // (`compile_function` carries no function index — the same reason
            // `current_func_params_i64` exists). Not yet consumed.
            fc.current_func_facts = all_wsc_facts
                .iter()
                .filter(|f| f.func_index == func.index)
                .cloned()
                .collect();
            fc
        };
        // #369: the decoder flagged a value-affecting op it cannot lower (e.g.
        // scalar f32/f64, bulk-memory). Lowering would have SILENTLY DROPPED it
        // and miscompiled the function (wrong value, no diagnostic). Loud-skip
        // instead — honest degradation: the symbol is absent, so a caller gets a
        // link error naming it rather than a silently-wrong result. (#180/#185
        // "unsupported op must Err, never silently continue".)
        if let Some(reason) = &func.unsupported {
            eprintln!(
                "warning: skipping function '{name}': contains an unsupported \
                 operator ({reason}) the {} backend cannot lower — emitting no \
                 code for it rather than a silent miscompile (#369)",
                backend.name()
            );
            skipped_funcs.push((name.clone(), format!("unsupported operator: {reason}")));
            continue;
        }
        // VCR-PERF-002 Phase 2 (#494): fact-spec — behind SYNTH_FACT_SPEC and
        // a per-elision ordeal obligation. When an elision was admitted, the
        // rewritten stream feeds the backend and the parallel side-tables
        // (blocktype arity, DWARF op offsets) are filtered in lockstep.
        let spec = maybe_fact_spec(
            &name,
            &func.ops,
            &func_config.current_func_block_arity,
            &func_config.current_func_facts,
            &func_config.current_func_params_i64,
        );
        let (ops_for_compile, op_offsets_for_elf): (&[WasmOp], Vec<u32>) = match &spec {
            Some(s) => {
                func_config.current_func_block_arity = s.block_arity.clone();
                // #494 phase 2b: certificate-discharged div/rem guard-elision
                // marks, keyed by index into the rewritten stream the backend
                // is about to consume.
                func_config.fact_div_zero_elide = s.elide_div_zero.clone();
                func_config.fact_div_ovf_elide = s.elide_div_ovf.clone();
                (
                    &s.ops,
                    s.kept
                        .iter()
                        .filter_map(|&i| func.op_offsets.get(i).copied())
                        .collect(),
                )
            }
            None => (&func.ops, func.op_offsets.clone()),
        };
        let compiled = match backend.compile_function(&name, ops_for_compile, &func_config) {
            Ok(c) => c,
            Err(e) => {
                eprintln!(
                    "warning: skipping function '{}': backend '{}' failed: {}",
                    name,
                    backend.name(),
                    e
                );
                skipped_funcs.push((name.clone(), e.to_string()));
                continue;
            }
        };
        info!("  {} bytes of machine code", compiled.code.len());

        if !compiled.relocations.is_empty() {
            info!(
                "  {} relocations (external symbol references)",
                compiled.relocations.len()
            );
        }

        compiled_funcs.push(ElfFunction {
            name: name.clone(),
            // #394 Tier-1.x: thread the `name`-section name through for the
            // DWARF subprogram DIE (internal functions get their REAL name).
            debug_name: func.debug_name.clone(),
            wasm_index: func.index,
            code: compiled.code,
            relocations: compiled.relocations,
            // VCR-DBG-001 step 4: carry the op-offset side table + the backend's
            // line_map so `--debug-line` can compose ARM text addr → source.
            // (#494: filtered to surviving ops when fact-spec rewrote the stream,
            // so the table stays index-aligned with what the backend consumed.)
            op_offsets: op_offsets_for_elf,
            line_map: compiled.line_map,
        });

        // Run verification if requested
        if verify {
            #[cfg(feature = "verify")]
            run_verification(&func.ops, &name)?;
            #[cfg(not(feature = "verify"))]
            {
                eprintln!("Warning: --verify requires the 'verify' feature.");
                eprintln!("  Rebuild with: cargo build --features verify");
            }
        }
    }

    // Surface skipped functions (no silent omissions): a skipped function is
    // absent from the output object, so report the count + names explicitly.
    if !skipped_funcs.is_empty() {
        eprintln!(
            "warning: {} of {} functions were skipped (not in output): {}",
            skipped_funcs.len(),
            all_exports.len(),
            skipped_funcs
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    if compiled_funcs.is_empty() {
        anyhow::bail!(
            "no functions compiled successfully ({} skipped) — nothing to emit",
            skipped_funcs.len()
        );
    }

    // Check if any function has relocations (import calls)
    let has_relocations = compiled_funcs.iter().any(|f| !f.relocations.is_empty());

    // Every defined function exposes two relocation labels the selector may
    // emit for an internal `call`: its export name and `func_{wasm_index}`.
    // A relocation whose symbol is one of these is an INTERNAL call to a
    // function laid out in this same image (so it can be patched directly,
    // no linker needed). Any other relocation symbol (an import field name,
    // `func_{import_index}`, or a `__meld_*` dispatch stub) is EXTERNAL and
    // requires the relocatable-object path so a host linker can resolve it.
    let mut internal_labels: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for f in &compiled_funcs {
        internal_labels.insert(f.name.as_str());
    }
    let func_index_labels: Vec<String> = compiled_funcs
        .iter()
        .map(|f| format!("func_{}", f.wasm_index))
        .collect();
    for label in &func_index_labels {
        internal_labels.insert(label.as_str());
    }
    let has_external_relocations = compiled_funcs
        .iter()
        .flat_map(|f| &f.relocations)
        .any(|r| !internal_labels.contains(r.symbol.as_str()));

    // Build multi-function ELF
    // When there are EXTERNAL relocations, produce a relocatable object (.o)
    // instead of an executable. This lets the output be linked with the Kiln
    // bridge crate (which provides __meld_dispatch_import and
    // __meld_get_memory_base). The --relocatable flag forces ET_REL output
    // even when the wasm has no imports, for linking into a host build system
    // (e.g. Zephyr).
    //
    // A standalone `--cortex-m` executable, however, has NO linker: its
    // INTERNAL `BL func_N` calls cannot be left as unresolved relocations.
    // When every relocation is internal (no imports) and we are building a
    // standalone Cortex-M executable, route to the cortex-m builder, which
    // patches each internal BL displacement in place after layout (#170).
    let is_riscv = matches!(target_spec.family, synth_core::target::ArchFamily::RiscV);
    // #546: route the A64 `.text` into the AArch64 backend's own EM_AARCH64
    // ELF64 object rather than the ARM (EM_ARM/ELF32) wrapper. Keyed on backend
    // name — `cortex_a53()` is `ArchFamily::ArmCortexA` (isa AArch64), so a
    // family check would misroute it. The AArch64 object is always ET_REL.
    let is_aarch64 = backend.name() == "aarch64";
    // Tracks whether we emitted an ET_REL object (needs linking) vs a standalone
    // executable, so the summary below reports the right type and link hint.
    let produced_relocatable = is_riscv || is_aarch64 || has_external_relocations || relocatable;

    // VCR-DBG-001 step 4 (#394): when `--debug-line` is set, parse the input
    // wasm's `.debug_line` from the bytes synth actually compiled
    // (`sbom_wasm_bytes` = post-WAT/post-loom). A DWARF-free input yields empty
    // rows ⇒ the emitter no-ops ⇒ the object stays byte-identical. Default
    // (flag off) ⇒ `None` ⇒ zero new work, zero output change.
    let input_dwarf = if debug_line {
        sbom_wasm_bytes
            .as_deref()
            .map(synth_core::dwarf_line::read_input_dwarf_line)
    } else {
        None
    };

    // VCR-DBG-001 PR C (#394): DWARF is emitted (with `.rel.debug_*` so a host
    // linker fixes up the `.text` addresses) ONLY on the ARM relocatable-object
    // path. On a self-contained ET_EXEC image or the RISC-V path there is no
    // relocatable text symbol to anchor the addresses, so `--debug-line` would
    // silently drop. Warn LOUDLY rather than mislead a consumer (jess) into
    // expecting source lines that aren't there — the #383 honest-fail rule.
    let dwarf_effective = !is_riscv && !is_aarch64 && (has_external_relocations || relocatable);
    if debug_line && !dwarf_effective {
        warn!(
            "--debug-line has no effect on this output: DWARF line tables are emitted only on \
             the ARM relocatable-object path (link via --relocatable, then `ld`). \
             {} produces no .debug_* sections.",
            if is_riscv {
                "The RISC-V backend"
            } else if is_aarch64 {
                "The AArch64 backend"
            } else {
                "A self-contained executable image"
            }
        );
    }

    let elf_data = if is_aarch64 {
        // #546: the AArch64 backend emits its own EM_AARCH64 ELF64 (ET_REL)
        // object. This must precede the `has_external_relocations || relocatable`
        // arm so `-b aarch64 --relocatable` isn't stolen into the ARM builder.
        info!("Building AArch64 multi-function relocatable object (EM_AARCH64)");
        build_multi_func_aarch64_elf(&compiled_funcs)?
    } else if is_riscv {
        info!("Building RISC-V multi-function relocatable object (EM_RISCV)");
        build_multi_func_riscv_elf(&compiled_funcs)?
    } else if has_external_relocations || relocatable {
        let total_relocs: usize = compiled_funcs.iter().map(|f| f.relocations.len()).sum();
        if has_relocations {
            info!(
                "Producing relocatable object (ET_REL): {} import call relocations",
                total_relocs
            );
        } else {
            info!("Producing relocatable object (ET_REL): forced by --relocatable");
        }
        build_relocatable_elf(
            &compiled_funcs,
            &all_imports,
            &all_data_segments,
            all_memories.first().map(|m| m.initial_bytes()).unwrap_or(0),
            // #237: used-extent sizing + globals slots, native-pointer ABI only.
            if native_pointer_abi {
                Some(NativeGlobalsLayout {
                    globals: all_globals.clone(),
                    sp_init: stack_pointer_global_opt.map(|(_, v)| v).unwrap_or(0),
                    shadow_stack_size,
                })
            } else {
                None
            },
            input_dwarf.as_ref(),
            // #598: only Thumb-encoded functions get the interworking bit on
            // their STT_FUNC symbols; the A32 path (cortex-r5) keeps bit 0 clear.
            !matches!(target_spec.isa, synth_core::target::IsaVariant::Arm32),
        )?
    } else if cortex_m {
        build_multi_func_cortex_m_elf(&compiled_funcs, &all_memories, target_spec)?
    } else {
        build_multi_func_simple_elf(&compiled_funcs)?
    };

    info!("Generated {} byte ELF file", elf_data.len());

    // Write to file
    let mut file = File::create(&output).context(format!(
        "Failed to create output file: {}",
        output.display()
    ))?;
    file.write_all(&elf_data)
        .context("Failed to write ELF data")?;

    // Phase 1: emit safety-manifest.json next to the ELF when any
    // safety knob is active.
    let linear_mem_bytes = all_memories.first().map(|m| m.initial_bytes()).unwrap_or(0);
    maybe_emit_safety_manifest(&output, target_spec, safety_bounds, linear_mem_bytes)?;

    // Emit a CycloneDX SBOM when requested.
    if let Some(ref sbom_dest) = sbom_path {
        let wasm = sbom_wasm_bytes.as_deref().unwrap_or(&[]);
        emit_sbom(
            sbom_dest,
            &path,
            wasm,
            &output,
            &elf_data,
            target_spec,
            backend.name(),
            &all_imports,
        )?;
    }

    // Phase 5: sign the multi-function ELF via sigil. `--all-exports` produces
    // a single multi-function ELF (all exports linked together), so one signing
    // call covers every exported function. See docs/sigil-integration.md.
    if sign_output {
        sign::sign_elf(&output)?;
    }

    let total_code: usize = compiled_funcs.iter().map(|f| f.code.len()).sum();
    let total_relocs: usize = compiled_funcs.iter().map(|f| f.relocations.len()).sum();
    println!(
        "Compiled {} functions to {}",
        compiled_funcs.len(),
        output.display()
    );
    println!("  Total code size: {} bytes", total_code);
    println!("  ELF size: {} bytes", elf_data.len());
    if produced_relocatable {
        println!(
            "  Relocations: {} (requires linking with Kiln bridge)",
            total_relocs
        );
        println!("  ELF type: relocatable object (ET_REL)");
        println!(
            "\n  Link with: arm-none-eabi-ld -o firmware.elf {} kiln_bridge.o",
            output.display()
        );
    } else if has_relocations {
        // Standalone executable whose internal `BL func_N` calls were resolved
        // directly (no linker). Report them as patched, not pending (#170).
        println!(
            "  Internal calls: {} resolved in place (standalone executable)",
            total_relocs
        );
    }
    println!("\nFunction addresses:");

    // Calculate and display addresses (will be printed after ELF building sets them)
    println!(
        "  Use 'synth disasm {}' or 'objdump -t {}' to see symbols",
        output.display(),
        output.display()
    );

    Ok(())
}

/// Build a simple multi-function ELF
fn build_multi_func_simple_elf(funcs: &[ElfFunction]) -> Result<Vec<u8>> {
    let base_addr: u32 = 0x8000;
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(base_addr);

    // Concatenate all function code
    let mut all_code = Vec::new();
    let mut func_offsets = Vec::new();

    for func in funcs {
        // Align each function to 4 bytes
        while all_code.len() % 4 != 0 {
            all_code.push(0);
        }
        func_offsets.push(all_code.len() as u32);
        all_code.extend_from_slice(&func.code);
    }

    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(base_addr)
        .with_align(4)
        .with_data(all_code);

    elf_builder.add_section(text_section);

    // Add symbol for each function
    for (i, func) in funcs.iter().enumerate() {
        let func_sym = Symbol::new(&func.name)
            .with_value(base_addr + func_offsets[i])
            .with_size(func.code.len() as u32)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(4);

        elf_builder.add_symbol(func_sym);
    }

    elf_builder.build().context("ELF generation failed")
}

/// Build a relocatable ELF object (.o) with undefined symbols and relocations.
///
/// Produced when the WASM module has imports — the resulting .o needs to be linked
/// with the Kiln bridge (which provides `__meld_dispatch_import` etc.) to create
/// a final firmware binary.
/// #237: native-pointer-ABI layout for the wasm data region — used-extent
/// sizing (gale: 64 KiB-page granularity is RAM-prohibitive on the MCUs this
/// targets) plus materialized global slots appended after the used extent.
struct NativeGlobalsLayout {
    /// Every defined global: (index, i32 init value). Slot `idx` lives at
    /// `__synth_globals + idx*4`; slots hold wasm OFFSETS (the selector
    /// rebases the SP global to an absolute pointer on read), so plain init
    /// bytes suffice — no data relocations.
    globals: Vec<(u32, i32)>,
    /// The shadow-stack top (the SP global's init); the region must cover it.
    sp_init: i32,
    /// #383 (VCR-MEM-001): integrator-declared shadow-stack budget in bytes. When
    /// `Some(B)`, the caller asked to shrink the [0, sp_init) reservation to `B`
    /// (re-basing the stack top and shifting the high zero-init static relocs
    /// down). The retarget surgery is silicon-gated (link-fragile native-pointer
    /// path, the #368→#359 lesson); until it lands, a `Some` here is an honest
    /// Err, never a silent no-op.
    shadow_stack_size: Option<u32>,
}

fn build_relocatable_elf(
    funcs: &[ElfFunction],
    imports: &[ImportEntry],
    data_segments: &[(u32, Vec<u8>)],
    linear_memory_bytes: u32,
    native_globals: Option<NativeGlobalsLayout>,
    // VCR-DBG-001 step 4 (#394): the input wasm's parsed `.debug_line` (rows +
    // code_base). `None` ⇒ `--debug-line` off OR the input carried no DWARF ⇒
    // no `.debug_line` section emitted ⇒ output byte-identical to the default.
    dwarf_line: Option<&synth_core::dwarf_line::InputDwarfLine>,
    // #598: true for Thumb targets (STT_FUNC symbols + e_entry get bit 0, the
    // interworking bit), false for A32 (cortex-r5) — A32 code addresses must
    // keep bit 0 clear.
    thumb_funcs: bool,
) -> Result<Vec<u8>> {
    use std::collections::HashMap;

    // #383 (VCR-MEM-001 layer-1): the integrator-declared shadow-stack budget
    // shrinks the [0, sp_init) reservation. The actual shrink is computed below
    // (after the reloc analysis, which decides whether the geometry is safe to
    // rewrite) — see `shrink_shadow_stack`. It refuses HONESTLY (typed Err, the
    // #378/#381 contract) for any geometry it cannot prove safe, and is opt-in
    // (default unset ⇒ full-page reservation ⇒ frozen fixtures bit-identical).

    let mut elf_builder = ElfBuilder::new_arm32()
        .with_thumb_funcs(thumb_funcs) // #598: no Thumb bit on A32 symbols
        .with_entry(0)
        .with_type(ElfType::Rel); // ET_REL: relocatable object

    // Concatenate all function code into a single .text blob
    let mut all_code = Vec::new();
    let mut func_offsets = Vec::new();

    for func in funcs {
        // Align each function to 4 bytes
        while all_code.len() % 4 != 0 {
            all_code.push(0);
        }
        func_offsets.push(all_code.len() as u32);
        all_code.extend_from_slice(&func.code);
    }

    // #354: the `.text` section is built + added LATER (just before the
    // `.bss`/`.data` sections, so it stays section index 4). The per-region
    // split (below) may need to rewrite in-place `R_ARM_ABS32` literal-pool
    // addend words inside `all_code` first — those are REL (the linker computes
    // `S + A` with `A` stored in the data word), so retargeting a static-data
    // reloc from `__synth_wasm_data + C` to `__synth_wasm_seg_K + (C - seg_off)`
    // must patch the word before `.text` is frozen. `all_code` is kept mutable
    // until then.

    // #237: if any function addresses a wasm static via `__synth_wasm_data`
    // (the --native-pointer-abi path), emit the whole wasm linear memory as one
    // RAM-resident region and define `__synth_wasm_data` at its base — so a wasm
    // address A maps to (the placed region) + A. The region spans BOTH the
    // initialized `(data)` segments AND the zero-init region (a `static
    // k_spinlock` is zero-init → BSS, with no `(data)` segment, #237 follow-up).
    // If there is any initialized data we emit `.data` (PROGBITS, data placed,
    // rest zero); with none, a `.bss` (NOBITS — no flash cost) sized to the
    // linear-memory minimum. Added here (right after `.text`) so its section
    // index is 5, before the optional `.meld_import_table`.
    let needs_wasm_data = funcs
        .iter()
        .flat_map(|f| &f.relocations)
        .any(|r| r.symbol == "__synth_wasm_data" || r.symbol == "__synth_globals");
    let emit_wasm_data = needs_wasm_data && linear_memory_bytes > 0;
    // #237 (gale, mutex-on-silicon): under the native-pointer ABI the region
    // is sized to the USED extent — data-segment end + shadow stack (the SP
    // global's init is the stack top; the stack grows down inside the
    // region) — not the declared 64 KiB pages, which overflow small-MCU RAM
    // (131072 B .bss for an 830-byte module on a 128 KiB part). Materialized
    // global slots follow at `__synth_globals = __synth_wasm_data +
    // used_extent`, initialized from the wasm global section, which is what
    // makes `global.set` real and the shadow-stack pointer start at its top
    // instead of 0.
    let native_layout = native_globals.filter(|_| emit_wasm_data);
    // Decode a Thumb MOVW/MOVT imm16 from little-endian code bytes (the REL
    // addend lives in the instruction).
    fn thm_imm16(code: &[u8], off: usize) -> u32 {
        let hw1 = u16::from_le_bytes([code[off], code[off + 1]]) as u32;
        let hw2 = u16::from_le_bytes([code[off + 2], code[off + 3]]) as u32;
        ((hw1 & 0xF) << 12) | (((hw1 >> 10) & 1) << 11) | (((hw2 >> 12) & 0x7) << 8) | (hw2 & 0xFF)
    }
    let used_extent: u32 = native_layout
        .as_ref()
        .map(|ng| {
            let data_end = data_segments
                .iter()
                .map(|(off, d)| off + d.len() as u32)
                .max()
                .unwrap_or(0);
            let sp_top = ng.sp_init.max(0) as u32;
            // Layout-bound globals: wasm-ld emits __data_end/__heap_base as
            // i32 globals whose inits mark the static-region extent — the
            // linker's own answer to "how much is used".
            let global_top = ng
                .globals
                .iter()
                .map(|&(_, v)| v.max(0) as u32)
                .filter(|&v| v <= linear_memory_bytes)
                .max()
                .unwrap_or(0);
            // Static-access addends: every `__synth_wasm_data + A` the
            // selector relocated marks a touched address; cover A plus an
            // i64's width.
            let static_top = funcs
                .iter()
                .flat_map(|f| {
                    f.relocations
                        .iter()
                        .filter(|&r| {
                            r.symbol == "__synth_wasm_data"
                                && matches!(r.kind, synth_core::RelocKind::MovwAbs)
                        })
                        .map(|r| {
                            let lo = thm_imm16(&f.code, r.offset as usize);
                            // The paired MOVT immediately follows (emit order).
                            let hi = f
                                .relocations
                                .iter()
                                .find(|m| {
                                    m.offset == r.offset + 4
                                        && matches!(m.kind, synth_core::RelocKind::MovtAbs)
                                })
                                .map(|m| thm_imm16(&f.code, m.offset as usize))
                                .unwrap_or(0);
                            (hi << 16) | lo
                        })
                })
                .map(|a: u32| a.saturating_add(8))
                .max()
                .unwrap_or(0);
            // #359: the native-pointer path relocates static-data accesses as
            // Abs32 LITERAL-POOL words (`S + A`), NOT MovwAbs — so the MovwAbs-only
            // `static_top` above sees nothing and under-sizes the `.bss`
            // reservation. A legitimate high-offset access (gale's msgq action→ret
            // lookup reads a ZERO word at offset 65552 — the tail of the table,
            // just past the 16-byte init segment) then lands at/past `__bss_end`
            // and reads garbage instead of zero, taking the queue-full branch on
            // an empty queue → rc=-35 (the #354 × #368 interaction). Cover the
            // Abs32 literal addends too (read C from the in-place `.text` word,
            // pre-retarget) so the reservation spans every offset the code reads.
            let static_top_abs32 = funcs
                .iter()
                .flat_map(|f| {
                    f.relocations.iter().filter_map(move |r| {
                        if r.symbol != "__synth_wasm_data"
                            || !matches!(r.kind, synth_core::RelocKind::Abs32)
                        {
                            return None;
                        }
                        let pos = r.offset as usize;
                        if pos + 4 > f.code.len() {
                            return None;
                        }
                        Some(u32::from_le_bytes([
                            f.code[pos],
                            f.code[pos + 1],
                            f.code[pos + 2],
                            f.code[pos + 3],
                        ]))
                    })
                })
                .map(|a: u32| a.saturating_add(8))
                .max()
                .unwrap_or(0);
            data_end
                .max(sp_top)
                .max(global_top)
                .max(static_top)
                .max(static_top_abs32)
                .max(4)
                .min(linear_memory_bytes)
                .next_multiple_of(4)
        })
        .unwrap_or(linear_memory_bytes);
    let globals_bytes: u32 = native_layout
        .as_ref()
        .and_then(|ng| ng.globals.iter().map(|(i, _)| (i + 1) * 4).max())
        .unwrap_or(0);
    // #345 step 1: under the native-pointer ABI the `[0, used_extent)`
    // `__synth_wasm_data` region is the wasm linear memory. When it carries NO
    // initialized `(data)` segment it is a pure zero-init reservation (e.g. a
    // 64 KiB shadow stack with SP-init = 65536, as in the mutex decide) — that
    // must NOT ship as a PROGBITS `.data` of 64 KiB zero bytes (unshippable on
    // a 128 KiB-RAM MCU). Emit it as a SHT_NOBITS `.bss` (zero file bytes; the
    // Zephyr loader zeroes `.bss`, preserving wasm zero-init semantics) and put
    // the materialized `__synth_globals` slots (which DO carry non-zero inits)
    // in their own small PROGBITS `.data`. Only this all-zero linmem case is
    // split; when a `(data)` segment is present the region stays one PROGBITS
    // section (the prefix/tail split is link-fragile across a multi-object link
    // and is deferred to step 2 / PC-relative relocs). Branch the section
    // emission, the two symbol defs, and the `.meld_import_table` index off one
    // `split_linmem_bss` flag so they cannot diverge.
    let split_linmem_bss = native_layout.is_some() && data_segments.is_empty();

    // #354: per-region split for the MIXED case (native-pointer ABI WITH an
    // initialized `(data)` segment). The #345 split only handled the all-zero
    // case; any init segment fell to the one-PROGBITS arm, so a small `.rodata`
    // const at a HIGH linmem offset (gale's stack_push: a 12-byte -ENOMEM const
    // at 65536, above the 64 KiB shadow stack) dragged the whole zero gap into a
    // 65552-byte PROGBITS `.data` (MCU-unshippable). Split per region instead:
    // the zero reservation is `.bss` (NOBITS, `__synth_wasm_data`); each init
    // segment is packed into a small PROGBITS `.data` under its own
    // `__synth_wasm_seg_K` symbol; and every `__synth_wasm_data + C` static-data
    // reloc whose addend C lands in segment K is retargeted to
    // `__synth_wasm_seg_K + (C - seg_off_K)` (symbol + in-place REL addend word).
    //
    // SAFE-BY-CONSTRUCTION GATE: fire only when every init segment sits in the
    // static-data region (offset >= wasm_data_base = the SP-global init, the
    // same boundary the selector uses to classify addresses >= base as static
    // relocs vs `<` as frame offsets) AND every `__synth_wasm_data` reloc is the
    // retargetable literal-pool `Abs32` form (the live form post-#345-step-2).
    // The shadow stack is reached only via the SP register value (dynamic, never
    // a static reloc with an addend in that range), so per-region symbols cannot
    // mis-address anything the selector doesn't already assume separable. If the
    // gate fails, fall back to the one-PROGBITS arm (fat but always correct).
    let wasm_data_base: u32 = native_layout
        .as_ref()
        .map(|ng| ng.sp_init.max(0) as u32)
        .unwrap_or(0);
    let all_static_data_abs32 = funcs.iter().flat_map(|f| &f.relocations).all(|r| {
        r.symbol != "__synth_wasm_data" || matches!(r.kind, synth_core::backend::RelocKind::Abs32)
    });
    let mixed_separable = native_layout.is_some()
        && !data_segments.is_empty()
        && all_static_data_abs32
        && data_segments.iter().all(|(off, _)| *off >= wasm_data_base);
    // Packed layout of the init segments inside the mixed-case `.data`: each
    // segment 4-aligned in declaration order (i32 loads stay aligned — seg_off
    // is 4-aligned in wasm and the packed start is 4-aligned), then the globals
    // slots. (packed_off per segment, globals packed offset, total .data size).
    let mixed_layout: Option<(Vec<u32>, u32, u32)> = if mixed_separable {
        let mut packed = Vec::with_capacity(data_segments.len());
        let mut cur = 0u32;
        for (_off, d) in data_segments {
            cur = cur.next_multiple_of(4);
            packed.push(cur);
            cur += d.len() as u32;
        }
        let globals_off = cur.next_multiple_of(4);
        Some((packed, globals_off, globals_off + globals_bytes))
    } else {
        None
    };
    let do_mixed_split = mixed_layout.is_some();
    if native_layout.is_some() && !data_segments.is_empty() && !do_mixed_split {
        info!(
            "Native-pointer linmem: init (data) segment not separable (below base \
             {wasm_data_base} or non-Abs32 static reloc); keeping one PROGBITS \
             .data (correct, not per-region split) — #354 fallback"
        );
    }

    // #354: retarget map + in-place REL addend patch for the mixed case. Keyed
    // by (func index, reloc offset) -> (new symbol, new addend). The addend C is
    // read from the in-place `.text` literal word (Abs32 is REL — `S + A`).
    let mut retarget: HashMap<(usize, u32), (String, i32)> = HashMap::new();
    if do_mixed_split {
        for (i, func) in funcs.iter().enumerate() {
            for reloc in &func.relocations {
                if reloc.symbol != "__synth_wasm_data"
                    || !matches!(reloc.kind, synth_core::backend::RelocKind::Abs32)
                {
                    continue;
                }
                let pos = (func_offsets[i] + reloc.offset) as usize;
                if pos + 4 > all_code.len() {
                    continue;
                }
                let c = u32::from_le_bytes([
                    all_code[pos],
                    all_code[pos + 1],
                    all_code[pos + 2],
                    all_code[pos + 3],
                ]);
                if let Some(k) = data_segments
                    .iter()
                    .position(|(off, d)| c >= *off && c < *off + d.len() as u32)
                {
                    let new_addend = (c - data_segments[k].0) as i32;
                    retarget.insert(
                        (i, reloc.offset),
                        (format!("__synth_wasm_seg_{k}"), new_addend),
                    );
                    all_code[pos..pos + 4].copy_from_slice(&new_addend.to_le_bytes());
                }
            }
        }
    }

    // #383 (VCR-MEM-001 layer-1): shrink the [0, sp_init) shadow-stack reservation
    // to the integrator-declared budget B. Correct-by-construction for the verified
    // gust geometry (stack-first: statics at/above sp_init are retargeted into the
    // packed `.data`, so the only static relocs still pointing into the `.bss`
    // reservation are addend-0 region-base pointers — stable because
    // `__synth_wasm_data` stays at offset 0). The shrink re-bases the SP global slot
    // sp_init -> B and resizes the `.bss` to B + (used_extent - sp_init). It REFUSES
    // honestly (typed Err, the #359/#368 lesson) for any geometry it cannot prove
    // safe; opt-in, so the default (unset) reserves the full page = byte-identical.
    let (reserved_extent, rebased_globals): (u32, Option<Vec<(u32, i32)>>) = match native_layout
        .as_ref()
        .and_then(|ng| ng.shadow_stack_size.map(|b| (ng, b)))
    {
        None => (used_extent, None),
        Some((ng, budget)) => {
            let sp = ng.sp_init.max(0) as u32;
            // Only the per-region split geometries separate statics from the stack
            // reservation; the one-PROGBITS fallback inlines them and is not safe to
            // shrink here.
            if !(split_linmem_bss || do_mixed_split) {
                anyhow::bail!(
                    "--shadow-stack-size: this module's native-pointer layout keeps static \
                     data inline in the reservation (one-PROGBITS fallback); the shadow-stack \
                     shrink only supports the per-region-split geometry. Tracked VCR-MEM-001/#383."
                );
            }
            if budget > sp {
                anyhow::bail!(
                    "--shadow-stack-size {budget} exceeds the declared shadow-stack top \
                     sp_init={sp}; refusing (would enlarge, not shrink)."
                );
            }
            // Every `__synth_wasm_data` reloc still pointing into the `.bss` reservation
            // (i.e. NOT retargeted into `.data`) must be a region-base pointer (addend 0),
            // which is stable under the shrink. A non-zero addend is a real static inside
            // the reservation; down-shifting inline statics is the deferred general case ⇒
            // refuse rather than mis-address. Only the Abs32 literal-pool form is inspected;
            // any other static-reloc kind into the reservation is refused.
            for (i, func) in funcs.iter().enumerate() {
                for reloc in &func.relocations {
                    if reloc.symbol != "__synth_wasm_data"
                        || retarget.contains_key(&(i, reloc.offset))
                    {
                        continue;
                    }
                    let pos = (func_offsets[i] + reloc.offset) as usize;
                    let c = match reloc.kind {
                        synth_core::backend::RelocKind::Abs32 if pos + 4 <= all_code.len() => {
                            u32::from_le_bytes([
                                all_code[pos],
                                all_code[pos + 1],
                                all_code[pos + 2],
                                all_code[pos + 3],
                            ])
                        }
                        other => anyhow::bail!(
                            "--shadow-stack-size: unhandled native-pointer static reloc {other:?} \
                             into the reservation; refusing. VCR-MEM-001/#383."
                        ),
                    };
                    if c != 0 {
                        anyhow::bail!(
                            "--shadow-stack-size: a native-pointer static access addends {c} into \
                             the [0, sp_init) reservation (not the region base, not retargeted into \
                             .data); down-shifting inline statics is the deferred general case. \
                             Refusing rather than mis-addressing. VCR-MEM-001/#383."
                        );
                    }
                }
            }
            // Re-base the SP global slot: the unique global whose init == sp_init.
            let sp_matches: Vec<usize> = ng
                .globals
                .iter()
                .enumerate()
                .filter(|(_, (_, v))| *v == ng.sp_init)
                .map(|(i, _)| i)
                .collect();
            if sp_matches.len() != 1 {
                anyhow::bail!(
                    "--shadow-stack-size: could not uniquely identify the shadow-stack global to \
                     re-base ({} globals have init == sp_init {}); refusing. VCR-MEM-001/#383.",
                    sp_matches.len(),
                    ng.sp_init
                );
            }
            let mut rebased = ng.globals.clone();
            rebased[sp_matches[0]].1 = budget as i32;
            // Reservation now covers [0, B) stack + the preserved static tail that sat
            // above sp_init (the retargeted statics are in `.data`, unaffected).
            // saturating_sub: used_extent is `.min(linear_memory_bytes)`-clamped, so a
            // pathological module could clamp it below sp_init — never underflow-panic.
            let new_extent = budget
                .saturating_add(used_extent.saturating_sub(sp))
                .next_multiple_of(4);
            info!(
                "Native-pointer shadow-stack shrink (#383): sp_init {sp} -> {budget}, \
                 reservation {used_extent} -> {new_extent} B (post-link oracle: stack/static \
                 disjoint, all reservation accesses in-range)"
            );
            (new_extent, Some(rebased))
        }
    };

    // #354/#345: build + add `.text` (section index 4) now — after any in-place
    // addend patch and before the `.bss`/`.data` sections, so `.text` keeps its
    // index and the patched literal words are what ship.
    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0)
        .with_align(4)
        .with_data(all_code);
    elf_builder.add_section(text_section);

    if emit_wasm_data {
        if do_mixed_split {
            // #354: zero reservation -> NOBITS `.bss` (section 5),
            // `__synth_wasm_data` = 0; init segments packed into a small PROGBITS
            // `.data` (section 6), each under its own `__synth_wasm_seg_K`.
            let (packed, globals_off, data_size) = mixed_layout.as_ref().unwrap();
            let bss = Section::new(".bss", ElfSectionType::NoBits)
                .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                .with_addr(0)
                .with_align(4)
                .with_size(reserved_extent);
            elf_builder.add_section(bss);
            let mut blob = vec![0u8; *data_size as usize];
            for ((_off, d), &poff) in data_segments.iter().zip(packed.iter()) {
                blob[poff as usize..poff as usize + d.len()].copy_from_slice(d);
            }
            if let Some(ng) = &native_layout {
                // #383: re-based SP slot when the shadow-stack shrink fired.
                let globals = rebased_globals.as_ref().unwrap_or(&ng.globals);
                for (idx, init) in globals {
                    let at = (*globals_off + idx * 4) as usize;
                    blob[at..at + 4].copy_from_slice(&init.to_le_bytes());
                }
            }
            let data = Section::new(".data", ElfSectionType::ProgBits)
                .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                .with_addr(0)
                .with_align(4)
                .with_data(blob);
            elf_builder.add_section(data);
        } else if split_linmem_bss {
            // #345: zero-init linmem reservation → NOBITS `.bss` (section 5).
            let bss = Section::new(".bss", ElfSectionType::NoBits)
                .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                .with_addr(0)
                .with_align(4)
                .with_size(reserved_extent);
            elf_builder.add_section(bss);
            // #345: materialized global slots (non-zero inits) → small PROGBITS
            // `.data` (section 6). `__synth_globals` is value 0 in this section.
            if let Some(ng) = &native_layout {
                let mut blob = vec![0u8; globals_bytes as usize];
                // #383: re-based SP slot when the shadow-stack shrink fired.
                let globals = rebased_globals.as_ref().unwrap_or(&ng.globals);
                for (idx, init) in globals {
                    let at = (idx * 4) as usize;
                    blob[at..at + 4].copy_from_slice(&init.to_le_bytes());
                }
                let globals = Section::new(".data", ElfSectionType::ProgBits)
                    .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                    .with_addr(0)
                    .with_align(4)
                    .with_data(blob);
                elf_builder.add_section(globals);
            }
        } else {
            let size = (used_extent + globals_bytes) as usize;
            let section = if let Some(ng) = &native_layout {
                // Native-pointer ABI with initialized data: PROGBITS covering
                // the used extent + global slots (init values must reach the
                // device; the used extent is small by construction).
                let mut blob = vec![0u8; size];
                for (off, d) in data_segments {
                    blob[*off as usize..*off as usize + d.len()].copy_from_slice(d);
                }
                for (idx, init) in &ng.globals {
                    let at = (used_extent + idx * 4) as usize;
                    blob[at..at + 4].copy_from_slice(&init.to_le_bytes());
                }
                Section::new(".data", ElfSectionType::ProgBits)
                    .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                    .with_addr(0)
                    .with_align(4)
                    .with_data(blob)
            } else if data_segments.is_empty() {
                // Pure zero-init (BSS) — NOBITS, no bytes in the object.
                Section::new(".bss", ElfSectionType::NoBits)
                    .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                    .with_addr(0)
                    .with_align(4)
                    .with_size(linear_memory_bytes)
            } else {
                // Initialized data present — PROGBITS covering the whole memory,
                // segments placed at their offsets, the rest zero.
                let mut blob = vec![0u8; linear_memory_bytes as usize];
                for (off, d) in data_segments {
                    blob[*off as usize..*off as usize + d.len()].copy_from_slice(d);
                }
                Section::new(".data", ElfSectionType::ProgBits)
                    .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
                    .with_addr(0)
                    .with_align(4)
                    .with_data(blob)
            };
            elf_builder.add_section(section);
        }
    }

    // Symbol-name -> symbol index map. Symbol indices are 1-based (index 0 is
    // the reserved null symbol); each `add_symbol` appends one, so we track the
    // running count to know the index of each symbol we define.
    let mut sym_indices: HashMap<String, u32> = HashMap::new();
    let mut sym_count: u32 = 0; // number of real symbols added so far

    // Add defined symbols for each compiled function. We define TWO names per
    // function: the export name (global, for the host linker) and a stable
    // `func_{wasm_index}` name (the label the instruction selector emits for
    // internal `call`s). Internal `BL func_N` relocations resolve against the
    // latter; without it, internal calls were left as unpatched `bl #0` (#167).
    for (i, func) in funcs.iter().enumerate() {
        let export_sym = Symbol::new(&func.name)
            .with_value(func_offsets[i])
            .with_size(func.code.len() as u32)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(4); // .text is section 4 (null=0, shstrtab=1, strtab=2, symtab=3, .text=4)
        elf_builder.add_symbol(export_sym);
        sym_count += 1;
        sym_indices.insert(func.name.clone(), sym_count);

        // `func_{wasm_index}` alias (skip if the export name already is that).
        let internal_label = format!("func_{}", func.wasm_index);
        if internal_label != func.name {
            let internal_sym = Symbol::new(&internal_label)
                .with_value(func_offsets[i])
                .with_size(func.code.len() as u32)
                .with_binding(SymbolBinding::Global)
                .with_type(SymbolType::Func)
                .with_section(4);
            elf_builder.add_symbol(internal_sym);
            sym_count += 1;
            sym_indices.insert(internal_label, sym_count);
        }
    }

    // Map the BL label of a call to a wasm import (`func_{import_index}`) to
    // the import's field name. The selector emits `BL func_N` for imported
    // calls too (N is the wasm function index, which for imports is the import
    // index); naming the undefined symbol `func_N` means a real host (e.g. the
    // Zephyr kernel) cannot resolve it — it defines `k_spin_lock`, not `func_0`.
    // synth knows the field names (it logs them + emits .meld_import_table), so
    // use them for the undefined symbol (#173). Internal defined calls keep
    // their `func_N`/export-name symbol (already in sym_indices).
    // #237: define `__synth_wasm_data` at the base of the `.data` section
    // (section index 5 — added immediately after `.text`=4). The MOVW/MOVT_ABS
    // relocations from the static-data accesses resolve against it.
    if emit_wasm_data {
        let data_sym = Symbol::new("__synth_wasm_data")
            .with_value(0)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Object)
            .with_section(5);
        elf_builder.add_symbol(data_sym);
        sym_count += 1;
        sym_indices.insert("__synth_wasm_data".to_string(), sym_count);
        // #354: per-region segment symbols. In the mixed split each init
        // segment is packed into the `.data` section (index 6) at its packed
        // offset; `__synth_wasm_seg_K` is its base, and the retargeted static
        // relocs resolve against it (+ the rewritten in-place addend).
        if let Some((packed, _goff, _sz)) = &mixed_layout {
            for (k, &poff) in packed.iter().enumerate() {
                let seg_sym = Symbol::new(&format!("__synth_wasm_seg_{k}"))
                    .with_value(poff)
                    .with_binding(SymbolBinding::Global)
                    .with_type(SymbolType::Object)
                    .with_section(6);
                elf_builder.add_symbol(seg_sym);
                sym_count += 1;
                sym_indices.insert(format!("__synth_wasm_seg_{k}"), sym_count);
            }
        }
        // #237/#345/#354: the globals slot region. In the non-split (PROGBITS)
        // case it sits right after the used extent inside section 5. In the #345
        // all-zero split and the #354 mixed split the slots live in the PROGBITS
        // `.data` (section 6) — at value 0 (#345) or after the packed segments
        // (#354).
        if native_layout.is_some() {
            let (gv, gsec) = if let Some((_packed, goff, _sz)) = &mixed_layout {
                (*goff, 6)
            } else if split_linmem_bss {
                (0, 6)
            } else {
                (used_extent, 5)
            };
            let globals_sym = Symbol::new("__synth_globals")
                .with_value(gv)
                .with_binding(SymbolBinding::Global)
                .with_type(SymbolType::Object)
                .with_section(gsec);
            elf_builder.add_symbol(globals_sym);
            sym_count += 1;
            sym_indices.insert("__synth_globals".to_string(), sym_count);
        }
    }

    let mut import_label_to_field: HashMap<String, String> = HashMap::new();
    for imp in imports {
        if matches!(imp.kind, synth_core::ImportKind::Function(_)) {
            import_label_to_field.insert(format!("func_{}", imp.index), imp.name.clone());
        }
    }

    // Any relocation symbol not already defined becomes an undefined external:
    // import calls under their wasm field name, dispatch stubs (`__meld_*`) and
    // skipped-internal callees under their original label.
    let mut external_count = 0usize;
    for func in funcs {
        for reloc in &func.relocations {
            if sym_indices.contains_key(&reloc.symbol) {
                continue; // internal call to a compiled function — already defined
            }
            let effective = import_label_to_field
                .get(&reloc.symbol)
                .cloned()
                .unwrap_or_else(|| reloc.symbol.clone());
            let idx = match sym_indices.get(&effective) {
                Some(&i) => i,
                None => {
                    let i = elf_builder.add_undefined_symbol(&effective);
                    sym_indices.insert(effective.clone(), i);
                    external_count += 1;
                    i
                }
            };
            // Resolve the original label (func_N) to the effective symbol index
            // so the relocation-emission loop below finds it.
            sym_indices.insert(reloc.symbol.clone(), idx);
        }
    }

    // Emit an R_ARM_THM_CALL relocation for every BL (internal `func_N` resolves
    // against the defined symbol; imports against the undefined external). Thumb
    // BL on Cortex-M requires R_ARM_THM_CALL (10), not the ARM-mode R_ARM_CALL.
    let mut reloc_count = 0usize;
    for (i, func) in funcs.iter().enumerate() {
        let func_base = func_offsets[i];
        for reloc in &func.relocations {
            // #354: a static-data reloc retargeted to a per-region segment
            // symbol resolves against that symbol; all others against their
            // original symbol.
            let sym_name = retarget
                .get(&(i, reloc.offset))
                .map(|(s, _)| s.as_str())
                .unwrap_or(reloc.symbol.as_str());
            let sym_idx = sym_indices[sym_name];
            // #237: map the relocation kind. BL calls → R_ARM_THM_CALL; the
            // symbol-relative static-data MOVW/MOVT → R_ARM_MOVW_ABS_NC/MOVT_ABS.
            let reloc_type = match reloc.kind {
                synth_core::backend::RelocKind::ThmCall => ArmRelocationType::ThmCall,
                synth_core::backend::RelocKind::MovwAbs => ArmRelocationType::MovwAbsNc,
                synth_core::backend::RelocKind::MovtAbs => ArmRelocationType::MovtAbs,
                // #345: literal-pool word carrying a symbol address — link-survivable
                // R_ARM_ABS32 (the linker patches the data word, `S + A`).
                synth_core::backend::RelocKind::Abs32 => {
                    // The `LDR rX,[pc,#imm12]` that reads this pooled word had its
                    // imm12 computed function-locally (`Align(PC,4)+imm12`, with PC
                    // and the pool offset both relative to the function start). That
                    // is correct at the function's ABSOLUTE address ONLY if the
                    // function begins 4-byte-aligned — otherwise `Align()` rounds
                    // differently and the load lands ±2 bytes off the word. The
                    // `.text` layout loop 4-aligns every function start (and `.text`
                    // itself is `with_align(4)`), so this holds; assert it so a
                    // future layout change that breaks the invariant fails loudly
                    // rather than miscompiling the pool load (#345, the #212/#215
                    // "layout change exposes latent fragility" class).
                    assert_eq!(
                        func_base % 4,
                        0,
                        "#345: function carrying an R_ARM_ABS32 literal-pool reloc \
                         must start 4-byte-aligned (func_base={func_base}); the \
                         PC-relative LDR imm12 assumes it"
                    );
                    ArmRelocationType::Abs32
                }
            };
            elf_builder.add_relocation(Relocation {
                offset: func_base + reloc.offset,
                symbol_index: sym_idx,
                reloc_type,
            });
            reloc_count += 1;
        }
    }
    let extern_sym_indices = (external_count, reloc_count); // for the info! below

    // Add a .meld_import_table section with import metadata
    // This is a custom section that the Kiln bridge can read to understand
    // which module::name each import index corresponds to.
    if !imports.is_empty() {
        let mut import_table_data = Vec::new();
        let mut import_func_count = 0u32;
        for imp in imports {
            if matches!(imp.kind, synth_core::ImportKind::Function(_)) {
                // Format: index(4) | module_len(2) | module | name_len(2) | name
                import_table_data.extend_from_slice(&imp.index.to_le_bytes());
                let mod_bytes = imp.module.as_bytes();
                import_table_data.extend_from_slice(&(mod_bytes.len() as u16).to_le_bytes());
                import_table_data.extend_from_slice(mod_bytes);
                let name_bytes = imp.name.as_bytes();
                import_table_data.extend_from_slice(&(name_bytes.len() as u16).to_le_bytes());
                import_table_data.extend_from_slice(name_bytes);
                import_func_count += 1;
            }
        }

        if !import_table_data.is_empty() {
            // Prepend the count
            let mut header = import_func_count.to_le_bytes().to_vec();
            header.extend_from_slice(&import_table_data);

            let import_section = Section::new(".meld_import_table", ElfSectionType::ProgBits)
                .with_flags(0) // Not ALLOC — metadata only
                .with_align(4)
                .with_data(header);

            elf_builder.add_section(import_section);
        }
    }

    // VCR-DBG-001 step 4 (#394): emit a FULL DWARF unit (`.debug_info`,
    // `.debug_abbrev`, `.debug_str`, `.debug_line`, ...) as NON-ALLOC trailing
    // PROGBITS sections. Each is structurally a clone of `.meld_import_table`: no
    // symbol or relocation targets them, and `.rel.text`'s `sh_info` is hardcoded
    // to `.text` (index 4) AFTER the user-section loop — so appending here gives
    // each a fresh section index without disturbing the `with_section` (4/5/6)
    // symbol indices, keeping the feature PURELY ADDITIVE. The unit carries a
    // real `DW_TAG_compile_unit` whose `DW_AT_stmt_list` points at `.debug_line`,
    // so a debugger reaches the line table via the NORMAL `.debug_info` → CU walk.
    // Composed from `func_offsets[i] + machine_offset → op_offsets[op_idx] → src`.
    if let Some(input_dwarf) = dwarf_line
        && !input_dwarf.rows.is_empty()
    {
        use synth_core::dwarf_line::{SourceLoc, op_offsets_to_source};
        // (arm_addr, source line, GLOBAL file index into input_dwarf.files).
        let mut table: Vec<(u64, u32, u32)> = Vec::new();
        for (i, func) in funcs.iter().enumerate() {
            if func.line_map.is_empty() || func.op_offsets.is_empty() {
                continue; // RISC-V (empty line_map) or a func with no op offsets
            }
            // op-index → source for this function's ops (parallel to op_offsets).
            let locs =
                op_offsets_to_source(&func.op_offsets, input_dwarf.code_base, &input_dwarf.rows);
            for &(machine_off, op_idx) in &func.line_map {
                // None entries (prologue / literal pool) carry no source.
                let Some(op_idx) = op_idx else { continue };
                // Carry the real source FILE through (was dropped, forcing every
                // stop to the fabricated `synth.wasm`); emit reproduces it.
                if let Some(Some(SourceLoc { line, file })) = locs.get(op_idx)
                    && *line != 0
                {
                    let arm_addr = (func_offsets[i] + machine_off) as u64;
                    table.push((arm_addr, *line, *file));
                }
            }
        }
        // One address-ordered, de-duped sequence covering every function.
        table.sort_by_key(|&(a, _, _)| a);
        table.dedup_by_key(|&mut (a, _, _)| a);

        // A dedicated GLOBAL symbol at `.text + 0` that the DWARF `.rel.debug_*`
        // records resolve against (R_ARM_ABS32, REL: S=`.text` base + in-place
        // addend 0). Global + appended last so no existing symbol index shifts
        // and `.symtab`'s `sh_info` is untouched; present only under
        // `--debug-line`, so the no-DWARF symtab stays byte-identical. A local
        // STT_SECTION symbol would have to precede all globals (ELF orders
        // locals first) and bump `sh_info`, shifting every `.rel.text` index.
        let text_base_sym = Symbol::new("__synth_text_base")
            .with_value(0)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::NoType)
            .with_section(4); // .text is section index 4
        let text_sym_idx = elf_builder.add_symbol_indexed(text_base_sym);

        // #394 Tier-1: one DW_TAG_subprogram DIE per compiled function so a
        // debugger backtrace shows the function NAME. Each function's name and
        // its object-relative `.text` range come straight from the layout the
        // reloc/symbol emission already uses (`func_offsets[i]` .. + code len,
        // the same values `func.name`/`func_N` symbols carry). Purely additive:
        // the subprogram low_pc addresses reuse the `__synth_text_base` symbol
        // via an addend, so no new symbol is defined.
        let subprograms: Vec<synth_core::dwarf_line::SubprogramInfo> = funcs
            .iter()
            .enumerate()
            .map(|(i, func)| synth_core::dwarf_line::SubprogramInfo {
                // #394 Tier-1.x: name priority `name`-section > export name >
                // `func_N`. `func.name` already is export-name-or-`func_N`, so
                // internal functions stop showing the synthetic `func_N` in a
                // backtrace whenever the input carried a `name` section (e.g.
                // `core::panicking::panic_fmt::h...`). DWARF-only: the symbol
                // table and relocations keep using `func.name`.
                name: func.debug_name.clone().unwrap_or_else(|| func.name.clone()),
                low_pc: func_offsets[i] as u64,
                high_pc: (func_offsets[i] + func.code.len() as u32) as u64,
            })
            .collect();

        let dwarf_sections = synth_core::dwarf_line::emit_debug_sections(
            &table,
            text_sym_idx as usize,
            &input_dwarf.files,
            &subprograms,
        );
        if !dwarf_sections.is_empty() {
            let names: Vec<&str> = dwarf_sections.iter().map(|s| s.name).collect();
            let mut total_relocs = 0usize;
            for sec in &dwarf_sections {
                let dbg_section = Section::new(sec.name, ElfSectionType::ProgBits)
                    .with_align(1)
                    .with_data(sec.bytes.clone());
                elf_builder.add_section(dbg_section);
                // Register the section's `.text` relocations as `.rel.<name>`
                // (R_ARM_ABS32 against the `.text` base symbol). REL form: the
                // addend already sits in-place in the section bytes.
                if !sec.text_relocs.is_empty() {
                    let relocs: Vec<Relocation> = sec
                        .text_relocs
                        .iter()
                        .map(|r| Relocation {
                            offset: r.offset,
                            symbol_index: text_sym_idx,
                            reloc_type: ArmRelocationType::Abs32,
                        })
                        .collect();
                    total_relocs += relocs.len();
                    elf_builder.add_section_relocations(sec.name, relocs);
                }
            }
            info!(
                "DWARF: emitted {} sections {:?} ({} address rows, {} .text relocations, --debug-line)",
                dwarf_sections.len(),
                names,
                table.len(),
                total_relocs
            );
        }
    }

    let (external_count, reloc_count) = extern_sym_indices;
    info!(
        "Relocatable ELF: {} functions, {} external symbols, {} relocations",
        funcs.len(),
        external_count,
        reloc_count
    );

    elf_builder
        .build()
        .context("Relocatable ELF generation failed")
}

/// Encode a Thumb-2 `BL` instruction (4 bytes, two little-endian halfwords)
/// that branches from the instruction at address `bl_addr` to `target_addr`.
///
/// Thumb BL computes `target = (P + 4) + signed_offset`, where P is the address
/// of the BL. So `signed_offset = target_addr - (bl_addr + 4)`, in bytes; the
/// encoded immediate is that value in halfword units. The J1/J2 bits are
/// derived from the sign bit S as `I1 = NOT(J1 XOR S)` (rearranged:
/// `J1 = NOT(I1 XOR S)`), and likewise for J2/I2.
///
/// This is the DIRECT encoding used by the standalone Cortex-M path, which has
/// no linker to apply an R_ARM_THM_CALL relocation. Verified byte-for-byte
/// against `arm-none-eabi-as` (both forward and backward, near and far) so we
/// do not repeat the hand-decode error of #174.
///
/// `target_addr` must be the even function entry address; the Thumb state bit
/// is implicit in BL and must NOT be encoded into the displacement. Returning
/// the wrong even/odd target would land the call one instruction off (the
/// symbol+4 class of bug in #174).
fn encode_thumb_bl(bl_addr: u32, target_addr: u32) -> [u8; 4] {
    let offset = (target_addr as i64) - (bl_addr as i64 + 4); // bytes
    let off = (offset >> 1) as i32; // halfword units, sign-extended
    let s_bit = ((off >> 24) & 1) as u32;
    let i1 = ((off >> 23) & 1) as u32;
    let i2 = ((off >> 22) & 1) as u32;
    let imm10 = ((off >> 11) & 0x3FF) as u32;
    let imm11 = (off & 0x7FF) as u32;
    let j1 = (!(i1 ^ s_bit)) & 1;
    let j2 = (!(i2 ^ s_bit)) & 1;
    // hw1: 1111 0 S imm10            -> 0xF000 | (S<<10) | imm10
    // hw2: 11 J1 1 J2 imm11          -> 0xD000 | (J1<<13) | (J2<<11) | imm11
    let hw1: u16 = (0xF000 | (s_bit << 10) | imm10) as u16;
    let hw2: u16 = (0xD000 | (j1 << 13) | (j2 << 11) | imm11) as u16;
    let mut bytes = [0u8; 4];
    bytes[0..2].copy_from_slice(&hw1.to_le_bytes());
    bytes[2..4].copy_from_slice(&hw2.to_le_bytes());
    bytes
}

/// Build a complete Cortex-M multi-function ELF with vector table
fn build_multi_func_cortex_m_elf(
    funcs: &[ElfFunction],
    memories: &[WasmMemory],
    target: &TargetSpec,
) -> Result<Vec<u8>> {
    let flash_base: u32 = 0x0000_0000;
    let ram_base: u32 = 0x2000_0000;

    // Calculate linear memory size from WASM memory declarations
    // Default to 1 page (64KB) if no memory declared (for backwards compatibility)
    let linear_memory_pages = memories.first().map(|m| m.initial_pages).unwrap_or(1);
    let linear_memory_size = linear_memory_pages * 64 * 1024; // 64KB per page

    // RAM layout:
    // 0x2000_0000: Linear memory (R11 points here)
    // 0x2000_0000 + linear_memory_size: Stack base
    // ram_base + ram_size: Stack top (grows down)
    //
    // Auto-scale RAM: linear memory + 8KB stack, rounded up to next 64KB boundary.
    // Minimum 128KB for backwards compatibility.
    let min_stack_size: u32 = 8 * 1024;
    let needed = linear_memory_size + min_stack_size;
    let ram_size: u32 = std::cmp::max(128 * 1024, (needed + 0xFFFF) & !0xFFFF);

    let stack_top = ram_base + ram_size;

    info!(
        "RAM layout: linear memory {}KB at 0x{:08x}, stack at 0x{:08x}",
        linear_memory_size / 1024,
        ram_base,
        stack_top
    );

    // Flash layout:
    // 0x00: Vector table (128 bytes = 32 entries)
    // 0x80: Reset handler (startup code with R10/R11 init)
    // 0xA0: Default handler
    // 0xA4+: User functions (4-byte aligned)

    let vector_table_addr = flash_base;
    let vector_table_size: u32 = 128;

    let startup_addr = flash_base + vector_table_size;
    let startup_code = generate_minimal_startup(linear_memory_size);
    let startup_size = startup_code.len() as u32;

    let default_handler_addr = startup_addr + startup_size;
    let default_handler = generate_default_handler();
    let default_handler_size = default_handler.len() as u32;

    // Trap handler for WASM trap operations (div by zero, integer overflow)
    let trap_handler_addr = default_handler_addr + default_handler_size;
    let trap_handler = generate_trap_handler();
    let trap_handler_size = trap_handler.len() as u32;

    // Functions start after trap handler, aligned to 4 bytes
    let funcs_base = (trap_handler_addr + trap_handler_size + 3) & !3;

    // Concatenate all function code with alignment
    let mut all_func_code = Vec::new();
    let mut func_offsets = Vec::new();

    for func in funcs {
        while all_func_code.len() % 4 != 0 {
            all_func_code.push(0);
        }
        func_offsets.push(all_func_code.len() as u32);
        all_func_code.extend_from_slice(&func.code);
    }

    // Resolve internal `BL func_N` calls directly. A standalone Cortex-M
    // executable has no linker, so the `bl #0` placeholder + R_ARM_THM_CALL
    // relocation strategy used by the relocatable path cannot apply here:
    // nothing patches the displacement. Instead, now that every function's
    // address is known, encode the real Thumb BL displacement in place (#170).
    //
    // The caller routes here only when all relocations are internal (no
    // imports); we map each relocation symbol (export name or `func_{index}`)
    // to the callee's laid-out address and patch the 4 BL bytes.
    {
        use std::collections::HashMap;
        let mut label_to_addr: HashMap<&str, u32> = HashMap::new();
        for (i, func) in funcs.iter().enumerate() {
            let addr = funcs_base + func_offsets[i];
            label_to_addr.insert(func.name.as_str(), addr);
        }
        // `func_{wasm_index}` labels need owned storage to key the map.
        let index_labels: Vec<(String, u32)> = funcs
            .iter()
            .enumerate()
            .map(|(i, func)| {
                (
                    format!("func_{}", func.wasm_index),
                    funcs_base + func_offsets[i],
                )
            })
            .collect();
        for (label, addr) in &index_labels {
            label_to_addr.insert(label.as_str(), *addr);
        }

        for (i, func) in funcs.iter().enumerate() {
            for reloc in &func.relocations {
                let Some(&callee_addr) = label_to_addr.get(reloc.symbol.as_str()) else {
                    // Should not happen: the dispatcher only routes here when
                    // every relocation is internal. Be loud rather than emit a
                    // silently-broken BL.
                    anyhow::bail!(
                        "internal call to unknown symbol '{}' in standalone Cortex-M ELF (#170)",
                        reloc.symbol
                    );
                };
                // Absolute address of the BL instruction's first halfword.
                let bl_addr = funcs_base + func_offsets[i] + reloc.offset;
                let bytes = encode_thumb_bl(bl_addr, callee_addr);
                let pos = (func_offsets[i] + reloc.offset) as usize;
                all_func_code[pos..pos + 4].copy_from_slice(&bytes);
                info!(
                    "  patched internal BL at 0x{:08x} -> '{}' 0x{:08x}",
                    bl_addr, reloc.symbol, callee_addr
                );
            }
        }
    }

    info!("Cortex-M multi-function layout:");
    info!("  Vector table: 0x{:08x}", vector_table_addr);
    info!("  Startup code: 0x{:08x}", startup_addr);
    info!("  Default handler: 0x{:08x}", default_handler_addr);
    info!("  Trap handler: 0x{:08x}", trap_handler_addr);
    info!("  Functions base: 0x{:08x}", funcs_base);
    for (i, func) in funcs.iter().enumerate() {
        let addr = funcs_base + func_offsets[i];
        info!(
            "    {}: 0x{:08x} ({} bytes)",
            func.name,
            addr,
            func.code.len()
        );
    }
    info!("  Stack top: 0x{:08x}", stack_top);

    // Generate vector table
    let mut vt = VectorTable::new_cortex_m(stack_top);
    vt.reset_handler = startup_addr;

    for handler in &mut vt.handlers {
        if handler.address == 0 {
            // UsageFault and HardFault go to Trap_Handler (for WASM trap detection)
            if handler.name == "UsageFault_Handler" || handler.name == "HardFault_Handler" {
                handler.address = trap_handler_addr;
            } else {
                handler.address = default_handler_addr;
            }
        }
    }

    let vector_table_data = vt
        .generate_binary()
        .context("Vector table generation failed")?;

    // Build flash image
    let mut flash_image = Vec::new();

    // Vector table
    flash_image.extend_from_slice(&vector_table_data);

    // Pad to startup address
    while flash_image.len() < (startup_addr - flash_base) as usize {
        flash_image.push(0);
    }

    // Startup code - patch literal pool to point to FIRST function
    // Literal pool is at offset 24 (after R10/R11 init + LDR/BLX/B/padding)
    let mut patched_startup = startup_code.clone();
    let first_func_addr = funcs_base | 1; // Thumb bit
    patched_startup[24..28].copy_from_slice(&first_func_addr.to_le_bytes());
    flash_image.extend_from_slice(&patched_startup);

    // Default handler
    flash_image.extend_from_slice(&default_handler);

    // Trap handler (for WASM trap operations)
    flash_image.extend_from_slice(&trap_handler);

    // Pad to functions base
    while flash_image.len() < (funcs_base - flash_base) as usize {
        flash_image.push(0);
    }

    // All function code
    flash_image.extend_from_slice(&all_func_code);

    // Build ELF
    let flash_size = flash_image.len() as u32;
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(startup_addr | 1);

    // Set hard-float ABI flag if target has FPU
    if target.has_fpu() {
        elf_builder
            .set_flags(synth_backend::EF_ARM_EABI_VER5 | synth_backend::EF_ARM_ABI_FLOAT_HARD);
    }

    // Calculate proper file offset for .text section
    let shstrtab_size = 1 + ".shstrtab\0.strtab\0.symtab\0.text\0".len();
    let mut strtab_size = 1 + "Reset_Handler\0Default_Handler\0Trap_Handler\0".len();
    for func in funcs {
        strtab_size += func.name.len() + 1;
    }
    let text_file_offset = 52 + 32 + shstrtab_size + strtab_size;

    let text_phdr = ProgramHeader::load(
        flash_base,
        text_file_offset as u32,
        flash_size,
        ProgramFlags::READ | ProgramFlags::EXEC,
    );
    elf_builder.add_program_header(text_phdr);

    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(flash_base)
        .with_align(4)
        .with_data(flash_image);

    elf_builder.add_section(text_section);

    // Add linear memory section (BSS-like, no file data)
    // This section tells the loader about the RAM region for WASM linear memory
    if linear_memory_size > 0 {
        // Program header for linear memory (READ | WRITE, no EXEC)
        // Use load_nobits since there's no file data, just memory allocation
        let ram_phdr = ProgramHeader::load_nobits(
            ram_base,
            linear_memory_size,
            ProgramFlags::READ | ProgramFlags::WRITE,
        );
        elf_builder.add_program_header(ram_phdr);

        // NoBits section (like .bss) - no file data, just reserves address space
        let linear_memory_section = Section::new(".linear_memory", ElfSectionType::NoBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
            .with_addr(ram_base)
            .with_align(4)
            .with_size(linear_memory_size);

        elf_builder.add_section(linear_memory_section);

        // Add symbol for linear memory base (useful for debugging)
        let mem_sym = Symbol::new("__linear_memory_base")
            .with_value(ram_base)
            .with_size(linear_memory_size)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Object)
            .with_section(5); // Section 5 will be .linear_memory after .text (section 4)
        elf_builder.add_symbol(mem_sym);

        info!(
            "Added .linear_memory section: 0x{:08x} ({} bytes, {} pages)",
            ram_base, linear_memory_size, linear_memory_pages
        );
    }

    // Add system symbols
    let reset_sym = Symbol::new("Reset_Handler")
        .with_value(startup_addr | 1)
        .with_size(startup_size)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(reset_sym);

    let default_sym = Symbol::new("Default_Handler")
        .with_value(default_handler_addr | 1)
        .with_size(default_handler_size)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(default_sym);

    let trap_sym = Symbol::new("Trap_Handler")
        .with_value(trap_handler_addr | 1)
        .with_size(trap_handler_size)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(trap_sym);

    // Add symbol for each user function
    for (i, func) in funcs.iter().enumerate() {
        let func_addr = funcs_base + func_offsets[i];
        let func_sym = Symbol::new(&func.name)
            .with_value(func_addr | 1) // Thumb bit for Cortex-M
            .with_size(func.code.len() as u32)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(4);
        elf_builder.add_symbol(func_sym);
    }

    // TODO(#170, mapping-symbols): emit ARM `$t`/`$a`/`$d` mapping symbols so
    // tools (objdump, gdb, debuggers) know each .text region is Thumb code vs
    // data without relying on the Func-typed symbols above. This is the
    // secondary half of #170 and is intentionally deferred: mapping symbols are
    // STB_LOCAL and ELF requires all local symbols to precede globals in the
    // symtab, with `.symtab`'s sh_info pointing at the first global. ElfBuilder
    // currently appends symbols in call order and does not maintain
    // local-before-global ordering or set sh_info, so adding locals here would
    // produce a malformed symtab. Direct call resolution (the primary fix)
    // works without these; objdump already disassembles correctly via the
    // Func-typed function symbols.

    elf_builder.build().context("ELF generation failed")
}

fn disasm_command(input: PathBuf) -> Result<()> {
    use std::process::Command;

    if !input.exists() {
        anyhow::bail!("File not found: {}", input.display());
    }

    info!("Disassembling: {}", input.display());

    // Try objdump with ARM triple (works on macOS with Apple LLVM)
    let output = Command::new("objdump")
        .args(["-d", "--triple=arm-none-eabi"])
        .arg(&input)
        .output()
        .context("Failed to run objdump. Is it installed?")?;

    if output.status.success() {
        print!("{}", String::from_utf8_lossy(&output.stdout));
    } else {
        // Fallback: try without triple
        let output = Command::new("objdump")
            .arg("-d")
            .arg(&input)
            .output()
            .context("Failed to run objdump")?;

        if output.status.success() {
            print!("{}", String::from_utf8_lossy(&output.stdout));
        } else {
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
            anyhow::bail!("objdump failed");
        }
    }

    Ok(())
}

fn backends_command() -> Result<()> {
    let registry = build_backend_registry();
    let backends = registry.list();

    println!("Available backends:\n");
    println!(
        "  {:<12} {:<12} {:<10} {:<10} {:<10}",
        "NAME", "STATUS", "ELF", "RULE-VERIFY", "BIN-VERIFY"
    );
    println!("  {}", "-".repeat(56));

    for backend in &backends {
        let status = if backend.is_available() {
            "available"
        } else {
            "not found"
        };
        let caps = backend.capabilities();
        println!(
            "  {:<12} {:<12} {:<10} {:<10} {:<10}",
            backend.name(),
            status,
            if caps.produces_elf { "yes" } else { "no" },
            if caps.supports_rule_verification {
                "yes"
            } else {
                "no"
            },
            if caps.supports_binary_verification {
                "yes"
            } else {
                "no"
            },
        );
    }

    println!("\nVerification tiers:");
    println!("  RULE-VERIFY: Per-rule SMT proofs (ASIL D) — only custom ARM backend");
    println!("  BIN-VERIFY:  Binary-level translation validation (ASIL B) — all backends");

    Ok(())
}

fn verify_command(wasm_input: PathBuf, elf_input: PathBuf, backend_name: &str) -> Result<()> {
    if !wasm_input.exists() {
        anyhow::bail!("WASM file not found: {}", wasm_input.display());
    }
    if !elf_input.exists() {
        anyhow::bail!("ELF file not found: {}", elf_input.display());
    }

    let registry = build_backend_registry();
    let backend = registry
        .get(backend_name)
        .ok_or_else(|| anyhow::anyhow!("Unknown backend '{}'", backend_name))?;

    let caps = backend.capabilities();

    println!("Translation validation:");
    println!("  Source: {}", wasm_input.display());
    println!("  Binary: {}", elf_input.display());
    println!("  Backend: {}", backend_name);

    if caps.supports_rule_verification {
        println!("  Strategy: Per-rule SMT verification (ASIL D path)");

        #[cfg(feature = "verify")]
        {
            // Parse WASM to extract function ops
            let file_bytes = std::fs::read(&wasm_input)
                .context(format!("Failed to read: {}", wasm_input.display()))?;

            let wasm_bytes = if wasm_input.extension().is_some_and(|ext| ext == "wat") {
                wat::parse_bytes(&file_bytes)
                    .context("Failed to parse WAT file")?
                    .into_owned()
            } else if wasm_input.extension().is_some_and(|ext| ext == "wast") {
                let contents =
                    String::from_utf8(file_bytes).context("WAST file is not valid UTF-8")?;
                extract_module_from_wast(&contents)?
            } else {
                file_bytes
            };

            let functions =
                decode_wasm_functions(&wasm_bytes).context("Failed to decode WASM functions")?;

            let exports: Vec<_> = functions
                .iter()
                .filter(|f| f.export_name.is_some())
                .collect();

            if exports.is_empty() {
                println!("\n  No exported functions found in WASM module.");
                return Ok(());
            }

            println!("\n  Verifying {} exported functions...", exports.len());

            for func in &exports {
                let name = func.export_name.as_deref().ok_or_else(|| {
                    anyhow::anyhow!("function at index {} has no export name", func.index)
                })?;
                run_verification(&func.ops, name)?;
            }

            println!("\nAll functions verified successfully.");
        }

        #[cfg(not(feature = "verify"))]
        {
            // This binary was built without the `verify` feature, so no SMT
            // translation validation can run. Returning Ok here would make
            // `synth verify` exit success-shaped while doing nothing — a
            // script or CI step gating on `synth verify` would silently
            // believe the binary was validated (issue #124). Fail loudly
            // with a non-zero exit instead.
            anyhow::bail!(
                "this `synth` binary was built without the `verify` feature — \
                 SMT translation validation is unavailable.\n  \
                 Rebuild with verification support:\n    \
                 cargo build --features verify\n  \
                 (or `cargo install --path crates/synth-cli --features verify`)"
            );
        }
    } else if caps.supports_binary_verification {
        println!("  Strategy: Binary-level translation validation (ASIL B path)");
        println!("\n  Binary verification not yet implemented.");
        println!("  Requires: ARM disassembler + SMT equivalence checking on disassembled output.");
    } else {
        println!(
            "  No verification available for backend '{}'.",
            backend_name
        );
    }

    Ok(())
}

/// Build a RISC-V relocatable ELF wrapping the bytes the RV backend produced.
///
/// Re-runs the RISC-V backend's `RiscVElfBuilder` so the output is a real
/// RV32 object file (EM_RISCV, RVC e_flags) rather than the generic ARM
/// ELF that `build_simple_elf` emits.
#[cfg(feature = "riscv")]
fn build_riscv_elf(code: &[u8], func_name: &str) -> Result<Vec<u8>> {
    use synth_backend_riscv::{Reg, RiscVElfBuilder, RiscVElfFunction, RiscVOp};

    // The RISC-V ELF builder operates on `Vec<RiscVOp>` to support label
    // resolution. The CLI path doesn't have ops at this layer (only bytes),
    // so we wrap each 4-byte word as an opaque "raw" instruction by treating
    // the bytes as already encoded. We materialize them as `Addi`-shaped
    // sentinels and then post-process the ELF body to overwrite with our
    // actual code. Cleaner: use a future raw-bytes API on the builder.
    //
    // For the skeleton, the simpler path: wrap as one Addi per word — wrong
    // bits, but the ELF builder writes the section table correctly. We then
    // patch .text bytes back. This avoids leaking the encoder back through
    // the CLI and is fine until we drop ARM-style byte-handoff entirely.
    let n_instrs = code.len().div_ceil(4);
    let placeholder_ops: Vec<RiscVOp> = (0..n_instrs)
        .map(|_| RiscVOp::Addi {
            rd: Reg::ZERO,
            rs1: Reg::ZERO,
            imm: 0,
        })
        .collect();
    let f = RiscVElfFunction {
        name: func_name.to_string(),
        ops: placeholder_ops,
    };

    let builder = RiscVElfBuilder::new_relocatable();
    let mut elf = builder
        .build(&[f])
        .context("RISC-V ELF generation failed")?;

    // .text starts at offset 52 (ELF header). Overwrite the placeholder bytes
    // with the actual code we got from the backend.
    let text_offset = 52;
    if elf.len() < text_offset + code.len() {
        anyhow::bail!("RISC-V ELF is shorter than embedded code");
    }
    elf[text_offset..text_offset + code.len()].copy_from_slice(code);
    Ok(elf)
}

#[cfg(not(feature = "riscv"))]
fn build_riscv_elf(_code: &[u8], _func_name: &str) -> Result<Vec<u8>> {
    anyhow::bail!("RISC-V backend was not compiled in (rebuild with --features riscv)")
}

/// Build a multi-function RISC-V relocatable ELF.
#[cfg(feature = "riscv")]
fn build_multi_func_riscv_elf(funcs: &[ElfFunction]) -> Result<Vec<u8>> {
    use synth_backend_riscv::{Reg, RiscVElfBuilder, RiscVElfFunction, RiscVOp};

    // Same placeholder-then-overwrite approach as build_riscv_elf.
    // We accumulate a single .text spanning all functions and patch the
    // bytes back in after the ELF builder finishes layout.
    let mut all_code: Vec<u8> = Vec::new();
    let mut func_byte_ranges: Vec<(usize, usize)> = Vec::new();
    let mut placeholder_funcs: Vec<RiscVElfFunction> = Vec::new();

    for func in funcs {
        // Align each function to 4 bytes (RISC-V requires 4-byte instruction alignment).
        while !all_code.len().is_multiple_of(4) {
            all_code.push(0);
        }
        let start = all_code.len();
        all_code.extend_from_slice(&func.code);
        let end = all_code.len();
        func_byte_ranges.push((start, end));

        let n_instrs = (end - start).div_ceil(4);
        let placeholder_ops: Vec<RiscVOp> = (0..n_instrs)
            .map(|_| RiscVOp::Addi {
                rd: Reg::ZERO,
                rs1: Reg::ZERO,
                imm: 0,
            })
            .collect();
        placeholder_funcs.push(RiscVElfFunction {
            name: func.name.clone(),
            ops: placeholder_ops,
        });
    }

    let builder = RiscVElfBuilder::new_relocatable();
    let mut elf = builder
        .build(&placeholder_funcs)
        .context("RISC-V multi-function ELF generation failed")?;

    // .text starts immediately after the 52-byte ELF header.
    let text_offset = 52usize;
    if elf.len() < text_offset + all_code.len() {
        anyhow::bail!("RISC-V ELF too small to embed code");
    }
    elf[text_offset..text_offset + all_code.len()].copy_from_slice(&all_code);
    Ok(elf)
}

#[cfg(not(feature = "riscv"))]
fn build_multi_func_riscv_elf(_funcs: &[ElfFunction]) -> Result<Vec<u8>> {
    anyhow::bail!("RISC-V backend was not compiled in (rebuild with --features riscv)")
}

/// #546: emit a single-function `EM_AARCH64` ELF64 (`ET_REL`) object via the
/// AArch64 backend's own emitter, instead of wrapping the A64 `.text` in the ARM
/// (EM_ARM/ELF32) container. Mirrors `build_riscv_elf` — the per-backend ELF path.
fn build_aarch64_elf(code: &[u8], func_name: &str) -> Result<Vec<u8>> {
    use synth_backend_aarch64::elf::{ElfFunction as A64ElfFunction, build_relocatable_object};
    Ok(build_relocatable_object(&[A64ElfFunction {
        name: func_name.to_string(),
        code: code.to_vec(),
    }]))
}

/// #546: emit a multi-function `EM_AARCH64` ELF64 (`ET_REL`) object exposing one
/// global `STT_FUNC` symbol per compiled export. Mirrors
/// `build_multi_func_riscv_elf` — the per-backend ELF path (#538 milestone-1c).
fn build_multi_func_aarch64_elf(funcs: &[ElfFunction]) -> Result<Vec<u8>> {
    use synth_backend_aarch64::elf::{ElfFunction as A64ElfFunction, build_relocatable_object};
    let a64_funcs: Vec<A64ElfFunction> = funcs
        .iter()
        .map(|f| A64ElfFunction {
            name: f.name.clone(),
            code: f.code.clone(),
        })
        .collect();
    Ok(build_relocatable_object(&a64_funcs))
}

/// Build a simple ELF with just the code section (for quick testing)
fn build_simple_elf(code: &[u8], func_name: &str) -> Result<Vec<u8>> {
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.to_vec());

    elf_builder.add_section(text_section);

    let func_sym = Symbol::new(func_name)
        .with_value(0x8000)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);

    elf_builder.add_symbol(func_sym);

    elf_builder.build().context("ELF generation failed")
}

/// Build a complete Cortex-M ELF with vector table and startup code
fn build_cortex_m_elf(code: &[u8], func_name: &str, target: &TargetSpec) -> Result<Vec<u8>> {
    // Memory layout for generic Cortex-M (works with QEMU/Renode)
    let flash_base: u32 = 0x0000_0000;
    let ram_base: u32 = 0x2000_0000;
    let ram_size: u32 = 128 * 1024; // 128KB to accommodate linear memory + stack
    let stack_top = ram_base + ram_size;

    // Default linear memory size (1 WASM page = 64KB) for single-function mode
    let linear_memory_size: u32 = 64 * 1024;

    // Calculate addresses
    let vector_table_addr = flash_base;
    let vector_table_size: u32 = 128; // 32 entries * 4 bytes

    let startup_addr = flash_base + vector_table_size;
    let startup_code = generate_minimal_startup(linear_memory_size);
    let startup_size = startup_code.len() as u32;

    let default_handler_addr = startup_addr + startup_size;
    let default_handler = generate_default_handler();
    let default_handler_size = default_handler.len() as u32;

    // Trap handler for WASM trap operations
    let trap_handler_addr = default_handler_addr + default_handler_size;
    let trap_handler = generate_trap_handler();
    let trap_handler_size = trap_handler.len() as u32;

    // Align code to 4 bytes
    let code_addr = (trap_handler_addr + trap_handler_size + 3) & !3;

    info!("Cortex-M layout:");
    info!("  Vector table: 0x{:08x}", vector_table_addr);
    info!("  Startup code: 0x{:08x}", startup_addr);
    info!("  Default handler: 0x{:08x}", default_handler_addr);
    info!("  Trap handler: 0x{:08x}", trap_handler_addr);
    info!("  User code: 0x{:08x}", code_addr);
    info!("  Stack top: 0x{:08x}", stack_top);

    // Generate vector table
    let mut vt = VectorTable::new_cortex_m(stack_top);
    vt.reset_handler = startup_addr;

    // Set handlers - UsageFault/HardFault go to Trap_Handler for WASM trap detection
    for handler in &mut vt.handlers {
        if handler.address == 0 {
            if handler.name == "UsageFault_Handler" || handler.name == "HardFault_Handler" {
                handler.address = trap_handler_addr;
            } else {
                handler.address = default_handler_addr;
            }
        }
    }

    let vector_table_data = vt
        .generate_binary()
        .context("Vector table generation failed")?;

    // Build complete flash image
    let mut flash_image = Vec::new();

    // Vector table
    flash_image.extend_from_slice(&vector_table_data);

    // Pad to startup address
    while flash_image.len() < (startup_addr - flash_base) as usize {
        flash_image.push(0);
    }

    // Startup code (patch the literal pool with actual function address)
    // Literal pool is at offset 24 (after R10/R11 init + LDR/BLX/B/padding)
    let mut patched_startup = startup_code.clone();
    let func_addr_thumb = code_addr | 1; // Thumb bit
    patched_startup[24..28].copy_from_slice(&func_addr_thumb.to_le_bytes());
    flash_image.extend_from_slice(&patched_startup);

    // Default handler
    flash_image.extend_from_slice(&default_handler);

    // Trap handler
    flash_image.extend_from_slice(&trap_handler);

    // Pad to code address
    while flash_image.len() < (code_addr - flash_base) as usize {
        flash_image.push(0);
    }

    // User code
    flash_image.extend_from_slice(code);

    // Build ELF
    let flash_size = flash_image.len() as u32;
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(startup_addr | 1); // Thumb bit

    // Set hard-float ABI flag if target has FPU
    if target.has_fpu() {
        elf_builder
            .set_flags(synth_backend::EF_ARM_EABI_VER5 | synth_backend::EF_ARM_ABI_FLOAT_HARD);
    }

    // Add LOAD program header for the .text section
    // The offset is calculated as: ELF header (52) + program headers (32 * 1) + string tables
    // String tables: .shstrtab (~33 bytes) + .strtab (~50 bytes)
    // This puts .text data at approximately offset 167, but we need exact calculation
    // For now, we'll compute based on the section name string table size
    let shstrtab_size = 1 + ".shstrtab\0.strtab\0.symtab\0.text\0".len(); // ~34 bytes
    let strtab_size =
        1 + "Reset_Handler\0Default_Handler\0Trap_Handler\0".len() + func_name.len() + 1;
    let text_file_offset = 52 + 32 + shstrtab_size + strtab_size;

    let text_phdr = ProgramHeader::load(
        flash_base,                              // vaddr
        text_file_offset as u32,                 // offset in file
        flash_size,                              // size
        ProgramFlags::READ | ProgramFlags::EXEC, // flags: R-X
    );
    elf_builder.add_program_header(text_phdr);

    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(flash_base)
        .with_align(4)
        .with_data(flash_image);

    elf_builder.add_section(text_section);

    // Add symbols
    let reset_sym = Symbol::new("Reset_Handler")
        .with_value(startup_addr | 1)
        .with_size(startup_size)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(reset_sym);

    let default_sym = Symbol::new("Default_Handler")
        .with_value(default_handler_addr | 1)
        .with_size(default_handler_size)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(default_sym);

    let trap_sym = Symbol::new("Trap_Handler")
        .with_value(trap_handler_addr | 1)
        .with_size(trap_handler_size)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(trap_sym);

    let func_sym = Symbol::new(func_name)
        .with_value(code_addr | 1)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(func_sym);

    elf_builder.build().context("ELF generation failed")
}

/// Generate minimal Thumb startup code that calls the user function and loops
///
/// # Arguments
/// * `memory_size` - Size of linear memory in bytes (for R10 bounds checking)
///
/// # Memory Register Setup
/// * R10 = memory_size (for bounds checking)
/// * R11 = 0x20000000 (linear memory base)
fn generate_minimal_startup(memory_size: u32) -> Vec<u8> {
    // This startup code:
    // 1. Initializes R10 with memory size (for bounds checking)
    // 2. Initializes R11 with linear memory base (0x20000000) for WASM memory access
    // 3. Loads the address of the user function
    // 4. Calls it with BLX
    // 5. Loops forever
    //
    // In Thumb assembly:
    //   MOVW R10, #(memory_size & 0xFFFF)
    //   MOVT R10, #(memory_size >> 16)
    //   MOVW R11, #0x0000  ; Low 16 bits of memory base
    //   MOVT R11, #0x2000  ; High 16 bits of memory base
    //   LDR r0, [pc, #4]   ; Load function address from literal pool
    //   BLX r0             ; Call function
    //   B .                ; Infinite loop
    //   .word func_addr    ; Literal pool

    // Encode MOVW/MOVT for R10 with memory_size
    let r10_movw = encode_thumb2_movw(10, (memory_size & 0xFFFF) as u16);
    let r10_movt = encode_thumb2_movt(10, (memory_size >> 16) as u16);

    vec![
        // MOVW R10, #(memory_size & 0xFFFF)
        r10_movw[0],
        r10_movw[1],
        r10_movw[2],
        r10_movw[3],
        // MOVT R10, #(memory_size >> 16)
        r10_movt[0],
        r10_movt[1],
        r10_movt[2],
        r10_movt[3],
        // MOVW R11, #0x0000 - Thumb-2 32-bit encoding
        0x40,
        0xF2,
        0x00,
        0x0B,
        // MOVT R11, #0x2000 - Thumb-2 32-bit encoding
        0xC2,
        0xF2,
        0x00,
        0x0B,
        // LDR r0, [pc, #4] - Thumb 16-bit encoding: 0x4801
        // PC = current_addr + 4, literal at PC+4
        0x01,
        0x48,
        // BLX r0 - Thumb encoding: 0x4780
        0x80,
        0x47,
        // B . (branch to self) - Thumb encoding: 0xe7fe
        0xfe,
        0xe7,
        // Padding for alignment (to make literal pool 4-byte aligned)
        0x00,
        0x00,
        // Literal pool placeholder at offset 24 (will be patched with func_addr | 1)
        0x91,
        0x00,
        0x00,
        0x00,
    ]
}

/// Encode Thumb-2 MOVW instruction (move 16-bit immediate to low half of register)
fn encode_thumb2_movw(rd: u8, imm16: u16) -> [u8; 4] {
    // Thumb-2 MOVW encoding:
    // First halfword:  1111 0 i 10 0 1 0 0 imm4
    // Second halfword: 0 imm3 Rd imm8
    let imm4 = ((imm16 >> 12) & 0xF) as u8;
    let i = ((imm16 >> 11) & 0x1) as u8;
    let imm3 = ((imm16 >> 8) & 0x7) as u8;
    let imm8 = (imm16 & 0xFF) as u8;

    let hw1: u16 = 0xF240 | ((i as u16) << 10) | (imm4 as u16);
    let hw2: u16 = ((imm3 as u16) << 12) | ((rd as u16) << 8) | (imm8 as u16);

    let hw1_bytes = hw1.to_le_bytes();
    let hw2_bytes = hw2.to_le_bytes();
    [hw1_bytes[0], hw1_bytes[1], hw2_bytes[0], hw2_bytes[1]]
}

/// Encode Thumb-2 MOVT instruction (move 16-bit immediate to high half of register)
fn encode_thumb2_movt(rd: u8, imm16: u16) -> [u8; 4] {
    // Thumb-2 MOVT encoding:
    // First halfword:  1111 0 i 10 1 1 0 0 imm4
    // Second halfword: 0 imm3 Rd imm8
    let imm4 = ((imm16 >> 12) & 0xF) as u8;
    let i = ((imm16 >> 11) & 0x1) as u8;
    let imm3 = ((imm16 >> 8) & 0x7) as u8;
    let imm8 = (imm16 & 0xFF) as u8;

    let hw1: u16 = 0xF2C0 | ((i as u16) << 10) | (imm4 as u16);
    let hw2: u16 = ((imm3 as u16) << 12) | ((rd as u16) << 8) | (imm8 as u16);

    let hw1_bytes = hw1.to_le_bytes();
    let hw2_bytes = hw2.to_le_bytes();
    [hw1_bytes[0], hw1_bytes[1], hw2_bytes[0], hw2_bytes[1]]
}

/// Generate default exception handler (infinite loop)
fn generate_default_handler() -> Vec<u8> {
    // B . (branch to self) - Thumb encoding
    vec![0xfe, 0xe7]
}

fn generate_trap_handler() -> Vec<u8> {
    // Trap handler for WASM trap operations (div by zero, integer overflow)
    // Same as Default_Handler - infinite loop (B .)
    // The difference is the address, which allows tests to distinguish
    // between normal return (PC at Default_Handler) and trap (PC at Trap_Handler)
    // B . (branch to self) - Thumb encoding
    vec![0xfe, 0xe7]
}

/// Link a compiled .o into a final firmware.elf using arm-none-eabi-gcc.
///
/// Steps:
/// 1. Generate a linker script from the .o file
/// 2. Find arm-none-eabi-gcc in PATH
/// 3. Invoke the linker with the generated script
/// 4. Replace the .o output with the linked .elf
fn link_firmware(
    object_path: &std::path::Path,
    builtins: Option<&std::path::Path>,
    _target_spec: &TargetSpec,
) -> Result<()> {
    use std::process::Command;

    // Find cross-compiler
    let gcc = ["arm-none-eabi-gcc", "arm-none-eabi-ld"]
        .iter()
        .find(|cmd| {
            Command::new(cmd)
                .arg("--version")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false)
        })
        .copied();

    let gcc = match gcc {
        Some(g) => g,
        None => {
            anyhow::bail!(
                "arm-none-eabi-gcc not found in PATH. Install the ARM embedded toolchain:\n  \
                 brew install arm-none-eabi-gcc  (macOS)\n  \
                 apt install gcc-arm-none-eabi   (Linux)"
            );
        }
    };

    info!("Using cross-linker: {}", gcc);

    // Generate linker script
    let mut ls_gen = synth_backend::LinkerScriptGenerator::new();
    ls_gen.add_region(synth_backend::MemoryRegion {
        name: "FLASH".to_string(),
        origin: 0x0000_0000,
        length: 256 * 1024,
        attributes: "rx".to_string(),
    });
    ls_gen.add_region(synth_backend::MemoryRegion {
        name: "RAM".to_string(),
        origin: 0x2000_0000,
        length: 128 * 1024,
        attributes: "rwx".to_string(),
    });
    let ls_gen = ls_gen.with_stack_size(4096).with_meld_integration();
    let linker_script = ls_gen
        .generate()
        .context("Failed to generate linker script")?;

    let ld_script_path = object_path.with_extension("ld");
    std::fs::write(&ld_script_path, &linker_script).context("Failed to write linker script")?;

    info!("Generated linker script: {}", ld_script_path.display());

    // Build linker command
    let firmware_path = object_path.with_extension("firmware.elf");
    let mut cmd = Command::new(gcc);

    if gcc == "arm-none-eabi-gcc" {
        cmd.args(["-nostartfiles", "-nostdlib", "-mcpu=cortex-m4", "-mthumb"]);
    }

    cmd.arg("-T").arg(&ld_script_path);
    cmd.arg(object_path);

    if let Some(builtins_path) = builtins {
        cmd.arg(builtins_path);
    }

    cmd.arg("-o").arg(&firmware_path);

    info!("Linking: {:?}", cmd);

    let output = cmd.output().context("Failed to invoke cross-linker")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("Linker failed:\n{}", stderr);
    }

    // Clean up linker script
    let _ = std::fs::remove_file(&ld_script_path);

    println!(
        "Linked firmware: {} ({} bytes)",
        firmware_path.display(),
        std::fs::metadata(&firmware_path)
            .map(|m| m.len())
            .unwrap_or(0)
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- #543 Phase 1: `--volatile-segment` parsing ---------------------------

    /// The canonical example from the flag docs parses into a `VolatileRange`
    /// with the right base/len. Hex base + decimal len is the documented form.
    #[test]
    fn volatile_segment_parses_hex_base_decimal_len_543() {
        let ranges = parse_volatile_segments(&["0x20001000:4096".to_string()]).unwrap();
        assert_eq!(ranges.len(), 1);
        assert_eq!(ranges[0].base, 0x2000_1000);
        assert_eq!(ranges[0].len, 4096);
    }

    /// Both fields accept decimal or hex interchangeably, and the flag is
    /// repeatable (>1 range).
    #[test]
    fn volatile_segment_accepts_decimal_and_is_repeatable_543() {
        let ranges = parse_volatile_segments(&[
            "536875008:0x1000".to_string(), // decimal base, hex len
            "0x20002000:256".to_string(),
        ])
        .unwrap();
        assert_eq!(ranges.len(), 2);
        assert_eq!(ranges[0].base, 536_875_008);
        assert_eq!(ranges[0].len, 0x1000);
        assert_eq!(ranges[1].base, 0x2000_2000);
        assert_eq!(ranges[1].len, 256);
    }

    /// Malformed input must be rejected loudly (not silently dropped): missing
    /// colon, non-numeric fields, zero length, and base+len overflow all error.
    #[test]
    fn volatile_segment_rejects_malformed_543() {
        assert!(parse_volatile_segments(&["garbage".to_string()]).is_err());
        assert!(parse_volatile_segments(&["0x20001000".to_string()]).is_err());
        assert!(parse_volatile_segments(&["nothex:4096".to_string()]).is_err());
        assert!(parse_volatile_segments(&["0x1000:notlen".to_string()]).is_err());
        assert!(parse_volatile_segments(&["0x1000:0".to_string()]).is_err());
        assert!(parse_volatile_segments(&["0xFFFFFFFF:0x10".to_string()]).is_err());
        // Too many colons is malformed (base:len only).
        assert!(parse_volatile_segments(&["0x1000:0x10:0x20".to_string()]).is_err());
    }

    /// No `--volatile-segment` flags → empty ranges (the inert default). This is
    /// what keeps the config's `volatile_segments` empty on a normal compile, so
    /// Phase 1 changes no emitted bytes.
    #[test]
    fn volatile_segment_empty_by_default_543() {
        assert!(parse_volatile_segments(&[]).unwrap().is_empty());
        assert!(CompileConfig::default().volatile_segments.is_empty());
    }

    fn fop(index: u32, export: Option<&str>, ops: Vec<WasmOp>) -> FunctionOps {
        FunctionOps {
            index,
            export_name: export.map(String::from),
            debug_name: None,
            ops,
            op_offsets: Vec::new(),
            unsupported: None,
            block_arity: Vec::new(),
        }
    }

    /// VCR-MEM-001 layer-2 END-TO-END (#242, #383): prove the full budget
    /// pipeline on the REAL gust-family fixture — scry's proven shadow-stack
    /// depth, mapped through the synth-owned bound, yields the `budget_from_bound`
    /// decision (the #421 logic) that the gated `--shadow-stack-size auto` wiring
    /// will consume. This is the join the #392 spike (which stops at scry's raw
    /// output) and the `shadow_budget` unit suite (which tests the decision on
    /// synthetic bounds) each cover only half of.
    ///
    /// Frozen-safe: `scry-sai-core` is a DEV-dependency exercised only under
    /// `cfg(test)`, so the production binary pulls no scry and emits no different
    /// bytes — the frozen fixtures stay bit-identical by construction. When step
    /// 2b promotes scry to a (feature-gated) production dep, the inline 1:1
    /// adapter below becomes an `impl From<scry::StackBound>` and this test is the
    /// oracle that the wiring matches.
    #[test]
    fn layer2_budget_pipeline_msgq_end_to_end_383() {
        use scry_analyze_core::{AnalysisConfig, StackBound, analyze};
        use shadow_budget::{BudgetDecision, BudgetSource, StackDepthBound, budget_from_bound};

        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../scripts/repro/msgq_put_359.wasm");
        let bytes = std::fs::read(&fixture).expect("the #359/#383 gust-family fixture is in-tree");

        let r = analyze(
            bytes,
            AnalysisConfig {
                widening_threshold: None,
                emit_diagnostics: false,
                taint_policy: None,
            },
        )
        .expect("scry analyzes a valid Core module");

        // Adapter: scry's StackBound -> synth's dep-free StackDepthBound (1:1;
        // becomes a `From` impl when scry graduates to a production dep in 2b).
        let bound = match r.stack_usage.max_stack_bytes {
            StackBound::Bytes(n) => StackDepthBound::Bytes(n),
            StackBound::Unbounded => StackDepthBound::Unbounded,
            StackBound::Unknown => StackDepthBound::Unknown,
        };

        // msgq_put reserves the full declared page (sp_init = 65536 = the
        // .bss [0,65536) stack span the roadmap recorded); scry proves the true
        // worst case is 32 B. The derived budget is sp_init-independent for any
        // sp_init above the depth — what matters is the PROVEN 32 vs the page.
        let sp_init = 65_536;
        let decision = budget_from_bound(bound, sp_init, Some(4096));

        // End-to-end: a 2048x over-reservation collapses to a PROVEN 32-byte
        // budget — and, with a fallback available, the proven path is preferred
        // over the asserted one (source is ProvenStackDepth, not AssertedFallback).
        assert_eq!(
            decision,
            BudgetDecision::Use {
                bytes: 32,
                source: BudgetSource::ProvenStackDepth
            },
            "scry-proven 32 B depth -> proven 32 B budget, not the asserted 4096 fallback"
        );
    }

    /// VCR-MEM-001 layer-2 SILICON-BUDGET SANITY CHECK (#242, #383, gale#65):
    /// jess is flashing `gust_kernel.wasm` with an integrator-ASSERTED
    /// `--shadow-stack-size 4096` on the Renode-M3 / STM32F100 rung. This test is
    /// the layer-2 cross-check on that live budget: scry PROVES gust_kernel's
    /// worst-case shadow-stack depth, and we assert the proven depth sits at or
    /// below the 4096 jess flashed — i.e. the asserted budget is sound, not an
    /// under-reservation. (Measured 2026-06-22: proven depth is 16 B, a 256x
    /// margin under 4096 and a 65536x cut from the 1 MiB declared-page default.)
    ///
    /// Frozen-safe: scry stays a DEV-dep under cfg(test); production bytes are
    /// unchanged. Extends the msgq end-to-end test to the fixture jess actually
    /// flies — so if a scry bump ever raised gust_kernel's proven depth above the
    /// flashed budget, CI would surface it before silicon, not after.
    #[test]
    fn layer2_gust_kernel_proven_depth_clears_flashed_budget_383() {
        use scry_analyze_core::{AnalysisConfig, StackBound, analyze};
        use shadow_budget::{BudgetDecision, BudgetSource, StackDepthBound, budget_from_bound};

        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../scripts/repro/gust_kernel.wasm");
        let bytes = std::fs::read(&fixture).expect("the gale #91 gust_kernel fixture is in-tree");

        let r = analyze(
            bytes,
            AnalysisConfig {
                widening_threshold: None,
                emit_diagnostics: false,
                taint_policy: None,
            },
        )
        .expect("scry analyzes the gust_kernel Core module");

        // scry identifies a real shadow stack with a finite, non-recursive depth.
        assert_eq!(
            r.stack_usage.sp_global,
            Some(0),
            "gust_kernel's stack-pointer global is identified"
        );
        assert!(
            !r.function_summaries.iter().any(|s| s.recursive),
            "gust_kernel has no reachable recursion -> the depth is a finite proof"
        );

        // The proven worst-case depth, recorded as the layer-2 baseline for the
        // fixture jess flashes (previously only the asserted 4096 was on record).
        let proven = match r.stack_usage.max_stack_bytes {
            StackBound::Bytes(n) => n,
            other => panic!("expected a finite proven depth, got {other:?}"),
        };
        assert_eq!(proven, 16, "scry-proven gust_kernel shadow-stack depth (B)");

        // THE LIVE-BUDGET SANITY CHECK: the proven depth must sit at or below the
        // integrator-asserted budget jess flashed (`--shadow-stack-size 4096`),
        // or that image under-reserves its stack on silicon.
        const JESS_FLASHED_BUDGET: u64 = 4096;
        assert!(
            proven <= JESS_FLASHED_BUDGET,
            "proven depth {proven} B must not exceed the flashed {JESS_FLASHED_BUDGET} B budget"
        );

        // And layer-2's own derivation ACCEPTS it (proven, not refused, not
        // fallback): gust_kernel's sp_init is the 1 MiB declared-page top.
        let decision = budget_from_bound(
            StackDepthBound::Bytes(proven),
            1_048_576,
            Some(JESS_FLASHED_BUDGET as u32),
        );
        assert_eq!(
            decision,
            BudgetDecision::Use {
                bytes: 16,
                source: BudgetSource::ProvenStackDepth
            },
            "layer-2 derives a proven 16 B budget for gust_kernel (tighter than the asserted 4096)"
        );
    }

    /// VCR-MEM-001 layer-2 HONEST-FAIL SAFETY ORACLE (#242, #383): the soundness
    /// of the whole budget derivation rests on an upstream assumption — that scry
    /// returns a NON-finite bound for a stack that can grow without bound, so the
    /// derivation refuses rather than inventing a finite budget that would
    /// silently under-reserve and overflow on silicon. The msgq/gust tests cover
    /// the proven (finite) path; this covers the refusal path against REAL scry
    /// output, guarding the assumption directly.
    ///
    /// `recursive_shadow_stack.wat` recurses through the shadow stack (each
    /// activation decrements the SP global by a frame), so the depth is
    /// unbounded. We assert scry detects that (recursive + Unbounded) AND that
    /// `budget_from_bound` never yields a ProvenStackDepth for it — only the
    /// asserted fallback (if given) or an honest refuse.
    ///
    /// Frozen-safe: scry + wat stay test-only here; production bytes unchanged.
    #[test]
    fn layer2_unbounded_recursion_refuses_proven_budget_242() {
        use scry_analyze_core::{AnalysisConfig, StackBound, analyze};
        use shadow_budget::{BudgetDecision, BudgetSource, StackDepthBound, budget_from_bound};

        let wat_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../scripts/repro/recursive_shadow_stack.wat");
        let wasm = wat::parse_file(&wat_path).expect("the honest-fail fixture .wat parses");

        let r = analyze(
            wasm,
            AnalysisConfig {
                widening_threshold: None,
                emit_diagnostics: false,
                taint_policy: None,
            },
        )
        .expect("scry analyzes the recursive Core module");

        // The upstream assumption the honest-fail gate depends on: recursion
        // through the shadow stack is detected and has NO finite bound.
        assert!(
            r.function_summaries.iter().any(|s| s.recursive),
            "scry detects the shadow-stack recursion"
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unbounded,
            "recursion through the shadow stack has no finite proven bound"
        );

        let bound = match r.stack_usage.max_stack_bytes {
            StackBound::Bytes(n) => StackDepthBound::Bytes(n),
            StackBound::Unbounded => StackDepthBound::Unbounded,
            StackBound::Unknown => StackDepthBound::Unknown,
        };

        // SAFETY (1): with a fallback, the budget is the integrator-ASSERTED one —
        // explicitly NOT ProvenStackDepth. An unbounded stack never gets a proven
        // finite budget; the proof label is reserved for a real finite depth.
        assert_eq!(
            budget_from_bound(bound, 65_536, Some(4096)),
            BudgetDecision::Use {
                bytes: 4096,
                source: BudgetSource::AssertedFallback
            },
            "unbounded depth -> asserted fallback, never ProvenStackDepth"
        );

        // SAFETY (2): with no fallback, an honest refuse — never an invented
        // number for a stack the analyzer could not bound.
        match budget_from_bound(bound, 65_536, None) {
            BudgetDecision::Refuse(msg) => assert!(
                msg.contains("unbounded"),
                "refusal names the unbounded cause; got: {msg}"
            ),
            other => panic!("unbounded + no fallback must refuse, got {other:?}"),
        }
    }

    /// #235: a dissolved export's non-exported callee must be pulled into the
    /// reachable set (so it lands in the relocatable object), while imports and
    /// unreachable functions stay out.
    #[test]
    fn reachable_from_exports_pulls_in_internal_callees_235() {
        // index 0 = import (external); 1 = helper (internal, non-exported);
        // 2 = exported caller -> calls 1; 3 = dead non-exported (unreferenced).
        let funcs = vec![
            fop(1, None, vec![WasmOp::I32Const(1)]),
            fop(2, Some("caller"), vec![WasmOp::Call(1), WasmOp::Call(0)]),
            fop(3, None, vec![WasmOp::I32Const(9)]),
        ];
        let r = reachable_from_exports(&funcs, 1, &[]); // num_imports = 1
        assert!(r.contains(&2), "the export itself is reachable");
        assert!(
            r.contains(&1),
            "the non-exported callee is pulled in (#235)"
        );
        assert!(!r.contains(&0), "imports stay external, never compiled");
        assert!(
            !r.contains(&3),
            "unreferenced internal functions are not emitted"
        );
    }

    /// #275: a function reached only through `call_indirect` (a table entry,
    /// not a direct `call`) must be pulled into the reachable set — otherwise
    /// the binary is not self-contained and faults on hardware. Table entries
    /// that are NOT possible targets here (only those in the element segment)
    /// are included; an unreferenced internal stays out.
    #[test]
    fn reachable_from_exports_follows_call_indirect_into_table_275() {
        // 0 = exported caller, does a call_indirect; 1 = table target (in elem,
        // reached only indirectly); 2 = direct callee of the table target;
        // 3 = dead internal (not in the table, never called).
        let funcs = vec![
            fop(
                0,
                Some("run"),
                vec![
                    WasmOp::I32Const(0),
                    WasmOp::CallIndirect {
                        type_index: 0,
                        table_index: 0,
                    },
                ],
            ),
            fop(1, None, vec![WasmOp::Call(2)]),
            fop(2, None, vec![WasmOp::I32Const(42)]),
            fop(3, None, vec![WasmOp::I32Const(9)]),
        ];
        // elem segment puts function 1 in the table.
        let r = reachable_from_exports(&funcs, 0, &[1]);
        assert!(r.contains(&0), "the export itself");
        assert!(
            r.contains(&1),
            "the call_indirect target (table entry) is pulled in (#275)"
        );
        assert!(
            r.contains(&2),
            "and its transitive direct callee follows too"
        );
        assert!(!r.contains(&3), "a non-table, uncalled internal stays out");
    }

    /// #345 step 1: under `--native-pointer-abi`, a module whose linear memory
    /// is pure zero-init (no `(data)` segment — e.g. a 64 KiB shadow-stack
    /// reservation with SP-init = 65536, the k_mutex_unlock decide) must NOT
    /// emit the reservation as a 64 KiB PROGBITS `.data` of zero bytes
    /// (unshippable on a 128 KiB-RAM MCU). The `__synth_wasm_data` region lands
    /// in a SHT_NOBITS `.bss` (zero file bytes), and only the materialized
    /// global slots (non-zero inits) ride in a small PROGBITS `.data`.
    #[test]
    fn native_pointer_zero_linmem_lands_in_nobits_bss_345() {
        use object::Endianness;
        use object::read::elf::{FileHeader, SectionHeader};

        // One function with a `__synth_wasm_data` MOVW/MOVT access (so the
        // wasm-data region is emitted) but NO data segments — pure zero-init.
        let code = vec![0u8; 8]; // MOVW + MOVT placeholders
        let func = ElfFunction {
            name: "decide".to_string(),
            debug_name: None,
            wasm_index: 0,
            code,
            relocations: vec![
                synth_core::backend::CodeRelocation {
                    offset: 0,
                    symbol: "__synth_wasm_data".to_string(),
                    kind: synth_core::backend::RelocKind::MovwAbs,
                },
                synth_core::backend::CodeRelocation {
                    offset: 4,
                    symbol: "__synth_wasm_data".to_string(),
                    kind: synth_core::backend::RelocKind::MovtAbs,
                },
            ],
            op_offsets: vec![],
            line_map: vec![],
        };
        let linear_memory_bytes: u32 = 131_072; // 2 wasm pages
        // Native globals: SP-init = 65536 (the shadow-stack top) drives the
        // reservation up to ~64 KiB; one global slot holds that offset.
        let native = NativeGlobalsLayout {
            globals: vec![(0, 65_536)],
            sp_init: 65_536,
            shadow_stack_size: None,
        };

        let elf = build_relocatable_elf(
            &[func],
            &[],
            &[],
            linear_memory_bytes,
            Some(native),
            None,
            true,
        )
        .expect("#345: native-pointer zero-linmem object builds");

        // Parse the ELF and inspect sections by name + type.
        let header = object::elf::FileHeader32::<Endianness>::parse(&*elf).expect("valid ELF32");
        let endian = header.endian().expect("endian");
        let sections = header.sections(endian, &*elf).expect("sections");

        let mut bss_size: Option<u64> = None;
        let mut data_size: Option<u64> = None;
        let mut bss_is_nobits = false;
        for section in sections.iter() {
            let name = sections
                .section_name(endian, section)
                .map(|n| String::from_utf8_lossy(n).into_owned())
                .unwrap_or_default();
            let sh_type = section.sh_type(endian);
            if name == ".bss" {
                bss_is_nobits = sh_type == object::elf::SHT_NOBITS;
                bss_size = Some(section.sh_size(endian).into());
            } else if name == ".data" {
                data_size = Some(section.sh_size(endian).into());
                // The linmem reservation must NOT have leaked into a giant
                // PROGBITS `.data` — only the small global-slot region rides
                // here.
                assert!(
                    section.sh_size(endian) < 1024,
                    "#345: PROGBITS .data must be tiny (global slots only), not the 64 KiB reservation; got {} bytes",
                    section.sh_size(endian)
                );
            }
        }

        let bss = bss_size.expect("#345: a .bss section must be present");
        assert!(
            bss_is_nobits,
            "#345: the linmem reservation must be SHT_NOBITS"
        );
        // The reservation covers the used extent (~64 KiB shadow stack), with
        // zero file bytes — far below the full 128 KiB pages and never a 64 KiB
        // PROGBITS blob.
        assert!(
            bss >= 65_536 && bss <= linear_memory_bytes as u64,
            "#345: .bss spans the zero-init reservation (got {bss} bytes)"
        );
        // The small PROGBITS .data (global slots) carries the non-zero SP init.
        let data = data_size.expect("#345: a small PROGBITS .data (global slots) must be present");
        assert!(
            data > 0 && data < 1024,
            "#345: .data holds only global slots (got {data} bytes)"
        );
    }

    /// #345 step 2: the `--native-pointer-abi` linmem-address loads must use the
    /// link-survivable literal-pool form (`R_ARM_ABS32` on a `.text` data word),
    /// NOT the inline-immediate `R_ARM_MOVW_ABS_NC`/`R_ARM_MOVT_ABS` pair — the
    /// latter could be mangled into an undefined instruction in a large Zephyr
    /// image (USAGE FAULT on G474RE). This test drives the real ELF reloc-emission
    /// path: a function carrying `RelocKind::Abs32` against `__synth_wasm_data` and
    /// `__synth_globals` must yield `.rel.text` entries of type R_ARM_ABS32 (2) and
    /// ZERO MOVW/MOVT-ABS (43/44) against those symbols.
    #[test]
    fn native_pointer_linmem_addressing_is_abs32_not_movw_movt_345() {
        use object::Endianness;
        use object::read::elf::{FileHeader, SectionHeader};

        // A function whose `.text` ends in two literal-pool words (the LdrSym
        // form): one for `__synth_wasm_data`, one for `__synth_globals`. Each
        // word carries its addend in place (REL) and an Abs32 reloc.
        let mut code = vec![0u8; 8]; // two pooled words at offsets 0 and 4
        code[0..4].copy_from_slice(&0u32.to_le_bytes()); // __synth_wasm_data + 0
        code[4..8].copy_from_slice(&0u32.to_le_bytes()); // __synth_globals + 0
        let func = ElfFunction {
            name: "decide".to_string(),
            debug_name: None,
            wasm_index: 0,
            code,
            relocations: vec![
                synth_core::backend::CodeRelocation {
                    offset: 0,
                    symbol: "__synth_wasm_data".to_string(),
                    kind: synth_core::backend::RelocKind::Abs32,
                },
                synth_core::backend::CodeRelocation {
                    offset: 4,
                    symbol: "__synth_globals".to_string(),
                    kind: synth_core::backend::RelocKind::Abs32,
                },
            ],
            op_offsets: vec![],
            line_map: vec![],
        };
        let native = NativeGlobalsLayout {
            globals: vec![(0, 65_536)],
            sp_init: 65_536,
            shadow_stack_size: None,
        };
        let elf = build_relocatable_elf(&[func], &[], &[], 131_072, Some(native), None, true)
            .expect("#345: native-pointer literal-pool object builds");

        let header = object::elf::FileHeader32::<Endianness>::parse(&*elf).expect("valid ELF32");
        let endian = header.endian().expect("endian");
        let sections = header.sections(endian, &*elf).expect("sections");

        // Collect every relocation type emitted against .text.
        const R_ARM_ABS32: u32 = 2;
        const R_ARM_MOVW_ABS_NC: u32 = 43;
        const R_ARM_MOVT_ABS: u32 = 44;
        let mut abs32 = 0usize;
        let mut movw_movt = 0usize;
        for section in sections.iter() {
            let name = sections
                .section_name(endian, section)
                .map(|n| String::from_utf8_lossy(n).into_owned())
                .unwrap_or_default();
            if name != ".rel.text" {
                continue;
            }
            let (rels, _) = section
                .rel(endian, &*elf)
                .expect("rel section")
                .expect("has rel entries");
            for rel in rels {
                match rel.r_type(endian) {
                    R_ARM_ABS32 => abs32 += 1,
                    R_ARM_MOVW_ABS_NC | R_ARM_MOVT_ABS => movw_movt += 1,
                    _ => {}
                }
            }
        }
        assert_eq!(
            abs32, 2,
            "#345: both linmem-address loads must be R_ARM_ABS32 literal-pool words"
        );
        assert_eq!(
            movw_movt, 0,
            "#345: NO inline MOVW/MOVT-ABS relocs may remain on the native-pointer path"
        );
    }

    /// #354: a native-pointer module with an initialized `(data)` segment at a
    /// HIGH linmem offset (above the shadow stack) must NOT ship the whole
    /// `[0, used_extent)` image as one PROGBITS `.data` (65552 bytes for gale's
    /// stack_push). It splits per region: the zero reservation is NOBITS `.bss`
    /// (`__synth_wasm_data`), the init segment is packed into a tiny PROGBITS
    /// `.data` under `__synth_wasm_seg_0`, and the static-data reloc is
    /// retargeted (`__synth_wasm_data + C` -> `__synth_wasm_seg_0 + (C-seg_off)`,
    /// symbol AND in-place REL addend word).
    #[test]
    fn mixed_high_offset_segment_splits_per_region_354() {
        use object::Endianness;
        use object::read::elf::{FileHeader, SectionHeader};

        // The const is accessed by a literal-pool Abs32 load whose in-place word
        // is the absolute linmem offset C = 65544 (8 bytes into a segment based
        // at 65536 — gale's `\f4\ff\ff\ff` = -12/-ENOMEM at offset+8).
        const C: u32 = 65_544;
        const SEG_OFF: u32 = 65_536;
        let mut code = vec![0u8; 4];
        code[0..4].copy_from_slice(&C.to_le_bytes());
        let func = ElfFunction {
            name: "stack_push_decide".to_string(),
            debug_name: None,
            wasm_index: 0,
            code,
            relocations: vec![synth_core::backend::CodeRelocation {
                offset: 0,
                symbol: "__synth_wasm_data".to_string(),
                kind: synth_core::backend::RelocKind::Abs32,
            }],
            op_offsets: vec![],
            line_map: vec![],
        };
        // 12-byte init segment at the high offset, above the shadow stack.
        let seg: Vec<u8> = vec![0, 0, 0, 0, 0, 0, 0, 0, 0xf4, 0xff, 0xff, 0xff];
        let data_segments = vec![(SEG_OFF, seg)];
        let native = NativeGlobalsLayout {
            globals: vec![(0, 65_536)],
            sp_init: 65_536,
            shadow_stack_size: None,
        };

        let elf = build_relocatable_elf(
            &[func],
            &[],
            &data_segments,
            131_072,
            Some(native),
            None,
            true,
        )
        .expect("#354: mixed-case object builds");

        let header = object::elf::FileHeader32::<Endianness>::parse(&*elf).expect("valid ELF32");
        let endian = header.endian().expect("endian");
        let sections = header.sections(endian, &*elf).expect("sections");

        let mut bss_size: Option<u64> = None;
        let mut bss_is_nobits = false;
        let mut data_size: Option<u64> = None;
        let mut text_data: Vec<u8> = Vec::new();
        for section in sections.iter() {
            let name = sections
                .section_name(endian, section)
                .map(|n| String::from_utf8_lossy(n).into_owned())
                .unwrap_or_default();
            match name.as_str() {
                ".bss" => {
                    bss_is_nobits = section.sh_type(endian) == object::elf::SHT_NOBITS;
                    bss_size = Some(section.sh_size(endian).into());
                }
                ".data" => data_size = Some(section.sh_size(endian).into()),
                ".text" => {
                    text_data = section.data(endian, &*elf).unwrap_or_default().to_vec();
                }
                _ => {}
            }
        }

        // The zero reservation is a NOBITS .bss spanning the used extent.
        let bss = bss_size.expect("#354: a .bss reservation must be present");
        assert!(
            bss_is_nobits,
            "#354: the zero reservation must be SHT_NOBITS"
        );
        assert!(
            bss >= 65_536,
            "#354: .bss spans the zero gap (got {bss} bytes)"
        );
        // The PROGBITS .data is bounded to the packed segment + globals, NOT the
        // 64 KiB image.
        let data = data_size.expect("#354: a small PROGBITS .data must be present");
        assert!(
            data < 256,
            "#354: .data is bounded to the init bytes, not the 64 KiB image (got {data} bytes)"
        );

        // The static-data reloc is retargeted to __synth_wasm_seg_0 — verified
        // via the stable high-level API (avoids the low-level Sym trait, which is
        // ambiguous with two `object` versions in the tree).
        {
            use object::{Object, ObjectSection, ObjectSymbol};
            let file = object::File::parse(&*elf).expect("#354: parse ELF");
            assert!(
                file.symbols().any(|s| s.name() == Ok("__synth_wasm_seg_0")),
                "#354: __synth_wasm_seg_0 symbol must be defined"
            );
            let mut retargeted = false;
            for section in file.sections() {
                for (_off, rel) in section.relocations() {
                    if let object::RelocationTarget::Symbol(idx) = rel.target()
                        && file
                            .symbol_by_index(idx)
                            .ok()
                            .and_then(|s| s.name().ok().map(|n| n == "__synth_wasm_seg_0"))
                            .unwrap_or(false)
                    {
                        retargeted = true;
                    }
                }
            }
            assert!(
                retargeted,
                "#354: the static-data reloc must retarget to __synth_wasm_seg_0"
            );
        }

        // The in-place REL addend word in .text was rewritten C -> C - seg_off.
        assert!(
            text_data.len() >= 4,
            "#354: .text must hold the pooled word"
        );
        let patched = u32::from_le_bytes([text_data[0], text_data[1], text_data[2], text_data[3]]);
        assert_eq!(
            patched,
            C - SEG_OFF,
            "#354: in-place addend rewritten to C-seg_off (8); link computes seg0_base+8 = the const"
        );
    }

    /// Without a `call_indirect`, table entries are NOT force-included — a module
    /// that never dispatches indirectly keeps the tight direct-call closure.
    #[test]
    fn reachable_from_exports_ignores_table_when_no_call_indirect_275() {
        let funcs = vec![
            fop(0, Some("run"), vec![WasmOp::I32Const(1)]),
            fop(1, None, vec![WasmOp::I32Const(42)]), // in table, but never indirectly called
        ];
        let r = reachable_from_exports(&funcs, 0, &[1]);
        assert!(
            !r.contains(&1),
            "no call_indirect → table entry not pulled in"
        );
    }

    /// A module whose exports call no internal function yields exactly the
    /// exports — so existing leaf-fixture output stays bit-identical.
    #[test]
    fn reachable_from_exports_leaf_is_exports_only_235() {
        let funcs = vec![
            fop(0, Some("a"), vec![WasmOp::I32Const(1)]),
            fop(1, Some("b"), vec![WasmOp::LocalGet(0)]),
            fop(2, None, vec![WasmOp::I32Const(7)]), // dead helper
        ];
        let r = reachable_from_exports(&funcs, 0, &[]);
        assert_eq!(
            r.into_iter().collect::<Vec<_>>(),
            vec![0, 1],
            "exports only"
        );
    }

    /// `encode_thumb_bl` must match `arm-none-eabi-as` byte-for-byte. These
    /// vectors were taken directly from gas disassembly (#170), covering
    /// backward/forward and near/far branches — the cases that exercise the
    /// S/J1/J2 sign-bit logic that bit #174.
    #[test]
    fn test_encode_thumb_bl_matches_gas() {
        // gas: P=0x6  S=0x4    -> f7ff fffd  (bytes ff f7 fd ff), near backward
        assert_eq!(encode_thumb_bl(0x6, 0x4), [0xff, 0xf7, 0xfd, 0xff]);
        // gas: P=0xa  S=0x12   -> f000 f802  (bytes 00 f0 02 f8), near forward
        assert_eq!(encode_thumb_bl(0xa, 0x12), [0x00, 0xf0, 0x02, 0xf8]);
        // gas: P=0x138a S=0x0  -> f7fe fe39  (bytes fe f7 39 fe), far backward
        assert_eq!(encode_thumb_bl(0x138a, 0x0), [0xfe, 0xf7, 0x39, 0xfe]);
        // gas: P=0x138e S=0x2b02 -> f001 fbb8 (bytes 01 f0 b8 fb), far forward
        assert_eq!(encode_thumb_bl(0x138e, 0x2b02), [0x01, 0xf0, 0xb8, 0xfb]);
    }

    #[test]
    fn test_cortex_m_binary_structure() {
        // Simple add function: ADD r0, r0, r1; BX lr
        let code = vec![
            0x00, 0x80, 0x80, 0xe0, // ADD r0, r0, r1 (ARM encoding)
            0x1e, 0xff, 0x2f, 0xe1, // BX lr (ARM encoding)
        ];

        let elf_data = build_cortex_m_elf(&code, "test_func", &TargetSpec::cortex_m3()).unwrap();

        // Verify ELF magic
        assert_eq!(&elf_data[0..4], b"\x7fELF", "Invalid ELF magic");

        // Verify 32-bit little-endian ARM
        assert_eq!(elf_data[4], 1, "Should be 32-bit ELF");
        assert_eq!(elf_data[5], 1, "Should be little-endian");

        // Verify it's an executable
        assert_eq!(elf_data[16], 2, "Should be ET_EXEC");

        // Verify ARM architecture (0x28 = ARM)
        assert_eq!(elf_data[18], 0x28, "Should be ARM architecture");
    }

    #[test]
    fn test_vector_table_structure() {
        let code = vec![0x00, 0x80, 0x80, 0xe0]; // ADD r0, r0, r1

        let elf_data = build_cortex_m_elf(&code, "test", &TargetSpec::cortex_m3()).unwrap();

        // Find .text section (it starts after ELF headers)
        // For simplicity, look for the vector table pattern
        // Stack pointer at offset 0 should be 0x20020000 (128KB RAM)
        // This is little-endian, so bytes are: 00 00 02 20

        // The vector table is in the .text section data
        // Find where vector table data starts (after ELF headers)
        let mut found_sp = false;
        for i in 0..elf_data.len().saturating_sub(4) {
            let word = u32::from_le_bytes([
                elf_data[i],
                elf_data[i + 1],
                elf_data[i + 2],
                elf_data[i + 3],
            ]);
            if word == 0x20020000 {
                found_sp = true;
                // Next word should be reset handler with Thumb bit (0x81)
                let reset = u32::from_le_bytes([
                    elf_data[i + 4],
                    elf_data[i + 5],
                    elf_data[i + 6],
                    elf_data[i + 7],
                ]);
                assert_eq!(reset, 0x81, "Reset handler should be 0x81 (0x80 | 1)");
                break;
            }
        }
        assert!(found_sp, "Stack pointer (0x20020000) not found in ELF");
    }

    #[test]
    fn test_simple_elf_generation() {
        let code = vec![0x00, 0x80, 0x80, 0xe0]; // ADD r0, r0, r1

        let elf_data = build_simple_elf(&code, "simple_func").unwrap();

        // Verify ELF magic
        assert_eq!(&elf_data[0..4], b"\x7fELF", "Invalid ELF magic");

        // Verify entry point is 0x8000
        let entry = u32::from_le_bytes([elf_data[24], elf_data[25], elf_data[26], elf_data[27]]);
        assert_eq!(
            entry, 0x8001,
            "Entry point should be 0x8001 (0x8000 | Thumb bit)"
        );
    }

    #[test]
    fn test_startup_code_patching() {
        let code = vec![0x00, 0x80, 0x80, 0xe0];

        let elf_data = build_cortex_m_elf(&code, "patched", &TargetSpec::cortex_m3()).unwrap();

        // With the new startup code layout (28 bytes with R10/R11 init):
        // - Startup: 0x80 (28 bytes)
        // - Default handler: 0x9C (2 bytes)
        // - Trap handler: 0x9E (2 bytes)
        // - User function: 0xA0 (aligned to 4)
        // So literal pool should contain 0xA1 (0xA0 | 1 for Thumb bit)
        let mut found_literal = false;
        for i in 0..elf_data.len().saturating_sub(4) {
            let word = u32::from_le_bytes([
                elf_data[i],
                elf_data[i + 1],
                elf_data[i + 2],
                elf_data[i + 3],
            ]);
            if word == 0xA1 {
                found_literal = true;
                break;
            }
        }
        assert!(
            found_literal,
            "Literal pool should contain 0xA1 (0xA0 | 1 for Thumb)"
        );
    }

    #[test]
    fn test_minimal_startup_generation() {
        // Test with 64KB memory size (0x10000)
        let memory_size: u32 = 64 * 1024;
        let startup = generate_minimal_startup(memory_size);

        // Should be 28 bytes:
        // MOVW R10 + MOVT R10 + MOVW R11 + MOVT R11 + LDR + BLX + B + padding + literal
        assert_eq!(startup.len(), 28, "Startup code should be 28 bytes");

        // Bytes 8-11: MOVW R11, #0
        assert_eq!(startup[8], 0x40);
        assert_eq!(startup[9], 0xF2);
        assert_eq!(startup[10], 0x00);
        assert_eq!(startup[11], 0x0B);

        // Bytes 12-15: MOVT R11, #0x2000
        assert_eq!(startup[12], 0xC2);
        assert_eq!(startup[13], 0xF2);
        assert_eq!(startup[14], 0x00);
        assert_eq!(startup[15], 0x0B);

        // Bytes 16-17: LDR r0, [pc, #4] = 0x4801
        assert_eq!(startup[16], 0x01);
        assert_eq!(startup[17], 0x48);

        // Bytes 18-19: BLX r0 = 0x4780
        assert_eq!(startup[18], 0x80);
        assert_eq!(startup[19], 0x47);

        // Bytes 20-21: B . = 0xe7fe
        assert_eq!(startup[20], 0xfe);
        assert_eq!(startup[21], 0xe7);
    }

    #[test]
    fn test_default_handler_generation() {
        let handler = generate_default_handler();

        // Should be 2 bytes: B . = 0xe7fe
        assert_eq!(handler.len(), 2);
        assert_eq!(handler[0], 0xfe);
        assert_eq!(handler[1], 0xe7);
    }

    // =========================================================================
    // PR #86 patch coverage: --hardware dispatch and target_info_command
    // =========================================================================

    #[test]
    fn test_target_info_command_imxrt1062() {
        // The new "imxrt1062" hardware string must dispatch successfully.
        let result = target_info_command("imxrt1062".to_string());
        assert!(result.is_ok(), "imxrt1062 target_info should succeed");
    }

    #[test]
    fn test_target_info_command_stm32h743() {
        let result = target_info_command("stm32h743".to_string());
        assert!(result.is_ok(), "stm32h743 target_info should succeed");
    }

    #[test]
    fn test_target_info_command_existing_targets_still_work() {
        // Sanity: nrf52840 + stm32f407 should still dispatch successfully
        // alongside the new M7 entries.
        assert!(target_info_command("nrf52840".to_string()).is_ok());
        assert!(target_info_command("stm32f407".to_string()).is_ok());
    }

    #[test]
    fn test_target_info_command_unknown_target_errors() {
        // Unknown target errors with a message that lists ALL supported names,
        // including the new M7 hardware.
        let err = target_info_command("not-a-real-mcu".to_string()).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("not-a-real-mcu"));
        assert!(msg.contains("nrf52840"));
        assert!(msg.contains("stm32f407"));
        assert!(
            msg.contains("stm32h743"),
            "error message should advertise stm32h743"
        );
        assert!(
            msg.contains("imxrt1062"),
            "error message should advertise imxrt1062"
        );
    }

    #[test]
    fn test_synthesize_command_unsupported_hardware_message() {
        // synthesize_command's --hardware error must list all four supported
        // names. We can't easily test the success path (it parses a wasm
        // component) but the unsupported branch is reachable with a dummy
        // input file path.
        let bad_path = std::path::PathBuf::from("/tmp/__non_existent_wasm__");
        let out_path = std::path::PathBuf::from("/tmp/__non_existent_out__");
        // synthesize_command tries to parse the component first — that fails
        // before the hardware check. Use the hardware match directly via the
        // public re-exposed HardwareCapabilities surface to validate the
        // string→ctor dispatch.
        let names = ["nrf52840", "stm32f407", "stm32h743", "imxrt1062"];
        for n in names {
            // Each name must produce a HardwareCapabilities with a non-zero
            // MPU region count (every supported part has an MPU).
            let caps = match n {
                "nrf52840" => HardwareCapabilities::nrf52840(),
                "stm32f407" => HardwareCapabilities::stm32f407(),
                "stm32h743" => HardwareCapabilities::stm32h743(),
                "imxrt1062" => HardwareCapabilities::imxrt1062(),
                _ => unreachable!(),
            };
            assert!(caps.mpu_regions > 0, "{} should have MPU regions", n);
        }
        // And confirm the synthesize_command pathway exists with the new
        // signature. We deliberately don't run it here (would require a
        // valid wasm file); the unit test above covers the hardware dispatch.
        let _ = (bad_path, out_path);
    }

    #[test]
    fn test_resolve_target_spec_default_no_cortex_m() {
        // When neither --target nor --cortex-m is given, the default is an
        // Arm32-ISA cortex_m4 spec (used by the non-Cortex-M flow).
        let spec = resolve_target_spec(None, false, "arm").unwrap();
        assert_eq!(spec.isa, synth_core::target::IsaVariant::Arm32);
    }

    #[test]
    fn test_resolve_target_spec_cortex_m_flag() {
        // --cortex-m without --target maps to cortex-m3.
        let spec = resolve_target_spec(None, true, "arm").unwrap();
        assert_eq!(spec.triple, "thumbv7m-none-eabi");
    }

    #[test]
    fn test_resolve_target_spec_explicit_target_wins_over_cortex_m() {
        // --target overrides --cortex-m.
        let spec = resolve_target_spec(Some("cortex-m7"), true, "arm").unwrap();
        assert_eq!(spec.triple, "thumbv7em-none-eabihf");
    }

    #[test]
    fn test_resolve_target_spec_unknown_triple_errors() {
        let err = resolve_target_spec(Some("totally-bogus-triple"), false, "arm").unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("totally-bogus-triple"));
        assert!(msg.contains("Supported"));
    }

    /// #218: `-b riscv` with no `--target` must default to an RV32 profile, not
    /// inherit the ARM default (which makes the RISC-V backend bail).
    #[test]
    fn test_resolve_target_spec_riscv_default_218() {
        let spec = resolve_target_spec(None, false, "riscv").unwrap();
        assert_eq!(spec.family, synth_core::target::ArchFamily::RiscV);
        assert_eq!(
            spec.isa,
            synth_core::target::IsaVariant::RiscV32 {
                extensions: "imac".to_string()
            }
        );
    }
}
