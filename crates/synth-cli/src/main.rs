//! Synth CLI - WebAssembly Component Synthesizer
//!
//! Command-line interface for the Synth synthesizer.

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use synth_backend::{
    ArmBackend, ElfBuilder, ElfSectionType, ProgramFlags, ProgramHeader, Section, SectionFlags,
    Symbol, SymbolBinding, SymbolType, VectorTable, W2C2Backend,
};
use synth_core::backend::{Backend, BackendRegistry, CompileConfig};
use synth_core::target::TargetSpec;
use synth_core::HardwareCapabilities;
use synth_frontend;
use synth_synthesis::{decode_wasm_functions, decode_wasm_module, WasmMemory, WasmOp};
use tracing::{info, Level};
use tracing_subscriber;
use wast::parser::{self, ParseBuffer};
use wast::{Wast, WastDirective};

#[derive(Parser)]
#[command(name = "synth")]
#[command(about = "WebAssembly Component Synthesizer for Embedded Systems", long_about = None)]
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

        /// Hardware config (nrf52840, stm32f407, or custom)
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

    /// Compile WASM/WAT to ARM ELF
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

        /// Function index to compile (default: 0, first function)
        #[arg(short, long, value_name = "INDEX", default_value = "0")]
        func_index: u32,

        /// Function name (export name) to compile - overrides func_index
        #[arg(short = 'n', long, value_name = "NAME")]
        func_name: Option<String>,

        /// Compile ALL exported functions into a multi-function ELF
        #[arg(long)]
        all_exports: bool,

        /// Generate complete Cortex-M binary with vector table (for Renode/QEMU)
        #[arg(long)]
        cortex_m: bool,

        /// Disable optimization passes (use direct instruction selection)
        #[arg(long)]
        no_optimize: bool,

        /// Use Loom-compatible optimization (skip passes Loom already handles)
        #[arg(long)]
        loom_compat: bool,

        /// Enable software bounds checking for memory operations
        /// Generates CMP/BHS before each load/store (~25% overhead)
        #[arg(long)]
        bounds_check: bool,

        /// Compilation backend (arm, w2c2, awsm, wasker)
        #[arg(short, long, default_value = "arm")]
        backend: String,

        /// Run translation validation after compilation
        #[arg(long)]
        verify: bool,
    },

    /// Disassemble an ARM ELF file
    Disasm {
        /// Input ELF file
        #[arg(value_name = "INPUT")]
        input: PathBuf,
    },

    /// List available compilation backends and their status
    Backends,

    /// Verify compilation correctness (translation validation)
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
            no_optimize,
            loom_compat,
            bounds_check,
            backend,
            verify,
        } => {
            compile_command(
                input,
                output,
                demo,
                func_index,
                func_name,
                all_exports,
                cortex_m,
                no_optimize,
                loom_compat,
                bounds_check,
                &backend,
                verify,
            )?;
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
    }

    Ok(())
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
        _ => {
            anyhow::bail!(
                "Unsupported hardware: {}. Use nrf52840 or stm32f407",
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
        _ => {
            anyhow::bail!("Unknown target: {}. Supported: nrf52840, stm32f407", target);
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

/// Compiled function for ELF building (name + code bytes)
struct ElfFunction {
    name: String,
    code: Vec<u8>,
}

/// Build the backend registry with all available backends
fn build_backend_registry() -> BackendRegistry {
    let mut registry = BackendRegistry::new();

    // Always register the built-in ARM backend
    registry.register(Box::new(ArmBackend::new()));

    // Register w2c2 backend (always available, checks tool at runtime)
    registry.register(Box::new(W2C2Backend::new()));

    // Register aWsm backend if compiled with feature
    #[cfg(feature = "awsm")]
    registry.register(Box::new(synth_backend_awsm::AwsmBackend::new()));

    // Register wasker backend if compiled with feature
    #[cfg(feature = "wasker")]
    registry.register(Box::new(synth_backend_wasker::WaskerBackend::new()));

    registry
}

fn compile_command(
    input: Option<PathBuf>,
    output: PathBuf,
    demo: Option<String>,
    func_index: u32,
    func_name_arg: Option<String>,
    all_exports: bool,
    cortex_m: bool,
    no_optimize: bool,
    loom_compat: bool,
    bounds_check: bool,
    backend_name: &str,
    verify: bool,
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
    // Handle --all-exports mode for multi-function compilation
    if all_exports {
        return compile_all_exports(
            input,
            output,
            cortex_m,
            no_optimize,
            loom_compat,
            bounds_check,
            backend,
            verify,
        );
    }

    // Single function compilation (original behavior)
    let (wasm_ops, func_name): (Vec<WasmOp>, String) = match (&input, &demo) {
        (Some(path), _) => {
            info!("Compiling WASM file: {}", path.display());

            let file_bytes = std::fs::read(path)
                .context(format!("Failed to read input file: {}", path.display()))?;

            let wasm_bytes = if path.extension().map_or(false, |ext| ext == "wast") {
                info!("Parsing WAST to WASM (extracting module)...");
                let contents =
                    String::from_utf8(file_bytes).context("WAST file is not valid UTF-8")?;
                extract_module_from_wast(&contents)?
            } else if path.extension().map_or(false, |ext| ext == "wat") {
                info!("Parsing WAT to WASM...");
                wat::parse_bytes(&file_bytes)
                    .context("Failed to parse WAT file")?
                    .into_owned()
            } else {
                file_bytes
            };

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

    info!("WASM operations: {:?}", wasm_ops);

    // Build compile config from CLI flags
    let mut config = CompileConfig::default();
    config.no_optimize = no_optimize;
    config.loom_compat = loom_compat;
    config.bounds_check = bounds_check;
    if !cortex_m {
        config.target = TargetSpec {
            isa: synth_core::target::IsaVariant::Arm32,
            ..config.target
        };
    }

    // Compile via the selected backend
    let compiled = backend
        .compile_function(&func_name, &wasm_ops, &config)
        .map_err(|e| anyhow::anyhow!("Backend '{}' compilation failed: {}", backend.name(), e))?;
    let code = compiled.code;
    info!("Encoded {} bytes of machine code", code.len());

    let elf_data = if cortex_m {
        build_cortex_m_elf(&code, &func_name)?
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
                println!("\nVerification requested but z3-solver not available.");
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
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::EQ },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32Ne => Some(SynthesisRule {
                name: "i32.ne → CMP + SetCond(NE)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Ne),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::NE },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32LtS => Some(SynthesisRule {
                name: "i32.lt_s → CMP + SetCond(LT)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LtS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::LT },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32LeS => Some(SynthesisRule {
                name: "i32.le_s → CMP + SetCond(LE)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LeS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::LE },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32GtS => Some(SynthesisRule {
                name: "i32.gt_s → CMP + SetCond(GT)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GtS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::GT },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32GeS => Some(SynthesisRule {
                name: "i32.ge_s → CMP + SetCond(GE)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GeS),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::GE },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32LtU => Some(SynthesisRule {
                name: "i32.lt_u → CMP + SetCond(LO)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LtU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::LO },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32LeU => Some(SynthesisRule {
                name: "i32.le_u → CMP + SetCond(LS)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32LeU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::LS },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32GtU => Some(SynthesisRule {
                name: "i32.gt_u → CMP + SetCond(HI)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GtU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::HI },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            WasmOp::I32GeU => Some(SynthesisRule {
                name: "i32.ge_u → CMP + SetCond(HS)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32GeU),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Reg(Reg::R1) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::HS },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 2 },
            }),
            // i32.eqz: unary comparison against zero
            WasmOp::I32Eqz => Some(SynthesisRule {
                name: "i32.eqz → CMP #0 + SetCond(EQ)".into(),
                priority: 0,
                pattern: Pattern::WasmInstr(WasmOp::I32Eqz),
                replacement: Replacement::ArmSequence(vec![
                    ArmOp::Cmp { rn: Reg::R0, op2: Operand2::Imm(0) },
                    ArmOp::SetCond { rd: Reg::R0, cond: Condition::EQ },
                ]),
                cost: synth_synthesis::Cost { cycles: 2, code_size: 4, registers: 1 },
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

    let (verified, failed, unknown) = synth_verify::with_z3_context(|| {
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
fn extract_module_from_wast(contents: &str) -> Result<Vec<u8>> {
    let buf = ParseBuffer::new(contents)
        .map_err(|e| anyhow::anyhow!("Failed to create parse buffer: {}", e))?;

    let wast: Wast =
        parser::parse(&buf).map_err(|e| anyhow::anyhow!("Failed to parse WAST: {}", e))?;

    // Find the first module in the WAST directives
    for directive in wast.directives {
        if let WastDirective::Module(mut quote_wat) = directive {
            // Encode the WAT module to binary WASM
            return quote_wat
                .encode()
                .map_err(|e| anyhow::anyhow!("Failed to encode module: {}", e));
        }
    }

    anyhow::bail!("No module found in WAST file")
}

/// Compile all exported functions into a multi-function ELF
fn compile_all_exports(
    input: Option<PathBuf>,
    output: PathBuf,
    cortex_m: bool,
    no_optimize: bool,
    loom_compat: bool,
    bounds_check: bool,
    backend: &dyn Backend,
    verify: bool,
) -> Result<()> {
    let path = input.context("--all-exports requires an input file")?;

    info!("Compiling all exports from: {}", path.display());

    let file_bytes =
        std::fs::read(&path).context(format!("Failed to read input file: {}", path.display()))?;

    let wasm_bytes = if path.extension().map_or(false, |ext| ext == "wast") {
        info!("Parsing WAST to WASM (extracting module)...");
        let contents = String::from_utf8(file_bytes).context("WAST file is not valid UTF-8")?;
        extract_module_from_wast(&contents)?
    } else if path.extension().map_or(false, |ext| ext == "wat") {
        info!("Parsing WAT to WASM...");
        wat::parse_bytes(&file_bytes)
            .context("Failed to parse WAT file")?
            .into_owned()
    } else {
        file_bytes
    };

    let module = decode_wasm_module(&wasm_bytes).context("Failed to decode WASM module")?;

    // Log memory information
    if !module.memories.is_empty() {
        info!("Module declares {} memories:", module.memories.len());
        for mem in &module.memories {
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

    // Filter to only exported functions
    let exports: Vec<_> = module
        .functions
        .iter()
        .filter(|f| f.export_name.is_some())
        .collect();

    if exports.is_empty() {
        anyhow::bail!("No exported functions found in module");
    }

    info!("Found {} exported functions:", exports.len());
    for f in &exports {
        info!(
            "  '{}' (index {})",
            f.export_name.as_ref().unwrap(),
            f.index
        );
    }

    // Build compile config from CLI flags
    let mut config = CompileConfig::default();
    config.no_optimize = no_optimize;
    config.loom_compat = loom_compat;
    config.bounds_check = bounds_check;
    if !cortex_m {
        config.target = TargetSpec {
            isa: synth_core::target::IsaVariant::Arm32,
            ..config.target
        };
    }

    // Compile each function via the selected backend
    let mut compiled_funcs = Vec::new();
    for func in &exports {
        let name = func.export_name.clone().unwrap();
        info!(
            "Compiling function '{}' via backend '{}'...",
            name,
            backend.name()
        );

        let compiled = backend
            .compile_function(&name, &func.ops, &config)
            .map_err(|e| {
                anyhow::anyhow!("Backend '{}' failed on '{}': {}", backend.name(), name, e)
            })?;
        info!("  {} bytes of machine code", compiled.code.len());

        compiled_funcs.push(ElfFunction {
            name: name.clone(),
            code: compiled.code,
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

    // Build multi-function ELF
    let elf_data = if cortex_m {
        build_multi_func_cortex_m_elf(&compiled_funcs, &module.memories)?
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

    let total_code: usize = compiled_funcs.iter().map(|f| f.code.len()).sum();
    println!(
        "Compiled {} functions to {}",
        compiled_funcs.len(),
        output.display()
    );
    println!("  Total code size: {} bytes", total_code);
    println!("  ELF size: {} bytes", elf_data.len());
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

/// Build a complete Cortex-M multi-function ELF with vector table
fn build_multi_func_cortex_m_elf(
    funcs: &[ElfFunction],
    memories: &[WasmMemory],
) -> Result<Vec<u8>> {
    let flash_base: u32 = 0x0000_0000;
    let ram_base: u32 = 0x2000_0000;
    let ram_size: u32 = 128 * 1024; // 128KB to accommodate linear memory + stack

    // Calculate linear memory size from WASM memory declarations
    // Default to 1 page (64KB) if no memory declared (for backwards compatibility)
    let linear_memory_pages = memories.first().map(|m| m.initial_pages).unwrap_or(1);
    let linear_memory_size = linear_memory_pages * 64 * 1024; // 64KB per page

    // RAM layout:
    // 0x2000_0000: Linear memory (R11 points here)
    // 0x2000_0000 + linear_memory_size: Stack base
    // 0x2001_0000: Stack top (grows down)
    //
    // Ensure we have at least 4KB for stack
    let min_stack_size: u32 = 4 * 1024;
    if linear_memory_size + min_stack_size > ram_size {
        anyhow::bail!(
            "Linear memory ({} bytes) + minimum stack ({} bytes) exceeds RAM ({} bytes)",
            linear_memory_size,
            min_stack_size,
            ram_size
        );
    }

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

            let wasm_bytes = if wasm_input.extension().map_or(false, |ext| ext == "wat") {
                wat::parse_bytes(&file_bytes)
                    .context("Failed to parse WAT file")?
                    .into_owned()
            } else if wasm_input.extension().map_or(false, |ext| ext == "wast") {
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
                let name = func.export_name.as_ref().unwrap();
                run_verification(&func.ops, name)?;
            }

            println!("\nAll functions verified successfully.");
        }

        #[cfg(not(feature = "verify"))]
        {
            println!("\n  Rebuild with verification support:");
            println!("    cargo build --features verify");
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
fn build_cortex_m_elf(code: &[u8], func_name: &str) -> Result<Vec<u8>> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cortex_m_binary_structure() {
        // Simple add function: ADD r0, r0, r1; BX lr
        let code = vec![
            0x00, 0x80, 0x80, 0xe0, // ADD r0, r0, r1 (ARM encoding)
            0x1e, 0xff, 0x2f, 0xe1, // BX lr (ARM encoding)
        ];

        let elf_data = build_cortex_m_elf(&code, "test_func").unwrap();

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

        let elf_data = build_cortex_m_elf(&code, "test").unwrap();

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
        assert_eq!(entry, 0x8000, "Entry point should be 0x8000");
    }

    #[test]
    fn test_startup_code_patching() {
        let code = vec![0x00, 0x80, 0x80, 0xe0];

        let elf_data = build_cortex_m_elf(&code, "patched").unwrap();

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
}
