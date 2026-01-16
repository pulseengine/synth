//! Synth CLI - WebAssembly Component Synthesizer
//!
//! Command-line interface for the Synth synthesizer.

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use synth_backend::{
    ArmEncoder, ElfBuilder, ElfSectionType, Section, SectionFlags, Symbol, SymbolBinding,
    SymbolType,
};
use synth_core::HardwareCapabilities;
use synth_frontend;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};
use tracing::{info, Level};
use tracing_subscriber;

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

    /// Compile WASM operations to ARM ELF (demo mode)
    Compile {
        /// Output ELF file
        #[arg(short, long, value_name = "OUTPUT", default_value = "output.elf")]
        output: PathBuf,

        /// Demo function to compile (add, mul, fib)
        #[arg(short, long, value_name = "DEMO", default_value = "add")]
        demo: String,
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
        Commands::Compile { output, demo } => {
            compile_command(output, demo)?;
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

fn compile_command(output: PathBuf, demo: String) -> Result<()> {
    info!("Compiling demo function: {}", demo);

    // Select WASM operations based on demo
    let (wasm_ops, func_name) = match demo.as_str() {
        "add" => (
            vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Add,
            ],
            "add",
        ),
        "mul" => (
            vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Mul,
            ],
            "mul",
        ),
        "calc" => (
            vec![
                WasmOp::I32Const(5),
                WasmOp::I32Const(3),
                WasmOp::I32Mul,
                WasmOp::I32Const(2),
                WasmOp::I32Add,
            ],
            "calc",
        ),
        _ => {
            anyhow::bail!(
                "Unknown demo: {}. Available: add, mul, calc",
                demo
            );
        }
    };

    info!("WASM operations: {:?}", wasm_ops);

    // Step 1: Instruction selection
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector
        .select(&wasm_ops)
        .context("Instruction selection failed")?;

    info!("Generated {} ARM instructions", arm_instrs.len());

    // Step 2: Encode to binary
    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();

    for instr in &arm_instrs {
        let encoded = encoder
            .encode(&instr.op)
            .context("ARM encoding failed")?;
        code.extend_from_slice(&encoded);
    }

    info!("Encoded {} bytes of machine code", code.len());

    // Step 3: Build ELF
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.clone());

    elf_builder.add_section(text_section);

    let func_sym = Symbol::new(func_name)
        .with_value(0x8000)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);

    elf_builder.add_symbol(func_sym);

    let elf_data = elf_builder.build().context("ELF generation failed")?;

    info!("Generated {} byte ELF file", elf_data.len());

    // Step 4: Write to file
    let mut file = File::create(&output)
        .context(format!("Failed to create output file: {}", output.display()))?;
    file.write_all(&elf_data)
        .context("Failed to write ELF data")?;

    println!("Compiled {} to {}", func_name, output.display());
    println!("  Code size: {} bytes", code.len());
    println!("  ELF size: {} bytes", elf_data.len());
    println!("\nInspect with: arm-none-eabi-objdump -d {}", output.display());

    Ok(())
}
