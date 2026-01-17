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
    SymbolType, VectorTable,
};
use synth_core::HardwareCapabilities;
use synth_frontend;
use synth_synthesis::{decode_wasm_functions, InstructionSelector, RuleDatabase, WasmOp};
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

        /// Generate complete Cortex-M binary with vector table (for Renode/QEMU)
        #[arg(long)]
        cortex_m: bool,
    },

    /// Disassemble an ARM ELF file
    Disasm {
        /// Input ELF file
        #[arg(value_name = "INPUT")]
        input: PathBuf,
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
            cortex_m,
        } => {
            compile_command(input, output, demo, func_index, cortex_m)?;
        }
        Commands::Disasm { input } => {
            disasm_command(input)?;
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

fn compile_command(
    input: Option<PathBuf>,
    output: PathBuf,
    demo: Option<String>,
    func_index: u32,
    cortex_m: bool,
) -> Result<()> {
    // Get WASM operations either from file or demo
    let (wasm_ops, func_name): (Vec<WasmOp>, String) = match (&input, &demo) {
        (Some(path), _) => {
            info!("Compiling WASM file: {}", path.display());

            // Read the file
            let file_bytes = std::fs::read(path)
                .context(format!("Failed to read input file: {}", path.display()))?;

            // If it's a .wat file, parse it first
            let wasm_bytes = if path.extension().map_or(false, |ext| ext == "wat") {
                info!("Parsing WAT to WASM...");
                wat::parse_bytes(&file_bytes)
                    .context("Failed to parse WAT file")?
                    .into_owned()
            } else {
                file_bytes
            };

            // Decode functions
            let functions = decode_wasm_functions(&wasm_bytes)
                .context("Failed to decode WASM functions")?;

            info!("Found {} functions in module", functions.len());

            // Get the requested function
            let func = functions
                .into_iter()
                .find(|f| f.index == func_index)
                .context(format!("Function index {} not found", func_index))?;

            let name = format!("func_{}", func.index);
            info!("Compiling function {} ({} ops)", name, func.ops.len());

            (func.ops, name)
        }
        (None, Some(demo_name)) => {
            info!("Compiling demo function: {}", demo_name);

            match demo_name.as_str() {
                "add" => (
                    vec![
                        WasmOp::LocalGet(0),
                        WasmOp::LocalGet(1),
                        WasmOp::I32Add,
                    ],
                    "add".to_string(),
                ),
                "mul" => (
                    vec![
                        WasmOp::LocalGet(0),
                        WasmOp::LocalGet(1),
                        WasmOp::I32Mul,
                    ],
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
                _ => {
                    anyhow::bail!(
                        "Unknown demo: {}. Available: add, mul, calc",
                        demo_name
                    );
                }
            }
        }
        (None, None) => {
            // Default to add demo
            info!("No input specified, using 'add' demo");
            (
                vec![
                    WasmOp::LocalGet(0),
                    WasmOp::LocalGet(1),
                    WasmOp::I32Add,
                ],
                "add".to_string(),
            )
        }
    };

    info!("WASM operations: {:?}", wasm_ops);

    // Determine number of parameters by looking at LocalGet indices
    let num_params = wasm_ops
        .iter()
        .filter_map(|op| {
            if let WasmOp::LocalGet(idx) = op {
                Some(*idx + 1)
            } else {
                None
            }
        })
        .max()
        .unwrap_or(0);

    info!("Detected {} parameters", num_params);

    // Step 1: Instruction selection with AAPCS-compliant stack-based allocation
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector
        .select_with_stack(&wasm_ops, num_params)
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
    let elf_data = if cortex_m {
        build_cortex_m_elf(&code, &func_name)?
    } else {
        build_simple_elf(&code, &func_name)?
    };

    info!("Generated {} byte ELF file", elf_data.len());

    // Step 4: Write to file
    let mut file = File::create(&output)
        .context(format!("Failed to create output file: {}", output.display()))?;
    file.write_all(&elf_data)
        .context("Failed to write ELF data")?;

    println!("Compiled {} to {}", func_name, output.display());
    println!("  Code size: {} bytes", code.len());
    println!("  ELF size: {} bytes", elf_data.len());
    println!("\nInspect with: synth disasm {}", output.display());

    Ok(())
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
    let ram_size: u32 = 64 * 1024; // 64KB
    let stack_top = ram_base + ram_size;

    // Calculate addresses
    let vector_table_addr = flash_base;
    let vector_table_size: u32 = 128; // 32 entries * 4 bytes

    let startup_addr = flash_base + vector_table_size;
    let startup_code = generate_minimal_startup();
    let startup_size = startup_code.len() as u32;

    let default_handler_addr = startup_addr + startup_size;
    let default_handler = generate_default_handler();
    let default_handler_size = default_handler.len() as u32;

    // Align code to 4 bytes
    let code_addr = (default_handler_addr + default_handler_size + 3) & !3;

    info!("Cortex-M layout:");
    info!("  Vector table: 0x{:08x}", vector_table_addr);
    info!("  Startup code: 0x{:08x}", startup_addr);
    info!("  Default handler: 0x{:08x}", default_handler_addr);
    info!("  User code: 0x{:08x}", code_addr);
    info!("  Stack top: 0x{:08x}", stack_top);

    // Generate vector table
    let mut vt = VectorTable::new_cortex_m(stack_top);
    vt.reset_handler = startup_addr;

    // Set all handlers to default handler
    for handler in &mut vt.handlers {
        if handler.address == 0 {
            handler.address = default_handler_addr;
        }
    }

    let vector_table_data = vt.generate_binary().context("Vector table generation failed")?;

    // Build complete flash image
    let mut flash_image = Vec::new();

    // Vector table
    flash_image.extend_from_slice(&vector_table_data);

    // Pad to startup address
    while flash_image.len() < (startup_addr - flash_base) as usize {
        flash_image.push(0);
    }

    // Startup code (patch the literal pool with actual function address)
    let mut patched_startup = startup_code.clone();
    let func_addr_thumb = code_addr | 1; // Thumb bit
    patched_startup[8..12].copy_from_slice(&func_addr_thumb.to_le_bytes());
    flash_image.extend_from_slice(&patched_startup);

    // Default handler
    flash_image.extend_from_slice(&default_handler);

    // Pad to code address
    while flash_image.len() < (code_addr - flash_base) as usize {
        flash_image.push(0);
    }

    // User code
    flash_image.extend_from_slice(code);

    // Build ELF
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(startup_addr | 1); // Thumb bit

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
fn generate_minimal_startup() -> Vec<u8> {
    // This startup code:
    // 1. Loads the address of the user function
    // 2. Calls it with BLX
    // 3. Loops forever
    //
    // In Thumb assembly:
    //   LDR r0, [pc, #4]   ; Load function address from literal pool
    //   BLX r0             ; Call function
    //   B .                ; Infinite loop
    //   .word func_addr    ; Literal pool (filled by linker conceptually)

    vec![
        // LDR r0, [pc, #4] - Thumb encoding: 0x4801
        0x01, 0x48,
        // BLX r0 - Thumb encoding: 0x4780
        0x80, 0x47,
        // B . (branch to self) - Thumb encoding: 0xe7fe
        0xfe, 0xe7,
        // Padding for alignment
        0x00, 0x00,
        // Literal pool placeholder (will be at offset 8)
        // The actual function address will be computed at runtime
        // For now, put a placeholder that points to the infinite loop
        0x85, 0x00, 0x00, 0x00, // Will be code_addr | 1
    ]
}

/// Generate default exception handler (infinite loop)
fn generate_default_handler() -> Vec<u8> {
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
        // Stack pointer at offset 0 should be 0x20010000 (64KB RAM)
        // This is little-endian, so bytes are: 00 00 01 20

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
            if word == 0x20010000 {
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
        assert!(found_sp, "Stack pointer (0x20010000) not found in ELF");
    }

    #[test]
    fn test_simple_elf_generation() {
        let code = vec![0x00, 0x80, 0x80, 0xe0]; // ADD r0, r0, r1

        let elf_data = build_simple_elf(&code, "simple_func").unwrap();

        // Verify ELF magic
        assert_eq!(&elf_data[0..4], b"\x7fELF", "Invalid ELF magic");

        // Verify entry point is 0x8000
        let entry = u32::from_le_bytes([
            elf_data[24],
            elf_data[25],
            elf_data[26],
            elf_data[27],
        ]);
        assert_eq!(entry, 0x8000, "Entry point should be 0x8000");
    }

    #[test]
    fn test_startup_code_patching() {
        let code = vec![0x00, 0x80, 0x80, 0xe0];

        let elf_data = build_cortex_m_elf(&code, "patched").unwrap();

        // The function should be at 0x90, so literal pool should contain 0x91
        // Search for the pattern 0x91 0x00 0x00 0x00 in the startup code area
        let mut found_literal = false;
        for i in 0..elf_data.len().saturating_sub(4) {
            let word = u32::from_le_bytes([
                elf_data[i],
                elf_data[i + 1],
                elf_data[i + 2],
                elf_data[i + 3],
            ]);
            if word == 0x91 {
                found_literal = true;
                break;
            }
        }
        assert!(found_literal, "Literal pool should contain 0x91 (0x90 | 1)");
    }

    #[test]
    fn test_minimal_startup_generation() {
        let startup = generate_minimal_startup();

        // Should be 12 bytes
        assert_eq!(startup.len(), 12, "Startup code should be 12 bytes");

        // First two bytes: LDR r0, [pc, #4] = 0x4801
        assert_eq!(startup[0], 0x01);
        assert_eq!(startup[1], 0x48);

        // Next two bytes: BLX r0 = 0x4780
        assert_eq!(startup[2], 0x80);
        assert_eq!(startup[3], 0x47);

        // Next two bytes: B . = 0xe7fe
        assert_eq!(startup[4], 0xfe);
        assert_eq!(startup[5], 0xe7);
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
