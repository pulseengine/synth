//! CLI tool for WAST test execution
//!
//! Usage:
//!   synth-test generate --wast input.wast --robot output.robot
//!   synth-test run --wast input.wast --elf module.elf
//!   synth-test stats --wast input.wast

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::path::PathBuf;
use synth_test::{GenerateOptions, RobotGenerator, SynthTestConfig, WastParser};
use synth_test::renode::RenodeController;
use synth_test::runner::{NativeRunner, RunnerConfig, print_results};

#[derive(Parser)]
#[command(name = "synth-test")]
#[command(about = "WAST test runner for Synth - execute WebAssembly spec tests on Renode")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run WAST tests directly on Renode (native mode)
    Run {
        /// Input WAST file
        #[arg(short, long)]
        wast: PathBuf,

        /// Pre-compiled ELF file
        #[arg(short, long)]
        elf: PathBuf,

        /// Renode platform file
        #[arg(short, long, default_value = "synth_cortex_m.repl")]
        platform: String,

        /// Function address (with Thumb bit)
        #[arg(long, default_value_t = 0x91)]
        func_addr: u32,

        /// Renode monitor port
        #[arg(long, default_value_t = 1234)]
        port: u16,
    },

    /// Generate Robot Framework test file from WAST
    Generate {
        /// Input WAST file
        #[arg(short, long)]
        wast: PathBuf,

        /// Output Robot file
        #[arg(short, long)]
        robot: PathBuf,

        /// Renode platform file path (as it will appear in the Robot file)
        #[arg(short, long, default_value = "${CURDIR}/../renode/synth_cortex_m.repl")]
        platform: String,

        /// Function address (with Thumb bit) - fallback when --elf not provided
        #[arg(long, default_value = "0x91")]
        func_addr: String,

        /// ELF file to read function addresses from symbol table (multi-function support)
        #[arg(short, long)]
        elf: Option<PathBuf>,

        /// Only include tests for these functions (can be repeated)
        #[arg(long = "filter-func", short = 'f')]
        filter_funcs: Vec<String>,
    },

    /// Parse WAST and show statistics
    Stats {
        /// Input WAST file
        #[arg(short, long)]
        wast: PathBuf,
    },

    /// List test cases from WAST file
    List {
        /// Input WAST file
        #[arg(short, long)]
        wast: PathBuf,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Run {
            wast,
            elf,
            platform,
            func_addr,
            port,
        } => {
            let parsed = WastParser::parse_file(&wast)
                .with_context(|| format!("Failed to parse WAST file: {}", wast.display()))?;

            println!("Running {} tests from {}", parsed.test_cases.len(), wast.display());
            println!("ELF: {}", elf.display());
            println!("Connecting to Renode on port {}...", port);

            let config = RunnerConfig {
                platform_file: platform,
                func_addr,
                renode: synth_test::renode::RenodeConfig {
                    monitor_port: port,
                    ..Default::default()
                },
                ..Default::default()
            };

            let mut runner = NativeRunner::new(config);

            // Note: Assumes Renode is already running
            // In future, we can auto-start it
            runner.controller = Some(synth_test::renode::telnet::TelnetController::new(
                runner.config.renode.clone()
            ));

            if let Some(ctrl) = &mut runner.controller {
                ctrl.connect().context("Failed to connect to Renode. Is it running?")?;
            }

            let (results, summary) = runner.run_all(&parsed, &elf)?;

            print_results(&results, &summary);

            if summary.failed > 0 {
                std::process::exit(1);
            }

            Ok(())
        }

        Commands::Generate {
            wast,
            robot,
            platform,
            func_addr,
            elf,
            filter_funcs,
        } => {
            let parsed = WastParser::parse_file(&wast)
                .with_context(|| format!("Failed to parse WAST file: {}", wast.display()))?;

            let func_addr_num = if func_addr.starts_with("0x") {
                u32::from_str_radix(&func_addr[2..], 16)?
            } else {
                func_addr.parse()?
            };

            let mut config = SynthTestConfig {
                platform_file: PathBuf::from(&platform),
                function_address: func_addr_num,
                ..Default::default()
            };

            // Load function addresses from ELF if provided (also updates handler addresses)
            if let Some(elf_path) = &elf {
                config = config.with_elf_symbols(elf_path)
                    .with_context(|| format!("Failed to read ELF symbols from {}", elf_path.display()))?;

                println!("Loaded {} function symbols from ELF:", config.function_addresses.len());
                for (name, addr) in &config.function_addresses {
                    println!("  {} = 0x{:X}", name, addr);
                }
                println!("  Default_Handler = 0x{:X}", config.default_handler_address);
                println!("  Trap_Handler = 0x{:X}", config.trap_handler_address);
            }

            let options = if filter_funcs.is_empty() {
                GenerateOptions::default()
            } else {
                GenerateOptions::with_filter(filter_funcs)
            };

            RobotGenerator::generate_with_options(&parsed, &config, &robot, &options)?;

            let test_count = if options.filter_funcs.is_empty() {
                parsed.stats.assert_return_count
            } else {
                parsed.test_cases.iter()
                    .filter(|tc| options.should_include(&tc.function))
                    .count()
            };

            println!(
                "Generated {} test cases from {} to {}",
                test_count,
                wast.display(),
                robot.display()
            );
            println!(
                "  Modules: {}, Assert_return: {}, Skipped: {}",
                parsed.stats.modules_loaded,
                parsed.stats.assert_return_count,
                parsed.stats.skipped
            );

            Ok(())
        }

        Commands::Stats { wast } => {
            let parsed = WastParser::parse_file(&wast)?;

            println!("WAST Statistics for {}", wast.display());
            println!("  Modules loaded:     {}", parsed.stats.modules_loaded);
            println!("  Assert_return:      {}", parsed.stats.assert_return_count);
            println!("  Assert_trap:        {}", parsed.stats.assert_trap_count);
            println!("  Invoke:             {}", parsed.stats.invoke_count);
            println!("  Skipped:            {}", parsed.stats.skipped);
            println!("  Total test cases:   {}", parsed.test_cases.len());

            Ok(())
        }

        Commands::List { wast } => {
            let parsed = WastParser::parse_file(&wast)?;

            println!("Test cases in {}:", wast.display());
            for (i, tc) in parsed.test_cases.iter().enumerate() {
                println!(
                    "  {:3}. {:20} {:?} -> {:?}",
                    i + 1,
                    tc.function,
                    tc.args,
                    tc.expected
                );
            }

            Ok(())
        }
    }
}
