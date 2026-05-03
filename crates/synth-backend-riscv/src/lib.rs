//! RISC-V backend for synth — RV32IMAC encoder, ELF builder, PMP allocator.
//!
//! Mirrors the structure of `synth-backend` (ARM Cortex-M) but emits RISC-V
//! machine code. The instruction selector lives in `synth-synthesis::riscv`;
//! this crate contains the binary encoder, ELF emission, linker script
//! generation, and Physical Memory Protection (PMP) allocator.
//!
//! Supported variants (per `TargetSpec::IsaVariant::RiscV32 { extensions }`):
//! - RV32I  — base 32-bit integer
//! - RV32IM — adds multiply/divide
//! - RV32IMA — adds atomics
//! - RV32IMAC — adds compressed (16-bit) instructions
//!
//! The encoder always emits 32-bit instructions in this skeleton. The 16-bit
//! C-extension encoding will be a peephole pass in a follow-up.

pub mod backend;
pub mod elf_builder;
pub mod encoder;
pub mod linker_script;
pub mod pmp;
pub mod register;
pub mod riscv_op;
pub mod selector;
pub mod startup;

pub use backend::RiscVBackend;
pub use elf_builder::{ElfMode, RiscVElfBuilder, RiscVElfFunction};
pub use encoder::{RiscVEncoder, RiscVEncodingError};
pub use linker_script::{LinkerScriptConfig, RiscVLinkerScriptGenerator};
pub use pmp::{PMPAllocator, PMPEntry, PMPError, PMPMode, PMPPermissions};
pub use register::{Reg, RegClass};
pub use riscv_op::{Branch, Csr, RiscVOp};
pub use selector::{RiscVSelection, SelectorError, select_simple};
pub use startup::{RiscVStartupGenerator, StartupConfig};
