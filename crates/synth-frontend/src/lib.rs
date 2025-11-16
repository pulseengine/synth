//! Synth Frontend - WebAssembly Component Model Parser
//!
//! This crate handles parsing and validation of WebAssembly Component Model binaries.

pub mod parser;
pub mod validator;

pub use parser::ComponentParser;
pub use validator::ComponentValidator;

use synth_core::{Component, Error, Result};
use std::path::Path;

/// Parse a WebAssembly component from a file
pub fn parse_component_file(path: &Path) -> Result<Component> {
    let bytes = std::fs::read(path).map_err(|e| {
        Error::parse(format!("Failed to read file {}: {}", path.display(), e))
    })?;

    parse_component(&bytes)
}

/// Parse a WebAssembly component from bytes
pub fn parse_component(bytes: &[u8]) -> Result<Component> {
    let parser = ComponentParser::new();
    parser.parse(bytes)
}

/// Validate a component
pub fn validate_component(component: &Component) -> Result<()> {
    let validator = ComponentValidator::new();
    validator.validate(component)
}
