//! WebAssembly Component Validator

use synth_core::{Component, Error, Result};

/// Component validator
pub struct ComponentValidator;

impl ComponentValidator {
    /// Create a new validator
    pub fn new() -> Self {
        Self
    }

    /// Validate a component
    pub fn validate(&self, component: &Component) -> Result<()> {
        // Basic validation checks

        // Check that we have at least one module
        if component.modules.is_empty() {
            return Err(Error::validation("Component must have at least one module"));
        }

        // Validate memory requirements
        let total_memory = component.total_memory_size();
        if total_memory == 0 {
            tracing::warn!("Component has no linear memory");
        }

        // Check for memory limits (e.g., 4GB limit for 32-bit)
        const MAX_MEMORY_32BIT: u64 = 4 * 1024 * 1024 * 1024; // 4GB
        if total_memory > MAX_MEMORY_32BIT {
            return Err(Error::validation(format!(
                "Total memory ({} bytes) exceeds 32-bit limit",
                total_memory
            )));
        }

        // Validate each module
        for module in &component.modules {
            self.validate_module(module)?;
        }

        Ok(())
    }

    /// Validate a single module
    fn validate_module(&self, module: &synth_core::CoreModule) -> Result<()> {
        // Check module has valid binary
        if module.binary.is_empty() {
            return Err(Error::validation("Module has empty binary"));
        }

        // Check WebAssembly magic number
        if module.binary.len() < 8 {
            return Err(Error::validation("Module binary too short"));
        }

        let magic = &module.binary[0..4];
        if magic != b"\x00asm" {
            return Err(Error::validation("Invalid WebAssembly magic number"));
        }

        // Validate memories
        for memory in &module.memories {
            // Check that initial size is not larger than maximum
            if let Some(max) = memory.maximum {
                if memory.initial > max {
                    return Err(Error::validation(format!(
                        "Memory initial size ({}) exceeds maximum ({})",
                        memory.initial, max
                    )));
                }
            }

            // Check reasonable limits (e.g., 4GB = 65536 pages for 32-bit)
            const MAX_PAGES_32BIT: u32 = 65536;
            if memory.initial > MAX_PAGES_32BIT {
                return Err(Error::validation(format!(
                    "Memory initial size ({} pages) exceeds 32-bit limit",
                    memory.initial
                )));
            }
        }

        Ok(())
    }
}

impl Default for ComponentValidator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_core::{Component, CoreModule};

    #[test]
    fn test_validate_empty_component() {
        let component = Component::new("test".to_string());
        let validator = ComponentValidator::new();

        let result = validator.validate(&component);
        assert!(result.is_err()); // Should fail - no modules
    }

    #[test]
    fn test_validate_valid_component() {
        let mut component = Component::new("test".to_string());

        // Add a module with valid WebAssembly magic
        let module = CoreModule {
            id: "module0".to_string(),
            binary: vec![0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00],
            functions: Vec::new(),
            memories: Vec::new(),
            tables: Vec::new(),
            globals: Vec::new(),
        };
        component.modules.push(module);

        let validator = ComponentValidator::new();
        let result = validator.validate(&component);
        assert!(result.is_ok());
    }
}
