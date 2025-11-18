//! WebAssembly Component Parser

use synth_core::{
    Component, CoreModule, Error, Export, ExportKind, Memory, Result,
};
use wasmparser::{Parser, Payload};

/// Component parser
pub struct ComponentParser;

impl ComponentParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self
    }

    /// Parse a WebAssembly component from bytes
    pub fn parse(&self, bytes: &[u8]) -> Result<Component> {
        let parser = Parser::new(0);

        // For PoC, we'll treat all WebAssembly modules as components
        // In production, we'd properly handle the Component Model format
        let mut component = Component::new("main".to_string());

        for payload in parser.parse_all(bytes) {
            let payload =
                payload.map_err(|e| Error::parse(format!("WebAssembly parse error: {}", e)))?;

            match payload {
                Payload::Version { .. } => {
                    // Validate version
                }
                Payload::ModuleSection { .. } => {
                    // This is a component with embedded modules
                    // For PoC, we'll handle this later
                }
                Payload::TypeSection(reader) => {
                    // Parse type section (function signatures)
                    for ty in reader {
                        let _ty =
                            ty.map_err(|e| Error::parse(format!("Failed to parse type: {}", e)))?;
                        // Store types for later use
                    }
                }
                Payload::FunctionSection(reader) => {
                    // Parse function declarations
                    for func in reader {
                        let _func_type_idx = func.map_err(|e| {
                            Error::parse(format!("Failed to parse function: {}", e))
                        })?;
                        // We'll fully implement this in the next iteration
                    }
                }
                Payload::MemorySection(reader) => {
                    // Parse linear memories
                    let mut memories = Vec::new();
                    for (index, memory) in reader.into_iter().enumerate() {
                        let mem = memory
                            .map_err(|e| Error::parse(format!("Failed to parse memory: {}", e)))?;

                        memories.push(Memory {
                            index: index as u32,
                            initial: mem.initial as u32,
                            maximum: mem.maximum.map(|m| m as u32),
                            shared: mem.shared,
                            memory64: mem.memory64,
                        });
                    }

                    // Create a core module if we don't have one yet
                    if component.modules.is_empty() {
                        let module = CoreModule {
                            id: "module0".to_string(),
                            binary: bytes.to_vec(),
                            functions: Vec::new(),
                            memories,
                            tables: Vec::new(),
                            globals: Vec::new(),
                        };
                        component.modules.push(module);
                    } else {
                        component.modules[0].memories.extend(memories);
                    }
                }
                Payload::ExportSection(reader) => {
                    // Parse exports
                    for export in reader {
                        let export = export
                            .map_err(|e| Error::parse(format!("Failed to parse export: {}", e)))?;

                        let kind = match export.kind {
                            wasmparser::ExternalKind::Func => ExportKind::Function(export.index),
                            wasmparser::ExternalKind::Memory => ExportKind::Memory(export.index),
                            wasmparser::ExternalKind::Table => ExportKind::Table(export.index),
                            wasmparser::ExternalKind::Global => ExportKind::Global(export.index),
                            _ => continue,
                        };

                        component.exports.push(Export {
                            name: export.name.to_string(),
                            kind,
                        });
                    }
                }
                Payload::CodeSectionEntry(body) => {
                    // Parse function bodies
                    // For PoC, we'll skip detailed parsing
                    let _locals = body
                        .get_locals_reader()
                        .map_err(|e| Error::parse(format!("Failed to parse locals: {}", e)))?;
                }
                _ => {
                    // Handle other sections as needed
                }
            }
        }

        // If we parsed a regular module, ensure it's in a component wrapper
        if component.modules.is_empty() {
            let module = CoreModule {
                id: "module0".to_string(),
                binary: bytes.to_vec(),
                functions: Vec::new(),
                memories: Vec::new(),
                tables: Vec::new(),
                globals: Vec::new(),
            };
            component.modules.push(module);
        }

        Ok(component)
    }
}

impl Default for ComponentParser {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_module() {
        // Minimal valid WebAssembly module
        let wasm = vec![
            0x00, 0x61, 0x73, 0x6D, // Magic number
            0x01, 0x00, 0x00, 0x00, // Version
        ];

        let parser = ComponentParser::new();
        let result = parser.parse(&wasm);
        assert!(result.is_ok());
    }
}
