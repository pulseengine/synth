//! WIT (WebAssembly Interface Types) Parser for Synth
//!
//! This crate implements a parser for the WIT interface definition language,
//! enabling Component Model support in Synth.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod types;

pub use ast::*;
pub use lexer::{Lexer, Token, TokenKind};
pub use parser::Parser;
pub use types::*;

use std::path::Path;

/// Parse a WIT file from source code
pub fn parse_wit(source: &str) -> Result<WitDocument, ParseError> {
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(lexer);
    parser.parse_document()
}

/// Parse a WIT file from a file path
pub fn parse_wit_file<P: AsRef<Path>>(path: P) -> Result<WitDocument, ParseError> {
    let source = std::fs::read_to_string(path)?;
    parse_wit(&source)
}

/// Parse error type
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub location: Option<Location>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(loc) = &self.location {
            write!(f, "Parse error at {}:{}: {}", loc.line, loc.column, self.message)
        } else {
            write!(f, "Parse error: {}", self.message)
        }
    }
}

impl std::error::Error for ParseError {}

impl From<std::io::Error> for ParseError {
    fn from(err: std::io::Error) -> Self {
        ParseError {
            message: err.to_string(),
            location: None,
        }
    }
}

/// Source location
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}

impl Location {
    pub fn new(line: usize, column: usize, offset: usize) -> Self {
        Self { line, column, offset }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_interface() {
        let source = r#"
            interface greeting {
                hello: func(name: string) -> string;
            }
        "#;

        let doc = parse_wit(source).expect("Failed to parse");
        assert!(!doc.items.is_empty());
    }

    #[test]
    fn test_parse_world() {
        let source = r#"
            world app {
                import log: func(msg: string);
                export run: func();
            }
        "#;

        let doc = parse_wit(source).expect("Failed to parse");
        assert!(!doc.items.is_empty());
    }

    #[test]
    fn test_parse_record() {
        let source = r#"
            interface types {
                record point {
                    x: s32,
                    y: s32,
                }
            }
        "#;

        let doc = parse_wit(source).expect("Failed to parse");
        assert!(!doc.items.is_empty());
    }

    #[test]
    fn test_parse_variant() {
        let source = r#"
            interface types {
                variant response {
                    ok(u32),
                    err(string),
                }
            }
        "#;

        let doc = parse_wit(source).expect("Failed to parse");
        assert!(!doc.items.is_empty());
    }

    #[test]
    fn test_parse_enum() {
        let source = r#"
            interface types {
                enum color {
                    red,
                    green,
                    blue,
                }
            }
        "#;

        let doc = parse_wit(source).expect("Failed to parse");
        assert!(!doc.items.is_empty());
    }
}
