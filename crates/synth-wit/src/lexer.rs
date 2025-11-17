//! WIT Lexer - Tokenization for WIT interface files

use crate::{Location, ParseError};

/// Token in WIT source
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub location: Location,
}

/// Token kinds
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // Keywords
    Interface,
    World,
    Import,
    Export,
    Package,
    Use,
    Func,
    Record,
    Variant,
    Enum,
    Flags,
    Resource,
    Type,
    Constructor,
    Static,

    // Primitive types
    U8, U16, U32, U64,
    S8, S16, S32, S64,
    F32, F64,
    Char,
    Bool,
    String,

    // Special types
    List,
    Option,
    Result,
    Tuple,

    // Symbols
    Colon,          // :
    Semicolon,      // ;
    Comma,          // ,
    Dot,            // .
    Arrow,          // ->
    LBrace,         // {
    RBrace,         // }
    LParen,         // (
    RParen,         // )
    LAngle,         // <
    RAngle,         // >
    Underscore,     // _

    // Identifiers and literals
    Identifier(String),

    // Special
    Eof,
}

/// WIT Lexer
pub struct Lexer {
    source: Vec<char>,
    position: usize,
    line: usize,
    column: usize,
}

impl Lexer {
    pub fn new(source: &str) -> Self {
        Self {
            source: source.chars().collect(),
            position: 0,
            line: 1,
            column: 1,
        }
    }

    fn current(&self) -> Option<char> {
        self.source.get(self.position).copied()
    }

    fn peek(&self, offset: usize) -> Option<char> {
        self.source.get(self.position + offset).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.current()?;
        self.position += 1;

        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }

        Some(ch)
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_comment(&mut self) {
        // Line comment: //
        if self.current() == Some('/') && self.peek(1) == Some('/') {
            while self.current().is_some() && self.current() != Some('\n') {
                self.advance();
            }
        }

        // Block comment: /* */
        if self.current() == Some('/') && self.peek(1) == Some('*') {
            self.advance(); // /
            self.advance(); // *

            while self.current().is_some() {
                if self.current() == Some('*') && self.peek(1) == Some('/') {
                    self.advance(); // *
                    self.advance(); // /
                    break;
                }
                self.advance();
            }
        }
    }

    fn location(&self) -> Location {
        Location::new(self.line, self.column, self.position)
    }

    fn read_identifier(&mut self) -> String {
        let mut ident = String::new();

        while let Some(ch) = self.current() {
            if ch.is_alphanumeric() || ch == '-' || ch == '_' {
                ident.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        ident
    }

    fn identifier_to_keyword(&self, ident: &str) -> TokenKind {
        match ident {
            "interface" => TokenKind::Interface,
            "world" => TokenKind::World,
            "import" => TokenKind::Import,
            "export" => TokenKind::Export,
            "package" => TokenKind::Package,
            "use" => TokenKind::Use,
            "func" => TokenKind::Func,
            "record" => TokenKind::Record,
            "variant" => TokenKind::Variant,
            "enum" => TokenKind::Enum,
            "flags" => TokenKind::Flags,
            "resource" => TokenKind::Resource,
            "type" => TokenKind::Type,
            "constructor" => TokenKind::Constructor,
            "static" => TokenKind::Static,

            // Primitive types
            "u8" => TokenKind::U8,
            "u16" => TokenKind::U16,
            "u32" => TokenKind::U32,
            "u64" => TokenKind::U64,
            "s8" => TokenKind::S8,
            "s16" => TokenKind::S16,
            "s32" => TokenKind::S32,
            "s64" => TokenKind::S64,
            "f32" => TokenKind::F32,
            "f64" => TokenKind::F64,
            "char" => TokenKind::Char,
            "bool" => TokenKind::Bool,
            "string" => TokenKind::String,

            // Special types
            "list" => TokenKind::List,
            "option" => TokenKind::Option,
            "result" => TokenKind::Result,
            "tuple" => TokenKind::Tuple,

            _ => TokenKind::Identifier(ident.to_string()),
        }
    }

    pub fn next_token(&mut self) -> Result<Token, ParseError> {
        loop {
            self.skip_whitespace();

            // Skip comments
            if self.current() == Some('/') &&
               (self.peek(1) == Some('/') || self.peek(1) == Some('*')) {
                self.skip_comment();
                continue;
            }

            break;
        }

        let location = self.location();

        let ch = match self.current() {
            Some(c) => c,
            None => return Ok(Token {
                kind: TokenKind::Eof,
                text: String::new(),
                location,
            }),
        };

        // Single-character tokens
        let kind = match ch {
            ':' => {
                self.advance();
                TokenKind::Colon
            }
            ';' => {
                self.advance();
                TokenKind::Semicolon
            }
            ',' => {
                self.advance();
                TokenKind::Comma
            }
            '.' => {
                self.advance();
                TokenKind::Dot
            }
            '{' => {
                self.advance();
                TokenKind::LBrace
            }
            '}' => {
                self.advance();
                TokenKind::RBrace
            }
            '(' => {
                self.advance();
                TokenKind::LParen
            }
            ')' => {
                self.advance();
                TokenKind::RParen
            }
            '<' => {
                self.advance();
                TokenKind::LAngle
            }
            '>' => {
                self.advance();
                TokenKind::RAngle
            }
            '_' => {
                self.advance();
                TokenKind::Underscore
            }
            '-' => {
                self.advance();
                if self.current() == Some('>') {
                    self.advance();
                    TokenKind::Arrow
                } else {
                    // Part of identifier
                    let mut ident = String::from("-");
                    ident.push_str(&self.read_identifier());
                    self.identifier_to_keyword(&ident)
                }
            }
            _ if ch.is_alphabetic() => {
                let ident = self.read_identifier();
                self.identifier_to_keyword(&ident)
            }
            _ => {
                return Err(ParseError {
                    message: format!("Unexpected character: '{}'", ch),
                    location: Some(location),
                });
            }
        };

        let text = match &kind {
            TokenKind::Identifier(s) => s.clone(),
            _ => String::new(),
        };

        Ok(Token { kind, text, location })
    }

    /// Tokenize entire source
    pub fn tokenize(&mut self) -> Result<Vec<Token>, ParseError> {
        let mut tokens = Vec::new();

        loop {
            let token = self.next_token()?;
            let is_eof = token.kind == TokenKind::Eof;
            tokens.push(token);

            if is_eof {
                break;
            }
        }

        Ok(tokens)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_keywords() {
        let source = "interface world import export func record variant enum";
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize().unwrap();

        assert_eq!(tokens[0].kind, TokenKind::Interface);
        assert_eq!(tokens[1].kind, TokenKind::World);
        assert_eq!(tokens[2].kind, TokenKind::Import);
        assert_eq!(tokens[3].kind, TokenKind::Export);
        assert_eq!(tokens[4].kind, TokenKind::Func);
        assert_eq!(tokens[5].kind, TokenKind::Record);
        assert_eq!(tokens[6].kind, TokenKind::Variant);
        assert_eq!(tokens[7].kind, TokenKind::Enum);
    }

    #[test]
    fn test_lex_types() {
        let source = "u32 s32 f32 string bool";
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize().unwrap();

        assert_eq!(tokens[0].kind, TokenKind::U32);
        assert_eq!(tokens[1].kind, TokenKind::S32);
        assert_eq!(tokens[2].kind, TokenKind::F32);
        assert_eq!(tokens[3].kind, TokenKind::String);
        assert_eq!(tokens[4].kind, TokenKind::Bool);
    }

    #[test]
    fn test_lex_symbols() {
        let source = ": ; , . -> { } ( ) < >";
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize().unwrap();

        assert_eq!(tokens[0].kind, TokenKind::Colon);
        assert_eq!(tokens[1].kind, TokenKind::Semicolon);
        assert_eq!(tokens[2].kind, TokenKind::Comma);
        assert_eq!(tokens[3].kind, TokenKind::Dot);
        assert_eq!(tokens[4].kind, TokenKind::Arrow);
        assert_eq!(tokens[5].kind, TokenKind::LBrace);
        assert_eq!(tokens[6].kind, TokenKind::RBrace);
        assert_eq!(tokens[7].kind, TokenKind::LParen);
        assert_eq!(tokens[8].kind, TokenKind::RParen);
        assert_eq!(tokens[9].kind, TokenKind::LAngle);
        assert_eq!(tokens[10].kind, TokenKind::RAngle);
    }

    #[test]
    fn test_lex_identifiers() {
        let source = "my-interface my_function hello-world";
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize().unwrap();

        match &tokens[0].kind {
            TokenKind::Identifier(s) => assert_eq!(s, "my-interface"),
            _ => panic!("Expected identifier"),
        }
        match &tokens[1].kind {
            TokenKind::Identifier(s) => assert_eq!(s, "my_function"),
            _ => panic!("Expected identifier"),
        }
    }

    #[test]
    fn test_lex_comments() {
        let source = r#"
            // Line comment
            interface test {
                /* Block comment */
                hello: func();
            }
        "#;
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize().unwrap();

        // Should skip comments
        assert_eq!(tokens[0].kind, TokenKind::Interface);
        match &tokens[1].kind {
            TokenKind::Identifier(s) => assert_eq!(s, "test"),
            _ => panic!("Expected identifier"),
        }
    }

    #[test]
    fn test_lex_function_signature() {
        let source = "hello: func(name: string) -> string;";
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize().unwrap();

        assert!(matches!(tokens[0].kind, TokenKind::Identifier(_)));
        assert_eq!(tokens[1].kind, TokenKind::Colon);
        assert_eq!(tokens[2].kind, TokenKind::Func);
        assert_eq!(tokens[3].kind, TokenKind::LParen);
        assert!(matches!(tokens[4].kind, TokenKind::Identifier(_)));
        assert_eq!(tokens[5].kind, TokenKind::Colon);
        assert_eq!(tokens[6].kind, TokenKind::String);
        assert_eq!(tokens[7].kind, TokenKind::RParen);
        assert_eq!(tokens[8].kind, TokenKind::Arrow);
        assert_eq!(tokens[9].kind, TokenKind::String);
        assert_eq!(tokens[10].kind, TokenKind::Semicolon);
    }
}
