//! WIT Parser - Parses tokenized WIT source into AST

use crate::{
    ast::*,
    lexer::{Lexer, Token, TokenKind},
    Location, ParseError,
};

pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
    eof_token: Token,
}

impl Parser {
    pub fn new(mut lexer: Lexer) -> Self {
        let tokens = lexer.tokenize().unwrap_or_default();
        let eof_token = Token {
            kind: TokenKind::Eof,
            text: String::new(),
            location: Location::new(0, 0, 0),
        };
        Self {
            tokens,
            position: 0,
            eof_token,
        }
    }

    fn current(&self) -> &Token {
        self.tokens.get(self.position).unwrap_or(&self.eof_token)
    }

    fn peek(&self, offset: usize) -> &Token {
        self.tokens
            .get(self.position + offset)
            .unwrap_or(&self.eof_token)
    }

    fn advance(&mut self) -> &Token {
        let token = &self.tokens[self.position];
        if self.position < self.tokens.len() {
            self.position += 1;
        }
        token
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        let token = self.current().clone();
        if token.kind == kind {
            self.advance();
            Ok(token)
        } else {
            Err(ParseError {
                message: format!("Expected {:?}, found {:?}", kind, token.kind),
                location: Some(token.location),
            })
        }
    }

    fn expect_identifier(&mut self) -> Result<String, ParseError> {
        let token = self.current().clone();
        match &token.kind {
            TokenKind::Identifier(s) => {
                self.advance();
                Ok(s.clone())
            }
            _ => Err(ParseError {
                message: format!("Expected identifier, found {:?}", token.kind),
                location: Some(token.location),
            }),
        }
    }

    pub fn parse_document(&mut self) -> Result<WitDocument, ParseError> {
        let mut items = Vec::new();

        while self.current().kind != TokenKind::Eof {
            items.push(self.parse_item()?);
        }

        Ok(WitDocument { items })
    }

    fn parse_item(&mut self) -> Result<WitItem, ParseError> {
        match &self.current().kind {
            TokenKind::Package => Ok(WitItem::Package(self.parse_package()?)),
            TokenKind::Use => Ok(WitItem::Use(self.parse_use()?)),
            TokenKind::Interface => Ok(WitItem::Interface(self.parse_interface()?)),
            TokenKind::World => Ok(WitItem::World(self.parse_world()?)),
            TokenKind::Type => Ok(WitItem::TypeDef(self.parse_typedef()?)),
            _ => Err(ParseError {
                message: format!("Unexpected token: {:?}", self.current().kind),
                location: Some(self.current().location),
            }),
        }
    }

    fn parse_package(&mut self) -> Result<Package, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::Package)?;

        let name = self.expect_identifier()?;
        let version = if self.current().kind == TokenKind::Identifier("@".to_string()) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            None
        };

        self.expect(TokenKind::Semicolon)?;

        Ok(Package {
            name,
            version,
            location,
        })
    }

    fn parse_use(&mut self) -> Result<Use, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::Use)?;

        let mut path = vec![self.expect_identifier()?];

        while self.current().kind == TokenKind::Dot {
            self.advance();
            path.push(self.expect_identifier()?);
        }

        self.expect(TokenKind::Dot)?;
        self.expect(TokenKind::LBrace)?;

        let mut items = Vec::new();
        loop {
            items.push(self.expect_identifier()?);

            if self.current().kind == TokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;
        self.expect(TokenKind::Semicolon)?;

        Ok(Use {
            path,
            items,
            location,
        })
    }

    fn parse_interface(&mut self) -> Result<Interface, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::Interface)?;

        let name = self.expect_identifier()?;
        self.expect(TokenKind::LBrace)?;

        let mut items = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            items.push(self.parse_interface_item()?);
        }

        self.expect(TokenKind::RBrace)?;

        Ok(Interface {
            name,
            items,
            location,
        })
    }

    fn parse_interface_item(&mut self) -> Result<InterfaceItem, ParseError> {
        match &self.current().kind {
            TokenKind::Type
            | TokenKind::Record
            | TokenKind::Variant
            | TokenKind::Enum
            | TokenKind::Flags => Ok(InterfaceItem::TypeDef(self.parse_typedef()?)),
            TokenKind::Resource => Ok(InterfaceItem::Resource(self.parse_resource()?)),
            TokenKind::Identifier(_) => Ok(InterfaceItem::Function(self.parse_function()?)),
            _ => Err(ParseError {
                message: format!("Unexpected token in interface: {:?}", self.current().kind),
                location: Some(self.current().location),
            }),
        }
    }

    fn parse_function(&mut self) -> Result<Function, ParseError> {
        let location = self.current().location;
        let name = self.expect_identifier()?;

        self.expect(TokenKind::Colon)?;
        self.expect(TokenKind::Func)?;
        self.expect(TokenKind::LParen)?;

        let mut params = Vec::new();

        if self.current().kind != TokenKind::RParen {
            loop {
                let param_name = self.expect_identifier()?;
                self.expect(TokenKind::Colon)?;
                let param_type = self.parse_type()?;
                params.push((param_name, param_type));

                if self.current().kind == TokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        self.expect(TokenKind::RParen)?;

        let results = if self.current().kind == TokenKind::Arrow {
            self.advance();
            vec![self.parse_type()?]
        } else {
            Vec::new()
        };

        self.expect(TokenKind::Semicolon)?;

        Ok(Function {
            name,
            params,
            results,
            location,
        })
    }

    fn parse_type(&mut self) -> Result<Type, ParseError> {
        match &self.current().kind {
            // Primitive types
            TokenKind::U8 => {
                self.advance();
                Ok(Type::U8)
            }
            TokenKind::U16 => {
                self.advance();
                Ok(Type::U16)
            }
            TokenKind::U32 => {
                self.advance();
                Ok(Type::U32)
            }
            TokenKind::U64 => {
                self.advance();
                Ok(Type::U64)
            }
            TokenKind::S8 => {
                self.advance();
                Ok(Type::S8)
            }
            TokenKind::S16 => {
                self.advance();
                Ok(Type::S16)
            }
            TokenKind::S32 => {
                self.advance();
                Ok(Type::S32)
            }
            TokenKind::S64 => {
                self.advance();
                Ok(Type::S64)
            }
            TokenKind::F32 => {
                self.advance();
                Ok(Type::F32)
            }
            TokenKind::F64 => {
                self.advance();
                Ok(Type::F64)
            }
            TokenKind::Char => {
                self.advance();
                Ok(Type::Char)
            }
            TokenKind::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            TokenKind::String => {
                self.advance();
                Ok(Type::String)
            }

            // Container types
            TokenKind::List => {
                self.advance();
                self.expect(TokenKind::LAngle)?;
                let inner = self.parse_type()?;
                self.expect(TokenKind::RAngle)?;
                Ok(Type::List(Box::new(inner)))
            }
            TokenKind::Option => {
                self.advance();
                self.expect(TokenKind::LAngle)?;
                let inner = self.parse_type()?;
                self.expect(TokenKind::RAngle)?;
                Ok(Type::Option(Box::new(inner)))
            }
            TokenKind::Result => {
                self.advance();
                self.expect(TokenKind::LAngle)?;

                let ok = if self.current().kind == TokenKind::Underscore {
                    self.advance();
                    None
                } else {
                    Some(Box::new(self.parse_type()?))
                };

                self.expect(TokenKind::Comma)?;

                let err = if self.current().kind == TokenKind::Underscore {
                    self.advance();
                    None
                } else {
                    Some(Box::new(self.parse_type()?))
                };

                self.expect(TokenKind::RAngle)?;
                Ok(Type::Result { ok, err })
            }
            TokenKind::Tuple => {
                self.advance();
                self.expect(TokenKind::LAngle)?;

                let mut types = vec![self.parse_type()?];

                while self.current().kind == TokenKind::Comma {
                    self.advance();
                    types.push(self.parse_type()?);
                }

                self.expect(TokenKind::RAngle)?;
                Ok(Type::Tuple(types))
            }

            // Named types
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();
                Ok(Type::Named(name))
            }

            _ => Err(ParseError {
                message: format!("Expected type, found {:?}", self.current().kind),
                location: Some(self.current().location),
            }),
        }
    }

    fn parse_typedef(&mut self) -> Result<TypeDef, ParseError> {
        let location = self.current().location;

        let kind = match &self.current().kind {
            TokenKind::Type => {
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(TokenKind::Semicolon)?;
                return Ok(TypeDef {
                    name,
                    ty: TypeDefKind::Alias(Type::Named("unknown".to_string())),
                    location,
                });
            }
            TokenKind::Record => {
                self.advance();
                let name = self.expect_identifier()?;
                let record = self.parse_record()?;
                (name, TypeDefKind::Record(record))
            }
            TokenKind::Variant => {
                self.advance();
                let name = self.expect_identifier()?;
                let variant = self.parse_variant()?;
                (name, TypeDefKind::Variant(variant))
            }
            TokenKind::Enum => {
                self.advance();
                let name = self.expect_identifier()?;
                let enum_def = self.parse_enum()?;
                (name, TypeDefKind::Enum(enum_def))
            }
            TokenKind::Flags => {
                self.advance();
                let name = self.expect_identifier()?;
                let flags = self.parse_flags()?;
                (name, TypeDefKind::Flags(flags))
            }
            _ => {
                return Err(ParseError {
                    message: format!("Expected type definition, found {:?}", self.current().kind),
                    location: Some(self.current().location),
                });
            }
        };

        Ok(TypeDef {
            name: kind.0,
            ty: kind.1,
            location,
        })
    }

    fn parse_record(&mut self) -> Result<Record, ParseError> {
        self.expect(TokenKind::LBrace)?;

        let mut fields = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            let location = self.current().location;
            let name = self.expect_identifier()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_type()?;
            self.expect(TokenKind::Comma)?;

            fields.push(Field { name, ty, location });
        }

        self.expect(TokenKind::RBrace)?;

        Ok(Record { fields })
    }

    fn parse_variant(&mut self) -> Result<Variant, ParseError> {
        self.expect(TokenKind::LBrace)?;

        let mut cases = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            let location = self.current().location;
            let name = self.expect_identifier()?;

            let ty = if self.current().kind == TokenKind::LParen {
                self.advance();
                let t = self.parse_type()?;
                self.expect(TokenKind::RParen)?;
                Some(t)
            } else {
                None
            };

            self.expect(TokenKind::Comma)?;

            cases.push(Case { name, ty, location });
        }

        self.expect(TokenKind::RBrace)?;

        Ok(Variant { cases })
    }

    fn parse_enum(&mut self) -> Result<Enum, ParseError> {
        self.expect(TokenKind::LBrace)?;

        let mut cases = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            cases.push(self.expect_identifier()?);
            self.expect(TokenKind::Comma)?;
        }

        self.expect(TokenKind::RBrace)?;

        Ok(Enum { cases })
    }

    fn parse_flags(&mut self) -> Result<Flags, ParseError> {
        self.expect(TokenKind::LBrace)?;

        let mut flags = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            flags.push(self.expect_identifier()?);
            self.expect(TokenKind::Comma)?;
        }

        self.expect(TokenKind::RBrace)?;

        Ok(Flags { flags })
    }

    fn parse_resource(&mut self) -> Result<Resource, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::Resource)?;

        let name = self.expect_identifier()?;
        self.expect(TokenKind::LBrace)?;

        let mut methods = Vec::new();
        let mut constructor = None;
        let mut static_methods = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            if self.current().kind == TokenKind::Constructor {
                self.advance();
                constructor = Some(self.parse_function()?);
            } else if self.current().kind == TokenKind::Static {
                self.advance();
                static_methods.push(self.parse_function()?);
            } else {
                methods.push(self.parse_function()?);
            }
        }

        self.expect(TokenKind::RBrace)?;

        Ok(Resource {
            name,
            methods,
            constructor,
            static_methods,
            location,
        })
    }

    fn parse_world(&mut self) -> Result<World, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::World)?;

        let name = self.expect_identifier()?;
        self.expect(TokenKind::LBrace)?;

        let mut items = Vec::new();

        while self.current().kind != TokenKind::RBrace {
            items.push(self.parse_world_item()?);
        }

        self.expect(TokenKind::RBrace)?;

        Ok(World {
            name,
            items,
            location,
        })
    }

    fn parse_world_item(&mut self) -> Result<WorldItem, ParseError> {
        match &self.current().kind {
            TokenKind::Import => Ok(WorldItem::Import(self.parse_world_import()?)),
            TokenKind::Export => Ok(WorldItem::Export(self.parse_world_export()?)),
            TokenKind::Use => Ok(WorldItem::Use(self.parse_use()?)),
            TokenKind::Type
            | TokenKind::Record
            | TokenKind::Variant
            | TokenKind::Enum
            | TokenKind::Flags => Ok(WorldItem::TypeDef(self.parse_typedef()?)),
            _ => Err(ParseError {
                message: format!("Unexpected token in world: {:?}", self.current().kind),
                location: Some(self.current().location),
            }),
        }
    }

    fn parse_world_import(&mut self) -> Result<WorldImport, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::Import)?;

        let name = self.expect_identifier()?;
        self.expect(TokenKind::Colon)?;

        let item = if self.current().kind == TokenKind::Interface {
            WorldImportItem::Interface(self.parse_interface()?)
        } else if self.current().kind == TokenKind::Func {
            // Parse function signature without the "name:" prefix
            let func = self.parse_function_signature(name.clone(), location)?;
            WorldImportItem::Function(func)
        } else {
            return Err(ParseError {
                message: format!(
                    "Expected interface or func, found {:?}",
                    self.current().kind
                ),
                location: Some(self.current().location),
            });
        };

        Ok(WorldImport {
            name,
            item,
            location,
        })
    }

    fn parse_world_export(&mut self) -> Result<WorldExport, ParseError> {
        let location = self.current().location;
        self.expect(TokenKind::Export)?;

        let name = self.expect_identifier()?;
        self.expect(TokenKind::Colon)?;

        let item = if self.current().kind == TokenKind::Interface {
            WorldExportItem::Interface(self.parse_interface()?)
        } else if self.current().kind == TokenKind::Func {
            // Parse function signature without the "name:" prefix
            let func = self.parse_function_signature(name.clone(), location)?;
            WorldExportItem::Function(func)
        } else {
            return Err(ParseError {
                message: format!(
                    "Expected interface or func, found {:?}",
                    self.current().kind
                ),
                location: Some(self.current().location),
            });
        };

        Ok(WorldExport {
            name,
            item,
            location,
        })
    }

    /// Parse function signature starting from "func(...)"
    /// Used when the function name has already been consumed
    fn parse_function_signature(
        &mut self,
        name: String,
        location: Location,
    ) -> Result<Function, ParseError> {
        self.expect(TokenKind::Func)?;
        self.expect(TokenKind::LParen)?;

        let mut params = Vec::new();

        if self.current().kind != TokenKind::RParen {
            loop {
                let param_name = self.expect_identifier()?;
                self.expect(TokenKind::Colon)?;
                let param_type = self.parse_type()?;
                params.push((param_name, param_type));

                if self.current().kind == TokenKind::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        self.expect(TokenKind::RParen)?;

        let results = if self.current().kind == TokenKind::Arrow {
            self.advance();
            vec![self.parse_type()?]
        } else {
            Vec::new()
        };

        self.expect(TokenKind::Semicolon)?;

        Ok(Function {
            name,
            params,
            results,
            location,
        })
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

        let lexer = Lexer::new(source);
        let mut parser = Parser::new(lexer);
        let doc = parser.parse_document().unwrap();

        assert_eq!(doc.items.len(), 1);
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

        let lexer = Lexer::new(source);
        let mut parser = Parser::new(lexer);
        let doc = parser.parse_document().unwrap();

        assert_eq!(doc.items.len(), 1);
    }

    #[test]
    fn test_parse_variant() {
        let source = r#"
            interface types {
                variant status {
                    success(u32),
                    failure(string),
                }
            }
        "#;

        let lexer = Lexer::new(source);
        let mut parser = Parser::new(lexer);
        let doc = parser.parse_document().unwrap();

        assert_eq!(doc.items.len(), 1);
    }
}
