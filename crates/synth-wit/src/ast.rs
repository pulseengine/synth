//! AST (Abstract Syntax Tree) for WIT

use crate::Location;

/// Top-level WIT document
#[derive(Debug, Clone)]
pub struct WitDocument {
    pub items: Vec<WitItem>,
}

/// Top-level WIT items
#[derive(Debug, Clone)]
pub enum WitItem {
    Interface(Interface),
    World(World),
    Package(Package),
    Use(Use),
    TypeDef(TypeDef),
}

/// Package declaration
#[derive(Debug, Clone)]
pub struct Package {
    pub name: String,
    pub version: Option<String>,
    pub location: Location,
}

/// Use statement
#[derive(Debug, Clone)]
pub struct Use {
    pub path: Vec<String>,
    pub items: Vec<String>,
    pub location: Location,
}

/// Interface definition
#[derive(Debug, Clone)]
pub struct Interface {
    pub name: String,
    pub items: Vec<InterfaceItem>,
    pub location: Location,
}

/// Items that can appear in an interface
#[derive(Debug, Clone)]
pub enum InterfaceItem {
    Function(Function),
    TypeDef(TypeDef),
    Resource(Resource),
}

/// Function definition
#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub results: Vec<Type>,
    pub location: Location,
}

/// Type definition
#[derive(Debug, Clone)]
pub struct TypeDef {
    pub name: String,
    pub ty: TypeDefKind,
    pub location: Location,
}

/// Type definition kinds
#[derive(Debug, Clone)]
pub enum TypeDefKind {
    Record(Record),
    Variant(Variant),
    Enum(Enum),
    Flags(Flags),
    Alias(Type),
}

/// Record type (struct)
#[derive(Debug, Clone)]
pub struct Record {
    pub fields: Vec<Field>,
}

/// Record field
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub ty: Type,
    pub location: Location,
}

/// Variant type (tagged union)
#[derive(Debug, Clone)]
pub struct Variant {
    pub cases: Vec<Case>,
}

/// Variant case
#[derive(Debug, Clone)]
pub struct Case {
    pub name: String,
    pub ty: Option<Type>,
    pub location: Location,
}

/// Enum type
#[derive(Debug, Clone)]
pub struct Enum {
    pub cases: Vec<String>,
}

/// Flags type (bitflags)
#[derive(Debug, Clone)]
pub struct Flags {
    pub flags: Vec<String>,
}

/// Resource definition
#[derive(Debug, Clone)]
pub struct Resource {
    pub name: String,
    pub methods: Vec<Function>,
    pub constructor: Option<Function>,
    pub static_methods: Vec<Function>,
    pub location: Location,
}

/// World definition
#[derive(Debug, Clone)]
pub struct World {
    pub name: String,
    pub items: Vec<WorldItem>,
    pub location: Location,
}

/// Items that can appear in a world
#[derive(Debug, Clone)]
pub enum WorldItem {
    Import(WorldImport),
    Export(WorldExport),
    Use(Use),
    TypeDef(TypeDef),
}

/// World import
#[derive(Debug, Clone)]
pub struct WorldImport {
    pub name: String,
    pub item: WorldImportItem,
    pub location: Location,
}

/// World import item
#[derive(Debug, Clone)]
pub enum WorldImportItem {
    Interface(Interface),
    Function(Function),
}

/// World export
#[derive(Debug, Clone)]
pub struct WorldExport {
    pub name: String,
    pub item: WorldExportItem,
    pub location: Location,
}

/// World export item
#[derive(Debug, Clone)]
pub enum WorldExportItem {
    Interface(Interface),
    Function(Function),
}

/// WIT types
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    // Primitive types
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
    S64,
    F32,
    F64,
    Char,
    Bool,
    String,

    // Container types
    List(Box<Type>),
    Option(Box<Type>),
    Result {
        ok: Option<Box<Type>>,
        err: Option<Box<Type>>,
    },
    Tuple(Vec<Type>),

    // Named types
    Named(String),

    // Generic parameter
    Generic(String),
}

impl Type {
    /// Check if type is a primitive
    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::S8
                | Type::S16
                | Type::S32
                | Type::S64
                | Type::F32
                | Type::F64
                | Type::Char
                | Type::Bool
        )
    }

    /// Get the size of the type in bytes (for primitives)
    pub fn size_bytes(&self) -> Option<usize> {
        match self {
            Type::U8 | Type::S8 | Type::Bool => Some(1),
            Type::U16 | Type::S16 => Some(2),
            Type::U32 | Type::S32 | Type::F32 | Type::Char => Some(4),
            Type::U64 | Type::S64 | Type::F64 => Some(8),
            _ => None,
        }
    }

    /// Get the alignment of the type (for primitives)
    pub fn alignment(&self) -> Option<usize> {
        self.size_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_is_primitive() {
        assert!(Type::U32.is_primitive());
        assert!(Type::S32.is_primitive());
        assert!(Type::F32.is_primitive());
        assert!(Type::Bool.is_primitive());
        assert!(!Type::String.is_primitive());
        assert!(!Type::List(Box::new(Type::U8)).is_primitive());
    }

    #[test]
    fn test_type_size() {
        assert_eq!(Type::U8.size_bytes(), Some(1));
        assert_eq!(Type::U16.size_bytes(), Some(2));
        assert_eq!(Type::U32.size_bytes(), Some(4));
        assert_eq!(Type::U64.size_bytes(), Some(8));
        assert_eq!(Type::F32.size_bytes(), Some(4));
        assert_eq!(Type::F64.size_bytes(), Some(8));
        assert_eq!(Type::String.size_bytes(), None);
    }

    #[test]
    fn test_complex_types() {
        let list_type = Type::List(Box::new(Type::U8));
        assert!(!list_type.is_primitive());

        let option_type = Type::Option(Box::new(Type::String));
        assert!(!option_type.is_primitive());

        let result_type = Type::Result {
            ok: Some(Box::new(Type::U32)),
            err: Some(Box::new(Type::String)),
        };
        assert!(!result_type.is_primitive());
    }
}
