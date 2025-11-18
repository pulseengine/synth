//! WebAssembly Component Model data structures

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// A WebAssembly Component
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Component {
    /// Component name/ID
    pub name: String,

    /// Core modules contained in this component
    pub modules: Vec<CoreModule>,

    /// Nested components
    pub components: Vec<Component>,

    /// Component instances
    pub instances: Vec<ComponentInstance>,

    /// Interfaces defined by this component
    pub interfaces: HashMap<String, WITInterface>,

    /// Imports required by this component
    pub imports: Vec<Import>,

    /// Exports provided by this component
    pub exports: Vec<Export>,
}

/// A core WebAssembly module
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoreModule {
    /// Module ID
    pub id: String,

    /// Module binary data
    pub binary: Vec<u8>,

    /// Functions defined in this module
    pub functions: Vec<Function>,

    /// Linear memories
    pub memories: Vec<Memory>,

    /// Tables
    pub tables: Vec<Table>,

    /// Globals
    pub globals: Vec<Global>,
}

/// A function in a core module
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Function {
    /// Function index
    pub index: u32,

    /// Function name (if available)
    pub name: Option<String>,

    /// Function type signature
    pub signature: FunctionSignature,

    /// Is this function exported?
    pub exported: bool,

    /// Is this function imported?
    pub imported: bool,
}

/// Function signature (parameters and results)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSignature {
    /// Parameter types
    pub params: Vec<ValueType>,

    /// Result types
    pub results: Vec<ValueType>,
}

/// WebAssembly value types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ValueType {
    I32,
    I64,
    F32,
    F64,
    V128,
    FuncRef,
    ExternRef,
}

/// Linear memory
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Memory {
    /// Memory index
    pub index: u32,

    /// Initial size in pages (64KB each)
    pub initial: u32,

    /// Maximum size in pages (if limited)
    pub maximum: Option<u32>,

    /// Is this memory shared?
    pub shared: bool,

    /// Memory64 (64-bit addressing)
    pub memory64: bool,
}

/// Table
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Table {
    /// Table index
    pub index: u32,

    /// Element type
    pub element_type: ValueType,

    /// Initial size
    pub initial: u32,

    /// Maximum size (if limited)
    pub maximum: Option<u32>,
}

/// Global variable
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Global {
    /// Global index
    pub index: u32,

    /// Value type
    pub value_type: ValueType,

    /// Is this global mutable?
    pub mutable: bool,
}

/// Component instance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComponentInstance {
    /// Instance ID
    pub id: String,

    /// Referenced component
    pub component: String,
}

/// WIT (WebAssembly Interface Type) interface
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WITInterface {
    /// Interface name
    pub name: String,

    /// Functions in this interface
    pub functions: Vec<WITFunction>,

    /// Types defined in this interface
    pub types: Vec<WITType>,
}

/// WIT function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WITFunction {
    /// Function name
    pub name: String,

    /// Parameters
    pub params: Vec<(String, WITType)>,

    /// Results
    pub results: Vec<WITType>,
}

/// WIT types (component model types)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WITType {
    Bool,
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
    String,
    List(Box<WITType>),
    Record(Vec<(String, WITType)>),
    Variant(Vec<(String, Option<WITType>)>),
    Enum(Vec<String>),
    Option(Box<WITType>),
    Result { ok: Box<WITType>, err: Box<WITType> },
}

/// Import declaration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Import {
    /// Import name
    pub name: String,

    /// Import kind
    pub kind: ImportKind,
}

/// Import kind
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ImportKind {
    Function(FunctionSignature),
    Memory(Memory),
    Table(Table),
    Global(Global),
}

/// Export declaration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Export {
    /// Export name
    pub name: String,

    /// Export kind
    pub kind: ExportKind,
}

/// Export kind
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ExportKind {
    Function(u32),
    Memory(u32),
    Table(u32),
    Global(u32),
}

impl Component {
    /// Create a new component
    pub fn new(name: String) -> Self {
        Self {
            name,
            modules: Vec::new(),
            components: Vec::new(),
            instances: Vec::new(),
            interfaces: HashMap::new(),
            imports: Vec::new(),
            exports: Vec::new(),
        }
    }

    /// Get total number of linear memories across all modules
    pub fn total_memories(&self) -> usize {
        self.modules.iter().map(|m| m.memories.len()).sum()
    }

    /// Get total memory size required (in bytes)
    pub fn total_memory_size(&self) -> u64 {
        self.modules
            .iter()
            .flat_map(|m| &m.memories)
            .map(|mem| mem.initial as u64 * 65536) // 64KB pages
            .sum()
    }
}
