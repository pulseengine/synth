//! Canonical ABI for WebAssembly Component Model
//!
//! This crate implements the Canonical ABI specification for lowering and lifting
//! values between the Component Model's high-level types and core WebAssembly types.
//!
//! The Canonical ABI defines how to:
//! - **Lower**: Convert high-level Component Model values to core WASM values
//! - **Lift**: Convert core WASM values back to high-level Component Model values
//!
//! ## Memory Management
//!
//! The ABI uses a linear memory model with:
//! - `memory`: The linear memory to allocate from
//! - `realloc`: Function for memory allocation/reallocation
//! - `free`: Function for memory deallocation (optional)
//!
//! ## String Encodings
//!
//! Strings can be encoded in multiple formats:
//! - UTF-8 (most common)
//! - UTF-16 (for interop with JavaScript, Java)
//! - Latin-1 (compact ASCII-compatible encoding)
//!
//! ## References
//!
//! - [Component Model Canonical ABI](https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md)
//! - [WIT Specification](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md)

pub mod lower;
pub mod lift;
pub mod memory;
pub mod options;

pub use lower::*;
pub use lift::*;
pub use memory::*;
pub use options::*;

use synth_wit::ast::Type;

/// Result type for ABI operations
pub type AbiResult<T> = Result<T, AbiError>;

/// Errors that can occur during ABI operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiError {
    /// Out of memory during allocation
    OutOfMemory,

    /// Invalid UTF-8 sequence
    InvalidUtf8,

    /// Invalid UTF-16 sequence
    InvalidUtf16,

    /// Invalid alignment for type
    InvalidAlignment { expected: usize, actual: usize },

    /// Invalid discriminant value for variant
    InvalidDiscriminant { value: u32 },

    /// Invalid enum case value
    InvalidEnumCase { value: u32, max: u32 },

    /// Invalid flags value (bit set outside valid range)
    InvalidFlags { value: u32, max_bits: u32 },

    /// Trap occurred during operation
    Trap(String),

    /// Generic error
    Other(String),
}

impl std::fmt::Display for AbiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbiError::OutOfMemory => write!(f, "Out of memory"),
            AbiError::InvalidUtf8 => write!(f, "Invalid UTF-8 sequence"),
            AbiError::InvalidUtf16 => write!(f, "Invalid UTF-16 sequence"),
            AbiError::InvalidAlignment { expected, actual } => {
                write!(f, "Invalid alignment: expected {}, got {}", expected, actual)
            }
            AbiError::InvalidDiscriminant { value } => {
                write!(f, "Invalid discriminant value: {}", value)
            }
            AbiError::InvalidEnumCase { value, max } => {
                write!(f, "Invalid enum case: {} (max: {})", value, max)
            }
            AbiError::InvalidFlags { value, max_bits } => {
                write!(f, "Invalid flags: 0x{:x} (max bits: {})", value, max_bits)
            }
            AbiError::Trap(msg) => write!(f, "Trap: {}", msg),
            AbiError::Other(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for AbiError {}

/// Core value representation for lowering
#[derive(Debug, Clone, PartialEq)]
pub enum CoreValue {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
}

impl CoreValue {
    pub fn as_i32(&self) -> Option<i32> {
        match self {
            CoreValue::I32(v) => Some(*v),
            _ => None,
        }
    }

    pub fn as_u32(&self) -> Option<u32> {
        match self {
            CoreValue::I32(v) => Some(*v as u32),
            _ => None,
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        match self {
            CoreValue::I64(v) => Some(*v),
            _ => None,
        }
    }

    pub fn as_f32(&self) -> Option<f32> {
        match self {
            CoreValue::F32(v) => Some(*v),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            CoreValue::F64(v) => Some(*v),
            _ => None,
        }
    }
}

/// Calculate alignment for a WIT type
pub fn alignment_of(ty: &Type) -> usize {
    match ty {
        Type::Bool | Type::S8 | Type::U8 => 1,
        Type::S16 | Type::U16 => 2,
        Type::S32 | Type::U32 | Type::F32 | Type::Char => 4,
        Type::S64 | Type::U64 | Type::F64 => 8,
        Type::String | Type::List(_) => 4, // ptr + len
        Type::Option(inner) => alignment_of(inner).max(1), // discriminant + payload
        Type::Result { ok, err } => {
            let ok_align = ok.as_ref().map(|t| alignment_of(t)).unwrap_or(1);
            let err_align = err.as_ref().map(|t| alignment_of(t)).unwrap_or(1);
            ok_align.max(err_align).max(1)
        }
        Type::Tuple(types) => {
            types.iter().map(alignment_of).max().unwrap_or(1)
        }
        Type::Named(_) | Type::Generic(_) => 4, // Default to word alignment
    }
}

/// Calculate size of a WIT type
pub fn size_of(ty: &Type) -> usize {
    match ty {
        Type::Bool | Type::S8 | Type::U8 => 1,
        Type::S16 | Type::U16 => 2,
        Type::S32 | Type::U32 | Type::F32 | Type::Char => 4,
        Type::S64 | Type::U64 | Type::F64 => 8,
        Type::String | Type::List(_) => 8, // ptr (4 bytes) + len (4 bytes)
        Type::Option(inner) => {
            let inner_size = size_of(inner);
            let align = alignment_of(inner);
            // Round up inner size to alignment, then add discriminant
            ((inner_size + align - 1) / align) * align + align_to(1, align)
        }
        Type::Result { ok, err } => {
            let ok_size = ok.as_ref().map(|t| size_of(t)).unwrap_or(0);
            let err_size = err.as_ref().map(|t| size_of(t)).unwrap_or(0);
            let payload_size = ok_size.max(err_size);
            let align = alignment_of(ty);
            // Discriminant + aligned payload
            align + align_to(payload_size, align)
        }
        Type::Tuple(types) => {
            let mut offset = 0;
            for t in types {
                offset = align_to(offset, alignment_of(t));
                offset += size_of(t);
            }
            align_to(offset, alignment_of(ty))
        }
        Type::Named(_) | Type::Generic(_) => 4, // Default
    }
}

/// Align an offset to the specified alignment
pub fn align_to(offset: usize, alignment: usize) -> usize {
    (offset + alignment - 1) / alignment * alignment
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alignment_primitives() {
        assert_eq!(alignment_of(&Type::U8), 1);
        assert_eq!(alignment_of(&Type::U16), 2);
        assert_eq!(alignment_of(&Type::U32), 4);
        assert_eq!(alignment_of(&Type::U64), 8);
        assert_eq!(alignment_of(&Type::F32), 4);
        assert_eq!(alignment_of(&Type::F64), 8);
        assert_eq!(alignment_of(&Type::Bool), 1);
    }

    #[test]
    fn test_size_primitives() {
        assert_eq!(size_of(&Type::U8), 1);
        assert_eq!(size_of(&Type::U16), 2);
        assert_eq!(size_of(&Type::U32), 4);
        assert_eq!(size_of(&Type::U64), 8);
        assert_eq!(size_of(&Type::F32), 4);
        assert_eq!(size_of(&Type::F64), 8);
        assert_eq!(size_of(&Type::Bool), 1);
    }

    #[test]
    fn test_size_string() {
        // String is (ptr, len) = 8 bytes
        assert_eq!(size_of(&Type::String), 8);
    }

    #[test]
    fn test_size_list() {
        // List is (ptr, len) = 8 bytes regardless of element type
        let list_u8 = Type::List(Box::new(Type::U8));
        let list_u32 = Type::List(Box::new(Type::U32));
        assert_eq!(size_of(&list_u8), 8);
        assert_eq!(size_of(&list_u32), 8);
    }

    #[test]
    fn test_align_to() {
        assert_eq!(align_to(0, 4), 0);
        assert_eq!(align_to(1, 4), 4);
        assert_eq!(align_to(4, 4), 4);
        assert_eq!(align_to(5, 4), 8);
        assert_eq!(align_to(7, 8), 8);
        assert_eq!(align_to(9, 8), 16);
    }

    #[test]
    fn test_core_value_accessors() {
        let v1 = CoreValue::I32(42);
        assert_eq!(v1.as_i32(), Some(42));
        assert_eq!(v1.as_u32(), Some(42u32));
        assert_eq!(v1.as_i64(), None);

        let v2 = CoreValue::F32(3.14);
        assert_eq!(v2.as_f32(), Some(3.14));
        assert_eq!(v2.as_i32(), None);
    }
}
