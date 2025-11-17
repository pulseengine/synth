//! Lowering: Converting Component Model values to core WASM values

use crate::{AbiError, AbiResult, AbiOptions, CoreValue, Memory, StringEncoding};
use synth_wit::ast::Type;

/// Lower a string to memory
pub fn lower_string<M: Memory>(
    mem: &mut M,
    s: &str,
    opts: &AbiOptions,
) -> AbiResult<(u32, u32)> {
    let (data, byte_len) = match opts.string_encoding {
        StringEncoding::Utf8 => {
            let bytes = s.as_bytes();
            (bytes.to_vec(), bytes.len())
        }
        StringEncoding::Utf16 => {
            let utf16: Vec<u16> = s.encode_utf16().collect();
            let bytes: Vec<u8> = utf16
                .iter()
                .flat_map(|&c| c.to_le_bytes())
                .collect();
            let len = bytes.len();
            (bytes, len)
        }
        StringEncoding::Latin1 => {
            // Convert to Latin-1, replacing non-Latin-1 chars with '?'
            let bytes: Vec<u8> = s
                .chars()
                .map(|c| {
                    let code = c as u32;
                    if code <= 0xFF {
                        code as u8
                    } else {
                        b'?'
                    }
                })
                .collect();
            let len = bytes.len();
            (bytes, len)
        }
    };

    // Allocate memory for the string
    let ptr = mem.allocate(byte_len, 1)?;

    // Write the string data
    mem.write(ptr, &data)?;

    // Return (ptr, len)
    Ok((ptr, byte_len as u32))
}

/// Lower a list to memory
pub fn lower_list<M: Memory>(
    mem: &mut M,
    elements: &[Vec<u8>],
    element_size: usize,
    element_align: usize,
) -> AbiResult<(u32, u32)> {
    let total_size = elements.len() * element_size;

    // Allocate memory for the list
    let ptr = mem.allocate(total_size, element_align)?;

    // Write each element
    for (i, elem) in elements.iter().enumerate() {
        let offset = ptr + (i * element_size) as u32;
        mem.write(offset, elem)?;
    }

    // Return (ptr, len)
    Ok((ptr, elements.len() as u32))
}

/// Lower a primitive value
pub fn lower_primitive(value: &ComponentValue, ty: &Type) -> AbiResult<Vec<CoreValue>> {
    match (value, ty) {
        (ComponentValue::Bool(b), Type::Bool) => Ok(vec![CoreValue::I32(*b as i32)]),
        (ComponentValue::S8(v), Type::S8) => Ok(vec![CoreValue::I32(*v as i32)]),
        (ComponentValue::U8(v), Type::U8) => Ok(vec![CoreValue::I32(*v as i32)]),
        (ComponentValue::S16(v), Type::S16) => Ok(vec![CoreValue::I32(*v as i32)]),
        (ComponentValue::U16(v), Type::U16) => Ok(vec![CoreValue::I32(*v as i32)]),
        (ComponentValue::S32(v), Type::S32) => Ok(vec![CoreValue::I32(*v)]),
        (ComponentValue::U32(v), Type::U32) => Ok(vec![CoreValue::I32(*v as i32)]),
        (ComponentValue::S64(v), Type::S64) => Ok(vec![CoreValue::I64(*v)]),
        (ComponentValue::U64(v), Type::U64) => Ok(vec![CoreValue::I64(*v as i64)]),
        (ComponentValue::F32(v), Type::F32) => Ok(vec![CoreValue::F32(*v)]),
        (ComponentValue::F64(v), Type::F64) => Ok(vec![CoreValue::F64(*v)]),
        _ => Err(AbiError::Other("Type mismatch".to_string())),
    }
}

/// Component Model value representation
#[derive(Debug, Clone, PartialEq)]
pub enum ComponentValue {
    Bool(bool),
    S8(i8),
    U8(u8),
    S16(i16),
    U16(u16),
    S32(i32),
    U32(u32),
    S64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    Char(char),
    String(String),
    List(Vec<ComponentValue>),
    Record(Vec<(String, ComponentValue)>),
    Variant { case: String, value: Option<Box<ComponentValue>> },
    Enum(String),
    Option(Option<Box<ComponentValue>>),
    Result(Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>>),
    Flags(Vec<String>),
}

/// Lower a record to memory
pub fn lower_record<M: Memory>(
    mem: &mut M,
    fields: &[(String, ComponentValue)],
    field_types: &[(String, Type)],
    opts: &AbiOptions,
) -> AbiResult<Vec<u8>> {
    use crate::{alignment_of, align_to, size_of};

    // Calculate total size needed
    let mut offset = 0;
    let mut max_align = 1;

    for (_, ty) in field_types {
        let align = alignment_of(ty);
        max_align = max_align.max(align);
        offset = align_to(offset, align);
        offset += size_of(ty);
    }

    // Round up to overall alignment
    let total_size = align_to(offset, max_align);
    let mut result = vec![0u8; total_size];

    // Lower each field
    offset = 0;
    for (i, (name, value)) in fields.iter().enumerate() {
        let (_, ty) = &field_types[i];
        let align = alignment_of(ty);
        offset = align_to(offset, align);

        // Lower the field value based on type
        match (value, ty) {
            (ComponentValue::String(s), Type::String) => {
                let (ptr, len) = lower_string(mem, s, opts)?;
                // Write (ptr, len) tuple
                result[offset..offset + 4].copy_from_slice(&ptr.to_le_bytes());
                result[offset + 4..offset + 8].copy_from_slice(&len.to_le_bytes());
            }
            _ => {
                // For primitives, lower and write
                let core_vals = lower_primitive(value, ty)?;
                if let Some(CoreValue::I32(v)) = core_vals.first() {
                    result[offset..offset + 4].copy_from_slice(&v.to_le_bytes());
                }
            }
        }

        offset += size_of(ty);
    }

    Ok(result)
}

/// Lower an option value
pub fn lower_option<M: Memory>(
    mem: &mut M,
    value: &Option<Box<ComponentValue>>,
    inner_ty: &Type,
    opts: &AbiOptions,
) -> AbiResult<Vec<u8>> {
    use crate::{alignment_of, size_of};

    match value {
        None => {
            // Discriminant = 0, no payload
            let size = 1 + size_of(inner_ty);
            let mut result = vec![0u8; size];
            result[0] = 0; // None
            Ok(result)
        }
        Some(val) => {
            // Discriminant = 1, followed by value
            let align = alignment_of(inner_ty);
            let value_size = size_of(inner_ty);
            let total_size = align + value_size;
            let mut result = vec![0u8; total_size];
            result[0] = 1; // Some

            // Lower the inner value
            match (val.as_ref(), inner_ty) {
                (ComponentValue::String(s), Type::String) => {
                    let (ptr, len) = lower_string(mem, s, opts)?;
                    result[align..align + 4].copy_from_slice(&ptr.to_le_bytes());
                    result[align + 4..align + 8].copy_from_slice(&len.to_le_bytes());
                }
                _ => {
                    let core_vals = lower_primitive(val, inner_ty)?;
                    if let Some(CoreValue::I32(v)) = core_vals.first() {
                        result[align..align + 4].copy_from_slice(&v.to_le_bytes());
                    }
                }
            }

            Ok(result)
        }
    }
}

/// Lower a result value
pub fn lower_result<M: Memory>(
    mem: &mut M,
    value: &Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>>,
    ok_ty: &Option<Box<Type>>,
    err_ty: &Option<Box<Type>>,
    opts: &AbiOptions,
) -> AbiResult<Vec<u8>> {
    use crate::{alignment_of, size_of};

    match value {
        Ok(ok_val) => {
            // Discriminant = 0 for Ok
            let ok_size = ok_ty.as_ref().map(|t| size_of(t)).unwrap_or(0);
            let err_size = err_ty.as_ref().map(|t| size_of(t)).unwrap_or(0);
            let payload_size = ok_size.max(err_size);
            let total_size = 4 + payload_size; // 4 bytes for discriminant

            let mut result = vec![0u8; total_size];
            result[0] = 0; // Ok variant

            // Lower ok value if present
            if let (Some(val), Some(ty)) = (ok_val, ok_ty) {
                match (val.as_ref(), ty.as_ref()) {
                    (ComponentValue::String(s), Type::String) => {
                        let (ptr, len) = lower_string(mem, s, opts)?;
                        result[4..8].copy_from_slice(&ptr.to_le_bytes());
                        result[8..12].copy_from_slice(&len.to_le_bytes());
                    }
                    _ => {
                        let core_vals = lower_primitive(val, ty)?;
                        if let Some(CoreValue::I32(v)) = core_vals.first() {
                            result[4..8].copy_from_slice(&v.to_le_bytes());
                        }
                    }
                }
            }

            Ok(result)
        }
        Err(err_val) => {
            // Discriminant = 1 for Err
            let ok_size = ok_ty.as_ref().map(|t| size_of(t)).unwrap_or(0);
            let err_size = err_ty.as_ref().map(|t| size_of(t)).unwrap_or(0);
            let payload_size = ok_size.max(err_size);
            let total_size = 4 + payload_size;

            let mut result = vec![0u8; total_size];
            result[0] = 1; // Err variant

            // Lower err value if present
            if let (Some(val), Some(ty)) = (err_val, err_ty) {
                match (val.as_ref(), ty.as_ref()) {
                    (ComponentValue::String(s), Type::String) => {
                        let (ptr, len) = lower_string(mem, s, opts)?;
                        result[4..8].copy_from_slice(&ptr.to_le_bytes());
                        result[8..12].copy_from_slice(&len.to_le_bytes());
                    }
                    _ => {
                        let core_vals = lower_primitive(val, ty)?;
                        if let Some(CoreValue::I32(v)) = core_vals.first() {
                            result[4..8].copy_from_slice(&v.to_le_bytes());
                        }
                    }
                }
            }

            Ok(result)
        }
    }
}

/// Lower an enum value
pub fn lower_enum(value: &ComponentValue, cases: &[String]) -> AbiResult<u32> {
    match value {
        ComponentValue::Enum(case_name) => {
            // Find the case index
            for (i, case) in cases.iter().enumerate() {
                if case == case_name {
                    return Ok(i as u32);
                }
            }
            Err(AbiError::Other(format!("Unknown enum case: {}", case_name)))
        }
        _ => Err(AbiError::Other("Expected enum value".to_string())),
    }
}

/// Lower a flags value (bitset)
pub fn lower_flags(value: &ComponentValue, flag_names: &[String]) -> AbiResult<u32> {
    match value {
        ComponentValue::Flags(flags) => {
            let mut bits = 0u32;

            for flag in flags {
                // Find the flag index
                let mut found = false;
                for (i, flag_name) in flag_names.iter().enumerate() {
                    if flag_name == flag {
                        if i >= 32 {
                            return Err(AbiError::InvalidFlags {
                                value: bits,
                                max_bits: 32,
                            });
                        }
                        bits |= 1 << i;
                        found = true;
                        break;
                    }
                }

                if !found {
                    return Err(AbiError::Other(format!("Unknown flag: {}", flag)));
                }
            }

            Ok(bits)
        }
        _ => Err(AbiError::Other("Expected flags value".to_string())),
    }
}

/// Lower a variant value (general sum type)
pub fn lower_variant<M: Memory>(
    mem: &mut M,
    value: &ComponentValue,
    cases: &[(String, Option<Type>)],
    opts: &AbiOptions,
) -> AbiResult<Vec<u8>> {
    use crate::{alignment_of, size_of};

    match value {
        ComponentValue::Variant { case, value: payload } => {
            // Find the case index
            let mut case_index = None;
            let mut case_type = None;

            for (i, (case_name, ty)) in cases.iter().enumerate() {
                if case_name == case {
                    case_index = Some(i);
                    case_type = ty.clone();
                    break;
                }
            }

            let case_index = case_index.ok_or_else(|| {
                AbiError::Other(format!("Unknown variant case: {}", case))
            })?;

            // Calculate max payload size
            let max_payload_size = cases
                .iter()
                .map(|(_, ty)| ty.as_ref().map(size_of).unwrap_or(0))
                .max()
                .unwrap_or(0);

            // Discriminant (4 bytes) + max payload size
            let total_size = 4 + max_payload_size;
            let mut result = vec![0u8; total_size];

            // Write discriminant
            result[0..4].copy_from_slice(&(case_index as u32).to_le_bytes());

            // Write payload if present
            if let (Some(payload_value), Some(ty)) = (payload, case_type) {
                match (payload_value.as_ref(), &ty) {
                    (ComponentValue::String(s), Type::String) => {
                        let (ptr, len) = lower_string(mem, s, opts)?;
                        result[4..8].copy_from_slice(&ptr.to_le_bytes());
                        result[8..12].copy_from_slice(&len.to_le_bytes());
                    }
                    _ => {
                        let core_vals = lower_primitive(payload_value, &ty)?;
                        if let Some(CoreValue::I32(v)) = core_vals.first() {
                            result[4..8].copy_from_slice(&v.to_le_bytes());
                        }
                    }
                }
            }

            Ok(result)
        }
        _ => Err(AbiError::Other("Expected variant value".to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::SimpleMemory;

    #[test]
    fn test_lower_string_utf8() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default(); // UTF-8

        let (ptr, len) = lower_string(&mut mem, "Hello, World!", &opts).unwrap();

        // Read back the string
        let data = mem.read(ptr, len as usize).unwrap();
        assert_eq!(&data, b"Hello, World!");
        assert_eq!(len, 13);
    }

    #[test]
    fn test_lower_string_utf16() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::new().with_encoding(StringEncoding::Utf16);

        let (ptr, len) = lower_string(&mut mem, "Hi", &opts).unwrap();

        // Read back and verify it's UTF-16 LE
        let data = mem.read(ptr, len as usize).unwrap();
        assert_eq!(len, 4); // 2 chars * 2 bytes each

        // "H" = 0x0048, "i" = 0x0069 in UTF-16
        assert_eq!(&data, &[0x48, 0x00, 0x69, 0x00]);
    }

    #[test]
    fn test_lower_string_latin1() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::new().with_encoding(StringEncoding::Latin1);

        let (ptr, len) = lower_string(&mut mem, "café", &opts).unwrap();

        let data = mem.read(ptr, len as usize).unwrap();
        // "café" in Latin-1: c=0x63, a=0x61, f=0x66, é=0xE9
        assert_eq!(&data, &[0x63, 0x61, 0x66, 0xE9]);
    }

    #[test]
    fn test_lower_primitive() {
        let val = ComponentValue::U32(42);
        let core_vals = lower_primitive(&val, &Type::U32).unwrap();

        assert_eq!(core_vals.len(), 1);
        assert_eq!(core_vals[0].as_u32(), Some(42));
    }

    #[test]
    fn test_lower_list() {
        let mut mem = SimpleMemory::new(1024);

        // Lower a list of 3 u32 values
        let elements = vec![
            vec![1, 0, 0, 0],  // 1 as little-endian u32
            vec![2, 0, 0, 0],  // 2
            vec![3, 0, 0, 0],  // 3
        ];

        let (ptr, len) = lower_list(&mut mem, &elements, 4, 4).unwrap();

        assert_eq!(len, 3);

        // Read back the values
        let val1 = mem.read_u32(ptr).unwrap();
        let val2 = mem.read_u32(ptr + 4).unwrap();
        let val3 = mem.read_u32(ptr + 8).unwrap();

        assert_eq!(val1, 1);
        assert_eq!(val2, 2);
        assert_eq!(val3, 3);
    }

    #[test]
    fn test_lower_record() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        // Create a simple record with two fields: x: u32, y: u32
        let fields = vec![
            ("x".to_string(), ComponentValue::U32(10)),
            ("y".to_string(), ComponentValue::U32(20)),
        ];
        let field_types = vec![
            ("x".to_string(), Type::U32),
            ("y".to_string(), Type::U32),
        ];

        let data = lower_record(&mut mem, &fields, &field_types, &opts).unwrap();

        // Should be 8 bytes: 4 for x, 4 for y
        assert_eq!(data.len(), 8);

        // Check values (little-endian)
        let x = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        let y = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);

        assert_eq!(x, 10);
        assert_eq!(y, 20);
    }

    #[test]
    fn test_lower_option_none() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let value: Option<Box<ComponentValue>> = None;
        let data = lower_option(&mut mem, &value, &Type::U32, &opts).unwrap();

        // Discriminant = 0 for None
        assert_eq!(data[0], 0);
    }

    #[test]
    fn test_lower_option_some() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let value = Some(Box::new(ComponentValue::U32(42)));
        let data = lower_option(&mut mem, &value, &Type::U32, &opts).unwrap();

        // Discriminant = 1 for Some
        assert_eq!(data[0], 1);

        // Value should be at offset 4 (aligned)
        let v = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
        assert_eq!(v, 42);
    }

    #[test]
    fn test_lower_result_ok() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let value: Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>> =
            Ok(Some(Box::new(ComponentValue::U32(100))));

        let ok_ty = Some(Box::new(Type::U32));
        let err_ty = Some(Box::new(Type::String));

        let data = lower_result(&mut mem, &value, &ok_ty, &err_ty, &opts).unwrap();

        // Discriminant = 0 for Ok
        assert_eq!(data[0], 0);

        // Value at offset 4
        let v = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
        assert_eq!(v, 100);
    }

    #[test]
    fn test_lower_result_err() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let value: Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>> =
            Err(Some(Box::new(ComponentValue::U32(404))));

        let ok_ty = Some(Box::new(Type::U32));
        let err_ty = Some(Box::new(Type::U32));

        let data = lower_result(&mut mem, &value, &ok_ty, &err_ty, &opts).unwrap();

        // Discriminant = 1 for Err
        assert_eq!(data[0], 1);

        // Value at offset 4
        let v = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
        assert_eq!(v, 404);
    }

    #[test]
    fn test_lower_enum() {
        let cases = vec![
            "red".to_string(),
            "green".to_string(),
            "blue".to_string(),
        ];

        let value = ComponentValue::Enum("green".to_string());
        let discriminant = lower_enum(&value, &cases).unwrap();

        assert_eq!(discriminant, 1); // green is index 1
    }

    #[test]
    fn test_lower_enum_unknown_case() {
        let cases = vec!["red".to_string(), "green".to_string()];
        let value = ComponentValue::Enum("purple".to_string());
        let result = lower_enum(&value, &cases);

        assert!(result.is_err());
    }

    #[test]
    fn test_lower_flags() {
        let flag_names = vec![
            "read".to_string(),
            "write".to_string(),
            "execute".to_string(),
        ];

        // Set read and execute flags
        let value = ComponentValue::Flags(vec!["read".to_string(), "execute".to_string()]);
        let bits = lower_flags(&value, &flag_names).unwrap();

        // Bits 0 and 2 should be set
        assert_eq!(bits, 0b101); // 5
    }

    #[test]
    fn test_lower_flags_empty() {
        let flag_names = vec!["read".to_string(), "write".to_string()];
        let value = ComponentValue::Flags(vec![]);
        let bits = lower_flags(&value, &flag_names).unwrap();

        assert_eq!(bits, 0);
    }

    #[test]
    fn test_lower_variant_without_payload() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let cases = vec![
            ("none".to_string(), None),
            ("some".to_string(), Some(Type::U32)),
        ];

        let value = ComponentValue::Variant {
            case: "none".to_string(),
            value: None,
        };

        let data = lower_variant(&mut mem, &value, &cases, &opts).unwrap();

        // Discriminant should be 0 (first case)
        let discriminant = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        assert_eq!(discriminant, 0);
    }

    #[test]
    fn test_lower_variant_with_payload() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let cases = vec![
            ("none".to_string(), None),
            ("some".to_string(), Some(Type::U32)),
        ];

        let value = ComponentValue::Variant {
            case: "some".to_string(),
            value: Some(Box::new(ComponentValue::U32(42))),
        };

        let data = lower_variant(&mut mem, &value, &cases, &opts).unwrap();

        // Discriminant should be 1 (second case)
        let discriminant = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        assert_eq!(discriminant, 1);

        // Payload at offset 4
        let payload = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
        assert_eq!(payload, 42);
    }
}
