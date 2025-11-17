//! Lifting: Converting core WASM values to Component Model values

use crate::{AbiError, AbiResult, AbiOptions, CoreValue, Memory, StringEncoding};
use crate::lower::ComponentValue;

/// Lift a string from memory
pub fn lift_string<M: Memory>(
    mem: &M,
    ptr: u32,
    len: u32,
    opts: &AbiOptions,
) -> AbiResult<String> {
    let data = mem.read(ptr, len as usize)?;

    match opts.string_encoding {
        StringEncoding::Utf8 => {
            String::from_utf8(data).map_err(|_| AbiError::InvalidUtf8)
        }
        StringEncoding::Utf16 => {
            if data.len() % 2 != 0 {
                return Err(AbiError::InvalidUtf16);
            }

            let utf16: Vec<u16> = data
                .chunks_exact(2)
                .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]))
                .collect();

            String::from_utf16(&utf16).map_err(|_| AbiError::InvalidUtf16)
        }
        StringEncoding::Latin1 => {
            // Latin-1 to UTF-8 conversion
            Ok(data.iter().map(|&b| b as char).collect())
        }
    }
}

/// Lift a list from memory
pub fn lift_list<M: Memory, F>(
    mem: &M,
    ptr: u32,
    len: u32,
    element_size: usize,
    lift_element: F,
) -> AbiResult<Vec<ComponentValue>>
where
    F: Fn(&M, u32) -> AbiResult<ComponentValue>,
{
    let mut result = Vec::with_capacity(len as usize);

    for i in 0..len {
        let offset = ptr + (i * element_size as u32);
        let element = lift_element(mem, offset)?;
        result.push(element);
    }

    Ok(result)
}

/// Lift a primitive value
pub fn lift_primitive(values: &[CoreValue], ty: &synth_wit::ast::Type) -> AbiResult<ComponentValue> {
    use synth_wit::ast::Type;

    if values.is_empty() {
        return Err(AbiError::Other("No values provided".to_string()));
    }

    match ty {
        Type::Bool => {
            let v = values[0].as_i32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::Bool(v != 0))
        }
        Type::S8 => {
            let v = values[0].as_i32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::S8(v as i8))
        }
        Type::U8 => {
            let v = values[0].as_i32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::U8(v as u8))
        }
        Type::S16 => {
            let v = values[0].as_i32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::S16(v as i16))
        }
        Type::U16 => {
            let v = values[0].as_i32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::U16(v as u16))
        }
        Type::S32 => {
            let v = values[0].as_i32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::S32(v))
        }
        Type::U32 => {
            let v = values[0].as_u32().ok_or(AbiError::Other("Expected i32".to_string()))?;
            Ok(ComponentValue::U32(v))
        }
        Type::S64 => {
            let v = values[0].as_i64().ok_or(AbiError::Other("Expected i64".to_string()))?;
            Ok(ComponentValue::S64(v))
        }
        Type::U64 => {
            let v = values[0].as_i64().ok_or(AbiError::Other("Expected i64".to_string()))?;
            Ok(ComponentValue::U64(v as u64))
        }
        Type::F32 => {
            let v = values[0].as_f32().ok_or(AbiError::Other("Expected f32".to_string()))?;
            Ok(ComponentValue::F32(v))
        }
        Type::F64 => {
            let v = values[0].as_f64().ok_or(AbiError::Other("Expected f64".to_string()))?;
            Ok(ComponentValue::F64(v))
        }
        _ => Err(AbiError::Other(format!("Unsupported type: {:?}", ty))),
    }
}

/// Lift a record from memory
pub fn lift_record<M: Memory>(
    mem: &M,
    data: &[u8],
    field_types: &[(String, synth_wit::ast::Type)],
    opts: &AbiOptions,
) -> AbiResult<Vec<(String, ComponentValue)>> {
    use crate::{alignment_of, align_to, size_of};
    use synth_wit::ast::Type;

    let mut result = Vec::new();
    let mut offset = 0;

    for (name, ty) in field_types {
        let align = alignment_of(ty);
        offset = align_to(offset, align);

        let value = match ty {
            Type::String => {
                // Read (ptr, len) tuple
                let ptr = u32::from_le_bytes([data[offset], data[offset + 1], data[offset + 2], data[offset + 3]]);
                let len = u32::from_le_bytes([data[offset + 4], data[offset + 5], data[offset + 6], data[offset + 7]]);
                let s = lift_string(mem, ptr, len, opts)?;
                ComponentValue::String(s)
            }
            Type::U32 => {
                let v = u32::from_le_bytes([data[offset], data[offset + 1], data[offset + 2], data[offset + 3]]);
                ComponentValue::U32(v)
            }
            Type::S32 => {
                let v = i32::from_le_bytes([data[offset], data[offset + 1], data[offset + 2], data[offset + 3]]);
                ComponentValue::S32(v)
            }
            _ => return Err(AbiError::Other(format!("Unsupported field type: {:?}", ty))),
        };

        result.push((name.clone(), value));
        offset += size_of(ty);
    }

    Ok(result)
}

/// Lift an option value from memory
pub fn lift_option<M: Memory>(
    mem: &M,
    data: &[u8],
    inner_ty: &synth_wit::ast::Type,
    opts: &AbiOptions,
) -> AbiResult<Option<Box<ComponentValue>>> {
    use crate::alignment_of;
    use synth_wit::ast::Type;

    let discriminant = data[0];

    match discriminant {
        0 => Ok(None), // None variant
        1 => {
            // Some variant
            let align = alignment_of(inner_ty);

            let value = match inner_ty {
                Type::String => {
                    let ptr = u32::from_le_bytes([data[align], data[align + 1], data[align + 2], data[align + 3]]);
                    let len = u32::from_le_bytes([data[align + 4], data[align + 5], data[align + 6], data[align + 7]]);
                    let s = lift_string(mem, ptr, len, opts)?;
                    ComponentValue::String(s)
                }
                Type::U32 => {
                    let v = u32::from_le_bytes([data[align], data[align + 1], data[align + 2], data[align + 3]]);
                    ComponentValue::U32(v)
                }
                Type::S32 => {
                    let v = i32::from_le_bytes([data[align], data[align + 1], data[align + 2], data[align + 3]]);
                    ComponentValue::S32(v)
                }
                _ => return Err(AbiError::Other(format!("Unsupported option type: {:?}", inner_ty))),
            };

            Ok(Some(Box::new(value)))
        }
        _ => Err(AbiError::InvalidDiscriminant { value: discriminant as u32 }),
    }
}

/// Lift a result value from memory
pub fn lift_result<M: Memory>(
    mem: &M,
    data: &[u8],
    ok_ty: &Option<Box<synth_wit::ast::Type>>,
    err_ty: &Option<Box<synth_wit::ast::Type>>,
    opts: &AbiOptions,
) -> AbiResult<Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>>> {
    use synth_wit::ast::Type;

    let discriminant = data[0];

    match discriminant {
        0 => {
            // Ok variant
            if let Some(ty) = ok_ty {
                let value = match ty.as_ref() {
                    Type::String => {
                        let ptr = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                        let len = u32::from_le_bytes([data[8], data[9], data[10], data[11]]);
                        let s = lift_string(mem, ptr, len, opts)?;
                        Some(Box::new(ComponentValue::String(s)))
                    }
                    Type::U32 => {
                        let v = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                        Some(Box::new(ComponentValue::U32(v)))
                    }
                    Type::S32 => {
                        let v = i32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                        Some(Box::new(ComponentValue::S32(v)))
                    }
                    _ => return Err(AbiError::Other("Unsupported ok type".to_string())),
                };
                Ok(Ok(value))
            } else {
                Ok(Ok(None))
            }
        }
        1 => {
            // Err variant
            if let Some(ty) = err_ty {
                let value = match ty.as_ref() {
                    Type::String => {
                        let ptr = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                        let len = u32::from_le_bytes([data[8], data[9], data[10], data[11]]);
                        let s = lift_string(mem, ptr, len, opts)?;
                        Some(Box::new(ComponentValue::String(s)))
                    }
                    Type::U32 => {
                        let v = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                        Some(Box::new(ComponentValue::U32(v)))
                    }
                    Type::S32 => {
                        let v = i32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                        Some(Box::new(ComponentValue::S32(v)))
                    }
                    _ => return Err(AbiError::Other("Unsupported err type".to_string())),
                };
                Ok(Err(value))
            } else {
                Ok(Err(None))
            }
        }
        _ => Err(AbiError::InvalidDiscriminant { value: discriminant as u32 }),
    }
}

/// Lift an enum value
pub fn lift_enum(discriminant: u32, cases: &[String]) -> AbiResult<ComponentValue> {
    if (discriminant as usize) < cases.len() {
        Ok(ComponentValue::Enum(cases[discriminant as usize].clone()))
    } else {
        Err(AbiError::InvalidEnumCase {
            value: discriminant,
            max: cases.len() as u32 - 1,
        })
    }
}

/// Lift a flags value (bitset)
pub fn lift_flags(bits: u32, flag_names: &[String]) -> AbiResult<ComponentValue> {
    let mut flags = Vec::new();

    for (i, flag_name) in flag_names.iter().enumerate() {
        if i >= 32 {
            break;
        }
        if (bits & (1 << i)) != 0 {
            flags.push(flag_name.clone());
        }
    }

    Ok(ComponentValue::Flags(flags))
}

/// Lift a variant value (general sum type)
pub fn lift_variant<M: Memory>(
    mem: &M,
    data: &[u8],
    cases: &[(String, Option<synth_wit::ast::Type>)],
    opts: &AbiOptions,
) -> AbiResult<ComponentValue> {
    use synth_wit::ast::Type;

    if data.len() < 4 {
        return Err(AbiError::Other("Variant data too short".to_string()));
    }

    // Read discriminant
    let discriminant = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);

    if (discriminant as usize) >= cases.len() {
        return Err(AbiError::InvalidDiscriminant { value: discriminant });
    }

    let (case_name, case_type) = &cases[discriminant as usize];

    // Read payload if present
    let payload = if let Some(ty) = case_type {
        let value = match ty {
            Type::String => {
                let ptr = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                let len = u32::from_le_bytes([data[8], data[9], data[10], data[11]]);
                let s = lift_string(mem, ptr, len, opts)?;
                ComponentValue::String(s)
            }
            Type::U32 => {
                let v = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                ComponentValue::U32(v)
            }
            Type::S32 => {
                let v = i32::from_le_bytes([data[4], data[5], data[6], data[7]]);
                ComponentValue::S32(v)
            }
            _ => return Err(AbiError::Other("Unsupported variant payload type".to_string())),
        };
        Some(Box::new(value))
    } else {
        None
    };

    Ok(ComponentValue::Variant {
        case: case_name.clone(),
        value: payload,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::SimpleMemory;
    use crate::lower::lower_string;

    #[test]
    fn test_lift_string_utf8() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        // Lower a string first
        let (ptr, len) = lower_string(&mut mem, "Hello!", &opts).unwrap();

        // Lift it back
        let s = lift_string(&mem, ptr, len, &opts).unwrap();
        assert_eq!(s, "Hello!");
    }

    #[test]
    fn test_lift_string_utf16() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::new().with_encoding(StringEncoding::Utf16);

        // Lower and lift
        let (ptr, len) = lower_string(&mut mem, "Hi👋", &opts).unwrap();
        let s = lift_string(&mem, ptr, len, &opts).unwrap();
        assert_eq!(s, "Hi👋");
    }

    #[test]
    fn test_lift_string_latin1() {
        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::new().with_encoding(StringEncoding::Latin1);

        // Lower and lift
        let (ptr, len) = lower_string(&mut mem, "café", &opts).unwrap();
        let s = lift_string(&mem, ptr, len, &opts).unwrap();
        assert_eq!(s, "café");
    }

    #[test]
    fn test_lift_primitive() {
        let values = vec![CoreValue::I32(42)];
        let val = lift_primitive(&values, &synth_wit::ast::Type::U32).unwrap();

        match val {
            ComponentValue::U32(v) => assert_eq!(v, 42),
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_roundtrip_primitives() {
        use crate::lower::lower_primitive;

        // Test i32 roundtrip
        let original = ComponentValue::S32(-123);
        let core_vals = lower_primitive(&original, &synth_wit::ast::Type::S32).unwrap();
        let lifted = lift_primitive(&core_vals, &synth_wit::ast::Type::S32).unwrap();
        assert_eq!(original, lifted);

        // Test f32 roundtrip
        let original = ComponentValue::F32(3.14);
        let core_vals = lower_primitive(&original, &synth_wit::ast::Type::F32).unwrap();
        let lifted = lift_primitive(&core_vals, &synth_wit::ast::Type::F32).unwrap();
        assert_eq!(original, lifted);
    }

    #[test]
    fn test_roundtrip_record() {
        use crate::lower::lower_record;

        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        // Lower a record
        let fields = vec![
            ("x".to_string(), ComponentValue::U32(42)),
            ("y".to_string(), ComponentValue::U32(99)),
        ];
        let field_types = vec![
            ("x".to_string(), synth_wit::ast::Type::U32),
            ("y".to_string(), synth_wit::ast::Type::U32),
        ];

        let data = lower_record(&mut mem, &fields, &field_types, &opts).unwrap();

        // Lift it back
        let lifted = lift_record(&mem, &data, &field_types, &opts).unwrap();

        assert_eq!(lifted.len(), 2);
        assert_eq!(lifted[0].0, "x");
        assert_eq!(lifted[0].1, ComponentValue::U32(42));
        assert_eq!(lifted[1].0, "y");
        assert_eq!(lifted[1].1, ComponentValue::U32(99));
    }

    #[test]
    fn test_roundtrip_option() {
        use crate::lower::lower_option;

        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        // Test None
        let value: Option<Box<ComponentValue>> = None;
        let data = lower_option(&mut mem, &value, &synth_wit::ast::Type::U32, &opts).unwrap();
        let lifted = lift_option(&mem, &data, &synth_wit::ast::Type::U32, &opts).unwrap();
        assert_eq!(lifted, None);

        // Test Some
        let value = Some(Box::new(ComponentValue::U32(123)));
        let data = lower_option(&mut mem, &value, &synth_wit::ast::Type::U32, &opts).unwrap();
        let lifted = lift_option(&mem, &data, &synth_wit::ast::Type::U32, &opts).unwrap();
        assert_eq!(lifted, Some(Box::new(ComponentValue::U32(123))));
    }

    #[test]
    fn test_roundtrip_result() {
        use crate::lower::lower_result;

        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let ok_ty = Some(Box::new(synth_wit::ast::Type::U32));
        let err_ty = Some(Box::new(synth_wit::ast::Type::U32));

        // Test Ok
        let value: Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>> =
            Ok(Some(Box::new(ComponentValue::U32(200))));
        let data = lower_result(&mut mem, &value, &ok_ty, &err_ty, &opts).unwrap();
        let lifted = lift_result(&mem, &data, &ok_ty, &err_ty, &opts).unwrap();
        assert!(lifted.is_ok());
        assert_eq!(lifted.unwrap(), Some(Box::new(ComponentValue::U32(200))));

        // Test Err
        let value: Result<Option<Box<ComponentValue>>, Option<Box<ComponentValue>>> =
            Err(Some(Box::new(ComponentValue::U32(404))));
        let data = lower_result(&mut mem, &value, &ok_ty, &err_ty, &opts).unwrap();
        let lifted = lift_result(&mem, &data, &ok_ty, &err_ty, &opts).unwrap();
        assert!(lifted.is_err());
        assert_eq!(lifted.unwrap_err(), Some(Box::new(ComponentValue::U32(404))));
    }

    #[test]
    fn test_roundtrip_enum() {
        use crate::lower::lower_enum;

        let cases = vec![
            "red".to_string(),
            "green".to_string(),
            "blue".to_string(),
        ];

        // Lower
        let value = ComponentValue::Enum("blue".to_string());
        let discriminant = lower_enum(&value, &cases).unwrap();
        assert_eq!(discriminant, 2);

        // Lift
        let lifted = lift_enum(discriminant, &cases).unwrap();
        assert_eq!(lifted, value);
    }

    #[test]
    fn test_roundtrip_flags() {
        use crate::lower::lower_flags;

        let flag_names = vec![
            "read".to_string(),
            "write".to_string(),
            "execute".to_string(),
        ];

        // Lower
        let value = ComponentValue::Flags(vec!["read".to_string(), "execute".to_string()]);
        let bits = lower_flags(&value, &flag_names).unwrap();

        // Lift
        let lifted = lift_flags(bits, &flag_names).unwrap();
        assert_eq!(lifted, value);
    }

    #[test]
    fn test_roundtrip_variant() {
        use crate::lower::lower_variant;

        let mut mem = SimpleMemory::new(1024);
        let opts = AbiOptions::default();

        let cases = vec![
            ("none".to_string(), None),
            ("some".to_string(), Some(synth_wit::ast::Type::U32)),
        ];

        // Test variant with payload
        let value = ComponentValue::Variant {
            case: "some".to_string(),
            value: Some(Box::new(ComponentValue::U32(123))),
        };

        let data = lower_variant(&mut mem, &value, &cases, &opts).unwrap();
        let lifted = lift_variant(&mem, &data, &cases, &opts).unwrap();

        match lifted {
            ComponentValue::Variant { case, value: payload } => {
                assert_eq!(case, "some");
                assert_eq!(*payload.unwrap(), ComponentValue::U32(123));
            }
            _ => panic!("Expected variant"),
        }

        // Test variant without payload
        let value = ComponentValue::Variant {
            case: "none".to_string(),
            value: None,
        };

        let data = lower_variant(&mut mem, &value, &cases, &opts).unwrap();
        let lifted = lift_variant(&mem, &data, &cases, &opts).unwrap();

        match lifted {
            ComponentValue::Variant { case, value: payload } => {
                assert_eq!(case, "none");
                assert!(payload.is_none());
            }
            _ => panic!("Expected variant"),
        }
    }
}
