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
}
