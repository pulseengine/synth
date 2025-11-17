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
}
