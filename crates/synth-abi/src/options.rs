//! ABI options and configuration

/// String encoding format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringEncoding {
    /// UTF-8 encoding (most common)
    Utf8,
    /// UTF-16 encoding (for JavaScript, Java interop)
    Utf16,
    /// Latin-1 (ISO 8859-1) encoding
    Latin1,
}

impl Default for StringEncoding {
    fn default() -> Self {
        StringEncoding::Utf8
    }
}

/// Options for Canonical ABI operations
#[derive(Debug, Clone)]
pub struct AbiOptions {
    /// String encoding to use
    pub string_encoding: StringEncoding,

    /// Memory index to use (for multi-memory proposal)
    pub memory_index: u32,

    /// Whether to use realloc for allocations
    pub use_realloc: bool,
}

impl Default for AbiOptions {
    fn default() -> Self {
        Self {
            string_encoding: StringEncoding::Utf8,
            memory_index: 0,
            use_realloc: true,
        }
    }
}

impl AbiOptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_encoding(mut self, encoding: StringEncoding) -> Self {
        self.string_encoding = encoding;
        self
    }

    pub fn with_memory(mut self, index: u32) -> Self {
        self.memory_index = index;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_options() {
        let opts = AbiOptions::default();
        assert_eq!(opts.string_encoding, StringEncoding::Utf8);
        assert_eq!(opts.memory_index, 0);
        assert!(opts.use_realloc);
    }

    #[test]
    fn test_builder_pattern() {
        let opts = AbiOptions::new()
            .with_encoding(StringEncoding::Utf16)
            .with_memory(1);

        assert_eq!(opts.string_encoding, StringEncoding::Utf16);
        assert_eq!(opts.memory_index, 1);
    }
}
