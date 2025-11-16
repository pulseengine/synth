//! Error types for Synth

/// Result type for Synth operations
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during synthesis
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Component parsing failed
    #[error("Failed to parse component: {0}")]
    ParseError(String),

    /// Component validation failed
    #[error("Component validation failed: {0}")]
    ValidationError(String),

    /// Synthesis failed
    #[error("Synthesis failed: {0}")]
    SynthesisError(String),

    /// Target not supported
    #[error("Target not supported: {0}")]
    UnsupportedTarget(String),

    /// Memory layout error
    #[error("Memory layout error: {0}")]
    MemoryLayoutError(String),

    /// MPU/PMP configuration error
    #[error("Hardware protection error: {0}")]
    HardwareProtectionError(String),

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// Other errors
    #[error("{0}")]
    Other(String),
}

impl Error {
    /// Create a parse error
    pub fn parse<S: Into<String>>(msg: S) -> Self {
        Error::ParseError(msg.into())
    }

    /// Create a validation error
    pub fn validation<S: Into<String>>(msg: S) -> Self {
        Error::ValidationError(msg.into())
    }

    /// Create a synthesis error
    pub fn synthesis<S: Into<String>>(msg: S) -> Self {
        Error::SynthesisError(msg.into())
    }
}
