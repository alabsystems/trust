//! Immutable inputs for the native paired qualification runner.
//!
//! An inspected pair is deliberately not an execution or proof capability.
//! The native receipt stage consumes the inspected owner and checks receipt
//! consistency and listed bytes. Actual compiler probes, dependency resolution,
//! admission, measurements and identity-aware comparisons remain later stages.
//! Persistent drift is detected before another stage may consume this snapshot;
//! this is not an OS snapshot or protection against restored-between-read edits.

use std::fmt;
use std::path::Path;

pub mod census;
pub mod dependencies;
pub mod improvement;
pub mod pair;
pub mod probes;
pub mod receipts;
pub mod seal;
pub mod source;
mod tree;
pub mod workloads;
#[cfg(feature = "native-repository")]
pub mod repository_source;

#[derive(Debug)]
pub struct Refusal(pub String);

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Refusal {}

impl From<std::io::Error> for Refusal {
    fn from(value: std::io::Error) -> Self {
        Self(value.to_string())
    }
}

pub type Result<T> = std::result::Result<T, Refusal>;

/// Git is an observational reader, not source authority. Every tracked file is
/// also hashed against its Git object ID. The host must provide its controlled,
/// bounded system-Git runner, never a PATH-selected or ambient-GIT_* command.
pub trait Git {
    fn probe(&self, root: &Path, args: &[&str]) -> Result<Vec<u8>>;
    fn validate_repository(&self, root: &Path) -> Result<()>;
}

pub(crate) fn refusal(message: impl Into<String>) -> Refusal {
    Refusal(message.into())
}

pub(crate) fn canonical_hex(value: &str, length: usize) -> bool {
    value.len() == length && value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

#[cfg(test)]
mod tests;
