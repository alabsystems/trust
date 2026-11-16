//! Checked receipt observations, never proof or build-writer authority.
//!
//! A stage receipt binds listed executable bytes and states build provenance.
//! A complete seal, actual compiler probes and source/build custody are separate
//! predicates. No public type here grants execution, release or proof standing.

use std::fmt;
use std::path::Path;

use trust_sha2::{Digest as _, Sha256};
pub use value::{Number, Object, Value};

mod candidate;
mod files;
pub mod inventory;
mod json;
pub mod llvm;
mod record;
mod regular_file;
mod value;
pub use candidate::CandidateReceipt;
pub use record::{invocation_errors, quoted_arguments};
pub use regular_file::read_required_regular_file;

pub const RECEIPT_NAME: &str = "tool-provenance.json";
pub const RECEIPT_SCHEMA: &str = "trust.stage-tool-provenance.v2";
pub const MAX_RECEIPT_BYTES: u64 = 16 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal(pub String);

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Refusal {}
impl From<std::io::Error> for Refusal {
    fn from(error: std::io::Error) -> Self {
        Self(error.to_string())
    }
}
pub type Result<T> = std::result::Result<T, Refusal>;

/// The receipt is optional for a plain x.py stage. Present malformed or rejected
/// records refuse; absence never becomes a completed candidate receipt.
#[derive(Debug)]
pub enum StageReceipt {
    Absent,
    Checked(CheckedReceipt),
}

/// Fields are private and there is no deserializer. This is an observation of
/// the listed files, not an immutable snapshot or authentication of the writer.
#[derive(Debug)]
pub struct CheckedReceipt {
    raw_sha256: String,
    data: Value,
    lines: Vec<String>,
    files_verified: usize,
}

impl CheckedReceipt {
    pub fn raw_sha256(&self) -> &str {
        &self.raw_sha256
    }
    pub fn data(&self) -> &Value {
        &self.data
    }
    pub fn provenance_lines(&self) -> &[String] {
        &self.lines
    }
    pub fn files_verified(&self) -> usize {
        self.files_verified
    }
}

impl StageReceipt {
    pub fn provenance_lines(&self) -> Vec<String> {
        match self {
            Self::Absent => vec!["stage_receipt=absent".into()],
            Self::Checked(receipt) => receipt.lines.clone(),
        }
    }
    pub fn checked(&self) -> Option<&CheckedReceipt> {
        match self {
            Self::Absent => None,
            Self::Checked(receipt) => Some(receipt),
        }
    }
    pub fn llvm_identity_unstated(&self) -> String {
        match self {
            Self::Absent => format!(
                "it carries no {RECEIPT_NAME}: no build-time stage evidence was recorded, or the receipt was removed"
            ),
            Self::Checked(receipt) => llvm::unstated(&receipt.data),
        }
    }
}

pub fn inspect(toolchain: &Path, reported_commit: &str) -> Result<StageReceipt> {
    inspect_with_limit(toolchain, reported_commit, MAX_RECEIPT_BYTES)
}

pub fn inspect_with_limit(
    toolchain: &Path,
    reported_commit: &str,
    limit: u64,
) -> Result<StageReceipt> {
    let Some(loaded) =
        files::read_receipt(&toolchain.join(RECEIPT_NAME), limit.min(MAX_RECEIPT_BYTES))?
    else {
        return Ok(StageReceipt::Absent);
    };
    let data =
        json::parse(&loaded.bytes).map_err(|error| Refusal(format!("it is not JSON: {error}")))?;
    if !data.is_object() {
        return Err(Refusal("it is not a JSON object".into()));
    }
    let (mut lines, files_verified) = record::validate(toolchain, reported_commit, &data)?;
    let raw_sha256 = hash(&loaded.bytes);
    lines.insert(1, format!("stage_receipt_sha256={raw_sha256}"));
    loaded.check_current()?;
    Ok(StageReceipt::Checked(CheckedReceipt { raw_sha256, data, lines, files_verified }))
}

pub fn release_status_holds(mode: &Value, trust: &Value, materialization: &Value) -> bool {
    mode.as_str() == Some("seed")
        && trust.as_bool() == Some(true)
        && materialization.as_str() == Some("fresh-from-validated-archives")
}

pub fn unrecordable_character(text: &str) -> bool {
    text.chars().any(|c| (c as u32) < 0x20 || (0x7f..=0x9f).contains(&(c as u32)))
}

pub(crate) fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
pub(crate) fn is_hex(value: &Value, lengths: &[usize]) -> bool {
    value.as_str().is_some_and(|s| {
        lengths.contains(&s.len())
            && s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    })
}
pub(crate) fn exact_keys(value: &Value, keys: &[&str]) -> bool {
    value
        .as_object()
        .is_some_and(|map| map.len() == keys.len() && keys.iter().all(|key| map.contains_key(key)))
}
pub(crate) fn object<'a>(parent: &'a Value, key: &str, where_: &str) -> Result<&'a Object> {
    parent[key].as_object().ok_or_else(|| Refusal(format!("{where_}{key} is not an object")))
}
pub(crate) fn digest(parent: &Value, key: &str, where_: &str) -> Result<String> {
    if !is_hex(&parent[key], &[64]) {
        return Err(Refusal(format!("{where_}{key} is not a sha256: {}", repr(&parent[key]))));
    }
    Ok(parent[key].as_str().unwrap().into())
}
pub(crate) fn repr(value: &Value) -> String {
    json::python_repr(value)
}

#[cfg(test)]
mod tests;
