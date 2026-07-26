// Runtime binary source identity validation.
//
// Wraps the checked binary identity (path, root digest, selected-image digest,
// function entry) imported by the runtime rewrite loop.

use serde::Deserialize;

use super::digests::is_canonical_sha256_hex;

#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
pub(crate) struct RuntimeBinarySourceIdentity {
    #[serde(default)]
    pub(crate) binary_path: Option<String>,
    #[serde(default)]
    pub(crate) binary_sha256: Option<String>,
    #[serde(default)]
    pub(crate) selected_image_sha256: Option<String>,
    #[serde(default)]
    pub(crate) function_entry: Option<u64>,
}

impl RuntimeBinarySourceIdentity {
    pub(crate) fn is_checked(&self) -> bool {
        self.blockers().is_empty()
    }

    pub(crate) fn blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        match self.binary_path.as_deref().map(str::trim) {
            Some(path) if !path.is_empty() => {}
            _ => blockers.push("missing binary_path".to_string()),
        }
        match self.binary_sha256.as_deref() {
            Some(sha256) if is_canonical_sha256_hex(sha256) => {}
            Some(_) => {
                blockers.push("binary_sha256 is not canonical lowercase SHA-256".to_string())
            }
            None => blockers.push("missing binary_sha256".to_string()),
        }
        match self.selected_image_sha256.as_deref() {
            Some(sha256) if is_canonical_sha256_hex(sha256) => {}
            Some(_) => blockers
                .push("selected_image_sha256 is not canonical lowercase SHA-256".to_string()),
            None => blockers.push("missing selected_image_sha256".to_string()),
        }
        if self.function_entry.is_none() {
            blockers.push("missing function_entry".to_string());
        }
        blockers
    }
}
