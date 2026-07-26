// trust-proof-cert persistent certificate store
//
// CertificateStore: in-memory store with filesystem persistence (JSON).
// Supports query by function, VcKind, ProofStrength.
// Staleness detection and pruning by source modification timestamp.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::timestamp::parse_timestamp_epoch;
use crate::{CertError, CertificateChain, CertificateId, FunctionHash, ProofCertificate};

/// A collection of proof certificates for a crate, with chain tracking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateStore {
    // Trust: BTreeMap for deterministic certificate output
    /// Map from certificate ID to certificate.
    pub certificates: BTreeMap<String, ProofCertificate>,
    /// Map from certificate ID to its verification chain.
    pub chains: BTreeMap<String, CertificateChain>,
    /// Crate name this store belongs to.
    pub crate_name: String,
    /// Store format version.
    pub version: u32,
}

pub const STORE_FORMAT_VERSION: u32 = 1;

/// Default filename for the certificate store JSON file.
pub const STORE_FILENAME: &str = "trust-proof-certs.json";

impl CertificateStore {
    /// Create a new empty store for a crate.
    pub fn new(crate_name: impl Into<String>) -> Self {
        CertificateStore {
            certificates: BTreeMap::new(),
            chains: BTreeMap::new(),
            crate_name: crate_name.into(),
            version: STORE_FORMAT_VERSION,
        }
    }

    /// Insert a certificate with its chain.
    pub fn insert(&mut self, cert: ProofCertificate, chain: CertificateChain) {
        let id = cert.id.0.clone();
        self.certificates.insert(id.clone(), cert);
        self.chains.insert(id, chain);
    }

    /// Remove a certificate by ID. Returns the removed certificate if it existed.
    pub fn remove(&mut self, id: &CertificateId) -> Option<ProofCertificate> {
        self.chains.remove(&id.0);
        self.certificates.remove(&id.0)
    }

    /// Get a certificate by ID.
    pub fn get(&self, id: &CertificateId) -> Option<&ProofCertificate> {
        self.certificates.get(&id.0)
    }

    /// Get the chain for a certificate.
    pub fn get_chain(&self, id: &CertificateId) -> Option<&CertificateChain> {
        self.chains.get(&id.0)
    }

    /// Find all certificates for a function.
    pub fn find_by_function(&self, function: &str) -> Vec<&ProofCertificate> {
        self.certificates.values().filter(|c| c.function == function).collect()
    }

    /// Find certificates by VC kind substring match.
    ///
    /// Matches against the `vc_snapshot.kind` field (Debug format of VcKind).
    pub fn find_by_vc_kind(&self, kind_substr: &str) -> Vec<&ProofCertificate> {
        self.certificates.values().filter(|c| c.vc_snapshot.kind.contains(kind_substr)).collect()
    }

    /// Find certificates by proof strength.
    pub fn find_by_strength(
        &self,
        strength: &trust_types::ProofStrength,
    ) -> Vec<&ProofCertificate> {
        self.certificates.values().filter(|c| c.solver.strength == *strength).collect()
    }

    /// Get all unique function names that have certificates.
    pub fn function_names(&self) -> Vec<String> {
        let mut names: Vec<String> =
            self.certificates.values().map(|c| c.function.clone()).collect();
        names.sort();
        names.dedup();
        names
    }

    /// Verify all certificates: check chains and staleness.
    pub fn verify_all(
        &self,
        current_hashes: &BTreeMap<String, FunctionHash>,
    ) -> Result<StoreVerification, CertError> {
        let mut result = StoreVerification {
            total: self.certificates.len(),
            valid: 0,
            stale: Vec::new(),
            chain_errors: Vec::new(),
        };

        for (id, cert) in &self.certificates {
            if let Some(chain) = self.chains.get(id)
                && let Err(e) = chain.verify_integrity()
            {
                result.chain_errors.push((id.clone(), format!("{e}")));
                continue;
            }

            if let Some(current_hash) = current_hashes.get(&cert.function) {
                if cert.is_fresh_for(current_hash) {
                    result.valid += 1;
                } else {
                    result.stale.push(id.clone());
                }
            } else {
                result.stale.push(id.clone());
            }
        }

        Ok(result)
    }

    /// Prune stale certificates: remove any certificate whose timestamp
    /// (parsed as seconds since epoch) is older than `source_modified_epoch`.
    ///
    /// Returns the IDs of removed certificates.
    pub fn prune_stale(&mut self, source_modified_epoch: u64) -> Vec<String> {
        let stale_ids: Vec<String> = self
            .certificates
            .iter()
            .filter(|(_id, cert)| {
                parse_timestamp_epoch(&cert.timestamp).unwrap_or(0) < source_modified_epoch
            })
            .map(|(id, _)| id.clone())
            .collect();

        for id in &stale_ids {
            self.certificates.remove(id);
            self.chains.remove(id);
        }

        stale_ids
    }

    /// Prune certificates for functions whose hashes have changed.
    ///
    /// Returns the IDs of removed certificates.
    pub fn prune_by_hash(
        &mut self,
        current_hashes: &BTreeMap<String, FunctionHash>,
    ) -> Vec<String> {
        let stale_ids: Vec<String> = self
            .certificates
            .iter()
            .filter(|(_id, cert)| {
                current_hashes.get(&cert.function).map(|h| !cert.is_fresh_for(h)).unwrap_or(true)
            })
            .map(|(id, _)| id.clone())
            .collect();

        for id in &stale_ids {
            self.certificates.remove(id);
            self.chains.remove(id);
        }

        stale_ids
    }

    /// Number of certificates.
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Is the store empty?
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    // -----------------------------------------------------------------------
    // Filesystem persistence
    // -----------------------------------------------------------------------

    /// Save the store to a JSON file at the given directory path.
    ///
    /// Creates the directory if it does not exist. The file is written
    /// atomically (write to temp, then rename).
    pub fn save_to_dir(&self, dir: impl AsRef<Path>) -> Result<PathBuf, CertError> {
        let dir = dir.as_ref();
        std::fs::create_dir_all(dir)?;
        let path = dir.join(STORE_FILENAME);
        let json = self.to_json()?;
        // Write atomically: temp file then rename
        let tmp_path = dir.join(format!(".{STORE_FILENAME}.tmp"));
        std::fs::write(&tmp_path, json.as_bytes())?;
        std::fs::rename(&tmp_path, &path)?;
        Ok(path)
    }

    /// Load a store from a directory. Returns None if the file does not exist.
    pub fn load_from_dir(dir: impl AsRef<Path>) -> Result<Option<Self>, CertError> {
        let path = dir.as_ref().join(STORE_FILENAME);
        if !path.exists() {
            return Ok(None);
        }
        let json = std::fs::read_to_string(&path)?;
        let store = Self::from_json(&json)?;
        Ok(Some(store))
    }

    /// Load a store from a directory, or create a new empty one if the file
    /// does not exist.
    pub fn load_or_create(
        dir: impl AsRef<Path>,
        crate_name: impl Into<String>,
    ) -> Result<Self, CertError> {
        match Self::load_from_dir(&dir)? {
            Some(store) => Ok(store),
            None => Ok(Self::new(crate_name)),
        }
    }

    /// Save the store to a specific file path (not a directory).
    pub fn save_to_file(&self, path: impl AsRef<Path>) -> Result<(), CertError> {
        let json = self.to_json()?;
        if let Some(parent) = path.as_ref().parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path.as_ref(), json.as_bytes())?;
        Ok(())
    }

    /// Load a store from a specific file path.
    pub fn load_from_file(path: impl AsRef<Path>) -> Result<Self, CertError> {
        let json = std::fs::read_to_string(path.as_ref())?;
        Self::from_json(&json)
    }
}

/// Result of verifying all certificates in a store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoreVerification {
    /// Total certificates checked.
    pub total: usize,
    /// Certificates that are valid (fresh + chain-intact).
    pub valid: usize,
    /// IDs of stale certificates.
    pub stale: Vec<String>,
    /// IDs with chain integrity errors: (id, error message).
    pub chain_errors: Vec<(String, String)>,
}

impl StoreVerification {
    /// True if all certificates are valid.
    pub fn all_valid(&self) -> bool {
        self.stale.is_empty() && self.chain_errors.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::timestamp::parse_timestamp_epoch;

    #[test]
    fn test_parse_timestamp_epoch_basic() {
        let t1 = parse_timestamp_epoch("2026-03-27T12:00:00Z");
        let t2 = parse_timestamp_epoch("2026-03-27T12:05:00Z");
        assert!(t1.is_some());
        assert!(t2.is_some());
        assert!(t2.unwrap() > t1.unwrap(), "later timestamp should have larger epoch");
    }

    #[test]
    fn test_parse_timestamp_epoch_invalid() {
        assert!(parse_timestamp_epoch("not-a-timestamp").is_none());
        assert!(parse_timestamp_epoch("").is_none());
    }
}
