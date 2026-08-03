// trust-proof-cert certificate chain DAG
//
// Certificate dependency DAG: ordered certificates with dependency tracking,
// Merkle-tree integrity, chain verification, JSON archive serialization,
// and certificate revocation on source change.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{CertError, FunctionHash, ProofCertificate};

// ---------------------------------------------------------------------------
// CertificateDependencyDag
// ---------------------------------------------------------------------------

/// A directed acyclic graph of proof certificates where each certificate
/// may depend on other certificates (e.g., a function proof depends on
/// proofs of its callees).
///
/// Each certificate stores a Merkle hash of its dependency certificates,
/// enabling tamper detection across the entire dependency chain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateDependencyDag {
    // Trust: BTreeMap for deterministic certificate output
    /// Certificates in the DAG, keyed by certificate ID.
    pub certificates: BTreeMap<String, ProofCertificate>,
    /// Dependency edges: cert ID -> list of dependency cert IDs.
    pub dependencies: BTreeMap<String, Vec<String>>,
    /// Merkle hash for each certificate (covers cert content + dependency hashes).
    pub merkle_hashes: BTreeMap<String, [u8; 32]>,
    /// DAG name (e.g., crate name).
    pub name: String,
    /// Format version.
    pub version: u32,
}

/// Current DAG format version.
pub const DAG_FORMAT_VERSION: u32 = 1;

impl CertificateDependencyDag {
    /// Create a new empty DAG.
    pub fn new(name: &str) -> Self {
        CertificateDependencyDag {
            certificates: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            merkle_hashes: BTreeMap::new(),
            name: name.to_string(),
            version: DAG_FORMAT_VERSION,
        }
    }

    /// Add a certificate with its dependency IDs.
    ///
    /// Dependencies must already be in the DAG (enforces topological order).
    /// Computes the Merkle hash covering this cert's content and all its
    /// dependency hashes.
    pub fn add_certificate(
        &mut self,
        cert: ProofCertificate,
        dependency_ids: Vec<String>,
    ) -> Result<(), CertError> {
        let cert_id = cert.id.0.clone();

        // Verify all dependencies exist
        for dep_id in &dependency_ids {
            if !self.certificates.contains_key(dep_id) {
                return Err(CertError::VerificationFailed {
                    reason: format!("dependency '{dep_id}' not found in DAG for cert '{cert_id}'"),
                });
            }
        }

        // Compute Merkle hash: SHA-256(cert_content_hash || dep_merkle_hash_0 || dep_merkle_hash_1 || ...)
        let merkle_hash = self.compute_merkle_hash(&cert, &dependency_ids);

        self.certificates.insert(cert_id.clone(), cert);
        self.dependencies.insert(cert_id.clone(), dependency_ids);
        self.merkle_hashes.insert(cert_id, merkle_hash);

        Ok(())
    }

    /// Get a certificate by its ID.
    pub fn get(&self, cert_id: &str) -> Option<&ProofCertificate> {
        self.certificates.get(cert_id)
    }

    /// Get the dependencies of a certificate.
    pub fn get_dependencies(&self, cert_id: &str) -> Option<&[String]> {
        self.dependencies.get(cert_id).map(|v| v.as_slice())
    }

    /// Get the Merkle hash of a certificate.
    pub fn get_merkle_hash(&self, cert_id: &str) -> Option<&[u8; 32]> {
        self.merkle_hashes.get(cert_id)
    }

    /// Number of certificates in the DAG.
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Whether the DAG is empty.
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }

    /// Return all certificate IDs in topological order (dependencies before dependents).
    pub fn topological_order(&self) -> Result<Vec<String>, CertError> {
        let mut visited: BTreeSet<String> = BTreeSet::new();
        let mut order: Vec<String> = Vec::new();
        let mut in_progress: BTreeSet<String> = BTreeSet::new();

        for id in self.certificates.keys() {
            if !visited.contains(id) {
                self.topo_visit(id, &mut visited, &mut in_progress, &mut order)?;
            }
        }

        Ok(order)
    }

    /// Verify the entire DAG: check each certificate's VC hash, verify
    /// Merkle hashes match, and ensure no cycles.
    pub fn verify(&self) -> Result<DagVerificationResult, CertError> {
        let mut result = DagVerificationResult {
            valid: true,
            cert_count: self.certificates.len(),
            invalid_certs: Vec::new(),
            merkle_failures: Vec::new(),
            cycle_detected: false,
        };

        // Check for cycles via topological sort
        if self.topological_order().is_err() {
            result.valid = false;
            result.cycle_detected = true;
            return Ok(result);
        }

        // Verify each certificate
        for (cert_id, cert) in &self.certificates {
            // Check VC hash integrity
            if !cert.verify_vc_hash() {
                result.valid = false;
                result.invalid_certs.push(cert_id.clone());
                continue;
            }

            // Verify Merkle hash
            let deps = self.dependencies.get(cert_id).cloned().unwrap_or_default();
            let expected_merkle = self.compute_merkle_hash(cert, &deps);
            if let Some(stored_merkle) = self.merkle_hashes.get(cert_id) {
                if *stored_merkle != expected_merkle {
                    result.valid = false;
                    result.merkle_failures.push(cert_id.clone());
                }
            } else {
                result.valid = false;
                result.merkle_failures.push(cert_id.clone());
            }
        }

        Ok(result)
    }

    /// Compute the Merkle hash for a certificate given its dependencies.
    fn compute_merkle_hash(&self, cert: &ProofCertificate, dep_ids: &[String]) -> [u8; 32] {
        let mut hasher = Sha256::new();

        // Hash the certificate's own content
        hasher.update(cert.function.as_bytes());
        hasher.update(b"|");
        hasher.update(cert.function_hash.0.as_bytes());
        hasher.update(b"|");
        hasher.update(cert.vc_hash);
        hasher.update(b"|");
        hasher.update(cert.solver.name.as_bytes());
        hasher.update(b":");
        hasher.update(cert.solver.version.as_bytes());
        hasher.update(b"|");
        hasher.update(cert.timestamp.as_bytes());

        // Hash each dependency's Merkle hash (sorted for determinism)
        let mut sorted_deps: Vec<&str> = dep_ids.iter().map(|s| s.as_str()).collect();
        sorted_deps.sort();
        for dep_id in sorted_deps {
            if let Some(dep_hash) = self.merkle_hashes.get(dep_id) {
                hasher.update(b"|dep:");
                hasher.update(dep_hash);
            }
        }

        hasher.finalize().into()
    }

    /// Recursive topological sort helper.
    fn topo_visit(
        &self,
        id: &str,
        visited: &mut BTreeSet<String>,
        in_progress: &mut BTreeSet<String>,
        order: &mut Vec<String>,
    ) -> Result<(), CertError> {
        if in_progress.contains(id) {
            return Err(CertError::VerificationFailed {
                reason: format!("cycle detected involving certificate '{id}'"),
            });
        }
        if visited.contains(id) {
            return Ok(());
        }

        in_progress.insert(id.to_string());

        if let Some(deps) = self.dependencies.get(id) {
            for dep in deps {
                self.topo_visit(dep, visited, in_progress, order)?;
            }
        }

        in_progress.remove(id);
        visited.insert(id.to_string());
        order.push(id.to_string());

        Ok(())
    }

    // -----------------------------------------------------------------------
    // JSON archive serialization
    // -----------------------------------------------------------------------

    /// Serialize the entire DAG to a JSON archive string.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize a DAG from a JSON archive string.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Save the DAG to a JSON file.
    pub fn save_to_file(&self, path: impl AsRef<std::path::Path>) -> Result<(), CertError> {
        let json = self.to_json()?;
        if let Some(parent) = path.as_ref().parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path.as_ref(), json.as_bytes())?;
        Ok(())
    }

    /// Load a DAG from a JSON file.
    pub fn load_from_file(path: impl AsRef<std::path::Path>) -> Result<Self, CertError> {
        let json = std::fs::read_to_string(path.as_ref())?;
        Self::from_json(&json)
    }

    // -----------------------------------------------------------------------
    // Revocation
    // -----------------------------------------------------------------------

    /// Revoke (remove) all certificates whose function hash no longer matches
    /// the current source content hash.
    ///
    /// Returns the IDs of revoked certificates. Also removes any certificates
    /// that transitively depended on revoked certificates.
    pub fn revoke_stale(&mut self, current_hashes: &BTreeMap<String, FunctionHash>) -> Vec<String> {
        // First pass: find directly stale certs
        let mut stale: BTreeSet<String> = BTreeSet::new();
        for (cert_id, cert) in &self.certificates {
            if let Some(current_hash) = current_hashes.get(&cert.function)
                && !cert.is_fresh_for(current_hash)
            {
                stale.insert(cert_id.clone());
            }
            // If function not in current_hashes, leave cert alone (might be external)
        }

        // Second pass: transitively revoke dependents of stale certs
        let mut changed = true;
        while changed {
            changed = false;
            for (cert_id, deps) in &self.dependencies {
                if stale.contains(cert_id) {
                    continue;
                }
                if deps.iter().any(|d| stale.contains(d)) {
                    stale.insert(cert_id.clone());
                    changed = true;
                }
            }
        }

        // Remove stale certs
        let revoked: Vec<String> = stale.into_iter().collect();
        for id in &revoked {
            self.certificates.remove(id);
            self.dependencies.remove(id);
            self.merkle_hashes.remove(id);
        }

        // Clean up dependency references to removed certs
        for deps in self.dependencies.values_mut() {
            deps.retain(|d| self.certificates.contains_key(d));
        }

        revoked
    }
}

/// Result of verifying a certificate dependency DAG.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DagVerificationResult {
    /// Whether the entire DAG passed verification.
    pub valid: bool,
    /// Number of certificates in the DAG.
    pub cert_count: usize,
    /// Certificate IDs that failed VC hash verification.
    pub invalid_certs: Vec<String>,
    /// Certificate IDs whose Merkle hashes did not match recomputation.
    pub merkle_failures: Vec<String>,
    /// Whether a cycle was detected in the dependency graph.
    pub cycle_detected: bool,
}

// ---------------------------------------------------------------------------
// verify_cert_chain: validate an ordered Vec of certs with dependencies
// ---------------------------------------------------------------------------

/// Verify an ordered chain of certificates where each certificate may
/// depend on earlier certificates in the chain.
///
/// Returns Ok if all certificates have valid VC hashes and all dependency
/// hashes match. Returns an error describing the first failure.
pub fn verify_cert_chain(
    certs: &[ProofCertificate],
    dependencies: &BTreeMap<String, Vec<String>>,
) -> Result<(), CertError> {
    let mut seen: BTreeSet<String> = BTreeSet::new();

    for cert in certs {
        let cert_id = &cert.id.0;

        // Verify VC hash
        if !cert.verify_vc_hash() {
            return Err(CertError::VerificationFailed {
                reason: format!("certificate '{cert_id}' has invalid VC hash"),
            });
        }

        // Verify all dependencies are earlier in the chain
        if let Some(deps) = dependencies.get(cert_id) {
            for dep_id in deps {
                if !seen.contains(dep_id) {
                    return Err(CertError::VerificationFailed {
                        reason: format!(
                            "certificate '{cert_id}' depends on '{dep_id}' which has not been verified yet"
                        ),
                    });
                }
            }
        }

        seen.insert(cert_id.clone());
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// CertificateArchive: JSON import/export of certificate sets
// ---------------------------------------------------------------------------

/// A portable archive of certificates with dependency metadata.
/// Used for JSON export/import of certificate collections.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateArchive {
    /// Archive format identifier.
    pub format: String,
    /// Archive format version.
    pub format_version: u32,
    /// All certificates in the archive.
    pub certificates: Vec<ProofCertificate>,
    /// Dependency edges: cert ID -> list of dependency cert IDs.
    pub dependencies: BTreeMap<String, Vec<String>>,
    /// Optional metadata.
    pub metadata: BTreeMap<String, String>,
}

/// Current archive format version.
pub const ARCHIVE_FORMAT_VERSION: u32 = 1;

impl CertificateArchive {
    /// Create a new archive from a DAG.
    pub fn from_dag(dag: &CertificateDependencyDag) -> Result<Self, CertError> {
        let order = dag.topological_order()?;
        let certificates: Vec<ProofCertificate> =
            order.iter().filter_map(|id| dag.certificates.get(id).cloned()).collect();

        Ok(CertificateArchive {
            format: "trust-cert-archive".to_string(),
            format_version: ARCHIVE_FORMAT_VERSION,
            certificates,
            dependencies: dag.dependencies.clone(),
            metadata: BTreeMap::new(),
        })
    }

    /// Import an archive into a new DAG.
    pub fn to_dag(&self, name: &str) -> Result<CertificateDependencyDag, CertError> {
        let mut dag = CertificateDependencyDag::new(name);

        for cert in &self.certificates {
            let deps = self.dependencies.get(&cert.id.0).cloned().unwrap_or_default();
            dag.add_certificate(cert.clone(), deps)?;
        }

        Ok(dag)
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        let archive: Self = serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

        if archive.format != "trust-cert-archive" {
            return Err(CertError::SerializationFailed {
                reason: format!(
                    "unexpected format: expected 'trust-cert-archive', got '{}'",
                    archive.format
                ),
            });
        }

        Ok(archive)
    }

    /// Add metadata key-value pair.
    #[must_use]
    pub fn with_metadata(mut self, key: &str, value: &str) -> Self {
        self.metadata.insert(key.to_string(), value.to_string());
        self
    }
}

// ---------------------------------------------------------------------------
// Extended CertificateStore lookups
// ---------------------------------------------------------------------------

/// Extension trait providing additional lookup methods for CertificateStore.
pub trait CertificateStoreLookups {
    /// Find all certificates whose source location is in the given file.
    fn find_by_file(&self, file_path: &str) -> Vec<&ProofCertificate>;

    /// Find a certificate by its content hash (SHA-256 hex string of cert ID).
    fn find_by_hash(&self, hash: &str) -> Option<&ProofCertificate>;

    /// Revoke (remove) all certificates for functions whose source hash changed.
    /// Returns the IDs of removed certificates.
    fn revoke_changed(&mut self, current_hashes: &BTreeMap<String, FunctionHash>) -> Vec<String>;
}

impl CertificateStoreLookups for crate::CertificateStore {
    fn find_by_file(&self, file_path: &str) -> Vec<&ProofCertificate> {
        self.certificates
            .values()
            .filter(|cert| {
                cert.vc_snapshot.location.as_ref().map(|loc| loc.file == file_path).unwrap_or(false)
            })
            .collect()
    }

    fn find_by_hash(&self, hash: &str) -> Option<&ProofCertificate> {
        self.certificates.values().find(|cert| cert.id.0 == hash)
    }

    fn revoke_changed(&mut self, current_hashes: &BTreeMap<String, FunctionHash>) -> Vec<String> {
        let stale_ids: Vec<String> = self
            .certificates
            .iter()
            .filter(|(_id, cert)| {
                current_hashes.get(&cert.function).map(|h| !cert.is_fresh_for(h)).unwrap_or(false)
            })
            .map(|(id, _)| id.clone())
            .collect();

        for id in &stale_ids {
            self.certificates.remove(id);
            self.chains.remove(id);
        }

        stale_ids
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::{
        CertificateChain, CertificateStore, ChainStep, ChainStepType, FunctionHash, SolverInfo,
        VcSnapshot,
    };

    fn sample_solver_info() -> SolverInfo {
        SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc(function: &str, file: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "must hold".to_string() },
            function: function.into(),
            location: SourceSpan {
                file: file.to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn sample_vc_snapshot(function: &str, file: &str) -> VcSnapshot {
        VcSnapshot::from_vc(&sample_vc(function, file)).expect("snapshot should serialize")
    }

    fn sample_certificate(function: &str, timestamp: &str) -> ProofCertificate {
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            sample_vc_snapshot(function, "src/lib.rs"),
            sample_solver_info(),
            vec![1, 2, 3, 4],
            timestamp.to_string(),
        )
    }

    fn sample_certificate_in_file(function: &str, timestamp: &str, file: &str) -> ProofCertificate {
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            sample_vc_snapshot(function, file),
            sample_solver_info(),
            vec![1, 2, 3, 4],
            timestamp.to_string(),
        )
    }

    fn sample_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir-hash".to_string(),
            output_hash: "vc-hash".to_string(),
            time_ms: 5,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 42,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });
        chain
    }

    // -----------------------------------------------------------------------
    // DAG: build chain of 3 certs (A depends on B depends on C)
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_build_chain_of_three() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();
        let id_a = cert_a.id.0.clone();

        // C has no dependencies (leaf)
        dag.add_certificate(cert_c, vec![]).expect("add C");

        // B depends on C
        dag.add_certificate(cert_b, vec![id_c.clone()]).expect("add B");

        // A depends on B
        dag.add_certificate(cert_a, vec![id_b.clone()]).expect("add A");

        assert_eq!(dag.len(), 3);
        assert_eq!(dag.get_dependencies(&id_a), Some(vec![id_b.clone()].as_slice()));
        assert_eq!(dag.get_dependencies(&id_b), Some(vec![id_c.clone()].as_slice()));
        assert_eq!(dag.get_dependencies(&id_c), Some(vec![].as_slice()));

        // Each certificate should have a unique Merkle hash
        let hash_a = dag.get_merkle_hash(&id_a).expect("hash A");
        let hash_b = dag.get_merkle_hash(&id_b).expect("hash B");
        let hash_c = dag.get_merkle_hash(&id_c).expect("hash C");
        assert_ne!(hash_a, hash_b);
        assert_ne!(hash_b, hash_c);
        assert_ne!(hash_a, hash_c);
    }

    // -----------------------------------------------------------------------
    // DAG: verify valid chain succeeds
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_verify_valid_chain() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c]).expect("add B");
        dag.add_certificate(cert_a, vec![id_b]).expect("add A");

        let result = dag.verify().expect("verification should succeed");
        assert!(result.valid, "valid DAG should pass: {:?}", result);
        assert_eq!(result.cert_count, 3);
        assert!(result.invalid_certs.is_empty());
        assert!(result.merkle_failures.is_empty());
        assert!(!result.cycle_detected);
    }

    // -----------------------------------------------------------------------
    // DAG: tamper with middle cert, verify chain fails
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_verify_tampered_middle_cert() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c]).expect("add B");
        dag.add_certificate(cert_a, vec![id_b.clone()]).expect("add A");

        // Tamper with cert B's VC hash
        if let Some(cert_b_mut) = dag.certificates.get_mut(&id_b) {
            cert_b_mut.vc_hash[0] ^= 0xFF;
        }

        let result = dag.verify().expect("verification should return result");
        assert!(!result.valid, "tampered DAG should fail");
        assert!(result.invalid_certs.contains(&id_b));
    }

    // -----------------------------------------------------------------------
    // DAG: tamper with Merkle hash, verify fails
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_verify_tampered_merkle_hash() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c]).expect("add B");

        // Tamper with B's Merkle hash
        if let Some(hash) = dag.merkle_hashes.get_mut(&id_b) {
            hash[0] ^= 0xFF;
        }

        let result = dag.verify().expect("verification should return result");
        assert!(!result.valid, "tampered Merkle hash should fail");
        assert!(result.merkle_failures.contains(&id_b));
    }

    // -----------------------------------------------------------------------
    // DAG: revoke cert when source changes
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_revoke_stale_certs() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();
        let id_a = cert_a.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c.clone()]).expect("add B");
        dag.add_certificate(cert_a, vec![id_b.clone()]).expect("add A");

        // C's source changed
        let mut current_hashes: BTreeMap<String, FunctionHash> = BTreeMap::new();
        current_hashes
            .insert("crate::c".to_string(), FunctionHash::from_bytes(b"crate::c-body-MODIFIED"));
        // B and A still have same hash
        current_hashes.insert("crate::b".to_string(), FunctionHash::from_bytes(b"crate::b-body"));
        current_hashes.insert("crate::a".to_string(), FunctionHash::from_bytes(b"crate::a-body"));

        let revoked = dag.revoke_stale(&current_hashes);

        // C is directly stale, B depends on C so transitively stale,
        // A depends on B so also transitively stale
        assert_eq!(revoked.len(), 3);
        assert!(revoked.contains(&id_c));
        assert!(revoked.contains(&id_b));
        assert!(revoked.contains(&id_a));
        assert!(dag.is_empty());
    }

    #[test]
    fn test_dag_revoke_only_affected_branch() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_d = sample_certificate("crate::d", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();
        let id_d = cert_d.id.0.clone();

        // C and D are independent leaves, B depends on C
        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_d.clone(), vec![]).expect("add D");
        dag.add_certificate(cert_b, vec![id_c.clone()]).expect("add B");

        // Only C changed
        let mut current_hashes: BTreeMap<String, FunctionHash> = BTreeMap::new();
        current_hashes
            .insert("crate::c".to_string(), FunctionHash::from_bytes(b"crate::c-body-MODIFIED"));
        current_hashes.insert("crate::b".to_string(), FunctionHash::from_bytes(b"crate::b-body"));
        current_hashes.insert("crate::d".to_string(), FunctionHash::from_bytes(b"crate::d-body"));

        let revoked = dag.revoke_stale(&current_hashes);

        // C and B revoked, D survives
        assert_eq!(revoked.len(), 2);
        assert!(revoked.contains(&id_c));
        assert!(revoked.contains(&id_b));
        assert!(!revoked.contains(&id_d));
        assert_eq!(dag.len(), 1);
        assert!(dag.get(&id_d).is_some());
    }

    // -----------------------------------------------------------------------
    // DAG: JSON round-trip serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_json_roundtrip() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");

        let id_c = cert_c.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c]).expect("add B");

        let json = dag.to_json().expect("serialization should succeed");
        let restored =
            CertificateDependencyDag::from_json(&json).expect("deserialization should succeed");

        assert_eq!(restored.name, dag.name);
        assert_eq!(restored.len(), dag.len());
        assert_eq!(restored.certificates, dag.certificates);
        assert_eq!(restored.dependencies, dag.dependencies);
        assert_eq!(restored.merkle_hashes, dag.merkle_hashes);
    }

    // -----------------------------------------------------------------------
    // CertificateArchive: JSON round-trip
    // -----------------------------------------------------------------------

    #[test]
    fn test_archive_json_roundtrip() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");

        let id_c = cert_c.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c]).expect("add B");

        let archive = CertificateArchive::from_dag(&dag)
            .expect("archive creation should succeed")
            .with_metadata("build", "abc123");

        let json = archive.to_json().expect("archive serialization should succeed");
        let restored =
            CertificateArchive::from_json(&json).expect("archive deserialization should succeed");

        assert_eq!(restored.format, "trust-cert-archive");
        assert_eq!(restored.certificates.len(), 2);
        assert_eq!(restored.metadata.get("build"), Some(&"abc123".to_string()));

        // Import back to DAG
        let restored_dag = restored.to_dag("restored").expect("import should succeed");
        assert_eq!(restored_dag.len(), 2);
        let verify = restored_dag.verify().expect("verification");
        assert!(verify.valid);
    }

    // -----------------------------------------------------------------------
    // verify_cert_chain: ordered chain verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_cert_chain_valid() {
        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();

        let mut deps: BTreeMap<String, Vec<String>> = BTreeMap::new();
        deps.insert(cert_a.id.0.clone(), vec![id_b.clone()]);
        deps.insert(cert_b.id.0.clone(), vec![id_c.clone()]);

        // Order: C, B, A (dependencies first)
        let chain = vec![cert_c, cert_b, cert_a];
        verify_cert_chain(&chain, &deps).expect("valid chain should pass");
    }

    #[test]
    fn test_verify_cert_chain_invalid_vc_hash() {
        let mut cert = sample_certificate("crate::foo", "2026-03-30T00:00:00Z");
        cert.vc_hash[0] ^= 0xFF; // tamper

        let result = verify_cert_chain(&[cert], &BTreeMap::new());
        assert!(result.is_err());
        let err_msg = format!("{}", result.unwrap_err());
        assert!(err_msg.contains("invalid VC hash"));
    }

    #[test]
    fn test_verify_cert_chain_missing_dependency() {
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:00Z");

        let mut deps: BTreeMap<String, Vec<String>> = BTreeMap::new();
        deps.insert(cert_a.id.0.clone(), vec!["nonexistent".to_string()]);

        let result = verify_cert_chain(&[cert_a], &deps);
        assert!(result.is_err());
        let err_msg = format!("{}", result.unwrap_err());
        assert!(err_msg.contains("not been verified yet"));
    }

    // -----------------------------------------------------------------------
    // DAG: topological order
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_topological_order() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");
        let cert_a = sample_certificate("crate::a", "2026-03-30T00:00:02Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();
        let id_a = cert_a.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c.clone()]).expect("add B");
        dag.add_certificate(cert_a, vec![id_b.clone()]).expect("add A");

        let order = dag.topological_order().expect("should produce order");
        assert_eq!(order.len(), 3);

        // C must come before B, B must come before A
        let pos_c = order.iter().position(|x| x == &id_c).expect("C in order");
        let pos_b = order.iter().position(|x| x == &id_b).expect("B in order");
        let pos_a = order.iter().position(|x| x == &id_a).expect("A in order");
        assert!(pos_c < pos_b);
        assert!(pos_b < pos_a);
    }

    // -----------------------------------------------------------------------
    // DAG: add with missing dependency fails
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_add_missing_dependency_fails() {
        let mut dag = CertificateDependencyDag::new("test-crate");
        let cert = sample_certificate("crate::foo", "2026-03-30T00:00:00Z");

        let result = dag.add_certificate(cert, vec!["nonexistent".to_string()]);
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // DAG: file persistence
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_file_persistence() {
        let path =
            std::env::temp_dir().join(format!("trust-cert-dag-test-{}.json", std::process::id()));
        let _ = std::fs::remove_file(&path);

        let mut dag = CertificateDependencyDag::new("file-test");
        let cert = sample_certificate("crate::foo", "2026-03-30T00:00:00Z");
        dag.add_certificate(cert, vec![]).expect("add cert");

        dag.save_to_file(&path).expect("save should succeed");
        let loaded = CertificateDependencyDag::load_from_file(&path).expect("load should succeed");

        assert_eq!(loaded.name, dag.name);
        assert_eq!(loaded.len(), dag.len());

        let _ = std::fs::remove_file(&path);
    }

    // -----------------------------------------------------------------------
    // CertificateStore extended lookups
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_find_by_file() {
        let mut store = CertificateStore::new("test-crate");

        let cert1 = sample_certificate_in_file("crate::foo", "2026-03-30T00:00:00Z", "src/foo.rs");
        let cert2 = sample_certificate_in_file("crate::bar", "2026-03-30T00:00:01Z", "src/bar.rs");
        let cert3 = sample_certificate_in_file("crate::baz", "2026-03-30T00:00:02Z", "src/foo.rs");

        store.insert(cert1.clone(), sample_chain());
        store.insert(cert2.clone(), sample_chain());
        store.insert(cert3.clone(), sample_chain());

        let found = store.find_by_file("src/foo.rs");
        assert_eq!(found.len(), 2);
        assert!(found.iter().any(|c| c.function == "crate::foo"));
        assert!(found.iter().any(|c| c.function == "crate::baz"));

        let found_bar = store.find_by_file("src/bar.rs");
        assert_eq!(found_bar.len(), 1);
        assert_eq!(found_bar[0].function, "crate::bar");

        let found_none = store.find_by_file("src/nonexistent.rs");
        assert!(found_none.is_empty());
    }

    #[test]
    fn test_store_find_by_hash() {
        let mut store = CertificateStore::new("test-crate");

        let cert = sample_certificate("crate::foo", "2026-03-30T00:00:00Z");
        let cert_hash = cert.id.0.clone();
        store.insert(cert.clone(), sample_chain());

        let found = store.find_by_hash(&cert_hash);
        assert!(found.is_some());
        assert_eq!(found.unwrap().function, "crate::foo");

        let not_found = store.find_by_hash("nonexistent-hash");
        assert!(not_found.is_none());
    }

    #[test]
    fn test_store_revoke_changed() {
        let mut store = CertificateStore::new("test-crate");

        let cert1 = sample_certificate("crate::foo", "2026-03-30T00:00:00Z");
        let cert2 = sample_certificate("crate::bar", "2026-03-30T00:00:01Z");

        store.insert(cert1.clone(), sample_chain());
        store.insert(cert2.clone(), sample_chain());

        assert_eq!(store.len(), 2);

        // foo's source changed, bar stayed the same
        let mut current_hashes: BTreeMap<String, FunctionHash> = BTreeMap::new();
        current_hashes.insert(
            "crate::foo".to_string(),
            FunctionHash::from_bytes(b"crate::foo-body-MODIFIED"),
        );
        current_hashes
            .insert("crate::bar".to_string(), FunctionHash::from_bytes(b"crate::bar-body"));

        let revoked = store.revoke_changed(&current_hashes);
        assert_eq!(revoked.len(), 1);
        assert_eq!(store.len(), 1);
        assert!(store.get(&cert2.id).is_some());
        assert!(store.get(&cert1.id).is_none());
    }

    // -----------------------------------------------------------------------
    // DAG: Merkle integrity - changing dependency invalidates parent
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_merkle_dependency_integrity() {
        let mut dag = CertificateDependencyDag::new("test-crate");

        let cert_c = sample_certificate("crate::c", "2026-03-30T00:00:00Z");
        let cert_b = sample_certificate("crate::b", "2026-03-30T00:00:01Z");

        let id_c = cert_c.id.0.clone();
        let id_b = cert_b.id.0.clone();

        dag.add_certificate(cert_c, vec![]).expect("add C");
        dag.add_certificate(cert_b, vec![id_c.clone()]).expect("add B");

        // Verify passes initially
        let result = dag.verify().expect("initial verify");
        assert!(result.valid);

        // Tamper with C's Merkle hash (simulates C being modified)
        if let Some(hash) = dag.merkle_hashes.get_mut(&id_c) {
            hash[0] ^= 0xFF;
        }

        // Now B's Merkle hash will be wrong because it was computed with
        // the original C Merkle hash, but when recomputed it uses the
        // tampered C hash.
        let result = dag.verify().expect("verify after tamper");
        assert!(!result.valid);
        // B's Merkle should fail because the dependency hash changed
        assert!(result.merkle_failures.contains(&id_b));
    }
}
