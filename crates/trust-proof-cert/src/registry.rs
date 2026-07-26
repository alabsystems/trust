// trust-proof-cert certificate registry
//
// Content-addressed certificate registry with indexed lookups,
// revocation, garbage collection, and snapshot export/import.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::timestamp::parse_timestamp_epoch;
use crate::{CertError, CertificateChain, CertificateId, ChainValidator, ProofCertificate};

/// Content-addressed identifier for registry entries.
/// Computed as SHA-256 of the certificate's canonical JSON.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RegistryId(pub String);

impl RegistryId {
    /// Compute a content-addressed ID from a certificate's canonical bytes.
    pub fn from_certificate(cert: &ProofCertificate) -> Result<Self, CertError> {
        let json = cert.to_json()?;
        let mut hasher = Sha256::new();
        hasher.update(json.as_bytes());
        Ok(RegistryId(format!("{:x}", hasher.finalize())))
    }
}

/// Reason a certificate was revoked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RevocationReason {
    /// The function body changed (certificate is stale).
    FunctionModified,
    /// The proof was found to be unsound.
    UnsoundProof,
    /// Superseded by a newer certificate.
    Superseded { replacement_id: RegistryId },
    /// Manual revocation with reason string.
    Manual { reason: String },
}

/// A revocation record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Revocation {
    /// When the revocation was recorded (ISO 8601).
    pub timestamp: String,
    /// Why the certificate was revoked.
    pub reason: RevocationReason,
}

/// Policy for garbage collection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GcPolicy {
    /// Remove certificates older than this many seconds (0 = no age limit).
    pub max_age_secs: u64,
    /// Remove superseded certificates (only keep the latest per function).
    pub remove_superseded: bool,
    /// Remove revoked certificates.
    pub remove_revoked: bool,
}

impl Default for GcPolicy {
    fn default() -> Self {
        GcPolicy { max_age_secs: 0, remove_superseded: true, remove_revoked: true }
    }
}

/// Statistics about the registry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegistryStats {
    /// Total number of certificates.
    pub total_certificates: usize,
    /// Number of valid (non-revoked) certificates.
    pub valid_certificates: usize,
    /// Number of revoked certificates.
    pub revoked_certificates: usize,
    /// Number of unique functions covered.
    pub unique_functions: usize,
    /// Approximate storage size in bytes (JSON serialized).
    pub storage_bytes: usize,
    /// Oldest certificate timestamp (if any).
    pub oldest_timestamp: Option<String>,
    /// Newest certificate timestamp (if any).
    pub newest_timestamp: Option<String>,
}

/// A serializable snapshot of the entire registry for export/import.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegistrySnapshot {
    // Trust: BTreeMap for deterministic certificate output
    /// All certificates indexed by registry ID.
    pub certificates: BTreeMap<String, ProofCertificate>,
    /// All chains indexed by registry ID.
    pub chains: BTreeMap<String, CertificateChain>,
    /// All revocations indexed by registry ID.
    pub revocations: BTreeMap<String, Revocation>,
    /// Snapshot version.
    pub version: u32,
}

const REGISTRY_SNAPSHOT_VERSION: u32 = 1;

/// Content-addressed certificate registry.
///
/// Provides indexed storage of proof certificates with:
/// - Content-addressed IDs (SHA-256 of certificate JSON)
/// - Secondary indexes by function name and VC kind
/// - Revocation tracking
/// - Garbage collection
/// - Export/import via serializable snapshots
pub struct CertificateRegistry {
    /// Primary storage: registry ID -> certificate.
    certificates: BTreeMap<String, ProofCertificate>,
    /// Certificate chains: registry ID -> chain.
    chains: BTreeMap<String, CertificateChain>,
    /// Revocation records: registry ID -> revocation info.
    revocations: BTreeMap<String, Revocation>,
    /// Index: function name -> set of registry IDs.
    fn_index: BTreeMap<String, BTreeSet<String>>,
    /// Index: VC kind string -> set of registry IDs.
    vc_kind_index: BTreeMap<String, BTreeSet<String>>,
    /// Map from original CertificateId -> RegistryId for cross-referencing.
    cert_id_map: BTreeMap<String, String>,
}

impl CertificateRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        CertificateRegistry {
            certificates: BTreeMap::new(),
            chains: BTreeMap::new(),
            revocations: BTreeMap::new(),
            fn_index: BTreeMap::new(),
            vc_kind_index: BTreeMap::new(),
            cert_id_map: BTreeMap::new(),
        }
    }

    /// Register a certificate and its chain. Returns the content-addressed registry ID.
    ///
    /// If a certificate with the same content already exists, returns its existing ID
    /// without duplicating.
    pub fn register(
        &mut self,
        cert: ProofCertificate,
        chain: CertificateChain,
    ) -> Result<RegistryId, CertError> {
        let reg_id = RegistryId::from_certificate(&cert)?;
        let id_str = reg_id.0.clone();

        // Idempotent: if already registered, return existing ID
        if self.certificates.contains_key(&id_str) {
            return Ok(reg_id);
        }

        // Build indexes
        self.fn_index.entry(cert.function.clone()).or_default().insert(id_str.clone());

        self.vc_kind_index.entry(cert.vc_snapshot.kind.clone()).or_default().insert(id_str.clone());

        self.cert_id_map.insert(cert.id.0.clone(), id_str.clone());

        self.certificates.insert(id_str.clone(), cert);
        self.chains.insert(id_str, chain);

        Ok(reg_id)
    }

    /// Look up a certificate by its registry ID.
    pub fn lookup(&self, id: &RegistryId) -> Option<&ProofCertificate> {
        self.certificates.get(&id.0)
    }

    /// Look up a certificate by its original CertificateId.
    pub fn lookup_by_cert_id(&self, cert_id: &CertificateId) -> Option<&ProofCertificate> {
        self.cert_id_map.get(&cert_id.0).and_then(|reg_id| self.certificates.get(reg_id))
    }

    /// Look up all certificates for a given function name.
    pub fn lookup_by_function(&self, fn_name: &str) -> Vec<&ProofCertificate> {
        self.fn_index
            .get(fn_name)
            .map(|ids| ids.iter().filter_map(|id| self.certificates.get(id)).collect())
            .unwrap_or_default()
    }

    /// Look up all certificates for a given VC kind (exact match on kind string).
    pub fn lookup_by_vc_kind(&self, kind: &str) -> Vec<&ProofCertificate> {
        self.vc_kind_index
            .get(kind)
            .map(|ids| ids.iter().filter_map(|id| self.certificates.get(id)).collect())
            .unwrap_or_default()
    }

    /// Get the chain for a registry entry.
    pub fn get_chain(&self, id: &RegistryId) -> Option<&CertificateChain> {
        self.chains.get(&id.0)
    }

    /// Revoke a certificate. Returns an error if the certificate is not in the registry.
    pub fn revoke(
        &mut self,
        id: &RegistryId,
        reason: RevocationReason,
        timestamp: String,
    ) -> Result<(), CertError> {
        if !self.certificates.contains_key(&id.0) {
            return Err(CertError::StoreError {
                reason: format!("certificate {} not found in registry", id.0),
            });
        }

        self.revocations.insert(id.0.clone(), Revocation { timestamp, reason });

        Ok(())
    }

    /// Check if a certificate is revoked.
    pub fn is_revoked(&self, id: &RegistryId) -> bool {
        self.revocations.contains_key(&id.0)
    }

    /// Check if a certificate is valid: exists, not revoked, and chain is intact.
    pub fn is_valid(&self, id: &RegistryId) -> bool {
        if !self.certificates.contains_key(&id.0) {
            return false;
        }
        if self.is_revoked(id) {
            return false;
        }
        if let Some(chain) = self.chains.get(&id.0) {
            ChainValidator::validate(chain).valid
        } else {
            false
        }
    }

    /// Garbage collect certificates according to the given policy.
    ///
    /// Returns the list of registry IDs that were removed.
    pub fn gc(&mut self, policy: &GcPolicy) -> Vec<RegistryId> {
        let mut to_remove: BTreeSet<String> = BTreeSet::new();

        // Collect revoked
        if policy.remove_revoked {
            for id in self.revocations.keys() {
                to_remove.insert(id.clone());
            }
        }

        // Collect aged-out certificates
        if policy.max_age_secs > 0 {
            // We use a simple ordering comparison on timestamps
            for (id, cert) in &self.certificates {
                if is_expired(&cert.timestamp, policy.max_age_secs) {
                    to_remove.insert(id.clone());
                }
            }
        }

        // Collect superseded (keep only the newest per function)
        if policy.remove_superseded {
            let mut by_function: BTreeMap<&str, Vec<(&str, &str)>> = BTreeMap::new();
            for (id, cert) in &self.certificates {
                by_function
                    .entry(&cert.function)
                    .or_default()
                    .push((id.as_str(), cert.timestamp.as_str()));
            }

            for (_fn_name, mut entries) in by_function {
                if entries.len() <= 1 {
                    continue;
                }
                // Sort by timestamp descending (lexicographic works for ISO 8601)
                entries.sort_by(|a, b| b.1.cmp(a.1));
                // Everything after the first (newest) is superseded
                for (id, _ts) in entries.into_iter().skip(1) {
                    to_remove.insert(id.to_string());
                }
            }
        }

        // Actually remove
        let mut removed = Vec::new();
        for id in &to_remove {
            self.remove_entry(id);
            removed.push(RegistryId(id.clone()));
        }

        removed
    }

    /// Export the entire registry as a serializable snapshot.
    pub fn export_registry(&self) -> RegistrySnapshot {
        RegistrySnapshot {
            certificates: self.certificates.clone(),
            chains: self.chains.clone(),
            revocations: self.revocations.clone(),
            version: REGISTRY_SNAPSHOT_VERSION,
        }
    }

    /// Import a registry snapshot, merging into the current registry.
    ///
    /// Certificates that already exist (by content address) are skipped.
    /// Revocations are merged (union).
    pub fn import_registry(&mut self, snapshot: RegistrySnapshot) -> Result<usize, CertError> {
        let mut imported = 0;

        for (id, cert) in snapshot.certificates {
            if self.certificates.contains_key(&id) {
                continue;
            }

            // Rebuild indexes
            self.fn_index.entry(cert.function.clone()).or_default().insert(id.clone());

            self.vc_kind_index.entry(cert.vc_snapshot.kind.clone()).or_default().insert(id.clone());

            self.cert_id_map.insert(cert.id.0.clone(), id.clone());

            self.certificates.insert(id.clone(), cert);

            if let Some(chain) = snapshot.chains.get(&id) {
                self.chains.insert(id, chain.clone());
            }

            imported += 1;
        }

        // Merge revocations
        for (id, revocation) in snapshot.revocations {
            self.revocations.entry(id).or_insert(revocation);
        }

        Ok(imported)
    }

    /// Compute registry statistics.
    pub fn stats(&self) -> RegistryStats {
        let total_certificates = self.certificates.len();
        let revoked_certificates = self.revocations.len();
        let valid_certificates = total_certificates.saturating_sub(revoked_certificates);
        let unique_functions = self.fn_index.len();

        // Approximate storage size
        let storage_bytes =
            self.certificates.values().filter_map(|c| c.to_json().ok()).map(|j| j.len()).sum();

        // Find oldest and newest timestamps
        let mut timestamps: Vec<&str> =
            self.certificates.values().map(|c| c.timestamp.as_str()).collect();
        timestamps.sort();

        let oldest_timestamp = timestamps.first().map(|s| (*s).to_string());
        let newest_timestamp = timestamps.last().map(|s| (*s).to_string());

        RegistryStats {
            total_certificates,
            valid_certificates,
            revoked_certificates,
            unique_functions,
            storage_bytes,
            oldest_timestamp,
            newest_timestamp,
        }
    }

    /// Number of certificates in the registry.
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }

    /// Get all unique function names in the registry.
    pub fn function_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.fn_index.keys().cloned().collect();
        names.sort();
        names
    }

    /// Internal: remove an entry by registry ID string, cleaning up all indexes.
    fn remove_entry(&mut self, id: &str) {
        if let Some(cert) = self.certificates.remove(id) {
            // Clean function index
            if let Some(set) = self.fn_index.get_mut(&cert.function) {
                set.remove(id);
                if set.is_empty() {
                    self.fn_index.remove(&cert.function);
                }
            }

            // Clean VC kind index
            if let Some(set) = self.vc_kind_index.get_mut(&cert.vc_snapshot.kind) {
                set.remove(id);
                if set.is_empty() {
                    self.vc_kind_index.remove(&cert.vc_snapshot.kind);
                }
            }

            // Clean cert_id_map
            self.cert_id_map.remove(&cert.id.0);
        }

        self.chains.remove(id);
        self.revocations.remove(id);
    }
}

impl Default for CertificateRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if a timestamp is older than max_age_secs from the current system time.
fn is_expired(timestamp: &str, max_age_secs: u64) -> bool {
    let epoch = parse_timestamp_epoch(timestamp).unwrap_or(0);
    // Trust: Use actual system time instead of hardcoded reference epoch.
    let now_epoch = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    now_epoch.saturating_sub(epoch) > max_age_secs
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::{CertificateChain, ChainStep, ChainStepType, FunctionHash, SolverInfo, VcSnapshot};

    fn sample_solver_info() -> SolverInfo {
        SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "must hold".to_string() },
            function: function.into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn sample_vc_snapshot(function: &str) -> VcSnapshot {
        VcSnapshot::from_vc(&sample_vc(function)).expect("snapshot should serialize")
    }

    fn sample_certificate(function: &str, timestamp: &str) -> ProofCertificate {
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            sample_vc_snapshot(function),
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

    #[test]
    fn test_registry_register_and_lookup() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let chain = sample_chain();

        let id = registry.register(cert.clone(), chain).unwrap();
        assert_eq!(registry.len(), 1);

        let found = registry.lookup(&id).unwrap();
        assert_eq!(found, &cert);
    }

    #[test]
    fn test_registry_idempotent_register() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let chain = sample_chain();

        let id1 = registry.register(cert.clone(), chain.clone()).unwrap();
        let id2 = registry.register(cert, chain).unwrap();

        assert_eq!(id1, id2);
        assert_eq!(registry.len(), 1);
    }

    #[test]
    fn test_registry_lookup_by_function() {
        let mut registry = CertificateRegistry::new();
        let cert1 = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let cert2 = sample_certificate("crate::foo", "2026-03-27T12:05:00Z");
        let cert3 = sample_certificate("crate::bar", "2026-03-27T12:00:00Z");

        registry.register(cert1, sample_chain()).unwrap();
        registry.register(cert2, sample_chain()).unwrap();
        registry.register(cert3, sample_chain()).unwrap();

        let foo_certs = registry.lookup_by_function("crate::foo");
        assert_eq!(foo_certs.len(), 2);

        let bar_certs = registry.lookup_by_function("crate::bar");
        assert_eq!(bar_certs.len(), 1);

        let baz_certs = registry.lookup_by_function("crate::baz");
        assert!(baz_certs.is_empty());
    }

    #[test]
    fn test_registry_lookup_by_vc_kind() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let kind = cert.vc_snapshot.kind.clone();

        registry.register(cert, sample_chain()).unwrap();

        let found = registry.lookup_by_vc_kind(&kind);
        assert_eq!(found.len(), 1);

        let not_found = registry.lookup_by_vc_kind("Nonexistent");
        assert!(not_found.is_empty());
    }

    #[test]
    fn test_registry_revoke() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let id = registry.register(cert, sample_chain()).unwrap();

        assert!(!registry.is_revoked(&id));
        assert!(registry.is_valid(&id));

        registry
            .revoke(&id, RevocationReason::FunctionModified, "2026-03-28T00:00:00Z".to_string())
            .unwrap();

        assert!(registry.is_revoked(&id));
        assert!(!registry.is_valid(&id));
    }

    #[test]
    fn test_registry_revoke_nonexistent() {
        let mut registry = CertificateRegistry::new();
        let fake_id = RegistryId("nonexistent".to_string());

        let result = registry.revoke(
            &fake_id,
            RevocationReason::Manual { reason: "test".to_string() },
            "2026-03-28T00:00:00Z".to_string(),
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_registry_gc_revoked() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let id = registry.register(cert, sample_chain()).unwrap();

        registry
            .revoke(&id, RevocationReason::UnsoundProof, "2026-03-28T00:00:00Z".to_string())
            .unwrap();

        let policy = GcPolicy { remove_revoked: true, ..GcPolicy::default() };

        let removed = registry.gc(&policy);
        assert_eq!(removed.len(), 1);
        assert_eq!(removed[0], id);
        assert!(registry.is_empty());
    }

    #[test]
    fn test_registry_gc_superseded() {
        let mut registry = CertificateRegistry::new();
        let old = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let new = sample_certificate("crate::foo", "2026-03-27T12:05:00Z");

        registry.register(old, sample_chain()).unwrap();
        registry.register(new, sample_chain()).unwrap();

        assert_eq!(registry.len(), 2);

        let policy = GcPolicy { remove_superseded: true, remove_revoked: false, max_age_secs: 0 };

        let removed = registry.gc(&policy);
        assert_eq!(removed.len(), 1);
        assert_eq!(registry.len(), 1);

        // The remaining certificate should be the newer one
        let remaining: Vec<&ProofCertificate> = registry.lookup_by_function("crate::foo");
        assert_eq!(remaining.len(), 1);
        assert_eq!(remaining[0].timestamp, "2026-03-27T12:05:00Z");
    }

    #[test]
    fn test_registry_gc_aged() {
        let mut registry = CertificateRegistry::new();
        let old = sample_certificate("crate::old", "2020-01-01T00:00:00Z");
        let recent = sample_certificate("crate::recent", "2026-03-28T12:00:00Z");

        registry.register(old, sample_chain()).unwrap();
        registry.register(recent, sample_chain()).unwrap();

        let policy = GcPolicy {
            max_age_secs: 365 * 86400, // 1 year
            remove_superseded: false,
            remove_revoked: false,
        };

        let removed = registry.gc(&policy);
        assert_eq!(removed.len(), 1);
        assert_eq!(registry.len(), 1);

        let remaining = registry.lookup_by_function("crate::recent");
        assert_eq!(remaining.len(), 1);
    }

    #[test]
    fn test_registry_export_import() {
        let mut registry = CertificateRegistry::new();
        let cert1 = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let cert2 = sample_certificate("crate::bar", "2026-03-27T12:01:00Z");

        let id1 = registry.register(cert1, sample_chain()).unwrap();
        registry.register(cert2, sample_chain()).unwrap();

        registry
            .revoke(
                &id1,
                RevocationReason::Manual { reason: "test".to_string() },
                "2026-03-28T00:00:00Z".to_string(),
            )
            .unwrap();

        let snapshot = registry.export_registry();
        assert_eq!(snapshot.certificates.len(), 2);
        assert_eq!(snapshot.revocations.len(), 1);

        // Import into a new registry
        let mut new_registry = CertificateRegistry::new();
        let imported = new_registry.import_registry(snapshot).unwrap();

        assert_eq!(imported, 2);
        assert_eq!(new_registry.len(), 2);
        assert!(new_registry.is_revoked(&id1));
    }

    #[test]
    fn test_registry_import_deduplicates() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        registry.register(cert, sample_chain()).unwrap();

        let snapshot = registry.export_registry();

        // Import the same snapshot again
        let imported = registry.import_registry(snapshot).unwrap();
        assert_eq!(imported, 0); // Nothing new imported
        assert_eq!(registry.len(), 1);
    }

    #[test]
    fn test_registry_stats() {
        let mut registry = CertificateRegistry::new();
        let cert1 = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let cert2 = sample_certificate("crate::bar", "2026-03-27T12:05:00Z");

        let id1 = registry.register(cert1, sample_chain()).unwrap();
        registry.register(cert2, sample_chain()).unwrap();

        registry
            .revoke(&id1, RevocationReason::FunctionModified, "2026-03-28T00:00:00Z".to_string())
            .unwrap();

        let stats = registry.stats();
        assert_eq!(stats.total_certificates, 2);
        assert_eq!(stats.valid_certificates, 1);
        assert_eq!(stats.revoked_certificates, 1);
        assert_eq!(stats.unique_functions, 2);
        assert!(stats.storage_bytes > 0);
        assert_eq!(stats.oldest_timestamp, Some("2026-03-27T12:00:00Z".to_string()));
        assert_eq!(stats.newest_timestamp, Some("2026-03-27T12:05:00Z".to_string()));
    }

    #[test]
    fn test_registry_function_names() {
        let mut registry = CertificateRegistry::new();
        registry
            .register(sample_certificate("crate::bar", "2026-03-27T12:00:00Z"), sample_chain())
            .unwrap();
        registry
            .register(sample_certificate("crate::foo", "2026-03-27T12:01:00Z"), sample_chain())
            .unwrap();

        let names = registry.function_names();
        assert_eq!(names, vec!["crate::bar", "crate::foo"]);
    }

    #[test]
    fn test_registry_is_valid_missing() {
        let registry = CertificateRegistry::new();
        let fake_id = RegistryId("nonexistent".to_string());
        assert!(!registry.is_valid(&fake_id));
    }

    #[test]
    fn test_registry_lookup_by_cert_id() {
        let mut registry = CertificateRegistry::new();
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let original_id = cert.id.clone();

        registry.register(cert.clone(), sample_chain()).unwrap();

        let found = registry.lookup_by_cert_id(&original_id).unwrap();
        assert_eq!(found, &cert);
    }
}
