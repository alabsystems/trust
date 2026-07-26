use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::CertificateChain;
use crate::signing::{CertSigningKey, CertificateSignature, TrustLevel};

/// Unique identifier for a proof certificate.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CertificateId(pub String);

impl CertificateId {
    /// Generate a new ID from components.
    pub fn generate(function: &str, timestamp: &str) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(function.as_bytes());
        hasher.update(b":");
        hasher.update(timestamp.as_bytes());
        let hash = hasher.finalize();
        CertificateId(format!("{hash:x}"))
    }
}

/// What solver/prover produced the proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverInfo {
    /// Solver name (e.g. "ay", "trust-wp", "clean").
    pub name: String,
    /// Solver version.
    pub version: String,
    /// Time spent solving in milliseconds.
    pub time_ms: u64,
    /// Proof strength from trust-types.
    pub strength: trust_types::ProofStrength,
    /// Proof evidence (reasoning + assurance) derived from `strength`.
    /// Note: no `skip_serializing_if` — SolverInfo goes through bincode (positional format)
    /// where skipping fields causes deserialization failures.
    pub evidence: Option<trust_types::ProofEvidence>,
}

/// Producer-reported certification status carried by a public record.
///
/// This enum is constructible and deserializable. Neither variant is an
/// acceptance verdict; consumers must replay the exact evidence under their own
/// policy before granting proof authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CertificationStatus {
    /// Producer reports a solver result with no independent kernel replay.
    Trusted,
    /// Producer claims a clean-kernel check occurred. The claim and optional
    /// signature are provenance metadata until the exact payload is rechecked.
    Certified,
}

/// SHA-256 hash of the function body (MIR or source).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FunctionHash(pub String);

impl FunctionHash {
    /// Compute hash from raw bytes (e.g. serialized MIR).
    pub fn from_bytes(data: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(data);
        FunctionHash(format!("{:x}", hasher.finalize()))
    }
}

/// Snapshot of the verification condition at proof time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcSnapshot {
    /// The VC kind tag.
    pub kind: String,
    /// Serialized formula (JSON string).
    pub formula_json: String,
    /// Source location.
    pub location: Option<SourceLocation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceLocation {
    pub file: String,
    pub line_start: u32,
    pub col_start: u32,
    pub line_end: u32,
    pub col_end: u32,
}

impl VcSnapshot {
    /// Create from a trust-types VerificationCondition.
    pub fn from_vc(vc: &trust_types::VerificationCondition) -> Result<Self, crate::CertError> {
        let kind = format!("{:?}", vc.kind);
        let formula_json = serde_json::to_string(&vc.formula)
            .map_err(|e| crate::CertError::SerializationFailed { reason: e.to_string() })?;
        let location = if vc.location.file.is_empty() {
            None
        } else {
            Some(SourceLocation {
                file: vc.location.file.clone(),
                line_start: vc.location.line_start,
                col_start: vc.location.col_start,
                line_end: vc.location.line_end,
                col_end: vc.location.col_end,
            })
        };
        Ok(VcSnapshot { kind, formula_json, location })
    }

    /// Compute the SHA-256 hash of the canonical VC bytes (JSON encoding).
    pub fn vc_hash(&self) -> [u8; 32] {
        // Canonical form: kind + formula_json, deterministic ordering
        let mut hasher = Sha256::new();
        hasher.update(self.kind.as_bytes());
        hasher.update(b":");
        hasher.update(self.formula_json.as_bytes());
        hasher.finalize().into()
    }
}

/// A single step in the solver's reasoning trace.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofStep {
    /// Step index in the proof sequence.
    pub index: u32,
    /// Rule or tactic applied (e.g. "resolution", "unit-propagation", "split").
    pub rule: String,
    /// Human-readable description of what this step does.
    pub description: String,
    /// Premises: indices of prior steps this step depends on.
    pub premises: Vec<u32>,
}

/// A public certificate record containing proof claims and provenance metadata.
///
/// Hashes, chains, steps, signatures, and status fields can be checked for
/// internal consistency, but this generic record does not provide a rule
/// semantics/replay engine. Record integrity must not be treated as proof truth.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofCertificate {
    /// Unique certificate ID.
    pub id: CertificateId,
    /// Function that was verified.
    pub function: String,
    /// Hash of the function body at proof time.
    pub function_hash: FunctionHash,
    /// SHA-256 hash of the canonical VC bytes.
    pub vc_hash: [u8; 32],
    /// Snapshot of the verification condition.
    pub vc_snapshot: VcSnapshot,
    /// Solver information.
    pub solver: SolverInfo,
    /// Structured proof steps from the solver's reasoning trace.
    pub proof_steps: Vec<ProofStep>,
    /// Witness bytes for existential proofs (e.g. satisfying assignment).
    pub witness: Option<Vec<u8>>,
    /// Certificate chain linking VC generation through solver to result.
    pub chain: CertificateChain,
    /// Opaque proof trace bytes from the solver.
    pub proof_trace: Vec<u8>,
    /// ISO 8601 timestamp when this certificate was generated.
    pub timestamp: String,
    /// Certification status.
    pub status: CertificationStatus,
    /// Format version for forward compatibility.
    pub version: u32,
    /// Ed25519 cryptographic signature over canonical certificate content.
    /// Prevents forgery by binding the certificate to a signing key.
    #[serde(default)]
    pub signature: Option<CertificateSignature>,
}

/// Current certificate format version.
pub const CERT_FORMAT_VERSION: u32 = 2;

impl ProofCertificate {
    /// Create a new solver-result certificate record.
    ///
    /// `Trusted` is producer metadata, not verifier-granted authority.
    pub fn new_trusted(
        function: String,
        function_hash: FunctionHash,
        vc_snapshot: VcSnapshot,
        solver: SolverInfo,
        proof_trace: Vec<u8>,
        timestamp: String,
    ) -> Self {
        let vc_hash = vc_snapshot.vc_hash();
        let id = CertificateId::generate(&function, &timestamp);
        ProofCertificate {
            id,
            function,
            function_hash,
            vc_hash,
            vc_snapshot,
            solver,
            proof_steps: Vec::new(),
            witness: None,
            chain: CertificateChain::new(),
            proof_trace,
            timestamp,
            status: CertificationStatus::Trusted,
            version: CERT_FORMAT_VERSION,
            signature: None,
        }
    }

    /// Builder method: attach proof steps.
    #[must_use]
    pub fn with_proof_steps(mut self, steps: Vec<ProofStep>) -> Self {
        self.proof_steps = steps;
        self
    }

    /// Builder method: attach a witness for existential proofs.
    #[must_use]
    pub fn with_witness(mut self, witness: Vec<u8>) -> Self {
        self.witness = Some(witness);
        self
    }

    /// Builder method: attach a certificate chain.
    #[must_use]
    pub fn with_chain(mut self, chain: CertificateChain) -> Self {
        self.chain = chain;
        self
    }

    /// Attach a signed `Certified` producer claim.
    ///
    /// Requires a key labeled Certifier or Root and binds the record content to
    /// that key. This method cannot establish that clean verification happened;
    /// a consumer must apply explicit anchor policy and replay the exact kernel
    /// payload before granting authority.
    pub fn upgrade_to_certified(
        &mut self,
        certifier_key: &CertSigningKey,
    ) -> Result<(), crate::CertError> {
        match certifier_key.trust_level() {
            TrustLevel::Certifier | TrustLevel::Root => {}
            TrustLevel::Solver => {
                return Err(crate::CertError::VerificationFailed {
                    reason: "upgrade_to_certified requires Certifier or Root trust level"
                        .to_string(),
                });
            }
        }
        self.status = CertificationStatus::Certified;
        // Re-sign with the certifier key to bind the new status
        self.signature = Some(certifier_key.sign(self));
        Ok(())
    }

    /// Check if the function hash still matches (staleness detection).
    pub fn is_fresh_for(&self, current_hash: &FunctionHash) -> bool {
        self.function_hash == *current_hash
    }

    /// Verify that the stored vc_hash matches the VC snapshot.
    pub fn verify_vc_hash(&self) -> bool {
        self.vc_hash == self.vc_snapshot.vc_hash()
    }

    /// Verify that the stored vc_hash matches the given canonical VC bytes.
    ///
    /// **Note:** The bytes must be in canonical format: `kind:formula_json`,
    /// matching the encoding used by [`VcSnapshot::vc_hash`]. For type-safe verification,
    /// prefer [`Self::verify_vc_hash_with_snapshot`].
    pub fn verify_vc_hash_against(&self, vc_bytes: &[u8]) -> bool {
        let mut hasher = Sha256::new();
        hasher.update(vc_bytes);
        let computed: [u8; 32] = hasher.finalize().into();
        self.vc_hash == computed
    }

    /// P1-14: Type-safe VC hash verification using a VcSnapshot.
    ///
    /// Compares the stored vc_hash against the hash of the given VcSnapshot,
    /// using the same canonical encoding as certificate generation.
    pub fn verify_vc_hash_with_snapshot(&self, snapshot: &VcSnapshot) -> bool {
        self.vc_hash == snapshot.vc_hash()
    }

    /// Check that proof-step records have a well-formed index/reference shape:
    /// - Indices are sequential starting from 0.
    /// - All premise references point to earlier steps.
    pub fn check_proof_step_shape(&self) -> Result<(), crate::CertError> {
        for (i, step) in self.proof_steps.iter().enumerate() {
            let expected = i as u32;
            if step.index != expected {
                return Err(crate::CertError::VerificationFailed {
                    reason: format!(
                        "proof step index mismatch: expected {expected}, got {}",
                        step.index
                    ),
                });
            }
            for &premise in &step.premises {
                if premise >= expected {
                    return Err(crate::CertError::VerificationFailed {
                        reason: format!(
                            "proof step {expected} references non-earlier premise {premise}"
                        ),
                    });
                }
            }
        }
        Ok(())
    }

    /// Serialize to JSON string.
    pub fn to_json(&self) -> Result<String, crate::CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| crate::CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON string.
    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        serde_json::from_str(json)
            .map_err(|e| crate::CertError::SerializationFailed { reason: e.to_string() })
    }
}
