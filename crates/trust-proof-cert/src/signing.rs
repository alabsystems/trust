// Trust: Ed25519 provenance signing for public certificate records
//
// A valid signature binds record bytes to a key. It does not establish that
// the signed proof claim is semantically true. Trust in a signer is supplied by
// an explicit verifier-owned policy; there is no process-global authority.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::{CertError, ProofCertificate};

/// Signer role recorded in a certificate signature.
///
/// The role is authenticated by the signature but is not itself authority. A
/// verifier-owned [`TrustAnchorPolicy`] decides whether a key/role pair is an
/// accepted provenance anchor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Solver-produced proof (ay, trust-wp, etc.). Can create Trusted certificates.
    Solver,
    /// Independent verifier (clean). Can upgrade to Certified.
    Certifier,
    /// Root trust anchor. Can sign any certificate.
    Root,
}

/// An Ed25519 signing key with an associated trust level.
pub struct CertSigningKey {
    key: SigningKey,
    trust_level: TrustLevel,
}

impl CertSigningKey {
    /// Generate a new random signing key at the given trust level.
    pub fn generate(trust_level: TrustLevel) -> Self {
        let mut rng = rand::thread_rng();
        let key = SigningKey::generate(&mut rng);
        CertSigningKey { key, trust_level }
    }

    /// Create from raw key bytes (32 bytes).
    pub fn from_bytes(bytes: &[u8; 32], trust_level: TrustLevel) -> Self {
        let key = SigningKey::from_bytes(bytes);
        CertSigningKey { key, trust_level }
    }

    /// Export the raw secret key bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }

    /// Get the trust level.
    pub fn trust_level(&self) -> TrustLevel {
        self.trust_level
    }

    /// Get the corresponding public verifying key.
    pub fn verifying_key(&self) -> CertVerifyingKey {
        CertVerifyingKey { key: self.key.verifying_key(), trust_level: self.trust_level }
    }

    /// Sign a certificate record for provenance.
    ///
    /// The signature covers every serialized record field except the signature
    /// itself. It does not replay or validate the claimed proof.
    pub fn sign(&self, cert: &ProofCertificate) -> CertificateSignature {
        let canonical = canonical_bytes(cert, self.trust_level);
        let sig = self.key.sign(&canonical);
        CertificateSignature {
            signature_bytes: sig.to_bytes().to_vec(),
            public_key_bytes: self.key.verifying_key().to_bytes().to_vec(),
            trust_level: self.trust_level,
        }
    }
}

/// An Ed25519 public verifying key with an associated trust level.
#[derive(Debug, Clone)]
pub struct CertVerifyingKey {
    key: VerifyingKey,
    trust_level: TrustLevel,
}

impl CertVerifyingKey {
    /// Create from raw public key bytes (32 bytes).
    pub fn from_bytes(bytes: &[u8; 32], trust_level: TrustLevel) -> Result<Self, CertError> {
        let key = VerifyingKey::from_bytes(bytes).map_err(|e| CertError::VerificationFailed {
            reason: format!("invalid Ed25519 public key: {e}"),
        })?;
        Ok(CertVerifyingKey { key, trust_level })
    }

    /// Get the trust level.
    pub fn trust_level(&self) -> TrustLevel {
        self.trust_level
    }

    /// Get the raw public key bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }

    /// Check a certificate signature's cryptographic integrity against this key.
    pub fn check_signature_integrity(
        &self,
        cert: &ProofCertificate,
        sig: &CertificateSignature,
    ) -> Result<(), CertError> {
        let canonical = canonical_bytes(cert, self.trust_level);
        let signature = Signature::from_slice(&sig.signature_bytes).map_err(|e| {
            CertError::VerificationFailed { reason: format!("invalid signature bytes: {e}") }
        })?;
        self.key.verify(&canonical, &signature).map_err(|e| CertError::VerificationFailed {
            reason: format!("Ed25519 signature verification failed: {e}"),
        })
    }
}

/// A cryptographic provenance signature over a certificate record's content.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateSignature {
    /// Raw Ed25519 signature bytes (64 bytes).
    pub signature_bytes: Vec<u8>,
    /// Public key of the signer (32 bytes).
    pub public_key_bytes: Vec<u8>,
    /// Signer role claimed by, and cryptographically bound to, this signature.
    pub trust_level: TrustLevel,
}

impl CertificateSignature {
    /// Check this signature's cryptographic integrity against the record.
    ///
    /// This reconstructs the key embedded in the record. Success proves only
    /// possession of that key, not that the key is trusted or the proof is true.
    pub fn check_integrity(&self, cert: &ProofCertificate) -> Result<(), CertError> {
        let pk_bytes: [u8; 32] = self.public_key_bytes.clone().try_into().map_err(|_| {
            CertError::VerificationFailed {
                reason: format!("public key must be 32 bytes, got {}", self.public_key_bytes.len()),
            }
        })?;
        let vk = CertVerifyingKey::from_bytes(&pk_bytes, self.trust_level)?;
        vk.check_signature_integrity(cert, self)
    }
}

/// Immutable verifier-owned provenance policy.
///
/// Policies are explicit values, so one test, plugin, or library caller cannot
/// mutate process-wide trust for another verification. Constructing a policy is
/// a verifier decision; it does not turn signature checking into proof replay.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TrustAnchorPolicy {
    anchors: Vec<([u8; 32], TrustLevel)>,
}

impl TrustAnchorPolicy {
    /// A fail-closed policy that accepts no provenance anchors.
    #[must_use]
    pub fn deny_all() -> Self {
        Self::default()
    }

    /// Construct a policy from explicit public-key/signer-role pairs.
    ///
    /// Duplicate pairs are removed deterministically. Public-key encoding is
    /// checked up front so malformed policy input fails before inspection.
    pub fn from_anchors(
        anchors: impl IntoIterator<Item = ([u8; 32], TrustLevel)>,
    ) -> Result<Self, CertError> {
        let mut anchors: Vec<_> = anchors.into_iter().collect();
        for (public_key, role) in &anchors {
            CertVerifyingKey::from_bytes(public_key, *role)?;
        }
        anchors.sort_unstable();
        anchors.dedup();
        Ok(Self { anchors })
    }

    /// Construct a policy from verifier-selected verifying keys.
    #[must_use]
    pub fn from_verifying_keys(keys: impl IntoIterator<Item = CertVerifyingKey>) -> Self {
        let anchors: Vec<_> =
            keys.into_iter().map(|key| (key.to_bytes(), key.trust_level())).collect();
        Self::from_anchors(anchors).expect("existing verifying keys are valid Ed25519 keys")
    }

    /// Whether this policy explicitly anchors the signature's key and role.
    #[must_use]
    pub fn anchors(&self, signature: &CertificateSignature) -> bool {
        let Ok(public_key) = <[u8; 32]>::try_from(signature.public_key_bytes.as_slice()) else {
            return false;
        };
        self.anchors.contains(&(public_key, signature.trust_level))
    }
}

/// Provenance inspection for a certificate record's optional signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SignatureProvenance {
    /// The public record carries no signature.
    Missing,
    /// The record carries a signature that does not match its content.
    Invalid { reason: String },
    /// The signature is cryptographically valid, but its key/role is not in the
    /// verifier's explicit anchor policy.
    ValidUnanchored { signer_role: TrustLevel },
    /// The signature is valid and its exact key/role pair is in the verifier's
    /// policy. This establishes provenance only, never proof truth.
    ValidAnchored { signer_role: TrustLevel },
}

/// Inspect signature integrity and provenance under an explicit policy.
#[must_use]
pub fn inspect_signature_provenance(
    cert: &ProofCertificate,
    policy: &TrustAnchorPolicy,
) -> SignatureProvenance {
    let Some(signature) = cert.signature.as_ref() else {
        return SignatureProvenance::Missing;
    };
    if let Err(error) = signature.check_integrity(cert) {
        return SignatureProvenance::Invalid { reason: error.to_string() };
    }
    if policy.anchors(signature) {
        SignatureProvenance::ValidAnchored { signer_role: signature.trust_level }
    } else {
        SignatureProvenance::ValidUnanchored { signer_role: signature.trust_level }
    }
}

/// A keystore holding signing keys at different trust levels.
pub struct Keystore {
    keys: Vec<CertSigningKey>,
}

impl Keystore {
    /// Create an empty keystore.
    pub fn new() -> Self {
        Keystore { keys: Vec::new() }
    }

    /// Add a signing key.
    pub fn add_key(&mut self, key: CertSigningKey) {
        self.keys.push(key);
    }

    /// Get the first key at the given trust level.
    pub fn key_for_level(&self, level: TrustLevel) -> Option<&CertSigningKey> {
        self.keys.iter().find(|k| k.trust_level == level)
    }

    /// Generate and add a key at the given trust level.
    pub fn generate_key(&mut self, level: TrustLevel) -> &CertSigningKey {
        self.keys.push(CertSigningKey::generate(level));
        self.keys.last().expect("just pushed")
    }

    /// Number of keys in the keystore.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Whether the keystore is empty.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }
}

impl Default for Keystore {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute deterministic bytes for provenance signing/integrity checking.
///
/// Every record field except `signature` is covered. Earlier payloads omitted
/// the chain, proof steps, trace, witness, solver strength/evidence, snapshot,
/// and certificate ID, allowing those fields to change without invalidating the
/// signature.
pub(crate) fn canonical_bytes(cert: &ProofCertificate, trust_level: TrustLevel) -> Vec<u8> {
    #[derive(Serialize)]
    struct SigningPayload<'a> {
        domain: &'static str,
        signer_role: TrustLevel,
        id: &'a crate::CertificateId,
        function: &'a str,
        function_hash: &'a crate::FunctionHash,
        vc_hash: &'a [u8; 32],
        vc_snapshot: &'a crate::VcSnapshot,
        solver: &'a crate::SolverInfo,
        proof_steps: &'a [crate::ProofStep],
        witness: &'a Option<Vec<u8>>,
        chain: &'a crate::CertificateChain,
        proof_trace: &'a [u8],
        timestamp: &'a str,
        status: crate::CertificationStatus,
        version: u32,
    }

    serde_json::to_vec(&SigningPayload {
        domain: "trust-proof-cert.provenance-signature.v2",
        signer_role: trust_level,
        id: &cert.id,
        function: &cert.function,
        function_hash: &cert.function_hash,
        vc_hash: &cert.vc_hash,
        vc_snapshot: &cert.vc_snapshot,
        solver: &cert.solver,
        proof_steps: &cert.proof_steps,
        witness: &cert.witness,
        chain: &cert.chain,
        proof_trace: &cert.proof_trace,
        timestamp: &cert.timestamp,
        status: cert.status,
        version: cert.version,
    })
    .expect("certificate signing fields have infallible serde implementations")
}

/// Sign a certificate in place, attaching the signature.
pub fn sign_certificate(cert: &mut ProofCertificate, key: &CertSigningKey) {
    cert.signature = Some(key.sign(cert));
}

/// Check a certificate record's signature integrity.
///
/// Success does not establish signer trust or proof truth. Use
/// [`inspect_signature_provenance`] with an explicit policy for provenance.
pub fn check_certificate_signature_integrity(cert: &ProofCertificate) -> Result<(), CertError> {
    match &cert.signature {
        None => Err(CertError::VerificationFailed {
            reason: "certificate has no cryptographic signature".to_string(),
        }),
        Some(sig) => sig.check_integrity(cert),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{FunctionHash, SolverInfo, VcSnapshot};

    fn make_test_cert() -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        ProofCertificate::new_trusted(
            "crate::test_fn".to_string(),
            FunctionHash::from_bytes(b"test-body"),
            vc_snapshot,
            solver,
            vec![],
            "2026-03-28T00:00:00Z".to_string(),
        )
    }

    #[test]
    fn test_sign_and_verify() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = key.sign(&cert);
        assert!(sig.check_integrity(&cert).is_ok());
    }

    #[test]
    fn test_sign_certificate_in_place() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let mut cert = make_test_cert();
        sign_certificate(&mut cert, &key);
        assert!(cert.signature.is_some());
        assert!(check_certificate_signature_integrity(&cert).is_ok());
    }

    #[test]
    fn test_unsigned_certificate_fails_verification() {
        let cert = make_test_cert();
        let result = check_certificate_signature_integrity(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("no cryptographic signature"));
    }

    #[test]
    fn test_tampered_certificate_fails_verification() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let mut cert = make_test_cert();
        let sig = key.sign(&cert);
        cert.signature = Some(sig);

        // Tamper with the function name
        cert.function = "crate::tampered_fn".to_string();

        let result = check_certificate_signature_integrity(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("signature verification failed"));
    }

    #[test]
    fn test_wrong_key_fails_verification() {
        let key1 = CertSigningKey::generate(TrustLevel::Solver);
        let key2 = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = key1.sign(&cert);

        // Verify with wrong key's public key
        let vk2 = key2.verifying_key();
        let result = vk2.check_signature_integrity(&cert, &sig);
        assert!(result.is_err());
    }

    #[test]
    fn test_keystore_basic() {
        let mut ks = Keystore::new();
        assert!(ks.is_empty());
        assert_eq!(ks.len(), 0);

        ks.generate_key(TrustLevel::Solver);
        ks.generate_key(TrustLevel::Certifier);
        assert_eq!(ks.len(), 2);

        assert!(ks.key_for_level(TrustLevel::Solver).is_some());
        assert!(ks.key_for_level(TrustLevel::Certifier).is_some());
        assert!(ks.key_for_level(TrustLevel::Root).is_none());
    }

    #[test]
    fn test_trust_levels() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let certifier_key = CertSigningKey::generate(TrustLevel::Certifier);
        let root_key = CertSigningKey::generate(TrustLevel::Root);

        assert_eq!(solver_key.trust_level(), TrustLevel::Solver);
        assert_eq!(certifier_key.trust_level(), TrustLevel::Certifier);
        assert_eq!(root_key.trust_level(), TrustLevel::Root);
    }

    #[test]
    fn test_key_serialization_roundtrip() {
        let key = CertSigningKey::generate(TrustLevel::Root);
        let bytes = key.to_bytes();
        let restored = CertSigningKey::from_bytes(&bytes, TrustLevel::Root);
        assert_eq!(key.verifying_key().to_bytes(), restored.verifying_key().to_bytes());
    }

    #[test]
    fn test_verifying_key_from_bytes() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let pk_bytes = key.verifying_key().to_bytes();
        let vk = CertVerifyingKey::from_bytes(&pk_bytes, TrustLevel::Solver);
        assert!(vk.is_ok());
    }

    #[test]
    fn test_verifying_key_from_bad_bytes() {
        let bad_bytes = [0u8; 32]; // all zeros is not a valid Ed25519 point
        // Note: all-zeros may or may not be a valid point depending on impl.
        // Use a clearly invalid approach:
        let result = CertVerifyingKey::from_bytes(&bad_bytes, TrustLevel::Solver);
        // Either succeeds or fails; just ensuring no panic
        let _ = result;
    }

    #[test]
    fn test_canonical_bytes_deterministic() {
        let cert = make_test_cert();
        let b1 = canonical_bytes(&cert, TrustLevel::Solver);
        let b2 = canonical_bytes(&cert, TrustLevel::Solver);
        assert_eq!(b1, b2);
    }

    #[test]
    fn test_canonical_bytes_differ_on_change() {
        let cert1 = make_test_cert();
        let mut cert2 = make_test_cert();
        cert2.function = "crate::other_fn".to_string();
        assert_ne!(
            canonical_bytes(&cert1, TrustLevel::Solver),
            canonical_bytes(&cert2, TrustLevel::Solver)
        );
    }

    #[test]
    fn test_canonical_bytes_differ_on_trust_level() {
        // P0-4: trust_level must affect canonical bytes
        let cert = make_test_cert();
        let solver_bytes = canonical_bytes(&cert, TrustLevel::Solver);
        let root_bytes = canonical_bytes(&cert, TrustLevel::Root);
        assert_ne!(
            solver_bytes, root_bytes,
            "different trust levels must produce different canonical bytes"
        );
    }

    #[test]
    fn test_trust_level_forgery_detected() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = solver_key.sign(&cert);

        let forged_sig = CertificateSignature { trust_level: TrustLevel::Root, ..sig.clone() };

        assert_eq!(forged_sig.signature_bytes, sig.signature_bytes);
        assert_eq!(forged_sig.public_key_bytes, sig.public_key_bytes);

        let result = forged_sig.check_integrity(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("signature verification failed"));
    }

    #[test]
    fn test_trust_level_matches_between_sign_and_verify() {
        let cert = make_test_cert();

        let root_key = CertSigningKey::generate(TrustLevel::Root);
        let root_sig = root_key.sign(&cert);
        assert!(root_sig.check_integrity(&cert).is_ok());

        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let solver_sig = solver_key.sign(&cert);
        let forged_sig =
            CertificateSignature { trust_level: TrustLevel::Root, ..solver_sig.clone() };

        let result = forged_sig.check_integrity(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("signature verification failed"));
    }

    #[test]
    fn test_signature_serde_roundtrip() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = key.sign(&cert);

        let json = serde_json::to_string(&sig).expect("should serialize");
        let restored: CertificateSignature =
            serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(sig, restored);
        assert!(restored.check_integrity(&cert).is_ok());
    }

    #[test]
    fn test_anchor_policy_is_explicit_and_isolated() {
        let key = CertSigningKey::generate(TrustLevel::Certifier);
        let mut cert = make_test_cert();
        sign_certificate(&mut cert, &key);

        let deny_all = TrustAnchorPolicy::deny_all();
        assert_eq!(
            inspect_signature_provenance(&cert, &deny_all),
            SignatureProvenance::ValidUnanchored { signer_role: TrustLevel::Certifier }
        );

        let anchored = TrustAnchorPolicy::from_verifying_keys([key.verifying_key()]);
        assert_eq!(
            inspect_signature_provenance(&cert, &anchored),
            SignatureProvenance::ValidAnchored { signer_role: TrustLevel::Certifier }
        );
        assert_eq!(
            inspect_signature_provenance(&cert, &deny_all),
            SignatureProvenance::ValidUnanchored { signer_role: TrustLevel::Certifier },
            "constructing one policy must not mutate another verifier's authority"
        );
    }

    #[test]
    fn test_policy_binds_signer_role_as_well_as_key() {
        let key = CertSigningKey::generate(TrustLevel::Certifier);
        let mut cert = make_test_cert();
        sign_certificate(&mut cert, &key);
        let wrong_role =
            TrustAnchorPolicy::from_anchors([(key.verifying_key().to_bytes(), TrustLevel::Root)])
                .unwrap();

        assert_eq!(
            inspect_signature_provenance(&cert, &wrong_role),
            SignatureProvenance::ValidUnanchored { signer_role: TrustLevel::Certifier }
        );
    }

    #[test]
    fn test_signature_covers_previously_omitted_record_fields() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let signature = key.sign(&cert);

        let mut trace_tampered = cert.clone();
        trace_tampered.proof_trace.push(0xAA);
        assert!(signature.check_integrity(&trace_tampered).is_err());

        let mut chain_tampered = cert.clone();
        chain_tampered.chain.push(crate::ChainStep {
            step_type: crate::ChainStepType::SolverProof,
            tool: "attacker".to_string(),
            tool_version: "0".to_string(),
            input_hash: "x".to_string(),
            output_hash: "y".to_string(),
            time_ms: 0,
            timestamp: cert.timestamp.clone(),
        });
        assert!(signature.check_integrity(&chain_tampered).is_err());

        let mut evidence_tampered = cert.clone();
        evidence_tampered.solver.time_ms += 1;
        assert!(signature.check_integrity(&evidence_tampered).is_err());
    }

    #[test]
    fn test_upgrade_requires_signature() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let certifier_key = CertSigningKey::generate(TrustLevel::Certifier);

        let mut cert = make_test_cert();
        // Sign with solver key first
        sign_certificate(&mut cert, &solver_key);

        // Upgrade should require Certifier or Root trust level
        let result = cert.upgrade_to_certified(&certifier_key);
        assert!(result.is_ok());
        assert_eq!(cert.status, crate::CertificationStatus::Certified);
    }

    #[test]
    fn test_upgrade_rejects_solver_level() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let mut cert = make_test_cert();
        sign_certificate(&mut cert, &solver_key);

        let result = cert.upgrade_to_certified(&solver_key);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Certifier or Root"));
    }
}
