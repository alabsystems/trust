// trust-proof-cert serialization
//
// Serialize/deserialize ProofChains to portable formats.
// Supports JSON (human-readable) and binary (compact, bincode).
// Includes format versioning for evolution.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use crate::CertError;
use crate::chain_verifier::ProofChain;

/// Magic bytes for binary proof chain files.
const CHAIN_MAGIC: &[u8; 4] = b"tRCH";

/// Binary format version for proof chains.
const CHAIN_BINARY_VERSION: u8 = 1;

/// Envelope wrapping a ProofChain with metadata for portable serialization.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub(crate) struct ProofChainEnvelope {
    /// Format identifier.
    pub format: String,
    /// Format version number.
    pub format_version: u32,
    /// The proof chain data.
    pub chain: ProofChain,
    // Trust: BTreeMap for deterministic certificate output
    /// Optional metadata (e.g., build hash, toolchain version).
    pub metadata: BTreeMap<String, String>,
}

impl ProofChainEnvelope {
    /// Create a new envelope wrapping a proof chain.
    pub fn new(chain: ProofChain) -> Self {
        ProofChainEnvelope {
            format: "trust-proof-chain".to_string(),
            format_version: 1,
            chain,
            metadata: BTreeMap::new(),
        }
    }
}

#[cfg(test)]
impl ProofChainEnvelope {
    /// Add metadata key-value pair.
    #[must_use]
    fn with_metadata(mut self, key: &str, value: &str) -> Self {
        self.metadata.insert(key.to_string(), value.to_string());
        self
    }
}

// ---------------------------------------------------------------------------
// JSON serialization
// ---------------------------------------------------------------------------

/// Serialize a ProofChain to pretty-printed JSON.
pub fn to_json(chain: &ProofChain) -> Result<String, CertError> {
    let envelope = ProofChainEnvelope::new(chain.clone());
    serde_json::to_string_pretty(&envelope)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
}

/// Deserialize a ProofChain from JSON.
pub fn from_json(json: &str) -> Result<ProofChain, CertError> {
    let envelope: ProofChainEnvelope = serde_json::from_str(json)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

    if envelope.format != "trust-proof-chain" {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "unexpected format: expected 'trust-proof-chain', got '{}'",
                envelope.format
            ),
        });
    }

    Ok(envelope.chain)
}

/// Serialize a ProofChain to compact JSON (no whitespace).
#[cfg(test)]
pub(crate) fn to_json_compact(chain: &ProofChain) -> Result<String, CertError> {
    let envelope = ProofChainEnvelope::new(chain.clone());
    serde_json::to_string(&envelope)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
}

// ---------------------------------------------------------------------------
// Binary serialization
// ---------------------------------------------------------------------------

/// Serialize a ProofChain to binary format.
///
/// Format: `MAGIC (4 bytes) | VERSION (1 byte) | bincode payload`
pub fn to_binary(chain: &ProofChain) -> Result<Vec<u8>, CertError> {
    let envelope = ProofChainEnvelope::new(chain.clone());
    let payload = bincode::serialize(&envelope)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

    let mut bytes = Vec::with_capacity(CHAIN_MAGIC.len() + 1 + payload.len());
    bytes.extend_from_slice(CHAIN_MAGIC);
    bytes.push(CHAIN_BINARY_VERSION);
    bytes.extend_from_slice(&payload);
    Ok(bytes)
}

/// Deserialize a ProofChain from binary format.
pub fn from_binary(bytes: &[u8]) -> Result<ProofChain, CertError> {
    let header_len = CHAIN_MAGIC.len() + 1;
    if bytes.len() < header_len {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "binary too short: expected at least {header_len} bytes, got {}",
                bytes.len()
            ),
        });
    }

    if &bytes[..CHAIN_MAGIC.len()] != CHAIN_MAGIC {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "invalid magic bytes: expected {:?}, got {:?}",
                CHAIN_MAGIC,
                &bytes[..CHAIN_MAGIC.len()]
            ),
        });
    }

    let version = bytes[CHAIN_MAGIC.len()];
    if version != CHAIN_BINARY_VERSION {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "unsupported binary format version: expected {CHAIN_BINARY_VERSION}, got {version}"
            ),
        });
    }

    let payload = &bytes[header_len..];
    let envelope: ProofChainEnvelope = bincode::deserialize(payload)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

    Ok(envelope.chain)
}

// ---------------------------------------------------------------------------
// File I/O helpers
// ---------------------------------------------------------------------------

/// Save a ProofChain to a JSON file.
#[cfg(test)]
pub(crate) fn save_json(
    chain: &ProofChain,
    path: impl AsRef<std::path::Path>,
) -> Result<(), CertError> {
    let json = to_json(chain)?;
    std::fs::write(path, json)?;
    Ok(())
}

/// Load a ProofChain from a JSON file.
#[cfg(test)]
pub(crate) fn load_json(path: impl AsRef<std::path::Path>) -> Result<ProofChain, CertError> {
    let json = std::fs::read_to_string(path)?;
    from_json(&json)
}

/// Save a ProofChain to a binary file.
#[cfg(test)]
pub(crate) fn save_binary(
    chain: &ProofChain,
    path: impl AsRef<std::path::Path>,
) -> Result<(), CertError> {
    let bytes = to_binary(chain)?;
    std::fs::write(path, bytes)?;
    Ok(())
}

/// Load a ProofChain from a binary file.
#[cfg(test)]
pub(crate) fn load_binary(path: impl AsRef<std::path::Path>) -> Result<ProofChain, CertError> {
    let bytes = std::fs::read(path)?;
    from_binary(&bytes)
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::{FunctionHash, SolverInfo, VcSnapshot};

    fn sample_solver() -> SolverInfo {
        SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "test".to_string() },
            function: function.into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 10,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_cert(function: &str) -> crate::ProofCertificate {
        let vc = sample_vc(function);
        let snapshot = VcSnapshot::from_vc(&vc).expect("snapshot");
        crate::ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            snapshot,
            sample_solver(),
            vec![1, 2, 3],
            "2026-03-29T00:00:00Z".to_string(),
        )
    }

    fn sample_chain() -> ProofChain {
        let mut chain = ProofChain::new("test-crate");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec![]);
        chain
    }

    #[test]
    fn test_json_roundtrip() {
        let chain = sample_chain();
        let json = to_json(&chain).expect("serialization should succeed");
        let restored = from_json(&json).expect("deserialization should succeed");

        assert_eq!(restored.name, chain.name);
        assert_eq!(restored.len(), chain.len());
        assert_eq!(restored.recorded_functions(), chain.recorded_functions());
    }

    #[test]
    fn test_json_compact_roundtrip() {
        let chain = sample_chain();
        let json = to_json_compact(&chain).expect("serialization");
        let restored = from_json(&json).expect("deserialization");
        assert_eq!(restored.name, chain.name);
        assert_eq!(restored.len(), chain.len());
    }

    #[test]
    fn test_binary_roundtrip() {
        let chain = sample_chain();
        let bytes = to_binary(&chain).expect("serialization");
        let restored = from_binary(&bytes).expect("deserialization");

        assert_eq!(restored.name, chain.name);
        assert_eq!(restored.len(), chain.len());
        assert_eq!(restored.recorded_functions(), chain.recorded_functions());
    }

    #[test]
    fn test_binary_magic_bytes() {
        let chain = sample_chain();
        let bytes = to_binary(&chain).expect("serialization");
        assert_eq!(&bytes[..4], b"tRCH");
        assert_eq!(bytes[4], 1);
    }

    #[test]
    fn test_binary_too_short() {
        let err = from_binary(b"tR").expect_err("should fail");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("too short"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn test_binary_wrong_magic() {
        let err = from_binary(b"XXXX\x01data").expect_err("should fail");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("invalid magic"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn test_binary_wrong_version() {
        let err = from_binary(b"tRCH\x99data").expect_err("should fail");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("unsupported"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn test_json_wrong_format() {
        let json = r#"{"format":"wrong","format_version":1,"chain":{},"metadata":{}}"#;
        let err = from_json(json).expect_err("should fail on wrong format");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("unexpected format") || reason.contains("missing field"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn test_envelope_metadata() {
        let chain = sample_chain();
        let envelope = ProofChainEnvelope::new(chain)
            .with_metadata("build_hash", "abc123")
            .with_metadata("toolchain", "nightly-2026-03-29");

        assert_eq!(envelope.metadata.get("build_hash"), Some(&"abc123".to_string()));
        assert_eq!(envelope.metadata.get("toolchain"), Some(&"nightly-2026-03-29".to_string()));
    }

    #[test]
    fn test_file_json_roundtrip() {
        let chain = sample_chain();
        let path =
            std::env::temp_dir().join(format!("trust-chain-json-{}.json", std::process::id()));
        let _ = std::fs::remove_file(&path);

        save_json(&chain, &path).expect("save should succeed");
        let loaded = load_json(&path).expect("load should succeed");

        assert_eq!(loaded.name, chain.name);
        assert_eq!(loaded.len(), chain.len());

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_file_binary_roundtrip() {
        let chain = sample_chain();
        let path = std::env::temp_dir().join(format!("trust-chain-bin-{}.bin", std::process::id()));
        let _ = std::fs::remove_file(&path);

        save_binary(&chain, &path).expect("save should succeed");
        let loaded = load_binary(&path).expect("load should succeed");

        assert_eq!(loaded.name, chain.name);
        assert_eq!(loaded.len(), chain.len());

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_empty_chain_serialization() {
        let chain = ProofChain::new("empty");

        // JSON
        let json = to_json(&chain).expect("json");
        let restored = from_json(&json).expect("from json");
        assert!(restored.is_empty());

        // Binary
        let bytes = to_binary(&chain).expect("binary");
        let restored = from_binary(&bytes).expect("from binary");
        assert!(restored.is_empty());
    }

    #[test]
    fn test_json_binary_equivalence() {
        let chain = sample_chain();

        let from_json_chain = {
            let json = to_json(&chain).expect("json");
            from_json(&json).expect("from json")
        };

        let from_bin_chain = {
            let bytes = to_binary(&chain).expect("binary");
            from_binary(&bytes).expect("from binary")
        };

        // Both should produce equivalent chains
        assert_eq!(from_json_chain.name, from_bin_chain.name);
        assert_eq!(from_json_chain.len(), from_bin_chain.len());
        assert_eq!(from_json_chain.recorded_functions(), from_bin_chain.recorded_functions());
    }
}
