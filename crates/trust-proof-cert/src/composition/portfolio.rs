// trust-proof-cert portfolio certificate composition
//
// Composed proof certificates from multiple verification tools.
// When the MIR router dispatches a function to multiple backends in parallel
// (portfolio racing or unsafe audit), the individual proof certificates from
// each backend are composed into a single ComposedCertificate that records
// the composition method (conjunction, disjunction, sequential).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};

/// Composed proof certificate from multiple verification tools.
///
/// Created when the MIR router's portfolio or unsafe-audit dispatch produces
/// proof certificates from multiple backends. The composed certificate records
/// each component's solver, proof hash, strategy, and timing, plus a hash
/// over all components.
#[derive(Debug, Clone)]
pub struct ComposedCertificate {
    /// Individual proof certificates from each verification backend.
    pub components: Vec<CertificateComponent>,
    /// How the component proofs were composed.
    pub composition_method: CompositionMethod,
    /// SHA-256 hash over all component proof hashes, providing a single
    /// identifier for the composed proof.
    pub composed_hash: String,
}

impl ComposedCertificate {
    /// Whether this composed certificate has any components.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    /// Total verification time across all components.
    #[must_use]
    pub fn total_time_ms(&self) -> u64 {
        self.components.iter().map(|c| c.time_ms).sum()
    }

    /// Number of components in this composition.
    #[must_use]
    pub fn component_count(&self) -> usize {
        self.components.len()
    }
}

/// A single component in a composed proof certificate.
///
/// Records which solver produced this component, the hash of its proof
/// certificate, the verification strategy used, and the wall-clock time.
#[derive(Debug, Clone)]
pub struct CertificateComponent {
    /// Name of the solver that produced this proof (e.g., "trust-mc-lib", "trust-wp-lib").
    pub solver: String,
    /// SHA-256 hash of the proof certificate bytes.
    pub proof_hash: String,
    /// The verification strategy that produced this component (e.g., "BoundedModelCheck").
    pub strategy: String,
    /// Wall-clock time for this component in milliseconds.
    pub time_ms: u64,
}

/// How multiple proof certificates are composed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompositionMethod {
    /// All components must prove (conjunction). Used by UnsafeAudit when
    /// both BMC and contract verification must agree.
    Conjunction,
    /// Any component proves (disjunction/portfolio). Used by portfolio racing
    /// where the first definitive result wins.
    Disjunction,
    /// Sequential: each component builds on the prior's result.
    Sequential,
}

impl std::fmt::Display for CompositionMethod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompositionMethod::Conjunction => f.write_str("conjunction"),
            CompositionMethod::Disjunction => f.write_str("disjunction"),
            CompositionMethod::Sequential => f.write_str("sequential"),
        }
    }
}

/// Compose proof certificates from multiple verification results.
///
/// # Arguments
///
/// * `components` - Individual certificate components from each backend.
/// * `method` - How the components should be composed.
///
/// # Returns
///
/// A `ComposedCertificate` with a deterministic hash over all components.
#[must_use]
pub fn compose_certificates(
    components: Vec<CertificateComponent>,
    method: CompositionMethod,
) -> ComposedCertificate {
    let mut hasher = Sha256::new();
    hasher.update(format!("method:{method}|").as_bytes());
    for component in &components {
        hasher.update(
            format!("{}:{}:{}|", component.solver, component.strategy, component.proof_hash,)
                .as_bytes(),
        );
    }
    let composed_hash = format!("{:x}", hasher.finalize());

    ComposedCertificate { components, composition_method: method, composed_hash }
}

/// Create a `CertificateComponent` from raw proof certificate bytes and metadata.
#[must_use]
pub fn make_component(
    solver: &str,
    strategy: &str,
    proof_bytes: &[u8],
    time_ms: u64,
) -> CertificateComponent {
    let mut hasher = Sha256::new();
    hasher.update(proof_bytes);
    let proof_hash = format!("{:x}", hasher.finalize());

    CertificateComponent {
        solver: solver.to_string(),
        proof_hash,
        strategy: strategy.to_string(),
        time_ms,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compose_empty_components() {
        let cert = compose_certificates(vec![], CompositionMethod::Disjunction);
        assert!(cert.is_empty());
        assert_eq!(cert.component_count(), 0);
        assert_eq!(cert.total_time_ms(), 0);
        assert!(!cert.composed_hash.is_empty());
    }

    #[test]
    fn test_compose_single_component() {
        let component = make_component("trust-mc-lib", "BoundedModelCheck", &[1, 2, 3], 42);
        let cert = compose_certificates(vec![component], CompositionMethod::Disjunction);

        assert!(!cert.is_empty());
        assert_eq!(cert.component_count(), 1);
        assert_eq!(cert.total_time_ms(), 42);
        assert_eq!(cert.composition_method, CompositionMethod::Disjunction);
        assert!(!cert.composed_hash.is_empty());
    }

    #[test]
    fn test_compose_multiple_components() {
        let c1 = make_component("trust-mc-lib", "BoundedModelCheck", &[1, 2, 3], 30);
        let c2 = make_component("trust-wp-lib", "ContractVerification", &[4, 5, 6], 50);
        let cert = compose_certificates(vec![c1, c2], CompositionMethod::Conjunction);

        assert_eq!(cert.component_count(), 2);
        assert_eq!(cert.total_time_ms(), 80);
        assert_eq!(cert.composition_method, CompositionMethod::Conjunction);
        assert_eq!(cert.components[0].solver, "trust-mc-lib");
        assert_eq!(cert.components[1].solver, "trust-wp-lib");
    }

    #[test]
    fn test_compose_deterministic_hash() {
        let c1 = make_component("trust-mc-lib", "BoundedModelCheck", &[1, 2, 3], 30);
        let c2 = make_component("trust-wp-lib", "ContractVerification", &[4, 5, 6], 50);
        let cert_a =
            compose_certificates(vec![c1.clone(), c2.clone()], CompositionMethod::Conjunction);
        let cert_b = compose_certificates(vec![c1, c2], CompositionMethod::Conjunction);
        assert_eq!(cert_a.composed_hash, cert_b.composed_hash);
    }

    #[test]
    fn test_different_methods_produce_different_hashes() {
        let c1 = make_component("trust-mc-lib", "BoundedModelCheck", &[1, 2, 3], 30);
        let cert_conj = compose_certificates(vec![c1.clone()], CompositionMethod::Conjunction);
        let cert_disj = compose_certificates(vec![c1], CompositionMethod::Disjunction);
        assert_ne!(cert_conj.composed_hash, cert_disj.composed_hash);
    }

    #[test]
    fn test_make_component_deterministic() {
        let a = make_component("ay", "SMT", &[10, 20, 30], 100);
        let b = make_component("ay", "SMT", &[10, 20, 30], 100);
        assert_eq!(a.proof_hash, b.proof_hash);
        assert_eq!(a.solver, b.solver);
    }

    #[test]
    fn test_composition_method_display() {
        assert_eq!(CompositionMethod::Conjunction.to_string(), "conjunction");
        assert_eq!(CompositionMethod::Disjunction.to_string(), "disjunction");
        assert_eq!(CompositionMethod::Sequential.to_string(), "sequential");
    }
}
