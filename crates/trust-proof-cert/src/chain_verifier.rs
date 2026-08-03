// trust-proof-cert chain verifier
//
// Inspects ProofChain structure: record integrity, dependency gaps, cycles,
// and structural coverage. Public chain metadata does not establish proof
// soundness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::dep_graph::DepGraph;
use crate::{ChainValidator, ProofCertificate};

/// A public/serializable collection of certificate and call-graph metadata.
///
/// The records claim properties about functions, but this type carries neither
/// exact caller/callee obligation bindings nor replay authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofChain {
    // Trust: BTreeMap for deterministic certificate output
    /// Certificates in this chain, keyed by function name.
    pub certificates: BTreeMap<String, ProofCertificate>,
    /// Call graph edges: caller -> list of callees.
    pub call_graph: BTreeMap<String, Vec<String>>,
    /// Name of this proof chain (e.g., crate name).
    pub name: String,
    /// Format version for serialization compatibility.
    pub version: u32,
}

/// Current proof chain format version.
pub const PROOF_CHAIN_VERSION: u32 = 1;

impl ProofChain {
    /// Create a new empty proof chain.
    pub fn new(name: &str) -> Self {
        ProofChain {
            certificates: BTreeMap::new(),
            call_graph: BTreeMap::new(),
            name: name.to_string(),
            version: PROOF_CHAIN_VERSION,
        }
    }

    /// Add a certificate with its callee dependencies.
    pub fn add_certificate(&mut self, cert: ProofCertificate, callees: Vec<String>) {
        let function = cert.function.clone();
        self.call_graph.insert(function.clone(), callees);
        self.certificates.insert(function, cert);
    }

    /// Get a certificate by function name.
    pub fn get_certificate(&self, function: &str) -> Option<&ProofCertificate> {
        self.certificates.get(function)
    }

    /// Return all function names that have public certificate records.
    ///
    /// Record presence is not a proof-validity claim.
    pub fn recorded_functions(&self) -> Vec<String> {
        self.certificates.keys().cloned().collect()
    }

    /// Return the number of certificates in the chain.
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Return true if the chain has no certificates.
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }

    /// Build a dependency graph from this chain's call graph.
    ///
    /// `DepNode::has_record` means only that a public certificate record is
    /// present. Use `verify_proof_chain` for integrity diagnostics; neither API
    /// grants proof authority.
    pub fn to_dep_graph(&self) -> DepGraph {
        let present: BTreeSet<String> = self.certificates.keys().cloned().collect();
        self.to_dep_graph_with_records(&present)
    }

    fn all_functions(&self) -> BTreeSet<String> {
        self.call_graph
            .keys()
            .cloned()
            .chain(self.call_graph.values().flatten().cloned())
            .chain(self.certificates.keys().cloned())
            .collect()
    }

    fn to_dep_graph_with_records(&self, records: &BTreeSet<String>) -> DepGraph {
        let mut graph = DepGraph::new();
        for func in self.all_functions() {
            let callees = self.call_graph.get(&func).cloned().unwrap_or_default();
            graph.add_function(&func, callees, records.contains(&func));
        }

        graph
    }
}

/// Result of verifying a proof chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChainVerificationResult {
    /// Whether the chain is proof-authoritatively sound.
    ///
    /// Private and forced to `false`, including during deserialization: public
    /// records cannot claim this capability.
    #[serde(default, skip_deserializing)]
    sound: bool,
    /// Whether the record graph is non-empty, format-valid, acyclic, complete,
    /// and internally self-consistent. This is diagnostic only.
    #[serde(default)]
    pub structurally_complete: bool,
    /// Functions whose internally valid records have structurally covered
    /// transitive dependencies. This is not semantic discharge.
    pub structurally_covered: Vec<String>,
    /// Gaps: functions present in the graph but without certificate records.
    pub gaps: Vec<ChainGap>,
    /// Certificate records that failed internal integrity checks.
    pub invalid_certs: Vec<String>,
    /// Circular dependencies detected (if any).
    pub cycles: Vec<Vec<String>>,
    /// Fraction of graph functions with internally valid records (0.0 - 1.0).
    pub integrity_valid_record_coverage: f64,
    /// Total number of functions in the call graph.
    pub total_functions: usize,
    /// Number of functions with internally valid certificate records.
    pub integrity_valid_count: usize,
    /// Whether the serialized proof-chain format version is recognized.
    #[serde(default)]
    pub format_valid: bool,
}

impl ChainVerificationResult {
    /// Proof-authoritative soundness. Always `false` for this metadata-only API.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        self.sound
    }
}

/// A structural gap in the record graph.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainGap {
    /// The function that is missing a certificate record.
    pub function: String,
    /// Functions that reference this missing function.
    pub depended_on_by: Vec<String>,
}

/// Inspect proof-chain structure without granting proof authority.
///
/// Structural completeness requires recognized format metadata, internally
/// consistent records, no missing graph nodes, no cycles, and transitive record
/// coverage. These checks do not bind exact caller assumptions to callee
/// guarantees and do not replay proofs, so `is_sound()` always returns false.
pub fn verify_proof_chain(chain: &ProofChain) -> ChainVerificationResult {
    let all_functions = chain.all_functions();
    let format_valid = chain.version == PROOF_CHAIN_VERSION;

    // Check each record's public integrity metadata. This deliberately does
    // not imply proof replay or trusted provenance.
    let mut invalid_certs = Vec::new();
    for (function, cert) in &chain.certificates {
        if cert.function != *function
            || !cert.verify_vc_hash()
            || !ChainValidator::validate(&cert.chain).valid
        {
            invalid_certs.push(function.clone());
        }
    }
    invalid_certs.sort();
    let invalid_set: BTreeSet<&str> = invalid_certs.iter().map(String::as_str).collect();
    let integrity_valid: BTreeSet<String> = chain
        .certificates
        .keys()
        .filter(|function| !invalid_set.contains(function.as_str()))
        .cloned()
        .collect();

    let dep_graph = chain.to_dep_graph_with_records(&integrity_valid);
    let sccs = dep_graph.find_sccs();

    // Find every absent record, including a root/caller that appears only as a
    // call-graph key. Build reverse edges once for deterministic diagnostics.
    let mut depended_on_by: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (caller, callees) in &chain.call_graph {
        for callee in callees {
            depended_on_by.entry(callee.clone()).or_default().insert(caller.clone());
        }
    }
    let gaps: Vec<ChainGap> = all_functions
        .iter()
        .filter(|function| !chain.certificates.contains_key(*function))
        .map(|function| ChainGap {
            function: function.clone(),
            depended_on_by: depended_on_by
                .get(function)
                .map(|callers| callers.iter().cloned().collect())
                .unwrap_or_default(),
        })
        .collect();

    // Extract cycles from SCCs
    let cycles: Vec<Vec<String>> = sccs
        .iter()
        .filter(|scc| {
            scc.is_recursive()
                || scc.functions.first().is_some_and(|function| {
                    chain.call_graph.get(function).is_some_and(|callees| callees.contains(function))
                })
        })
        .map(|scc| scc.functions.clone())
        .collect();

    // Fixed point over integrity-valid records. Unlike the legacy one-hop
    // calculation, a caller is covered only when every transitive callee is
    // already covered.
    let mut covered: BTreeSet<String> = BTreeSet::new();
    loop {
        let before = covered.len();
        for function in &integrity_valid {
            let callees = chain.call_graph.get(function).map(Vec::as_slice).unwrap_or(&[]);
            if callees.iter().all(|callee| covered.contains(callee)) {
                covered.insert(function.clone());
            }
        }
        if covered.len() == before {
            break;
        }
    }
    let structurally_covered: Vec<String> = covered.into_iter().collect();

    let total_functions = all_functions.len();
    let integrity_valid_count = integrity_valid.len();

    let integrity_valid_record_coverage = if total_functions == 0 {
        0.0
    } else {
        integrity_valid_count as f64 / total_functions as f64
    };

    let structurally_complete = total_functions > 0
        && format_valid
        && gaps.is_empty()
        && invalid_certs.is_empty()
        && cycles.is_empty()
        && structurally_covered.len() == total_functions;

    ChainVerificationResult {
        sound: false,
        structurally_complete,
        structurally_covered,
        gaps,
        invalid_certs,
        cycles,
        integrity_valid_record_coverage,
        total_functions,
        integrity_valid_count,
        format_valid,
    }
}

/// Quick structural-completeness check.
///
/// `true` is a graph/integrity diagnostic only, never proof soundness.
pub fn is_chain_complete(chain: &ProofChain) -> bool {
    let result = verify_proof_chain(chain);
    result.structurally_complete
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::{ChainStep, ChainStepType, FunctionHash, SolverInfo, VcSnapshot};

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

    fn make_cert(function: &str) -> ProofCertificate {
        let vc = sample_vc(function);
        let snapshot = VcSnapshot::from_vc(&vc).expect("snapshot");
        let mut cert = ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            snapshot,
            sample_solver(),
            vec![1, 2, 3],
            "2026-03-29T00:00:00Z".to_string(),
        );
        cert.chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "source".to_string(),
            output_hash: "vc".to_string(),
            time_ms: 1,
            timestamp: cert.timestamp.clone(),
        });
        cert.chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc".to_string(),
            output_hash: "proof".to_string(),
            time_ms: 1,
            timestamp: cert.timestamp.clone(),
        });
        cert
    }

    #[test]
    fn test_proof_chain_new() {
        let chain = ProofChain::new("my-crate");
        assert!(chain.is_empty());
        assert_eq!(chain.len(), 0);
        assert_eq!(chain.name, "my-crate");
        assert_eq!(chain.version, PROOF_CHAIN_VERSION);
    }

    #[test]
    fn test_proof_chain_add_certificate() {
        let mut chain = ProofChain::new("test");
        let cert = make_cert("foo");
        chain.add_certificate(cert.clone(), vec!["bar".to_string()]);

        assert_eq!(chain.len(), 1);
        assert!(!chain.is_empty());
        assert_eq!(chain.recorded_functions(), vec!["foo"]);
        assert_eq!(chain.get_certificate("foo"), Some(&cert));
    }

    #[test]
    fn test_verify_complete_chain() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec![]);

        let result = verify_proof_chain(&chain);
        assert!(!result.is_sound());
        assert!(result.structurally_complete, "chain metadata should be complete: {result:?}");
        assert!(result.gaps.is_empty());
        assert!(result.invalid_certs.is_empty());
        assert!(result.cycles.is_empty());
        assert_eq!(result.total_functions, 2);
        assert_eq!(result.integrity_valid_count, 2);
        assert!((result.integrity_valid_record_coverage - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_verify_chain_with_gap() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        // bar is missing

        let result = verify_proof_chain(&chain);
        assert!(!result.is_sound());
        assert!(!result.structurally_complete);
        assert_eq!(result.gaps.len(), 1);
        assert_eq!(result.gaps[0].function, "bar");
        assert_eq!(result.gaps[0].depended_on_by, vec!["foo"]);
    }

    #[test]
    fn test_verify_chain_with_cycle() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec!["foo".to_string()]);

        let result = verify_proof_chain(&chain);
        assert!(!result.is_sound());
        assert!(!result.structurally_complete);
        assert!(!result.cycles.is_empty());
    }

    #[test]
    fn test_verify_chain_with_invalid_cert() {
        let mut chain = ProofChain::new("test");
        let mut bad_cert = make_cert("foo");
        bad_cert.vc_hash[0] ^= 0xFF; // corrupt
        chain.add_certificate(bad_cert, vec![]);

        let result = verify_proof_chain(&chain);
        assert!(!result.is_sound());
        assert!(!result.structurally_complete);
        assert_eq!(result.invalid_certs, vec!["foo"]);
    }

    #[test]
    fn test_verify_empty_chain() {
        let chain = ProofChain::new("test");
        let result = verify_proof_chain(&chain);
        assert!(!result.is_sound());
        assert!(!result.structurally_complete);
        assert_eq!(result.total_functions, 0);
        assert!((result.integrity_valid_record_coverage - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_is_chain_complete() {
        let mut complete = ProofChain::new("test");
        complete.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        complete.add_certificate(make_cert("bar"), vec![]);
        assert!(is_chain_complete(&complete));

        let mut incomplete = ProofChain::new("test");
        incomplete.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        assert!(!is_chain_complete(&incomplete));
    }

    #[test]
    fn test_proof_chain_to_dep_graph() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("a"), vec!["b".to_string(), "c".to_string()]);
        chain.add_certificate(make_cert("b"), vec!["c".to_string()]);
        chain.add_certificate(make_cert("c"), vec![]);

        let graph = chain.to_dep_graph();
        assert_eq!(graph.len(), 3);

        let a = graph.get_node("a").expect("a should exist");
        assert!(a.has_record);
        assert_eq!(a.callees.len(), 2);
    }

    #[test]
    fn test_verify_chain_multiple_gaps() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(
            make_cert("main"),
            vec!["helper_a".to_string(), "helper_b".to_string()],
        );

        let result = verify_proof_chain(&chain);
        assert!(!result.is_sound());
        assert!(!result.structurally_complete);
        assert_eq!(result.gaps.len(), 2);
        let gap_names: Vec<&str> = result.gaps.iter().map(|g| g.function.as_str()).collect();
        assert!(gap_names.contains(&"helper_a"));
        assert!(gap_names.contains(&"helper_b"));
    }

    #[test]
    fn test_verify_chain_structurally_covered_functions() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec![]);

        let result = verify_proof_chain(&chain);
        // Both are structurally covered: bar is a leaf and foo points to bar.
        assert!(result.structurally_covered.contains(&"bar".to_string()));
        assert!(result.structurally_covered.contains(&"foo".to_string()));
    }

    #[test]
    fn test_verify_chain_partial_structural_coverage() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string(), "baz".to_string()]);
        chain.add_certificate(make_cert("bar"), vec![]);
        // baz is missing

        let result = verify_proof_chain(&chain);
        // bar is structurally covered; foo is not because baz is missing.
        assert!(result.structurally_covered.contains(&"bar".to_string()));
        assert!(!result.structurally_covered.contains(&"foo".to_string()));
    }

    #[test]
    fn test_gap_depended_on_by_multiple() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("caller_a"), vec!["shared".to_string()]);
        chain.add_certificate(make_cert("caller_b"), vec!["shared".to_string()]);

        let result = verify_proof_chain(&chain);
        assert_eq!(result.gaps.len(), 1);
        let gap = &result.gaps[0];
        assert_eq!(gap.function, "shared");
        assert!(gap.depended_on_by.contains(&"caller_a".to_string()));
        assert!(gap.depended_on_by.contains(&"caller_b".to_string()));
    }

    #[test]
    fn test_forged_sound_json_is_ignored() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec![]);
        let report = verify_proof_chain(&chain);
        assert!(report.structurally_complete);

        let json = serde_json::to_string(&report).unwrap();
        assert!(json.contains("\"structurally_covered\""));
        assert!(json.contains("\"integrity_valid_count\""));
        assert!(json.contains("\"integrity_valid_record_coverage\""));
        assert!(!json.contains("\"discharged\""));
        assert!(!json.contains("\"proven_count\""));
        let legacy_discharged = json.replace("structurally_covered", "discharged");
        assert!(serde_json::from_str::<ChainVerificationResult>(&legacy_discharged).is_err());
        let legacy_proven_count = json.replace("integrity_valid_count", "proven_count");
        assert!(serde_json::from_str::<ChainVerificationResult>(&legacy_proven_count).is_err());
        let forged = json.replace("\"sound\":false", "\"sound\":true");
        assert_ne!(forged, json);
        let restored: ChainVerificationResult = serde_json::from_str(&forged).unwrap();
        assert!(!restored.is_sound());
        assert!(restored.structurally_complete);
    }

    #[test]
    fn test_self_cycle_is_reported() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["foo".to_string()]);

        let result = verify_proof_chain(&chain);
        assert_eq!(result.cycles, vec![vec!["foo".to_string()]]);
        assert!(!result.structurally_complete);
        assert!(!result.is_sound());
    }

    #[test]
    fn test_missing_root_call_graph_key_is_a_gap() {
        let mut chain = ProofChain::new("test");
        chain.call_graph.insert("missing_root".to_string(), vec![]);

        let result = verify_proof_chain(&chain);
        assert_eq!(
            result.gaps,
            vec![ChainGap { function: "missing_root".to_string(), depended_on_by: vec![] }]
        );
        assert!(!result.structurally_complete);
    }

    #[test]
    fn test_orphan_certificate_record_is_counted() {
        let mut chain = ProofChain::new("test");
        chain.certificates.insert("orphan".to_string(), make_cert("orphan"));

        let result = verify_proof_chain(&chain);
        assert_eq!(result.total_functions, 1);
        assert_eq!(result.integrity_valid_count, 1);
        assert_eq!(result.structurally_covered, vec!["orphan"]);
        assert!(result.structurally_complete);
        assert!(!result.is_sound());
    }

    #[test]
    fn test_invalid_transitive_callee_blocks_structural_coverage() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("root"), vec!["middle".to_string()]);
        chain.add_certificate(make_cert("middle"), vec!["leaf".to_string()]);
        let mut invalid_leaf = make_cert("leaf");
        invalid_leaf.vc_hash[0] ^= 1;
        chain.add_certificate(invalid_leaf, vec![]);

        let result = verify_proof_chain(&chain);
        assert_eq!(result.invalid_certs, vec!["leaf"]);
        assert!(result.structurally_covered.is_empty());
        assert!(!result.structurally_complete);
    }

    #[test]
    fn test_wrong_format_version_fails_structural_completeness() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec![]);
        chain.version = PROOF_CHAIN_VERSION + 1;

        let result = verify_proof_chain(&chain);
        assert!(!result.format_valid);
        assert!(!result.structurally_complete);
    }

    #[test]
    fn test_certificate_map_key_mismatch_is_invalid() {
        let mut chain = ProofChain::new("test");
        chain.certificates.insert("alias".to_string(), make_cert("actual"));
        chain.call_graph.insert("alias".to_string(), vec![]);

        let result = verify_proof_chain(&chain);
        assert_eq!(result.invalid_certs, vec!["alias"]);
        assert!(!result.structurally_complete);
    }
}
