// trust-clean/composition_transfer.rs: Clean proof transfer integration with composition DAG
//
// Bridges the proof composition DAG (trust-proof-cert) with clean proof obligation
// generation. When function A calls function B and B has a clean proof, this module
// generates `assume` statements for A's proof context, allowing modular verification
// across function boundaries.
//
// Phase 4 — composition DAG integration
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_proof_cert::composition::CompositionNode;
use trust_proof_cert::{CompositionNodeStatus, ProofComposition};
use trust_types::Formula;
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::obligation::{ObligationId, ObligationSource, ProofObligation};

// ---------------------------------------------------------------------------
// ProofStatus — clean proof status for a function
// ---------------------------------------------------------------------------

/// The clean proof status of a function in the composition DAG.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofStatus {
    /// Function is reported as having a complete certified proof.
    ///
    /// This public label is not, by itself, assumption authority.
    Certified,
    /// Function has a solver proof but no clean certification.
    Trusted,
    /// Function's proof is stale (source changed since last proof).
    Stale,
    /// No proof exists for this function.
    Missing,
}

impl ProofStatus {
    /// Returns `true` if the reporting status says a proof exists.
    ///
    /// This is informational only and must not gate proof reuse.
    #[must_use]
    pub fn is_proved(&self) -> bool {
        matches!(self, ProofStatus::Certified | ProofStatus::Trusted)
    }

    /// A bare reporting status never authorizes assumptions in callers.
    ///
    /// `ProofStatus` is public and freely constructible. In particular,
    /// `Certified` can be derived from the composition DAG's chain-integrity
    /// status, which is not a kernel replay of the claimed theorem. Assumption
    /// authority therefore lives only in the private capability set maintained
    /// by [`ProofStatusRegistry`].
    #[must_use]
    pub fn is_assumable(&self) -> bool {
        false
    }
}

impl From<CompositionNodeStatus> for ProofStatus {
    fn from(status: CompositionNodeStatus) -> Self {
        match status {
            CompositionNodeStatus::Valid => ProofStatus::Certified,
            CompositionNodeStatus::ChainBroken => ProofStatus::Trusted,
            CompositionNodeStatus::Stale => ProofStatus::Stale,
            CompositionNodeStatus::Missing => ProofStatus::Missing,
        }
    }
}

// ---------------------------------------------------------------------------
// ProofStatusRegistry — maps function paths to their clean proof status
// ---------------------------------------------------------------------------

/// Registry mapping function paths to their clean proof status.
///
/// Built from a `ProofComposition` DAG or populated manually for reporting.
/// `CleanProofTransfer` authorizes a callee only when this registry also carries
/// the private capability minted by the local kernel path.
#[derive(Debug, Clone)]
pub struct ProofStatusRegistry {
    /// Function path -> proof status.
    statuses: FxHashMap<String, ProofStatus>,
    /// Functions whose exact local obligation was checked by the Clean kernel.
    ///
    /// This set is deliberately private and is never populated by public status
    /// registration or by a public `ProofComposition` DAG.
    kernel_assumable: FxHashSet<String>,
}

impl ProofStatusRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn new() -> Self {
        ProofStatusRegistry {
            statuses: FxHashMap::default(),
            kernel_assumable: FxHashSet::default(),
        }
    }

    /// Build a registry from a `ProofComposition` DAG.
    ///
    /// Each node in the DAG maps to a reporting `ProofStatus` based on its
    /// `CompositionNodeStatus`. This never grants assumption authority: the
    /// public composition API checks chain integrity, not the exact theorem in
    /// the local Clean kernel.
    #[must_use]
    pub fn from_composition(composition: &ProofComposition) -> Self {
        let mut statuses = FxHashMap::default();
        for function in composition.functions() {
            if let Some(node) = composition.get_node(&function) {
                statuses.insert(function, ProofStatus::from(node.status));
            }
        }
        ProofStatusRegistry { statuses, kernel_assumable: FxHashSet::default() }
    }

    /// Register a function's reporting status.
    ///
    /// Public status registration can never mint assumption authority. Updating
    /// an existing function also revokes any prior capability, even when the new
    /// label is `Certified`, so a public relabel cannot preserve stale authority.
    pub fn register(&mut self, function: impl Into<String>, status: ProofStatus) {
        let function = function.into();
        self.kernel_assumable.remove(&function);
        self.statuses.insert(function, status);
    }

    /// Record authority produced by the local exact Clean kernel path.
    ///
    /// This is crate-private by design. Production call sites are confined to
    /// `whole_program`, immediately after its kernel check succeeds.
    pub(crate) fn register_kernel_certified(&mut self, function: impl Into<String>) {
        let function = function.into();
        self.statuses.insert(function.clone(), ProofStatus::Certified);
        self.kernel_assumable.insert(function);
    }

    /// Look up a function's proof status.
    #[must_use]
    pub fn get(&self, function: &str) -> Option<&ProofStatus> {
        self.statuses.get(function)
    }

    /// Returns `true` only when the function carries private local-kernel
    /// authority in addition to a `Certified` reporting status.
    #[must_use]
    pub fn is_assumable(&self, function: &str) -> bool {
        self.kernel_assumable.contains(function)
            && matches!(self.statuses.get(function), Some(ProofStatus::Certified))
    }

    /// Return all functions with assumable proofs.
    #[must_use]
    pub fn assumable_functions(&self) -> Vec<&str> {
        let mut result: Vec<&str> = self
            .kernel_assumable
            .iter()
            .filter(|function| {
                matches!(self.statuses.get(function.as_str()), Some(ProofStatus::Certified))
            })
            .map(String::as_str)
            .collect();
        result.sort();
        result
    }

    /// Return all registered function paths.
    #[must_use]
    pub fn functions(&self) -> Vec<&str> {
        let mut result: Vec<&str> = self.statuses.keys().map(|s| s.as_str()).collect();
        result.sort();
        result
    }

    /// Number of registered functions.
    #[must_use]
    pub fn len(&self) -> usize {
        self.statuses.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.statuses.is_empty()
    }
}

impl Default for ProofStatusRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// TransferObligation — an assume statement for a caller's proof context
// ---------------------------------------------------------------------------

/// An obligation generated by proof transfer: an `assume` statement
/// asserting that a callee's proven postcondition holds at the call site
/// in the caller's proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransferObligation {
    /// The caller function receiving the assumption.
    pub caller: String,
    /// The callee function whose proof is being transferred.
    pub callee: String,
    /// The postcondition being assumed (from the callee's proof).
    pub assumed_postcondition: Formula,
}

// ---------------------------------------------------------------------------
// CleanProofTransfer — generates assume obligations from the composition DAG
// ---------------------------------------------------------------------------

/// Generates clean proof obligations with `assume` statements for callee
/// postconditions based on the composition DAG and proof status registry.
///
/// When function A calls function B and B has private local-kernel authority,
/// `CleanProofTransfer` generates an assumption in A's proof context
/// that B's postcondition holds. This enables modular verification:
/// each function is verified independently, and inter-function reasoning
/// uses assumptions backed by certified proofs.
pub struct CleanProofTransfer<'a> {
    /// The proof status registry for looking up callee proof states.
    registry: &'a ProofStatusRegistry,
}

impl<'a> CleanProofTransfer<'a> {
    /// Create a new transfer engine with the given proof status registry.
    #[must_use]
    pub fn new(registry: &'a ProofStatusRegistry) -> Self {
        CleanProofTransfer { registry }
    }

    /// Generate `assume` obligations for a composition node.
    ///
    /// For each dependency (callee) with private local-kernel authority,
    /// generates a `TransferObligation` asserting the callee's postcondition
    /// in the caller's proof context.
    ///
    /// `postconditions` maps callee function names to their proven postconditions.
    /// Callees without entries in `postconditions` are skipped even if authorized
    /// (the postcondition formula is needed to generate the assumption).
    #[must_use]
    pub fn generate_assumptions(
        &self,
        node: &CompositionNode,
        postconditions: &FxHashMap<String, Formula>,
    ) -> Vec<TransferObligation> {
        let mut obligations = Vec::new();

        for callee in &node.dependencies {
            // A public Certified label is insufficient; require the private
            // capability produced by a local kernel check.
            if !self.registry.is_assumable(callee) {
                continue;
            }

            // Need the postcondition formula to generate the assume
            if let Some(postcondition) = postconditions.get(callee) {
                obligations.push(TransferObligation {
                    caller: node.function.clone(),
                    callee: callee.clone(),
                    assumed_postcondition: postcondition.clone(),
                });
            }
        }

        obligations
    }

    /// Generate proof obligations for a caller node, incorporating assumptions
    /// from certified callee proofs.
    ///
    /// Returns a `ProofObligation` for the caller's goal with callee postconditions
    /// added as hypotheses (assumptions). The caller only needs to prove its own
    /// properties under the assumption that its callees satisfy their contracts.
    ///
    /// `goal` is the caller's verification condition to prove.
    /// `postconditions` maps callee function names to their proven postconditions.
    /// `obligation_id` is the ID to assign to the generated obligation.
    #[must_use]
    pub fn generate_obligation_with_assumptions(
        &self,
        node: &CompositionNode,
        goal: Formula,
        postconditions: &FxHashMap<String, Formula>,
        obligation_id: ObligationId,
    ) -> ProofObligation {
        let assumptions = self.generate_assumptions(node, postconditions);

        let hypotheses: Vec<Formula> =
            assumptions.iter().map(|a| a.assumed_postcondition.clone()).collect();

        let source = ObligationSource {
            vc_kind: trust_types::VcKind::Assertion {
                message: format!(
                    "modular verification of {} with {} assumed callee proofs",
                    node.function,
                    hypotheses.len()
                ),
            },
            function: node.function.clone(),
            description: format!(
                "proof obligation with transferred assumptions from: {}",
                assumptions.iter().map(|a| a.callee.as_str()).collect::<Vec<_>>().join(", ")
            ),
        };

        ProofObligation::with_hypotheses(obligation_id, goal, hypotheses, source)
    }

    /// Generate transfer obligations for all nodes in a composition DAG.
    ///
    /// Processes nodes in topological order (callees before callers) so that
    /// proof transfer flows bottom-up through the call graph.
    ///
    /// Returns a map from function name to the list of transfer obligations
    /// generated for that function.
    pub fn transfer_all(
        &self,
        composition: &ProofComposition,
        postconditions: &FxHashMap<String, Formula>,
    ) -> Result<FxHashMap<String, Vec<TransferObligation>>, trust_proof_cert::CompositionError>
    {
        let order = composition.topological_order()?;
        let mut result: FxHashMap<String, Vec<TransferObligation>> = FxHashMap::default();

        for function in &order {
            if let Some(node) = composition.get_node(function) {
                let obligations = self.generate_assumptions(node, postconditions);
                if !obligations.is_empty() {
                    result.insert(function.clone(), obligations);
                }
            }
        }

        Ok(result)
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use trust_proof_cert::composition::CompositionNode;
    use trust_proof_cert::{
        CompositionNodeStatus, FunctionHash, ProofCertificate, ProofComposition, SolverInfo,
        VcSnapshot,
    };
    use trust_types::{Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition};

    use super::*;

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

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

    fn make_cert(function: &str) -> ProofCertificate {
        use trust_proof_cert::chain::{ChainStep, ChainStepType};

        let vc_snapshot =
            VcSnapshot::from_vc(&sample_vc(function)).expect("snapshot should serialize");
        let mut cert = ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            vc_snapshot,
            SolverInfo {
                name: "ay".to_string(),
                version: "1.0.0".to_string(),
                time_ms: 42,
                strength: ProofStrength::smt_unsat(),
                evidence: None,
            },
            vec![1, 2, 3],
            "2026-04-12T00:00:00Z".to_string(),
        );
        // Add a structurally complete, self-consistent chain (VcGeneration →
        // SolverProof with linked hashes) so `ProofComposition::add_certificate`'s
        // validation (`verify_vc_hash` + `ChainValidator::validate`) yields
        // Valid → Certified. This is still only metadata integrity, not proof
        // authority (see `ProofStatusRegistry::is_assumable`).
        cert.chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "source".to_string(),
            output_hash: "abc".to_string(),
            time_ms: 1,
            timestamp: "2026-04-12T00:00:00Z".to_string(),
        });
        cert.chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "abc".to_string(),
            output_hash: "def".to_string(),
            time_ms: 1,
            timestamp: "2026-04-12T00:00:00Z".to_string(),
        });
        cert
    }

    fn postconditions_map() -> FxHashMap<String, Formula> {
        let mut map = FxHashMap::default();
        map.insert(
            "crate::bar".to_string(),
            Formula::Gt(
                Box::new(Formula::Var("result".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        );
        map.insert(
            "crate::baz".to_string(),
            Formula::Eq(
                Box::new(Formula::Var("output".to_string(), Sort::Int)),
                Box::new(Formula::Int(42)),
            ),
        );
        map
    }

    // -----------------------------------------------------------------------
    // ProofStatus tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_status_is_proved() {
        assert!(ProofStatus::Certified.is_proved());
        assert!(ProofStatus::Trusted.is_proved());
        assert!(!ProofStatus::Stale.is_proved());
        assert!(!ProofStatus::Missing.is_proved());
    }

    #[test]
    fn test_bare_proof_status_is_never_assumable() {
        assert!(!ProofStatus::Certified.is_assumable());
        assert!(!ProofStatus::Trusted.is_assumable());
        assert!(!ProofStatus::Stale.is_assumable());
        assert!(!ProofStatus::Missing.is_assumable());
    }

    #[test]
    fn test_proof_status_from_composition_node_status() {
        assert_eq!(ProofStatus::from(CompositionNodeStatus::Valid), ProofStatus::Certified);
        assert_eq!(ProofStatus::from(CompositionNodeStatus::ChainBroken), ProofStatus::Trusted);
        assert_eq!(ProofStatus::from(CompositionNodeStatus::Stale), ProofStatus::Stale);
        assert_eq!(ProofStatus::from(CompositionNodeStatus::Missing), ProofStatus::Missing);
    }

    // -----------------------------------------------------------------------
    // ProofStatusRegistry tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_new_is_empty() {
        let reg = ProofStatusRegistry::new();
        assert!(reg.is_empty());
        assert_eq!(reg.len(), 0);
    }

    #[test]
    fn test_registry_default_is_empty() {
        let reg = ProofStatusRegistry::default();
        assert!(reg.is_empty());
    }

    #[test]
    fn test_registry_register_and_get() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::foo", ProofStatus::Certified);
        reg.register("crate::bar", ProofStatus::Trusted);

        assert_eq!(reg.get("crate::foo"), Some(&ProofStatus::Certified));
        assert_eq!(reg.get("crate::bar"), Some(&ProofStatus::Trusted));
        assert_eq!(reg.get("crate::baz"), None);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn test_registry_is_assumable() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("certified_fn", ProofStatus::Certified);
        reg.register("trusted_fn", ProofStatus::Trusted);
        reg.register("stale_fn", ProofStatus::Stale);
        reg.register_kernel_certified("kernel_fn");

        assert!(!reg.is_assumable("certified_fn"));
        assert!(reg.is_assumable("kernel_fn"));
        assert!(!reg.is_assumable("trusted_fn"));
        assert!(!reg.is_assumable("stale_fn"));
        assert!(!reg.is_assumable("unknown_fn"));

        // Even a public Certified relabel revokes an existing capability.
        reg.register("kernel_fn", ProofStatus::Certified);
        assert!(!reg.is_assumable("kernel_fn"));
    }

    #[test]
    fn test_registry_assumable_functions() {
        let mut reg = ProofStatusRegistry::new();
        reg.register_kernel_certified("crate::a");
        reg.register("crate::b", ProofStatus::Trusted);
        reg.register_kernel_certified("crate::c");

        let assumable = reg.assumable_functions();
        assert_eq!(assumable, vec!["crate::a", "crate::c"]);
    }

    #[test]
    fn test_registry_functions() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::b", ProofStatus::Certified);
        reg.register("crate::a", ProofStatus::Missing);

        let funcs = reg.functions();
        assert_eq!(funcs, vec!["crate::a", "crate::b"]);
    }

    #[test]
    fn test_registry_from_composition() {
        let mut comp = ProofComposition::new();
        let cert = make_cert("crate::foo");
        comp.add_certificate(cert, vec![]);
        comp.add_missing("crate::bar", vec![]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        assert_eq!(reg.len(), 2);
        assert_eq!(reg.get("crate::foo"), Some(&ProofStatus::Certified));
        assert_eq!(reg.get("crate::bar"), Some(&ProofStatus::Missing));
        assert!(!reg.is_assumable("crate::foo"));
    }

    #[test]
    fn forged_self_consistent_composition_cannot_inject_postcondition() {
        // `make_cert` creates a certificate whose public chain-integrity check
        // passes. Both the certificate bytes and the claimed theorem are caller
        // controlled; Valid/Certified is therefore reporting metadata only.
        let mut composition = ProofComposition::new();
        composition.add_certificate(make_cert("crate::bar"), vec![]);
        composition.add_certificate(make_cert("crate::foo"), vec!["crate::bar".to_string()]);

        let registry = ProofStatusRegistry::from_composition(&composition);
        assert_eq!(registry.get("crate::bar"), Some(&ProofStatus::Certified));
        assert!(!registry.is_assumable("crate::bar"));

        let arbitrary_postcondition = Formula::Eq(
            Box::new(Formula::Var("attacker_chosen".to_string(), Sort::Int)),
            Box::new(Formula::Int(0x5eed)),
        );
        let mut postconditions = FxHashMap::default();
        postconditions.insert("crate::bar".to_string(), arbitrary_postcondition);

        let caller = composition.get_node("crate::foo").expect("forged caller node");
        let assumptions =
            CleanProofTransfer::new(&registry).generate_assumptions(caller, &postconditions);
        assert!(
            assumptions.is_empty(),
            "a self-consistent public certificate chain must not authorize an arbitrary assumption"
        );
    }

    // -----------------------------------------------------------------------
    // TransferObligation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_transfer_obligation_fields() {
        let obl = TransferObligation {
            caller: "A".to_string(),
            callee: "B".to_string(),
            assumed_postcondition: Formula::Bool(true),
        };
        assert_eq!(obl.caller, "A");
        assert_eq!(obl.callee, "B");
        assert_eq!(obl.assumed_postcondition, Formula::Bool(true));
    }

    // -----------------------------------------------------------------------
    // CleanProofTransfer::generate_assumptions tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_assumptions_certified_callee() {
        let mut reg = ProofStatusRegistry::new();
        reg.register_kernel_certified("crate::bar");

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].caller, "crate::foo");
        assert_eq!(obligations[0].callee, "crate::bar");
        assert_eq!(
            obligations[0].assumed_postcondition,
            Formula::Gt(
                Box::new(Formula::Var("result".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn test_generate_assumptions_trusted_callee_not_assumed() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Trusted);

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert!(obligations.is_empty(), "Trusted callee should not generate assumptions");
    }

    #[test]
    fn test_generate_assumptions_missing_callee_not_assumed() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Missing);

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: None,
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Missing,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert!(obligations.is_empty());
    }

    #[test]
    fn test_generate_assumptions_no_postcondition_skipped() {
        let mut reg = ProofStatusRegistry::new();
        reg.register_kernel_certified("crate::bar");

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        // Empty postconditions — no formula available
        let empty_postconditions = FxHashMap::default();
        let obligations = transfer.generate_assumptions(&node, &empty_postconditions);

        assert!(
            obligations.is_empty(),
            "should skip certified callee without postcondition formula"
        );
    }

    #[test]
    fn test_generate_assumptions_multiple_callees() {
        let mut reg = ProofStatusRegistry::new();
        reg.register_kernel_certified("crate::bar");
        reg.register_kernel_certified("crate::baz");

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string(), "crate::baz".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert_eq!(obligations.len(), 2);
        let callees: Vec<&str> = obligations.iter().map(|o| o.callee.as_str()).collect();
        assert!(callees.contains(&"crate::bar"));
        assert!(callees.contains(&"crate::baz"));
    }

    #[test]
    fn test_generate_assumptions_no_dependencies() {
        let reg = ProofStatusRegistry::new();
        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::leaf".into(),
            cert_id: Some("cert-leaf".to_string()),
            dependencies: vec![],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert!(obligations.is_empty());
    }

    #[test]
    fn test_generate_assumptions_mixed_callee_statuses() {
        let mut reg = ProofStatusRegistry::new();
        reg.register_kernel_certified("crate::bar");
        reg.register("crate::baz", ProofStatus::Trusted);

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string(), "crate::baz".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        // Only crate::bar (Certified) should produce an assumption
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].callee, "crate::bar");
    }

    // -----------------------------------------------------------------------
    // CleanProofTransfer::generate_obligation_with_assumptions tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_obligation_with_assumptions() {
        let mut reg = ProofStatusRegistry::new();
        reg.register_kernel_certified("crate::bar");
        reg.register_kernel_certified("crate::baz");

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string(), "crate::baz".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let goal = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postconditions = postconditions_map();

        let obl = transfer.generate_obligation_with_assumptions(
            &node,
            goal.clone(),
            &postconditions,
            ObligationId(1),
        );

        assert_eq!(obl.id, ObligationId(1));
        assert_eq!(obl.goal, goal);
        assert_eq!(obl.hypotheses.len(), 2, "should have 2 assumed postconditions");
        assert!(obl.status.is_pending());
        assert_eq!(obl.source.function, "crate::foo");
        assert!(obl.source.description.contains("crate::bar"));
        assert!(obl.source.description.contains("crate::baz"));
    }

    #[test]
    fn test_generate_obligation_no_certified_callees() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Trusted);

        let transfer = CleanProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".into(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let goal = Formula::Bool(true);
        let postconditions = postconditions_map();

        let obl = transfer.generate_obligation_with_assumptions(
            &node,
            goal,
            &postconditions,
            ObligationId(1),
        );

        assert!(obl.hypotheses.is_empty(), "no certified callees = no assumptions");
    }

    // -----------------------------------------------------------------------
    // CleanProofTransfer::transfer_all tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_transfer_all_linear_chain() {
        // c -> b -> a (leaf), a and b have proof certificates
        let mut comp = ProofComposition::new();
        let cert_a = make_cert("a");
        let cert_b = make_cert("b");
        let cert_c = make_cert("c");

        comp.add_certificate(cert_a, vec![]);
        comp.add_certificate(cert_b, vec!["a".to_string()]);
        comp.add_certificate(cert_c, vec!["b".to_string()]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = CleanProofTransfer::new(&reg);

        let mut postconditions = FxHashMap::default();
        postconditions.insert("a".to_string(), Formula::Bool(true));
        postconditions.insert("b".to_string(), Formula::Bool(false));

        let result = transfer.transfer_all(&comp, &postconditions).expect("should succeed");

        // Public composition nodes retain their reporting status, but no node
        // carries the private local-kernel capability required for transfer.
        assert_eq!(reg.get("a"), Some(&ProofStatus::Certified));
        assert_eq!(reg.get("b"), Some(&ProofStatus::Certified));
        assert!(!reg.is_assumable("a"));
        assert!(!reg.is_assumable("b"));
        assert!(result.is_empty());
    }

    #[test]
    fn test_transfer_all_empty_composition() {
        let comp = ProofComposition::new();
        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = CleanProofTransfer::new(&reg);

        let result = transfer
            .transfer_all(&comp, &FxHashMap::default())
            .expect("empty composition should succeed");

        assert!(result.is_empty());
    }

    #[test]
    fn test_transfer_all_cycle_returns_error() {
        let mut comp = ProofComposition::new();
        let cert_a = make_cert("a");
        let cert_b = make_cert("b");

        // a -> b and b -> a: cycle
        comp.add_certificate(cert_a, vec!["b".to_string()]);
        comp.add_certificate(cert_b, vec!["a".to_string()]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = CleanProofTransfer::new(&reg);

        let result = transfer.transfer_all(&comp, &FxHashMap::default());
        assert!(result.is_err(), "cyclic composition should return error");
    }

    #[test]
    fn test_transfer_all_with_missing_callee() {
        let mut comp = ProofComposition::new();
        let cert_a = make_cert("a");

        comp.add_certificate(cert_a, vec!["b".to_string()]);
        comp.add_missing("b", vec![]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = CleanProofTransfer::new(&reg);

        let mut postconditions = FxHashMap::default();
        postconditions.insert("b".to_string(), Formula::Bool(true));

        let result = transfer.transfer_all(&comp, &postconditions).expect("should succeed");

        // 'a' depends on 'b' which is Missing -> no transfer
        assert!(
            result.is_empty() || result.get("a").is_none_or(|v| v.is_empty()),
            "missing callee should not generate transfer"
        );
    }
}
