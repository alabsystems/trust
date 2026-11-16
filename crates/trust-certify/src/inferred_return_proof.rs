//! Retained, independently replayable facts for inferred return composition.
//!
//! The graph contains untrusted inputs. A checked graph exists only after the
//! existing synthesizer regenerates each node's complete original-body check
//! group and every presented CleanCic payload passes direct kernel replay.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use trust_types::{CalleeIdentity, VerifiableFunction};

/// Exact original input and evidence for one monomorphic callee.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InferredReturnProofNode {
    pub identity: CalleeIdentity,
    pub function: VerifiableFunction,
    pub children: Vec<CalleeIdentity>,
    pub evidence: Vec<trust_ir::ProofEvidence>,
}

/// A shared DAG, not recursively duplicated certificate trees.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InferredReturnProofGraph {
    pub nodes: Vec<InferredReturnProofNode>,
}

/// Opaque checked inputs. Serialized graphs can never construct this token.
#[derive(Clone, Debug)]
pub struct CheckedInferredReturns {
    graph: Arc<InferredReturnProofGraph>,
    inputs: BTreeMap<CalleeIdentity, trust_vcgen::InferredReturnCall>,
    digest: String,
}

impl CheckedInferredReturns {
    pub fn graph(&self) -> &InferredReturnProofGraph {
        &self.graph
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    /// Select exactly the identities the typed caller names. Their actual
    /// argument/destination binding is checked by the shared generator.
    pub fn inputs_for(
        &self,
        function: &VerifiableFunction,
    ) -> Option<Vec<trust_vcgen::InferredReturnCall>> {
        let mut identities = BTreeSet::new();
        for block in &function.body.blocks {
            if let trust_types::Terminator::Call { callee_identity, .. } = &block.terminator {
                identities.insert((*callee_identity)?);
            }
        }
        identities.into_iter().map(|id| self.inputs.get(&id).cloned()).collect()
    }
}

/// Replay each immutable node once. Ambiguous identities, cycles, missing
/// dependencies, changed original bodies and incomplete check groups refuse.
/// No solver or proof search is invoked by certificate replay.
pub fn replay_inferred_return_graph(
    graph: &InferredReturnProofGraph,
) -> Result<CheckedInferredReturns, String> {
    if !graph_within_depth_gate(graph) {
        return Err("inferred return formula exceeds replay depth bound".into());
    }
    crate::on_certify_stack_if_needed(|| Some(replay_inferred_return_graph_on_stack(graph)))
        .ok_or_else(|| "inferred return replay worker did not complete".to_string())?
}

pub(crate) fn graph_within_depth_gate(graph: &InferredReturnProofGraph) -> bool {
    graph.nodes.iter().all(|node| {
        node.function
            .preconditions
            .iter()
            .chain(&node.function.postconditions)
            .all(crate::violation_within_depth_gate)
    })
}

// The source-clause replay worker already owns the certification stack. Its
// nested graph consumes that stack instead of starting a second graph worker.
pub(crate) fn replay_inferred_return_graph_on_stack(
    graph: &InferredReturnProofGraph,
) -> Result<CheckedInferredReturns, String> {
    if graph.nodes.is_empty() || graph.nodes.len() > 32 {
        return Err("inferred return graph must contain 1..=32 exact nodes".into());
    }
    let mut nodes = BTreeMap::new();
    let mut names = BTreeSet::new();
    for node in &graph.nodes {
        if nodes.insert(node.identity, node).is_some() || !names.insert(&node.function.def_path) {
            return Err("ambiguous inferred return identity or function path".into());
        }
    }
    let mut checked = BTreeMap::new();
    let mut visiting = BTreeSet::new();
    for id in nodes.keys() {
        check_node(*id, &nodes, &mut visiting, &mut checked, 0)?;
    }
    let bytes = serde_json::to_vec(graph).map_err(|e| e.to_string())?;
    Ok(CheckedInferredReturns {
        graph: Arc::new(graph.clone()),
        inputs: checked,
        digest: trust_types::stable_sha256_hex(&bytes),
    })
}

fn check_node(
    identity: CalleeIdentity,
    nodes: &BTreeMap<CalleeIdentity, &InferredReturnProofNode>,
    visiting: &mut BTreeSet<CalleeIdentity>,
    checked: &mut BTreeMap<CalleeIdentity, trust_vcgen::InferredReturnCall>,
    depth: usize,
) -> Result<(), String> {
    if checked.contains_key(&identity) {
        return Ok(());
    }
    if depth > 8 || !visiting.insert(identity) {
        return Err("cyclic or over-depth inferred return graph".into());
    }
    let node = nodes.get(&identity).ok_or("missing inferred return dependency")?;
    // The existing original-body checker clears ALL entry preconditions.
    // Extractor-derived enum ranges remain in the retained source bytes, but
    // cannot be hypotheses of the checked unconditional return fact.
    if !node.function.contracts.is_empty()
        || !node.function.spec.is_empty()
        || !node.function.postconditions.is_empty()
    {
        return Err("inferred return body carries an authored assumption or guarantee".into());
    }
    let children = node.children.iter().copied().collect::<BTreeSet<_>>();
    if children.len() != node.children.len() {
        return Err("duplicate inferred return dependency".into());
    }
    let mut called = BTreeSet::new();
    for block in &node.function.body.blocks {
        if let trust_types::Terminator::Call { callee_identity, .. } = &block.terminator {
            called.insert(callee_identity.ok_or("unbound original callee identity")?);
        }
    }
    if children != called {
        return Err("inferred return dependencies differ from original calls".into());
    }
    let mut inputs = Vec::new();
    for child in &node.children {
        check_node(*child, nodes, visiting, checked, depth + 1)?;
        inputs.push(checked[child].clone());
    }
    let mut rows = trust_types::vc_context::VcContext::default();
    let candidate =
        trust_vcgen::infer_return_candidate_with_calls_rows(&node.function, &inputs, &mut rows)
            .map_err(str::to_owned)?;
    // A complete-looking original-body candidate still cannot be consumed
    // after the function budget degraded any of its regeneration work.
    if trust_types::verify_budget::exhausted_readonly() {
        return Err("inferred-return regeneration exceeded the function verification budget".into());
    }
    if candidate.check_vcs().is_empty() || candidate.check_vcs().len() != node.evidence.len() {
        return Err("inferred return original-body check group is incomplete".into());
    }
    for (index, (vc, evidence)) in candidate.check_vcs().iter().zip(&node.evidence).enumerate() {
        if !crate::replay_presented_vc_evidence(vc, evidence) {
            return Err(format!(
                "inferred return {} original-body check {index} ({:?}) certificate refused",
                node.function.def_path, vc.kind
            ));
        }
    }
    let input = trust_vcgen::InferredReturnCall::new(identity, &candidate)
        .ok_or("inferred return is outside the typed composition fragment")?;
    visiting.remove(&identity);
    checked.insert(identity, input);
    Ok(())
}
