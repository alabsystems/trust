// trust-proof-cert DAG-based composition pipeline
//
// ProofComposition DAG, IncrementalComposition with change tracking,
// and composition verification.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::{ChainValidator, ProofCertificate};

use super::types::{
    ChangeKind, ComposedProof, CompositionError, CompositionNodeStatus, FunctionStrength,
};

/// A node in the proof composition DAG.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompositionNode {
    /// Function name this node represents.
    pub function: String,
    /// Certificate ID (if present).
    pub cert_id: Option<String>,
    /// Functions this node depends on (callees).
    pub dependencies: Vec<String>,
    /// Current status.
    pub status: CompositionNodeStatus,
}

/// Manages a directed acyclic graph of proof certificates for modular
/// whole-program composition metadata.
///
/// Each node represents a function with its certificate. Edges represent
/// call dependencies (caller -> callee). This type validates graph shape and
/// self-consistency only. It does not carry a trust-root configuration or
/// replay-bound evidence and therefore cannot establish proof soundness.
#[derive(Debug, Clone)]
pub struct ProofComposition {
    // Trust: BTreeMap for deterministic certificate output
    /// Nodes indexed by function name.
    pub(crate) nodes: BTreeMap<String, CompositionNode>,
    /// Certificates indexed by function name.
    certificates: BTreeMap<String, ProofCertificate>,
}

impl ProofComposition {
    /// Create a new empty composition.
    pub fn new() -> Self {
        ProofComposition { nodes: BTreeMap::new(), certificates: BTreeMap::new() }
    }

    /// Add a certificate record for a function with its call dependencies.
    ///
    /// `CompositionNodeStatus::Valid` means only that the record's VC hash and
    /// mutable hash-chain metadata are internally self-consistent.
    pub fn add_certificate(&mut self, cert: ProofCertificate, dependencies: Vec<String>) {
        let function = cert.function.clone();
        let cert_id = cert.id.0.clone();
        let status = if cert.verify_vc_hash() && ChainValidator::validate(&cert.chain).valid {
            CompositionNodeStatus::Valid
        } else {
            CompositionNodeStatus::ChainBroken
        };
        self.nodes.insert(
            function.clone(),
            CompositionNode {
                function: function.clone(),
                cert_id: Some(cert_id),
                dependencies,
                status,
            },
        );
        self.certificates.insert(function, cert);
    }

    /// Mark a function as required but without a certificate yet.
    pub fn add_missing(&mut self, function: &str, dependencies: Vec<String>) {
        // Replacing an existing node with `Missing` must also revoke the stored
        // record; otherwise lookups and generated manifests can observe stale
        // certificate metadata behind a missing status.
        self.certificates.remove(function);
        self.nodes.insert(
            function.to_string(),
            CompositionNode {
                function: function.into(),
                cert_id: None,
                dependencies,
                status: CompositionNodeStatus::Missing,
            },
        );
    }

    /// Get a node by function name.
    pub fn get_node(&self, function: &str) -> Option<&CompositionNode> {
        self.nodes.get(function)
    }

    /// Get a certificate by function name.
    pub fn get_certificate(&self, function: &str) -> Option<&ProofCertificate> {
        self.certificates.get(function)
    }

    /// Return all function names in the composition.
    pub fn functions(&self) -> Vec<String> {
        self.nodes.keys().cloned().collect()
    }

    /// Return the number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Return true if the composition has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Return explicit missing nodes and dangling dependency names.
    pub fn missing_functions(&self) -> Vec<String> {
        let mut missing: BTreeSet<String> = self
            .nodes
            .values()
            .filter(|n| n.status == CompositionNodeStatus::Missing)
            .map(|n| n.function.clone())
            .collect();
        for node in self.nodes.values() {
            for dependency in &node.dependencies {
                if !self.nodes.contains_key(dependency) {
                    missing.insert(dependency.clone());
                }
            }
        }
        missing.into_iter().collect()
    }

    /// Detect cycles in the dependency DAG using DFS.
    ///
    /// Returns `None` if the DAG is acyclic, or `Some(cycle)` with the
    /// list of function names forming a cycle.
    pub fn detect_cycle(&self) -> Option<Vec<String>> {
        // Standard DFS cycle detection with coloring
        // White=0, Gray=1, Black=2
        let mut color: BTreeMap<&str, u8> = BTreeMap::new();
        for key in self.nodes.keys() {
            color.insert(key.as_str(), 0);
        }

        let mut path: Vec<String> = Vec::new();

        for key in self.nodes.keys() {
            if color[key.as_str()] == 0
                && let Some(cycle) = self.dfs_cycle(key, &mut color, &mut path)
            {
                return Some(cycle);
            }
        }
        None
    }

    /// DFS helper for cycle detection.
    fn dfs_cycle<'a>(
        &'a self,
        node: &'a str,
        color: &mut BTreeMap<&'a str, u8>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        color.insert(node, 1); // Gray
        path.push(node.to_string());

        if let Some(n) = self.nodes.get(node) {
            for dep in &n.dependencies {
                match color.get(dep.as_str()) {
                    Some(1) => {
                        // Found a back edge -> cycle
                        let start = path.iter().position(|p| p == dep).unwrap_or(0);
                        let mut cycle: Vec<String> = path[start..].to_vec();
                        cycle.push(dep.clone());
                        return Some(cycle);
                    }
                    Some(0) | None => {
                        if let Some(cycle) = self.dfs_cycle(dep, color, path) {
                            return Some(cycle);
                        }
                    }
                    _ => {} // Black, already processed
                }
            }
        }

        color.insert(node, 2); // Black
        path.pop();
        None
    }

    /// Return nodes in topological order (dependencies before dependents).
    /// Returns `Err` if the graph contains a cycle.
    pub fn topological_order(&self) -> Result<Vec<String>, CompositionError> {
        if let Some(cycle) = self.detect_cycle() {
            return Err(CompositionError::CircularDependency { cycle: cycle.join(" -> ") });
        }

        let mut in_degree: BTreeMap<String, usize> = BTreeMap::new();
        let mut dependents: BTreeMap<String, Vec<String>> = BTreeMap::new();
        // Count in-degrees and index each within-DAG edge once.
        for node in self.nodes.values() {
            let mut count = 0;
            for dependency in &node.dependencies {
                if self.nodes.contains_key(dependency) {
                    count += 1;
                    dependents.entry(dependency.clone()).or_default().push(node.function.clone());
                }
            }
            in_degree.insert(node.function.clone(), count);
        }

        let mut ready: BTreeSet<String> =
            in_degree.iter().filter(|(_, deg)| **deg == 0).map(|(name, _)| name.clone()).collect();

        let mut result = Vec::new();
        while let Some(func) = ready.pop_first() {
            result.push(func.clone());
            if let Some(nodes) = dependents.get(&func) {
                for dependent in nodes {
                    let deg = in_degree
                        .get_mut(dependent)
                        .expect("dependent index must reference a DAG node");
                    assert!(*deg > 0, "dependency index must not underflow");
                    *deg -= 1;
                    if *deg == 0 {
                        ready.insert(dependent.clone());
                    }
                }
            }
        }

        Ok(result)
    }
}

impl Default for ProofComposition {
    fn default() -> Self {
        Self::new()
    }
}

/// Incremental proof composition with change tracking.
///
/// Wraps [ProofComposition] and tracks spec/body hashes for each function
/// to enable precise invalidation when functions change. Fail-closed:
/// invalidated functions are stale until explicitly re-verified.
#[derive(Debug, Clone)]
pub struct IncrementalComposition {
    /// The underlying proof composition DAG.
    dag: ProofComposition,
    /// SHA-256 hash of each function's spec (annotations + signature).
    spec_hashes: BTreeMap<String, [u8; 32]>,
    /// SHA-256 hash of each function's body/IR artifact.
    body_hashes: BTreeMap<String, [u8; 32]>,
    /// Functions currently marked as stale (need re-verification).
    stale: BTreeSet<String>,
}

impl IncrementalComposition {
    /// Create a new incremental composition.
    pub fn new() -> Self {
        IncrementalComposition {
            dag: ProofComposition::new(),
            spec_hashes: BTreeMap::new(),
            body_hashes: BTreeMap::new(),
            stale: BTreeSet::new(),
        }
    }

    /// Add a certificate with its hashes and dependencies.
    pub fn add_certificate(
        &mut self,
        cert: ProofCertificate,
        dependencies: Vec<String>,
        spec_hash: [u8; 32],
        body_hash: [u8; 32],
    ) {
        let function = cert.function.clone();
        self.dag.add_certificate(cert, dependencies);
        self.spec_hashes.insert(function.clone(), spec_hash);
        self.body_hashes.insert(function.clone(), body_hash);
        if self
            .dag
            .get_node(&function)
            .is_some_and(|node| node.status == CompositionNodeStatus::Valid)
        {
            self.stale.remove(&function);
        }
    }

    /// Compute the set of functions needing re-verification after a change.
    ///
    /// For [`ChangeKind::BodyOnly`]: only the changed function itself.
    /// For [`ChangeKind::SpecChanged`]: the changed function plus all transitive callers.
    ///
    /// All returned functions are marked stale (fail-closed).
    pub fn invalidated_by(&mut self, changed_fn: &str, change_kind: ChangeKind) -> Vec<String> {
        let mut invalidated = vec![changed_fn.to_string()];
        self.stale.insert(changed_fn.to_string());
        if let Some(node) = self.dag.nodes.get_mut(changed_fn) {
            if node.status == CompositionNodeStatus::Valid {
                node.status = CompositionNodeStatus::Stale;
            }
        } else {
            self.dag.add_missing(changed_fn, Vec::new());
        }

        if change_kind == ChangeKind::SpecChanged {
            // Build the reverse call index once, then BFS all transitive
            // callers in O(V + E) rather than rescanning/cloning every node at
            // every level.
            let mut callers: BTreeMap<String, Vec<String>> = BTreeMap::new();
            for node in self.dag.nodes.values() {
                for dependency in &node.dependencies {
                    callers.entry(dependency.clone()).or_default().push(node.function.clone());
                }
            }
            let mut queue: std::collections::VecDeque<String> = std::collections::VecDeque::new();
            queue.push_back(changed_fn.to_string());
            let mut visited: BTreeSet<String> = BTreeSet::new();
            visited.insert(changed_fn.to_string());

            while let Some(current) = queue.pop_front() {
                if let Some(direct_callers) = callers.get(&current) {
                    for func in direct_callers {
                        if !visited.insert(func.clone()) {
                            continue;
                        }
                        invalidated.push(func.clone());
                        self.stale.insert(func.clone());
                        if let Some(stale_node) = self.dag.nodes.get_mut(func) {
                            if stale_node.status == CompositionNodeStatus::Valid {
                                stale_node.status = CompositionNodeStatus::Stale;
                            }
                        }
                        queue.push_back(func.clone());
                    }
                }
            }
        }

        invalidated.sort();
        invalidated
    }

    /// Update a single function's certificate after successful re-verification.
    ///
    /// Removes the function from the stale set and updates hashes.
    pub fn update_certificate(
        &mut self,
        cert: ProofCertificate,
        dependencies: Vec<String>,
        new_spec_hash: [u8; 32],
        new_body_hash: [u8; 32],
    ) {
        let function = cert.function.clone();
        self.dag.add_certificate(cert, dependencies);
        self.spec_hashes.insert(function.clone(), new_spec_hash);
        self.body_hashes.insert(function.clone(), new_body_hash);
        if self
            .dag
            .get_node(&function)
            .is_some_and(|node| node.status == CompositionNodeStatus::Valid)
        {
            self.stale.remove(&function);
        }
    }

    /// Return the set of functions currently marked as stale.
    pub fn stale_functions(&self) -> Vec<String> {
        self.stale.iter().cloned().collect()
    }

    /// Check if a function is currently stale.
    pub fn is_stale(&self, function: &str) -> bool {
        self.stale.contains(function)
    }

    /// Get the underlying DAG.
    pub fn dag(&self) -> &ProofComposition {
        &self.dag
    }

    /// Get the spec hash for a function.
    pub fn spec_hash(&self, function: &str) -> Option<&[u8; 32]> {
        self.spec_hashes.get(function)
    }

    /// Get the body hash for a function.
    pub fn body_hash(&self, function: &str) -> Option<&[u8; 32]> {
        self.body_hashes.get(function)
    }

    /// Build producer-reported per-function strength metadata.
    ///
    /// This includes stale records for diagnostics and grants no authority.
    pub fn function_strengths(&self) -> Vec<FunctionStrength> {
        let mut strengths = Vec::new();
        for func in self.dag.functions() {
            if let Some(cert) = self.dag.get_certificate(&func) {
                strengths.push(FunctionStrength {
                    function: func,
                    strength: cert.solver.strength.clone(),
                    status: cert.status,
                });
            }
        }
        strengths
    }
}

impl Default for IncrementalComposition {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of verifying a proof composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompositionVerification {
    /// Whether the entire composition is proof-authoritatively sound.
    ///
    /// This is always `false` until the API accepts sealed trust roots and
    /// exact replay-bound evidence. It is not an alias for graph completeness.
    pub sound: bool,
    /// Whether the graph is acyclic, complete, and internally self-consistent.
    /// This is a structural diagnostic only.
    pub structurally_complete: bool,
    /// Functions with internally self-consistent certificate metadata.
    pub integrity_valid_functions: Vec<String>,
    /// Functions with missing certificates.
    pub missing_functions: Vec<String>,
    /// Functions with broken chains.
    pub broken_chains: Vec<String>,
    /// Functions invalidated by a body/spec change.
    pub stale_functions: Vec<String>,
    /// Cycle detected (if any).
    pub cycle: Option<Vec<String>>,
    /// Why structural completeness cannot be promoted to proof authority.
    pub authority_error: CompositionError,
    /// A composed proof. Always `None` without replay-bound authority.
    pub composed: Option<ComposedProof>,
}

/// Inspect a proof-composition graph without granting proof authority.
///
/// A graph is structurally complete when:
/// 1. The dependency DAG is acyclic
/// 2. Every node has an internally self-consistent record (no missing or broken metadata)
///
/// These conditions are necessary but not sufficient for sound proof
/// composition. Public certificate records, self-consistent hash chains, and
/// producer-set status labels do not demonstrate replay or trusted provenance,
/// so `sound` remains false and `composed` remains `None`.
pub fn verify_composition(composition: &ProofComposition) -> CompositionVerification {
    let mut integrity_valid_functions = Vec::new();
    let mut missing_functions = Vec::new();
    let mut broken_chains = Vec::new();
    let mut stale_functions = Vec::new();

    for node in composition.nodes.values() {
        match node.status {
            CompositionNodeStatus::Valid => {
                integrity_valid_functions.push(node.function.clone());
            }
            CompositionNodeStatus::Missing => missing_functions.push(node.function.clone()),
            CompositionNodeStatus::ChainBroken => broken_chains.push(node.function.clone()),
            CompositionNodeStatus::Stale => stale_functions.push(node.function.clone()),
        }
    }

    // A dependency absent from the DAG is missing even when callers forgot to
    // add an explicit `Missing` node for it.
    for node in composition.nodes.values() {
        for dependency in &node.dependencies {
            if !composition.nodes.contains_key(dependency) {
                missing_functions.push(dependency.clone());
            }
        }
    }

    integrity_valid_functions.sort();
    missing_functions.sort();
    missing_functions.dedup();
    broken_chains.sort();
    stale_functions.sort();

    // Check for cycles
    let cycle = composition.detect_cycle();

    let structurally_complete = missing_functions.is_empty()
        && broken_chains.is_empty()
        && stale_functions.is_empty()
        && cycle.is_none();
    let authority_error =
        CompositionError::ProofAuthorityUnavailable { operation: "verify_composition" };

    CompositionVerification {
        sound: false,
        structurally_complete,
        integrity_valid_functions,
        missing_functions,
        broken_chains,
        stale_functions,
        cycle,
        authority_error,
        composed: None,
    }
}
