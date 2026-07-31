// trust-types/formula/contracts: Contract and metadata types for verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::Formula;
use crate::fx::FxHashMap;

/// Trust: Serializable state machine metadata for temporal VC dispatch.
///
/// Bridges trust-types `StateMachine` (MIR-level) to trust-temporal
/// `StateMachine` (model-checking level). The ty backend converts this
/// to a trust-temporal StateMachine for CTL/LTL/liveness/fairness checking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateMachineMetadata {
    /// State names, indexed by position (position = state ID).
    pub states: Vec<String>,
    /// Indices of initial states (into the `states` vec).
    ///
    /// The current in-process Ty representation supports exactly one initial
    /// state. Consumers must reject empty, multiple, or out-of-range entries;
    /// they must never silently select or invent an initial state.
    pub init_states: Vec<usize>,
    /// Transitions: (from_state_idx, event_label, to_state_idx).
    pub transitions: Vec<(usize, String, usize)>,
    /// Labels for each state: state_idx -> list of atomic proposition labels.
    pub labels: FxHashMap<usize, Vec<String>>,
}

impl StateMachineMetadata {
    /// Trust: Convert a trust-types `StateMachine` to `StateMachineMetadata`.
    #[must_use]
    pub fn from_trust_types_sm(sm: &crate::StateMachine) -> Self {
        let states: Vec<String> = sm.states.iter().map(|s| s.name.clone()).collect();
        let init_states = sm.initial_state.map_or_else(Vec::new, |init| {
            sm.states.iter().position(|s| s.discriminant == init).into_iter().collect()
        });
        let transitions = sm
            .transitions
            .iter()
            .filter_map(|t| {
                let from_idx = sm.states.iter().position(|s| s.discriminant == t.from)?;
                let to_idx = sm.states.iter().position(|s| s.discriminant == t.to)?;
                let from_name = &sm.states[from_idx].name;
                let to_name = &sm.states[to_idx].name;
                Some((from_idx, format!("{from_name}_to_{to_name}"), to_idx))
            })
            .collect();
        let labels = states.iter().enumerate().map(|(i, name)| (i, vec![name.clone()])).collect();
        Self { states, init_states, transitions, labels }
    }
}

/// Trust: metadata key under which a temporal VC's model payload travels on a
/// public `TrustObligation` (the full-verifier lane's obligation type carries
/// no formula or state machine, only metadata entries).
pub const TY_TEMPORAL_MODEL_METADATA_KEY: &str = "trust.ty.temporal_model";

/// Trust: schema marker for [`TyTemporalModelPayload`].
pub const TY_TEMPORAL_MODEL_SCHEMA_VERSION: &str = "trust.ty.temporal-model.v1";

/// Trust: serialized temporal-model transport for the native ty engine.
///
/// `trust-mir-extract` drops `VerificationCondition.formula` when building the
/// public `TrustContractBundle`, and temporal VCs never had a usable formula
/// anyway — their model is the `VcKind` payload itself (CTL/LTL property +
/// optional [`StateMachineMetadata`], or a liveness/fairness constraint). This
/// wrapper carries that `VcKind` verbatim through `TrustObligation::metadata`
/// so `NativeTyEngine` can rebuild and model-check the exact machine the
/// producer emitted.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TyTemporalModelPayload {
    /// Always [`TY_TEMPORAL_MODEL_SCHEMA_VERSION`]; consumers reject others.
    pub schema_version: String,
    /// The temporal `VcKind` exactly as emitted (Temporal / Liveness /
    /// Fairness / DeadState / Deadlock), including any inline machine.
    pub vc_kind: super::VcKind,
}

impl TyTemporalModelPayload {
    /// Wrap a temporal `VcKind` for metadata transport. Returns `None` for
    /// non-temporal kinds (nothing for ty to check).
    #[must_use]
    pub fn from_vc_kind(kind: &super::VcKind) -> Option<Self> {
        use super::VcKind;
        match kind {
            VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::DeadState { .. }
            | VcKind::Deadlock => Some(Self {
                schema_version: TY_TEMPORAL_MODEL_SCHEMA_VERSION.to_string(),
                vc_kind: kind.clone(),
            }),
            _ => None,
        }
    }

    /// Serialize to the metadata value string.
    pub fn to_metadata_value(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Parse a metadata value string, enforcing the schema marker.
    pub fn from_metadata_value(value: &str) -> Result<Self, String> {
        let payload: Self = serde_json::from_str(value)
            .map_err(|e| format!("malformed {TY_TEMPORAL_MODEL_METADATA_KEY} payload: {e}"))?;
        if payload.schema_version != TY_TEMPORAL_MODEL_SCHEMA_VERSION {
            return Err(format!(
                "unsupported temporal-model schema `{}` (expected `{}`)",
                payload.schema_version, TY_TEMPORAL_MODEL_SCHEMA_VERSION
            ));
        }
        Ok(payload)
    }
}

// Trust: Contract metadata for deductive verification routing.
//
// Tracks which contract clauses are present on a VC so the router
// can prioritize trust_wp (deductive engine) for contract-bearing VCs.

/// Metadata about contract clauses (including compatibility-desugared
/// attributes) attached to a verification condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ContractMetadata {
    /// Whether the function has a `requires` clause.
    pub has_requires: bool,
    /// Whether the function has an `ensures` clause.
    pub has_ensures: bool,
    /// Whether the function has an invariant clause.
    pub has_invariant: bool,
    /// Whether the function has a `decreases` clause.
    pub has_variant: bool,
    // trust-wp-style contract metadata for Horn clause lowering.
    /// Whether the function has a loop-invariant clause.
    #[serde(default)]
    pub has_loop_invariant: bool,
    /// Whether the function has a `#[refine(...)]` annotation.
    #[serde(default)]
    pub has_type_refinement: bool,
    /// Whether the function has a `#[modifies(...)]` annotation.
    #[serde(default)]
    pub has_modifies: bool,
    /// Dense index of the one authored contract clause that produced this VC.
    ///
    /// This is an identity hint, not proof authority. Consumers that use it to
    /// relate a body-aware VC back to a source clause must revalidate the index
    /// against the canonical function/compiler contract vectors, including the
    /// clause kind, predicate body, and source span. `None` is deliberately the
    /// fail-closed representation for synthetic, inferred, or ambiguous rows.
    #[serde(default)]
    pub source_contract_index: Option<usize>,
}

impl ContractMetadata {
    /// Returns true if any contract annotation is present.
    #[must_use]
    pub fn has_any(&self) -> bool {
        self.has_requires
            || self.has_ensures
            || self.has_invariant
            || self.has_variant
            || self.has_loop_invariant
            || self.has_type_refinement
            || self.has_modifies
    }

    /// Returns true if any trust-wp-specific contract is present.
    #[must_use]
    pub fn has_trust_wp_contracts(&self) -> bool {
        self.has_loop_invariant || self.has_type_refinement || self.has_modifies
    }
}

/// Provenance of the single-writer invariant the mmap temporal model rests on.
///
/// SOUNDNESS: this exists so the unsound case is *unrepresentable*. Removing the
/// `Truncate` environment action from the model is equivalent to asserting the
/// hazard away, so only evidence that was actually CHECKED may do it. A bare
/// `bool` could not tell a caller's promise apart from a discharged obligation,
/// and the promise silently won — `#[trust::single_writer]` is set by an
/// attribute-presence test with no verification, and it used to reduce the model
/// to two states with no bad state at all, which a complete exploration then
/// graded `AssuranceLevel::Sound`. That is an unverified assertion laundered into
/// a proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SingleWriterEvidence {
    /// No single-writer invariant is claimed. The hazard is modeled.
    None,
    /// DECLARED by `#[trust::single_writer]` — an unverified caller assertion,
    /// exactly the promise `MmapMut::map_mut`'s `unsafe` contract asks of the
    /// caller. It is a real obligation *on the caller*, not a discharged one, so
    /// it must NOT remove the hazard: the model keeps `Truncate` and `ty`
    /// fail-closes. Over-rejection is the correct direction here.
    Declared,
    /// VERIFIED — the single-writer invariant was discharged by a checked proof
    /// rather than asserted. Only this may disable `Truncate`.
    ///
    /// Nothing constructs this yet. It is the seam a future single-writer proof
    /// plugs into; until such a proof exists, the mmap lane fail-closes, and that
    /// is intended.
    Verified,
}

impl SingleWriterEvidence {
    /// True only when the invariant was CHECKED. A declaration is not a proof.
    #[must_use]
    pub fn discharges_truncate(self) -> bool {
        matches!(self, Self::Verified)
    }
}

impl StateMachineMetadata {
    /// The SOUND temporal model of the mmap captured-length hazard, checked with
    /// the CTL property `AG !bad` (no reachable access-while-stale state).
    ///
    /// The environment `Truncate` action models a concurrent shrink of the
    /// backing file. CRITICAL SOUNDNESS POINT: re-validation does NOT remove the
    /// hazard (a TOCTOU lets `Truncate` fire between the live-size re-read and the
    /// access), so the model enables `Truncate` from the mapped state whenever the
    /// file is concurrently truncatable, and `ty` CATCHES the stale access with
    /// the `Mapped → truncate → stale_access` trace.
    ///
    /// Only a **verified** single-writer invariant disables `Truncate`. A
    /// `#[trust::single_writer]` declaration does not: see
    /// [`SingleWriterEvidence`] for why the distinction is a type rather than a
    /// `bool`.
    #[must_use]
    pub fn mmap_temporal_model(single_writer: SingleWriterEvidence) -> Self {
        let mut labels = FxHashMap::default();
        // Always-present states: Mapped (init) and a safe access; self-loops keep
        // the transition relation total for the CTL model checker.
        let mut states = vec!["Mapped".to_string(), "SafeAccess".to_string()];
        let mut transitions =
            vec![(0usize, "access".to_string(), 1usize), (1, "idle".to_string(), 1)];
        if !single_writer.discharges_truncate() {
            // Truncatable file: env can shrink the mapping (Mapped → Stale), and
            // an access while stale reaches the bad state.
            states.push("Stale".to_string()); // 2
            states.push("BadAccess".to_string()); // 3
            labels.insert(3usize, vec!["bad".to_string()]);
            transitions.push((0, "truncate".to_string(), 2));
            transitions.push((2, "stale_access".to_string(), 3));
            transitions.push((3, "idle".to_string(), 3));
        }
        StateMachineMetadata { states, init_states: vec![0], transitions, labels }
    }
}

// trust_wp contract IR for Horn clause lowering.
//
// Captures the full contract representation needed to lower function contracts
// to Constrained Horn Clauses (CHCs). The trust_wp backend uses this as input
// for its strongest-postcondition reasoning engine.

/// A loop invariant with its associated loop header block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoopInvariantContract {
    /// The invariant formula (parsed from the annotation body).
    pub formula: Formula,
    /// Block ID of the loop header this invariant applies to.
    pub header_block: usize,
    /// The original expression string from the annotation.
    pub expr: String,
}

/// A type refinement predicate binding a variable to a constraint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeRefinementContract {
    /// The variable being refined.
    pub variable: String,
    /// The refinement predicate formula (e.g., `v > 0`).
    pub predicate: Formula,
    /// The original expression string from the annotation.
    pub expr: String,
}

/// Intermediate representation of trust-wp-style contracts for a function.
///
/// Aggregates all contract annotations into a form suitable for lowering
/// to Horn clauses. The trust_vcgen contracts module populates this from
/// parsed `Contract` entries, and the trust-router trust_wp backend consumes
/// it for CHC system construction.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct TrustWpContractIr {
    /// Preconditions (from `#[requires(...)]`).
    pub preconditions: Vec<Formula>,
    /// Postconditions (from `#[ensures(...)]`).
    pub postconditions: Vec<Formula>,
    /// Loop invariants with associated loop headers.
    pub loop_invariants: Vec<LoopInvariantContract>,
    /// Type refinement predicates binding variables to constraints.
    pub type_refinements: Vec<TypeRefinementContract>,
    /// Variables the function is allowed to modify (from `#[modifies(...)]`).
    /// Everything else is implicitly preserved (frame condition).
    pub modifies_set: Vec<String>,
}

impl TrustWpContractIr {
    /// Returns true if this IR contains any contract information.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty()
            && self.postconditions.is_empty()
            && self.loop_invariants.is_empty()
            && self.type_refinements.is_empty()
            && self.modifies_set.is_empty()
    }

    /// Build a `ContractMetadata` summarizing which contract kinds are present.
    #[must_use]
    pub fn to_metadata(&self) -> ContractMetadata {
        ContractMetadata {
            has_requires: !self.preconditions.is_empty(),
            has_ensures: !self.postconditions.is_empty(),
            has_invariant: false,
            has_variant: false,
            has_loop_invariant: !self.loop_invariants.is_empty(),
            has_type_refinement: !self.type_refinements.is_empty(),
            has_modifies: !self.modifies_set.is_empty(),
            source_contract_index: None,
        }
    }
}
