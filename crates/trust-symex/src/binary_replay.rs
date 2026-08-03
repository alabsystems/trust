// trust-symex binary replay scaffolding
//
// Provides conservative counterexample replay classification for lifted
// binary functions. This module validates against the lifted IR that
// trust-symex can execute and exposes an explicit trait boundary for external
// machine-code replay backends.

// Replay errors carry full counterexample state (registers, memory snapshot,
// constraint history) — they are intentionally large because callers need
// the full record to render diagnostics. Boxing is unnecessary since each
// invocation produces at most one Err.
#![allow(clippy::result_large_err)]
// Replay step constructors take the full execution slot (function, block,
// instruction, register file, memory, constraint stack, mode, label) by
// design; collapsing into a builder pattern would not simplify call sites.
#![allow(clippy::too_many_arguments)]
// The full replay return type is intentionally explicit at the public
// boundary so callers can pattern-match on it without an indirection.
#![allow(clippy::type_complexity)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use trust_disasm::{
    ControlFlow, Instruction, Operand as DisasmOperand, decode_aarch64, decode_x86_64,
    operand::{MemoryOperand, RegKind, Register},
};
use trust_machine_sem::{
    Aarch64Semantics, ConcreteState, Effect, MachineState, Semantics, X86_64Semantics,
};
use trust_types::digest::{is_stable_sha256_hex, stable_sha256_hex};
use trust_types::{
    BasicBlock, BinaryArtifactDigest, BinaryFactSubject, BinaryOrigin as TrustBinaryOrigin,
    BinarySelectedImageIdentity, BinaryStackBase, BinaryStorageLocation, ConstValue,
    Counterexample, CounterexampleTrace, CounterexampleValue, Formula, Operand, ReplayStatus,
    Rvalue, SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics, SourceSpan,
    Statement, Terminator, Ty, VerifiableFunction, VerificationCondition, VerificationResult,
};

use crate::adapter::{AdapterConfig, AdapterResult, replay_with_trace};

fn stable_json_sha256<T: Serialize>(value: &T) -> Option<String> {
    serde_json::to_vec(value).ok().map(|bytes| stable_sha256_hex(&bytes))
}

fn binary_witness_verification_context(
    vc: &VerificationCondition,
) -> Option<BinaryWitnessVerificationContext> {
    let vc_digest = stable_json_sha256(vc)?;
    let kind = serde_json::to_string(&vc.kind).unwrap_or_else(|_| format!("{:?}", vc.kind));
    Some(BinaryWitnessVerificationContext {
        vc_digest,
        kind,
        function: vc.function.to_string(),
        location: vc.location.clone(),
    })
}

/// Origin metadata for a binary function when no lifted body is available.
///
/// Passing a `BinaryOrigin` to replay is intentionally classified as
/// [`BinaryReplayStatus::NeedsMachineReplay`] until a machine-code replay
/// backend is wired in.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryOrigin {
    /// Optional path, build id, or image label for the binary.
    pub image: Option<String>,
    /// Optional architecture triple or processor family.
    pub architecture: Option<String>,
    /// Optional symbol or function name.
    pub function: Option<String>,
    /// Optional entry address for the function.
    pub entry: Option<u64>,
}

impl BinaryOrigin {
    /// Create origin metadata for a function entry address.
    #[must_use]
    pub fn new(entry: u64) -> Self {
        Self { entry: Some(entry), ..Self::default() }
    }
}

/// Replay target accepted by the binary replay API.
#[derive(Debug)]
pub enum BinaryReplayTarget<'a> {
    /// A lifted function whose body can be replayed by `trust-symex`.
    LiftedFunction(&'a VerifiableFunction),
    /// Binary-only origin metadata requiring a future machine-code executor.
    BinaryOrigin(BinaryOrigin),
}

impl<'a> BinaryReplayTarget<'a> {
    /// Create a lifted-function replay target.
    #[must_use]
    pub fn lifted(function: &'a VerifiableFunction) -> Self {
        Self::LiftedFunction(function)
    }

    /// Create a binary-origin replay target.
    #[must_use]
    pub fn binary_origin(origin: BinaryOrigin) -> Self {
        Self::BinaryOrigin(origin)
    }
}

/// A solver witness plus optional replay expectation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BinaryReplayInput {
    /// Counterexample-like model from a solver or bounded checker.
    pub counterexample: Counterexample,
    /// Exact root binary artifact digest associated with this witness.
    ///
    /// Instruction-byte provenance proves which bytes the trace names.
    /// Artifact digest identity proves those bytes came from the same root
    /// binary image that the replay backend executed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_digest: Option<BinaryArtifactDigest>,
    /// Exact selected loader image digest/range associated with this witness.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentity>,
    /// Whether proof-grade replay must carry selected-image identity.
    #[serde(default)]
    pub requires_selected_image_identity: bool,
    /// Exact machine instruction provenance associated with this witness.
    ///
    /// Machine replay can only satisfy proof-grade counterexample evidence
    /// when the normalized witness already names the original instruction
    /// bytes. Backend-observed bytes are checked against this provenance; they
    /// are not allowed to define it after the fact.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_provenance: Vec<TrustBinaryOrigin>,
    /// Original verification condition that produced the SAT witness.
    ///
    /// Lifted replay is only a confirmation of the witness against lifted IR
    /// when the original VC is threaded through with the model. Without it,
    /// the report stays at `NeedsMachineReplay` rather than relying on a
    /// synthetic placeholder predicate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verification_condition: Option<VerificationCondition>,
    /// Explicit mapping from solver model assignment names to per-step trace
    /// assignment names.
    ///
    /// Some solver traces SSA-rename variables between the top-level model and
    /// execution trace. Proof-grade replay can use this map instead of relying
    /// on raw assignment-name overlap.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub binding_map: Vec<BinaryWitnessBinding>,
    /// What replay is expected to demonstrate.
    ///
    /// A raw model without an expectation and trace is never classified as
    /// confirmed.
    pub expectation: Option<BinaryReplayExpectation>,
}

impl BinaryReplayInput {
    /// Create replay input from a counterexample-like model.
    #[must_use]
    pub fn new(counterexample: Counterexample) -> Self {
        Self {
            counterexample,
            artifact_digest: None,
            selected_image: None,
            requires_selected_image_identity: false,
            instruction_provenance: Vec::new(),
            verification_condition: None,
            binding_map: Vec::new(),
            expectation: None,
        }
    }

    /// Attach exact root binary artifact digest recovered from the parser.
    #[must_use]
    pub fn with_artifact_digest(mut self, artifact_digest: BinaryArtifactDigest) -> Self {
        self.artifact_digest = Some(artifact_digest);
        self
    }

    /// Attach exact selected loader image digest/range recovered from the parser.
    #[must_use]
    pub fn with_selected_image(mut self, selected_image: BinarySelectedImageIdentity) -> Self {
        self.selected_image = Some(selected_image);
        self
    }

    /// Require selected-image identity before machine replay can satisfy proof-grade evidence.
    #[must_use]
    pub fn require_selected_image_identity(mut self) -> Self {
        self.requires_selected_image_identity = true;
        self
    }

    /// Attach exact instruction provenance recovered from the binary artifact.
    #[must_use]
    pub fn with_instruction_provenance(
        mut self,
        instruction_provenance: impl Into<Vec<TrustBinaryOrigin>>,
    ) -> Self {
        self.instruction_provenance = instruction_provenance.into();
        self
    }

    /// Attach the original verification condition that produced this witness.
    #[must_use]
    pub fn with_verification_condition(mut self, vc: VerificationCondition) -> Self {
        self.verification_condition = Some(vc);
        self
    }

    /// Attach an explicit model-to-trace binding map for SSA-renamed traces.
    #[must_use]
    pub fn with_binding_map(mut self, binding_map: impl Into<Vec<BinaryWitnessBinding>>) -> Self {
        self.binding_map = binding_map.into();
        self
    }

    /// Add one explicit model-to-trace binding.
    #[must_use]
    pub fn with_binding(mut self, binding: BinaryWitnessBinding) -> Self {
        self.binding_map.push(binding);
        self
    }

    /// Attach the expected replay outcome.
    #[must_use]
    pub fn with_expectation(mut self, expectation: BinaryReplayExpectation) -> Self {
        self.expectation = Some(expectation);
        self
    }
}

impl From<Counterexample> for BinaryReplayInput {
    fn from(counterexample: Counterexample) -> Self {
        Self::new(counterexample)
    }
}

impl From<&Counterexample> for BinaryReplayInput {
    fn from(counterexample: &Counterexample) -> Self {
        Self::new(counterexample.clone())
    }
}

/// Expected outcome for a replayed witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryReplayExpectation {
    /// Replay should terminate normally.
    Terminates,
    /// Replay should reach a lifted `Unreachable` terminator.
    ReachesUnreachable,
    /// Replay should visit a block.
    VisitsBlock(usize),
    /// Replay should end at a specific block.
    EndsAtBlock(usize),
}

/// Explicit model-to-trace assignment binding for a normalized witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryWitnessBinding {
    /// Top-level solver model assignment name.
    pub model_name: String,
    /// Per-step trace assignment name.
    pub trace_name: String,
    /// Trace step where the renamed trace assignment must appear. When omitted,
    /// any trace step may satisfy the binding.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trace_step: Option<u32>,
}

impl BinaryWitnessBinding {
    #[must_use]
    pub fn new(model_name: impl Into<String>, trace_name: impl Into<String>) -> Self {
        Self { model_name: model_name.into(), trace_name: trace_name.into(), trace_step: None }
    }

    #[must_use]
    pub fn at_trace_step(mut self, trace_step: u32) -> Self {
        self.trace_step = Some(trace_step);
        self
    }
}

/// Source of a normalized binary witness assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryWitnessRecordSource {
    /// Top-level solver model assignment.
    ModelAssignment,
    /// Per-step assignment from a counterexample trace.
    TraceAssignment,
}

/// A solver value normalized for binary witness replay.
///
/// Top-level model assignments retain the typed `trust-types`
/// [`CounterexampleValue`]. Trace-step assignments are often raw strings from
/// solver/BMC output, so the raw spelling is retained even when a typed value
/// can be recovered.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryWitnessValue {
    /// Typed value when the input can be represented as a `trust-types`
    /// counterexample value.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub typed: Option<CounterexampleValue>,
    /// Raw solver spelling.
    pub raw: String,
}

impl BinaryWitnessValue {
    fn typed(value: &CounterexampleValue) -> Self {
        Self { typed: Some(value.clone()), raw: value.to_string() }
    }

    fn raw(value: &str) -> Self {
        Self { typed: parse_raw_counterexample_value(value), raw: value.to_owned() }
    }
}

/// Normalized program point for a binary witness trace step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryWitnessProgramPoint {
    /// Original program point label from the trace.
    pub raw: String,
    /// Lifted basic block index, when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub block: Option<usize>,
    /// Machine instruction provenance, when present in the trace label or
    /// inherited from binary-origin metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<TrustBinaryOrigin>,
}

/// A structured assignment in a normalized binary witness.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryWitnessRecord {
    /// Where this assignment came from.
    pub source: BinaryWitnessRecordSource,
    /// Raw solver variable name.
    pub raw_name: String,
    /// Normalized assignment value.
    pub value: BinaryWitnessValue,
    /// Existing `trust-types` subject schema for the assignment.
    pub subject: BinaryFactSubject,
    /// Existing `trust-types` storage schema when a physical location is
    /// recoverable from the solver name or lifted local metadata.
    pub storage: BinaryStorageLocation,
    /// Function provenance for this assignment.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    /// Lifted local index when the solver name maps to a TrustIr local.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub local_index: Option<usize>,
    /// Trace or instruction provenance for this assignment.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub program_point: Option<BinaryWitnessProgramPoint>,
}

/// One normalized trace step in a binary witness.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryWitnessTraceStep {
    /// Original solver/BMC step number.
    pub step: u32,
    /// Normalized program point.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub program_point: Option<BinaryWitnessProgramPoint>,
    /// Assignments observed at this step.
    pub assignments: Vec<BinaryWitnessRecord>,
}

/// Structured binary replay witness derived from solver/counterexample data.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct BinaryWitness {
    /// Function name or symbol associated with the witness.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    /// Function-entry or instruction provenance for the witness as a whole.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<TrustBinaryOrigin>,
    /// All normalized records, including top-level model assignments and trace
    /// step assignments.
    pub records: Vec<BinaryWitnessRecord>,
    /// Normalized counterexample trace steps.
    pub trace: Vec<BinaryWitnessTraceStep>,
    /// Number of raw top-level solver assignments received.
    pub raw_model_assignments: usize,
    /// Number of raw trace steps received.
    pub raw_trace_steps: usize,
    /// Whether the input carried any execution trace. A raw model without this
    /// remains unconfirmed regardless of replay configuration.
    pub has_execution_trace: bool,
    /// Source metadata retained during witness normalization.
    #[serde(default)]
    pub provenance: BinaryWitnessProvenance,
}

/// Stable proof-context identity retained with a normalized binary witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryWitnessVerificationContext {
    /// SHA-256 over the serialized verification condition that produced the witness.
    pub vc_digest: String,
    /// Serialized VC kind, retained for diagnostics without re-parsing the formula.
    pub kind: String,
    /// Function named by the verification condition.
    pub function: String,
    /// Source or binary location named by the verification condition.
    pub location: SourceSpan,
}

/// Source metadata retained when normalizing a binary witness.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryWitnessProvenance {
    /// Function name or symbol used as normalization context.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    /// Function-entry or binary-origin context used during normalization.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<TrustBinaryOrigin>,
    /// Exact root binary artifact digest used to bind normalized witness
    /// provenance to backend replay evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_digest: Option<BinaryArtifactDigest>,
    /// Exact selected loader image digest/range used to bind normalized witness
    /// provenance to backend replay evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentity>,
    /// Verification condition identity that produced this witness, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verification_context: Option<BinaryWitnessVerificationContext>,
    /// True when proof-grade replay must validate selected-image identity.
    #[serde(default)]
    pub requires_selected_image_identity: bool,
    /// Raw top-level solver assignment names, in deterministic order.
    pub model_assignment_names: Vec<String>,
    /// Raw trace program point labels, preserving missing labels.
    pub trace_program_points: Vec<Option<String>>,
    /// Instruction provenance recovered from normalized trace program points.
    pub trace_instruction_origins: Vec<TrustBinaryOrigin>,
    /// Explicit model-to-trace assignment bindings supplied with the witness.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub binding_map: Vec<BinaryWitnessBinding>,
}

/// Machine-code replay classification for a normalized binary witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayStatus {
    /// A machine-code backend replayed the witness and produced matching
    /// instruction-level evidence.
    Replayed,
    /// Machine replay contradicted the normalized witness.
    Spurious,
    /// No backend or insufficient witness provenance was available.
    NeedsMachineReplay,
    /// The backend cannot replay this witness shape or target.
    Unsupported,
    /// Machine replay was attempted but the backend failed before producing
    /// checked replay evidence.
    Failed,
}

impl BinaryMachineReplayStatus {
    #[must_use]
    pub fn as_trust_types_status(self) -> ReplayStatus {
        match self {
            Self::Replayed => ReplayStatus::Replayed,
            Self::Spurious => ReplayStatus::Spurious,
            Self::NeedsMachineReplay => ReplayStatus::NotAttempted,
            Self::Unsupported => ReplayStatus::Failed,
            Self::Failed => ReplayStatus::Failed,
        }
    }
}

impl fmt::Display for BinaryMachineReplayStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Replayed => f.write_str("replayed"),
            Self::Spurious => f.write_str("spurious"),
            Self::NeedsMachineReplay => f.write_str("needs_machine_replay"),
            Self::Unsupported => f.write_str("unsupported"),
            Self::Failed => f.write_str("failed"),
        }
    }
}

/// Configuration for machine-code replay validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayConfig {
    /// Require the backend instruction trace to exactly match instruction
    /// provenance from the normalized witness.
    pub require_exact_instruction_trace: bool,
    /// Require the backend artifact digest to exactly match the normalized
    /// witness artifact digest before reporting proof-grade replay.
    pub require_exact_artifact_digest: bool,
}

impl Default for BinaryMachineReplayConfig {
    fn default() -> Self {
        Self { require_exact_instruction_trace: true, require_exact_artifact_digest: true }
    }
}

/// One instruction observed by a machine-code replay backend.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineInstructionEvidence {
    /// Original machine-code instruction provenance.
    pub origin: TrustBinaryOrigin,
    /// Optional backend execution step.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
}

impl BinaryMachineInstructionEvidence {
    #[must_use]
    pub fn new(origin: TrustBinaryOrigin) -> Self {
        Self { origin, step: None }
    }
}

/// Control-flow capability a backend explicitly validated during replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayCapability {
    /// Conditional branch PC update was validated by decoded machine semantics.
    ConditionalBranch,
    /// Direct unconditional branch target was validated.
    DirectBranch,
    /// Register or memory indirect unconditional branch target was validated.
    IndirectBranch,
    /// Direct call target and return context were validated.
    DirectCall,
    /// Register or memory indirect call target and return context were validated.
    IndirectCall,
    /// Return target was validated from explicit call/stack witness context.
    Return,
}

impl fmt::Display for BinaryMachineReplayCapability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ConditionalBranch => f.write_str("conditional_branch"),
            Self::DirectBranch => f.write_str("direct_branch"),
            Self::IndirectBranch => f.write_str("indirect_branch"),
            Self::DirectCall => f.write_str("direct_call"),
            Self::IndirectCall => f.write_str("indirect_call"),
            Self::Return => f.write_str("return"),
        }
    }
}

/// Backend evidence for a validated non-fallthrough control-flow capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayCapabilityEvidence {
    pub capability: BinaryMachineReplayCapability,
    pub architecture: String,
    pub instruction_address: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_bytes: Vec<u8>,
    pub validation: String,
}

impl BinaryMachineReplayCapabilityEvidence {
    #[must_use]
    pub fn new(
        capability: BinaryMachineReplayCapability,
        architecture: impl Into<String>,
        instruction_address: u64,
        validation: impl Into<String>,
    ) -> Self {
        Self {
            capability,
            architecture: architecture.into(),
            instruction_address,
            step: None,
            instruction_bytes: Vec::new(),
            validation: validation.into(),
        }
    }

    #[must_use]
    pub fn with_step(mut self, step: Option<u32>) -> Self {
        self.step = step;
        self
    }

    #[must_use]
    pub fn with_instruction_bytes(mut self, instruction_bytes: impl Into<Vec<u8>>) -> Self {
        self.instruction_bytes = instruction_bytes.into();
        self
    }
}

/// Machine-effect class that a backend explicitly consumed for one replayed
/// instruction step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayEffectKind {
    /// Decoded instruction had no explicit machine-state effect; the backend
    /// still consumed the instruction step as a no-op.
    NoStateChange,
    /// General-purpose register write.
    RegisterWrite,
    /// Stack-pointer write.
    StackPointerWrite,
    /// Memory read.
    MemoryRead,
    /// Memory write.
    MemoryWrite,
    /// Condition-flag update.
    FlagUpdate,
    /// Program-counter update.
    ProgramCounterUpdate,
    /// Branch/call/return control-flow effect.
    ControlFlow,
    /// SIMD/FP register write.
    FloatingPointRegisterWrite,
    /// AArch64 synchronization/barrier effect.
    Aarch64SyncBoundary,
    /// AArch64 atomic/acquire/release effect.
    Aarch64AtomicAccess,
}

impl fmt::Display for BinaryMachineReplayEffectKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoStateChange => f.write_str("no_state_change"),
            Self::RegisterWrite => f.write_str("register_write"),
            Self::StackPointerWrite => f.write_str("stack_pointer_write"),
            Self::MemoryRead => f.write_str("memory_read"),
            Self::MemoryWrite => f.write_str("memory_write"),
            Self::FlagUpdate => f.write_str("flag_update"),
            Self::ProgramCounterUpdate => f.write_str("program_counter_update"),
            Self::ControlFlow => f.write_str("control_flow"),
            Self::FloatingPointRegisterWrite => f.write_str("floating_point_register_write"),
            Self::Aarch64SyncBoundary => f.write_str("aarch64_sync_boundary"),
            Self::Aarch64AtomicAccess => f.write_str("aarch64_atomic_access"),
        }
    }
}

/// Concrete scalar memory access consumed while replaying a machine-effect
/// witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayMemoryAccessEvidence {
    pub address: u64,
    pub width_bytes: u32,
}

impl BinaryMachineReplayMemoryAccessEvidence {
    #[must_use]
    pub const fn new(address: u64, width_bytes: u32) -> Self {
        Self { address, width_bytes }
    }

    #[must_use]
    pub fn end_address(self) -> Option<u64> {
        if self.width_bytes == 0 {
            return None;
        }
        self.address.checked_add(u64::from(self.width_bytes))
    }
}

/// Backend evidence that a machine-effect witness was consumed for one
/// replayed instruction step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayEffectEvidence {
    pub kind: BinaryMachineReplayEffectKind,
    pub architecture: String,
    pub instruction_address: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witness_step: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub subject: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub memory_access: Option<BinaryMachineReplayMemoryAccessEvidence>,
    pub validation: String,
}

impl BinaryMachineReplayEffectEvidence {
    #[must_use]
    pub fn new(
        kind: BinaryMachineReplayEffectKind,
        architecture: impl Into<String>,
        instruction_address: u64,
        validation: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            architecture: architecture.into(),
            instruction_address,
            step: None,
            witness_step: None,
            subject: None,
            memory_access: None,
            validation: validation.into(),
        }
    }

    #[must_use]
    pub fn with_step(mut self, step: Option<u32>) -> Self {
        self.step = step;
        self
    }

    #[must_use]
    pub fn with_witness_step(mut self, witness_step: Option<u32>) -> Self {
        self.witness_step = witness_step;
        self
    }

    #[must_use]
    pub fn with_subject(mut self, subject: impl Into<String>) -> Self {
        self.subject = Some(subject.into());
        self
    }

    #[must_use]
    pub fn with_memory_access(
        mut self,
        memory_access: BinaryMachineReplayMemoryAccessEvidence,
    ) -> Self {
        self.memory_access = Some(memory_access);
        self
    }
}

/// Typed effect-witness diagnostic carried when a replay cannot be consumed
/// by source backprop as proof-grade machine-effect evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayEffectDiagnosticKind {
    /// A replayed instruction step omitted required effect evidence.
    MissingMachineEffectWitness,
    /// The effect class exists, but this replay layer cannot proof-consume it.
    UnsupportedMachineEffectWitnessClass,
}

impl fmt::Display for BinaryMachineReplayEffectDiagnosticKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingMachineEffectWitness => f.write_str("missing_machine_effect_witness"),
            Self::UnsupportedMachineEffectWitnessClass => {
                f.write_str("unsupported_machine_effect_witness_class")
            }
        }
    }
}

/// Structured effect diagnostic for replay reports.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayEffectDiagnostic {
    pub kind: BinaryMachineReplayEffectDiagnosticKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub effect_kind: Option<BinaryMachineReplayEffectKind>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instruction_address: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witness_step: Option<u32>,
    pub diagnostic: String,
}

impl BinaryMachineReplayEffectDiagnostic {
    #[must_use]
    pub fn new(
        kind: BinaryMachineReplayEffectDiagnosticKind,
        diagnostic: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            effect_kind: None,
            instruction_address: None,
            step: None,
            witness_step: None,
            diagnostic: diagnostic.into(),
        }
    }

    #[must_use]
    pub fn with_effect_kind(mut self, effect_kind: BinaryMachineReplayEffectKind) -> Self {
        self.effect_kind = Some(effect_kind);
        self
    }

    #[must_use]
    pub fn with_instruction(mut self, instruction_address: u64, step: Option<u32>) -> Self {
        self.instruction_address = Some(instruction_address);
        self.step = step;
        self
    }

    #[must_use]
    pub fn with_witness_step(mut self, witness_step: Option<u32>) -> Self {
        self.witness_step = witness_step;
        self
    }
}

/// Replay boundary kind that requires exact boundary semantics before
/// proof-grade replay can be accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayBoundaryKind {
    /// System-call style transition.
    Syscall,
    /// Architectural exception boundary.
    Exception,
    /// Trap or breakpoint boundary.
    Trap,
}

impl fmt::Display for BinaryMachineReplayBoundaryKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syscall => f.write_str("syscall"),
            Self::Exception => f.write_str("exception"),
            Self::Trap => f.write_str("trap"),
        }
    }
}

/// Boundary semantics status carried by replay evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayBoundarySemantics {
    /// The replay reached a boundary for which exact witness semantics are not
    /// represented; proof-grade replay must fail closed.
    UnsupportedNoExactWitness,
}

impl fmt::Display for BinaryMachineReplayBoundarySemantics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedNoExactWitness => f.write_str("unsupported_no_exact_witness"),
        }
    }
}

/// Structured evidence for a syscall/exception/trap replay boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayBoundaryEvidence {
    pub kind: BinaryMachineReplayBoundaryKind,
    pub architecture: String,
    pub instruction_address: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_bytes: Vec<u8>,
    pub opcode: String,
    pub encoding: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub immediate: Option<u64>,
    pub semantics: BinaryMachineReplayBoundarySemantics,
    pub diagnostic: String,
}

/// Source-backprop attestation result for one replayed instruction slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayAttestationStatus {
    Accepted,
    Rejected,
}

impl fmt::Display for BinaryMachineReplayAttestationStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accepted => f.write_str("accepted"),
            Self::Rejected => f.write_str("rejected"),
        }
    }
}

/// Stable identity for a consumed machine effect in a source-backprop
/// attestation slice.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayEffectIdentity {
    pub kind: BinaryMachineReplayEffectKind,
    pub architecture: String,
    pub instruction_address: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub subject: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub memory_access: Option<BinaryMachineReplayMemoryAccessEvidence>,
}

impl BinaryMachineReplayEffectIdentity {
    #[must_use]
    pub fn from_evidence(evidence: &BinaryMachineReplayEffectEvidence) -> Self {
        Self {
            kind: evidence.kind,
            architecture: evidence.architecture.clone(),
            instruction_address: evidence.instruction_address,
            step: evidence.step,
            subject: evidence.subject.clone(),
            memory_access: evidence.memory_access,
        }
    }
}

/// Narrow accepted/rejected source-backprop attestation for one replayed
/// instruction's original bytes/range and consumed modeled machine effects.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayAttestationSlice {
    pub status: BinaryMachineReplayAttestationStatus,
    pub instruction_address: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub byte_range: Option<BinaryMachineReplayByteRangeEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_bytes: Vec<u8>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effect_identities: Vec<BinaryMachineReplayEffectIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostic: Option<String>,
}

impl BinaryMachineReplayAttestationSlice {
    #[must_use]
    pub fn accepted(
        instruction: &BinaryMachineInstructionEvidence,
        selected_image: BinarySelectedImageIdentity,
        byte_range: BinaryMachineReplayByteRangeEvidence,
        effect_identities: Vec<BinaryMachineReplayEffectIdentity>,
    ) -> Self {
        Self {
            status: BinaryMachineReplayAttestationStatus::Accepted,
            instruction_address: instruction.origin.instruction_address,
            step: instruction.step,
            selected_image: Some(selected_image),
            byte_range: Some(byte_range),
            instruction_bytes: instruction.origin.instruction_bytes.clone(),
            effect_identities,
            diagnostic: None,
        }
    }

    #[must_use]
    pub fn rejected(
        instruction: &BinaryMachineInstructionEvidence,
        selected_image: Option<BinarySelectedImageIdentity>,
        byte_range: Option<BinaryMachineReplayByteRangeEvidence>,
        effect_identities: Vec<BinaryMachineReplayEffectIdentity>,
        diagnostic: impl Into<String>,
    ) -> Self {
        Self {
            status: BinaryMachineReplayAttestationStatus::Rejected,
            instruction_address: instruction.origin.instruction_address,
            step: instruction.step,
            selected_image,
            byte_range,
            instruction_bytes: instruction.origin.instruction_bytes.clone(),
            effect_identities,
            diagnostic: Some(diagnostic.into()),
        }
    }

    #[must_use]
    pub fn is_accepted(&self) -> bool {
        self.status == BinaryMachineReplayAttestationStatus::Accepted
    }
}

/// Original-byte file range attested by a machine replay backend.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayByteRangeEvidence {
    pub instruction_address: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    /// Root-artifact file offset for the replayed instruction bytes.
    pub file_offset: u64,
    /// Number of original bytes replayed for this instruction.
    pub size: u64,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_bytes: Vec<u8>,
}

impl BinaryMachineReplayByteRangeEvidence {
    #[must_use]
    pub fn new(
        instruction_address: u64,
        step: Option<u32>,
        file_offset: u64,
        size: u64,
        instruction_bytes: impl Into<Vec<u8>>,
    ) -> Self {
        Self {
            instruction_address,
            step,
            file_offset,
            size,
            instruction_bytes: instruction_bytes.into(),
        }
    }

    #[must_use]
    pub fn end_offset(&self) -> Option<u64> {
        self.file_offset.checked_add(self.size)
    }
}

/// Typed byte/range diagnostic for replay identity evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryMachineReplayByteRangeDiagnosticKind {
    /// Replay did not attest a root-artifact byte range for a replayed instruction.
    MissingOriginalByteRangeAttestation,
    /// Attested range/bytes did not match the replayed instruction evidence.
    MismatchedOriginalByteRangeAttestation,
    /// Attested instruction bytes are outside the selected loader-image range.
    OriginalByteRangeOutsideSelectedImage,
    /// Backend selected-image file range differs from the normalized witness.
    SelectedImageByteRangeMismatch,
    /// Backend selected-image digest differs while the selected range matches.
    SelectedImageDigestMismatch,
}

impl fmt::Display for BinaryMachineReplayByteRangeDiagnosticKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingOriginalByteRangeAttestation => {
                f.write_str("missing_original_byte_range_attestation")
            }
            Self::MismatchedOriginalByteRangeAttestation => {
                f.write_str("mismatched_original_byte_range_attestation")
            }
            Self::OriginalByteRangeOutsideSelectedImage => {
                f.write_str("original_byte_range_outside_selected_image")
            }
            Self::SelectedImageByteRangeMismatch => {
                f.write_str("selected_image_byte_range_mismatch")
            }
            Self::SelectedImageDigestMismatch => f.write_str("selected_image_digest_mismatch"),
        }
    }
}

/// Structured diagnostic attached to replay reports when byte/range identity is not proof-grade.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayByteRangeDiagnostic {
    pub kind: BinaryMachineReplayByteRangeDiagnosticKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instruction_address: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file_offset: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub size: Option<u64>,
    pub diagnostic: String,
}

impl BinaryMachineReplayByteRangeDiagnostic {
    #[must_use]
    pub fn new(
        kind: BinaryMachineReplayByteRangeDiagnosticKind,
        diagnostic: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            instruction_address: None,
            step: None,
            file_offset: None,
            size: None,
            diagnostic: diagnostic.into(),
        }
    }

    #[must_use]
    pub fn with_instruction(mut self, instruction_address: u64, step: Option<u32>) -> Self {
        self.instruction_address = Some(instruction_address);
        self.step = step;
        self
    }

    #[must_use]
    pub fn with_file_range(mut self, file_offset: u64, size: u64) -> Self {
        self.file_offset = Some(file_offset);
        self.size = Some(size);
        self
    }
}

/// Backend-provided machine replay result before witness/provenance validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayResult {
    pub status: BinaryMachineReplayStatus,
    pub backend: String,
    pub reason: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_digest: Option<BinaryArtifactDigest>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentity>,
    pub instruction_trace: Vec<BinaryMachineInstructionEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub capability_evidence: Vec<BinaryMachineReplayCapabilityEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effect_evidence: Vec<BinaryMachineReplayEffectEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effect_diagnostics: Vec<BinaryMachineReplayEffectDiagnostic>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub byte_range_evidence: Vec<BinaryMachineReplayByteRangeEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub byte_range_diagnostics: Vec<BinaryMachineReplayByteRangeDiagnostic>,
}

impl BinaryMachineReplayResult {
    #[must_use]
    pub fn unavailable(reason: impl Into<String>) -> Self {
        Self {
            status: BinaryMachineReplayStatus::NeedsMachineReplay,
            backend: "unavailable".into(),
            reason: reason.into(),
            artifact_digest: None,
            selected_image: None,
            instruction_trace: Vec::new(),
            capability_evidence: Vec::new(),
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
        }
    }

    #[must_use]
    pub fn replayed(
        backend: impl Into<String>,
        instruction_trace: Vec<BinaryMachineInstructionEvidence>,
    ) -> Self {
        Self {
            status: BinaryMachineReplayStatus::Replayed,
            backend: backend.into(),
            reason: "machine-code backend reported replay success".into(),
            artifact_digest: None,
            selected_image: None,
            instruction_trace,
            capability_evidence: Vec::new(),
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_capability_evidence(
        mut self,
        capability_evidence: impl Into<Vec<BinaryMachineReplayCapabilityEvidence>>,
    ) -> Self {
        self.capability_evidence = capability_evidence.into();
        self
    }

    #[must_use]
    pub fn with_effect_evidence(
        mut self,
        effect_evidence: impl Into<Vec<BinaryMachineReplayEffectEvidence>>,
    ) -> Self {
        self.effect_evidence = effect_evidence.into();
        self
    }

    #[must_use]
    pub fn with_effect_diagnostics(
        mut self,
        effect_diagnostics: impl Into<Vec<BinaryMachineReplayEffectDiagnostic>>,
    ) -> Self {
        self.effect_diagnostics = effect_diagnostics.into();
        self
    }

    #[must_use]
    pub fn with_byte_range_evidence(
        mut self,
        byte_range_evidence: impl Into<Vec<BinaryMachineReplayByteRangeEvidence>>,
    ) -> Self {
        self.byte_range_evidence = byte_range_evidence.into();
        self
    }

    #[must_use]
    pub fn with_byte_range_diagnostics(
        mut self,
        byte_range_diagnostics: impl Into<Vec<BinaryMachineReplayByteRangeDiagnostic>>,
    ) -> Self {
        self.byte_range_diagnostics = byte_range_diagnostics.into();
        self
    }

    #[must_use]
    pub fn with_artifact_digest(mut self, artifact_digest: BinaryArtifactDigest) -> Self {
        self.artifact_digest = Some(artifact_digest);
        self
    }

    #[must_use]
    pub fn with_optional_artifact_digest(
        mut self,
        artifact_digest: Option<BinaryArtifactDigest>,
    ) -> Self {
        self.artifact_digest = artifact_digest;
        self
    }

    #[must_use]
    pub fn with_selected_image(mut self, selected_image: BinarySelectedImageIdentity) -> Self {
        self.selected_image = Some(selected_image);
        self
    }

    #[must_use]
    pub fn with_optional_selected_image(
        mut self,
        selected_image: Option<BinarySelectedImageIdentity>,
    ) -> Self {
        self.selected_image = selected_image;
        self
    }

    #[must_use]
    pub fn failed(backend: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            status: BinaryMachineReplayStatus::Failed,
            backend: backend.into(),
            reason: reason.into(),
            artifact_digest: None,
            selected_image: None,
            instruction_trace: Vec::new(),
            capability_evidence: Vec::new(),
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
        }
    }
}

impl Default for BinaryMachineReplayResult {
    fn default() -> Self {
        Self::unavailable("machine-code replay backend unavailable")
    }
}

/// Validated machine replay report attached to a binary replay result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMachineReplayReport {
    pub status: BinaryMachineReplayStatus,
    #[serde(
        serialize_with = "serialize_replay_status",
        deserialize_with = "deserialize_replay_status"
    )]
    pub trust_types_status: ReplayStatus,
    pub backend: String,
    pub reason: String,
    /// Artifact digest required by the normalized witness.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_artifact_digest: Option<BinaryArtifactDigest>,
    /// Artifact digest returned by the backend replay evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub observed_artifact_digest: Option<BinaryArtifactDigest>,
    /// True only when backend artifact identity matches normalized witness
    /// artifact identity, or artifact identity was not required.
    pub matched_artifact_digest: bool,
    /// Selected loader image identity required by the normalized witness.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_selected_image: Option<BinarySelectedImageIdentity>,
    /// Selected loader image identity returned by the backend replay evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub observed_selected_image: Option<BinarySelectedImageIdentity>,
    /// True only when backend selected-image identity matches normalized witness
    /// selected-image identity, or selected-image identity was not required.
    #[serde(default)]
    pub matched_selected_image: bool,
    /// Instruction provenance required by the normalized witness.
    pub expected_instruction_trace: Vec<TrustBinaryOrigin>,
    /// Instruction provenance returned by the backend.
    pub observed_instruction_trace: Vec<BinaryMachineInstructionEvidence>,
    /// True only when backend evidence matches the normalized witness.
    pub matched_instruction_trace: bool,
    /// Backend evidence for validated non-fallthrough control-flow capability.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub capability_evidence: Vec<BinaryMachineReplayCapabilityEvidence>,
    /// True only when every decoded non-fallthrough control-flow instruction
    /// requiring explicit backend capability evidence has matching evidence.
    #[serde(default)]
    pub matched_capability_evidence: bool,
    /// Backend evidence for consumed machine effects at replayed instruction
    /// steps.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effect_evidence: Vec<BinaryMachineReplayEffectEvidence>,
    /// Structured machine-effect witness diagnostics.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effect_diagnostics: Vec<BinaryMachineReplayEffectDiagnostic>,
    /// True only when every replayed instruction step has matching supported
    /// machine-effect evidence and no unsupported effect diagnostic.
    #[serde(default)]
    pub matched_effect_evidence: bool,
    /// Original-byte file ranges attested for replayed instructions.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub byte_range_evidence: Vec<BinaryMachineReplayByteRangeEvidence>,
    /// Structured byte/range identity diagnostics.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub byte_range_diagnostics: Vec<BinaryMachineReplayByteRangeDiagnostic>,
    /// Structured syscall/exception/trap boundary diagnostics. Presence means
    /// replay reached a boundary that cannot satisfy proof-grade evidence
    /// unless exact boundary semantics are represented.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub boundary_evidence: Vec<BinaryMachineReplayBoundaryEvidence>,
    /// Accepted/rejected instruction-level attestations joining selected-image
    /// identity, original instruction byte ranges, and consumed modeled
    /// machine-effect identities.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub attestation_slices: Vec<BinaryMachineReplayAttestationSlice>,
    /// SHA-256 over the finalized replay transcript fields, excluding this digest.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay_transcript_digest: Option<String>,
}

impl BinaryMachineReplayReport {
    /// True only when this report carries the exact replay identity a
    /// source-backprop gate needs from symex: replayed status, matched
    /// instruction provenance, root artifact identity, selected-image identity,
    /// original byte/range attestation, explicit control-flow capability
    /// evidence, replay transcript digest, and no unchecked boundary.
    #[must_use]
    pub fn source_backprop_replay_ready(&self) -> bool {
        self.source_backprop_replay_blocker_reason().is_none()
    }

    /// Human-readable reason this machine replay report must not be consumed
    /// by source backprop yet.
    #[must_use]
    pub fn source_backprop_replay_blocker_reason(&self) -> Option<String> {
        if !self.boundary_evidence.is_empty() {
            return Some(boundary_reason_from_evidence(&self.boundary_evidence[0]));
        }
        if let Some(diagnostic) = self.byte_range_diagnostics.first() {
            return Some(format!("source-backprop blocked: {}", diagnostic.diagnostic));
        }
        if self.status != BinaryMachineReplayStatus::Replayed
            || self.trust_types_status != ReplayStatus::Replayed
        {
            if !self.reason.is_empty() {
                return Some(format!("source-backprop blocked: {}", self.reason));
            }
            return Some(format!(
                "source-backprop requires replayed machine evidence; report status is {} / {:?}",
                self.status, self.trust_types_status
            ));
        }
        if self.expected_instruction_trace.is_empty() {
            return Some(
                "source-backprop requires expected instruction provenance from the normalized witness"
                    .into(),
            );
        }
        if self.observed_instruction_trace.is_empty() {
            return Some(
                "source-backprop requires observed instruction provenance from machine replay"
                    .into(),
            );
        }
        if !self.matched_instruction_trace {
            return Some(
                "source-backprop requires exact matched instruction trace identity".into(),
            );
        }
        if !self.matched_artifact_digest {
            return Some(
                "source-backprop requires exact matched root binary artifact digest identity"
                    .into(),
            );
        }
        if let Some(reason) = self.source_backprop_artifact_digest_blocker_reason() {
            return Some(reason);
        }
        if !self.matched_selected_image {
            return Some(
                "source-backprop requires exact matched selected-image digest/range identity"
                    .into(),
            );
        }
        if let Some(reason) = self.source_backprop_selected_image_blocker_reason() {
            return Some(reason);
        }
        if let Some(reason) = self.source_backprop_byte_range_attestation_blocker_reason() {
            return Some(reason);
        }
        if let Some(reason) = missing_control_flow_capability_evidence_reason_from_parts(
            &self.observed_instruction_trace,
            &self.capability_evidence,
        ) {
            return Some(format!(
                "source-backprop requires explicit backend capability evidence for every replayed branch/call/return validation: {reason}"
            ));
        }
        if !self.matched_capability_evidence {
            return Some(
                "source-backprop requires explicit backend capability evidence for every replayed branch/call/return validation"
                    .into(),
            );
        }
        if let Some(reason) = self.source_backprop_effect_evidence_blocker_reason() {
            return Some(reason);
        }
        if let Some(reason) = self.source_backprop_attestation_slice_blocker_reason() {
            return Some(reason);
        }
        if let Some(reason) = self.source_backprop_replay_transcript_digest_blocker_reason() {
            return Some(reason);
        }
        None
    }

    fn source_backprop_replay_transcript_digest_blocker_reason(&self) -> Option<String> {
        let Some(digest) = self.replay_transcript_digest.as_deref() else {
            return Some(
                "source-backprop requires a replay transcript digest binding finalized machine evidence"
                    .into(),
            );
        };
        if !is_stable_sha256_hex(digest) {
            return Some(
                "source-backprop requires a canonical SHA-256 replay transcript digest".into(),
            );
        }
        let Some(observed) = self.compute_replay_transcript_digest() else {
            return Some(
                "source-backprop requires a replay transcript digest that can be recomputed from report evidence"
                    .into(),
            );
        };
        if digest != observed {
            return Some(
                "source-backprop requires replay transcript digest to match current machine evidence"
                    .into(),
            );
        }
        None
    }

    fn source_backprop_attestation_slice_blocker_reason(&self) -> Option<String> {
        if self.attestation_slices.is_empty() {
            return Some(
                "source-backprop requires an accepted instruction byte/range plus machine-effect attestation slice"
                    .into(),
            );
        }
        if let Some(rejected) = self.attestation_slices.iter().find(|slice| !slice.is_accepted()) {
            let reason = rejected
                .diagnostic
                .as_deref()
                .unwrap_or("attestation slice was rejected without a diagnostic");
            return Some(format!("source-backprop blocked: {reason}"));
        }
        for instruction in &self.observed_instruction_trace {
            let address = instruction.origin.instruction_address;
            let Some(slice) = self.attestation_slices.iter().find(|slice| {
                slice.instruction_address == address
                    && slice.step == instruction.step
                    && slice.is_accepted()
            }) else {
                return Some(format!(
                    "source-backprop requires an accepted instruction byte/range plus machine-effect attestation slice for instruction 0x{address:x}"
                ));
            };
            if let Some(reason) = accepted_attestation_slice_blocker_reason(slice, instruction) {
                return Some(reason);
            }
        }
        None
    }

    fn source_backprop_effect_evidence_blocker_reason(&self) -> Option<String> {
        if let Some(diagnostic) = self.effect_diagnostics.first() {
            return Some(format!("source-backprop blocked: {}", diagnostic.diagnostic));
        }
        if let Some(reason) = machine_effect_evidence_blocker_reason_from_parts(
            &self.observed_instruction_trace,
            &self.effect_evidence,
            &self.effect_diagnostics,
        ) {
            return Some(format!(
                "source-backprop requires machine-effect witnesses consumed for every replayed instruction step: {reason}"
            ));
        }
        if !self.matched_effect_evidence {
            return Some(
                "source-backprop requires machine-effect witnesses consumed for every replayed instruction step"
                    .into(),
            );
        }
        None
    }

    fn source_backprop_byte_range_attestation_blocker_reason(&self) -> Option<String> {
        let selected_image = self.expected_selected_image.as_ref()?;
        let selected_end = selected_image.end_offset()?;
        if self.byte_range_evidence.is_empty() {
            return Some(
                "source-backprop requires original byte/range attestation for every replayed instruction in the selected image"
                    .into(),
            );
        }

        for instruction in &self.observed_instruction_trace {
            let address = instruction.origin.instruction_address;
            let Some(step) = instruction.step else {
                return Some(format!(
                    "source-backprop requires replayed instruction 0x{address:x} to be bound to a machine trace step before original byte/range attestation can be used"
                ));
            };
            let Some(evidence) = self.byte_range_evidence.iter().find(|evidence| {
                evidence.instruction_address == address && evidence.step == Some(step)
            }) else {
                return Some(format!(
                    "source-backprop requires original byte/range attestation for replayed instruction 0x{address:x} at machine trace step {step}"
                ));
            };
            if evidence.size != instruction.origin.instruction_bytes.len() as u64
                || evidence.instruction_bytes != instruction.origin.instruction_bytes
            {
                return Some(format!(
                    "source-backprop requires original byte/range attestation to match replayed bytes for instruction 0x{address:x}"
                ));
            }
            let Some(evidence_end) = evidence.end_offset() else {
                return Some(format!(
                    "source-backprop requires non-overflowing original byte/range attestation for instruction 0x{address:x}"
                ));
            };
            if evidence.file_offset < selected_image.file_offset || evidence_end > selected_end {
                return Some(format!(
                    "source-backprop requires original byte/range attestation for instruction 0x{address:x} to lie inside selected-image byte range [0x{:x}..0x{:x})",
                    selected_image.file_offset, selected_end
                ));
            }
        }
        None
    }

    fn source_backprop_artifact_digest_blocker_reason(&self) -> Option<String> {
        let Some(expected) = self.expected_artifact_digest.as_ref() else {
            return Some(
                "source-backprop requires expected root binary artifact digest identity".into(),
            );
        };
        let Some(observed) = self.observed_artifact_digest.as_ref() else {
            return Some(
                "source-backprop requires observed root binary artifact digest identity".into(),
            );
        };
        if !expected.is_canonical_sha256() {
            return Some(
                "source-backprop requires canonical expected root binary artifact digest identity"
                    .into(),
            );
        }
        if !observed.is_canonical_sha256() {
            return Some(
                "source-backprop requires canonical observed root binary artifact digest identity"
                    .into(),
            );
        }
        if expected != observed {
            return Some(
                "source-backprop requires exact matched root binary artifact digest identity"
                    .into(),
            );
        }
        None
    }

    fn source_backprop_selected_image_blocker_reason(&self) -> Option<String> {
        let Some(expected) = self.expected_selected_image.as_ref() else {
            return Some(
                "source-backprop requires expected selected-image digest/range identity".into(),
            );
        };
        let Some(observed) = self.observed_selected_image.as_ref() else {
            return Some(
                "source-backprop requires observed selected-image digest/range identity".into(),
            );
        };
        if !selected_image_identity_is_replay_grade(expected) {
            return Some(
                "source-backprop requires canonical expected selected-image digest/range identity"
                    .into(),
            );
        }
        if !selected_image_identity_is_replay_grade(observed) {
            return Some(
                "source-backprop requires canonical observed selected-image digest/range identity"
                    .into(),
            );
        }
        if expected != observed {
            return Some(
                "source-backprop requires exact matched selected-image digest/range identity"
                    .into(),
            );
        }
        None
    }

    fn new(
        status: BinaryMachineReplayStatus,
        backend: impl Into<String>,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            status,
            trust_types_status: status.as_trust_types_status(),
            backend: backend.into(),
            reason: reason.into(),
            expected_artifact_digest: None,
            observed_artifact_digest: None,
            matched_artifact_digest: false,
            expected_selected_image: None,
            observed_selected_image: None,
            matched_selected_image: false,
            expected_instruction_trace: Vec::new(),
            observed_instruction_trace: Vec::new(),
            matched_instruction_trace: false,
            capability_evidence: Vec::new(),
            matched_capability_evidence: false,
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            matched_effect_evidence: false,
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
            boundary_evidence: Vec::new(),
            attestation_slices: Vec::new(),
            replay_transcript_digest: None,
        }
    }

    fn from_backend_result(
        status: BinaryMachineReplayStatus,
        result: BinaryMachineReplayResult,
        expected_artifact_digest: Option<BinaryArtifactDigest>,
        matched_artifact_digest: bool,
        expected_selected_image: Option<BinarySelectedImageIdentity>,
        matched_selected_image: bool,
        expected_instruction_trace: Vec<TrustBinaryOrigin>,
        matched_instruction_trace: bool,
        reason: impl Into<String>,
    ) -> Self {
        let report = Self {
            status,
            trust_types_status: status.as_trust_types_status(),
            backend: result.backend,
            reason: reason.into(),
            expected_artifact_digest,
            observed_artifact_digest: result.artifact_digest,
            matched_artifact_digest,
            expected_selected_image,
            observed_selected_image: result.selected_image,
            matched_selected_image,
            expected_instruction_trace,
            observed_instruction_trace: result.instruction_trace,
            matched_instruction_trace,
            capability_evidence: result.capability_evidence,
            matched_capability_evidence: false,
            effect_evidence: result.effect_evidence,
            effect_diagnostics: result.effect_diagnostics,
            matched_effect_evidence: false,
            byte_range_evidence: result.byte_range_evidence,
            byte_range_diagnostics: result.byte_range_diagnostics,
            boundary_evidence: Vec::new(),
            attestation_slices: Vec::new(),
            replay_transcript_digest: None,
        };
        report.with_derived_attestation_slices()
    }

    fn with_matched_capability_evidence(mut self, matched_capability_evidence: bool) -> Self {
        self.matched_capability_evidence = matched_capability_evidence;
        self.with_replay_transcript_digest()
    }

    fn with_matched_effect_evidence(mut self, matched_effect_evidence: bool) -> Self {
        self.matched_effect_evidence = matched_effect_evidence;
        self.with_replay_transcript_digest()
    }

    fn with_boundary_evidence(
        mut self,
        boundary_evidence: Vec<BinaryMachineReplayBoundaryEvidence>,
    ) -> Self {
        self.boundary_evidence = boundary_evidence;
        self.attestation_slices = machine_attestation_slices_from_report(&self);
        self.with_replay_transcript_digest()
    }

    fn with_derived_attestation_slices(mut self) -> Self {
        self.attestation_slices = machine_attestation_slices_from_report(&self);
        self.with_replay_transcript_digest()
    }

    fn ensure_byte_range_diagnostic(
        mut self,
        diagnostic: BinaryMachineReplayByteRangeDiagnostic,
    ) -> Self {
        if !self.byte_range_diagnostics.iter().any(|existing| existing == &diagnostic) {
            self.byte_range_diagnostics.push(diagnostic);
        }
        self.attestation_slices = machine_attestation_slices_from_report(&self);
        self.with_replay_transcript_digest()
    }

    fn ensure_effect_diagnostic(mut self, diagnostic: BinaryMachineReplayEffectDiagnostic) -> Self {
        if !self.effect_diagnostics.iter().any(|existing| existing == &diagnostic) {
            self.effect_diagnostics.push(diagnostic);
        }
        self.attestation_slices = machine_attestation_slices_from_report(&self);
        self.with_replay_transcript_digest()
    }

    fn with_replay_transcript_digest(mut self) -> Self {
        self.replay_transcript_digest = self.compute_replay_transcript_digest();
        self
    }

    fn compute_replay_transcript_digest(&self) -> Option<String> {
        stable_json_sha256(&BinaryMachineReplayTranscript {
            status: &self.status,
            trust_types_status: &self.trust_types_status,
            backend: &self.backend,
            reason: &self.reason,
            expected_artifact_digest: &self.expected_artifact_digest,
            observed_artifact_digest: &self.observed_artifact_digest,
            matched_artifact_digest: self.matched_artifact_digest,
            expected_selected_image: &self.expected_selected_image,
            observed_selected_image: &self.observed_selected_image,
            matched_selected_image: self.matched_selected_image,
            expected_instruction_trace: &self.expected_instruction_trace,
            observed_instruction_trace: &self.observed_instruction_trace,
            matched_instruction_trace: self.matched_instruction_trace,
            capability_evidence: &self.capability_evidence,
            matched_capability_evidence: self.matched_capability_evidence,
            effect_evidence: &self.effect_evidence,
            effect_diagnostics: &self.effect_diagnostics,
            matched_effect_evidence: self.matched_effect_evidence,
            byte_range_evidence: &self.byte_range_evidence,
            byte_range_diagnostics: &self.byte_range_diagnostics,
            boundary_evidence: &self.boundary_evidence,
            attestation_slices: &self.attestation_slices,
        })
    }
}

#[derive(Serialize)]
struct BinaryMachineReplayTranscript<'a> {
    status: &'a BinaryMachineReplayStatus,
    trust_types_status: &'a ReplayStatus,
    backend: &'a str,
    reason: &'a str,
    expected_artifact_digest: &'a Option<BinaryArtifactDigest>,
    observed_artifact_digest: &'a Option<BinaryArtifactDigest>,
    matched_artifact_digest: bool,
    expected_selected_image: &'a Option<BinarySelectedImageIdentity>,
    observed_selected_image: &'a Option<BinarySelectedImageIdentity>,
    matched_selected_image: bool,
    expected_instruction_trace: &'a [TrustBinaryOrigin],
    observed_instruction_trace: &'a [BinaryMachineInstructionEvidence],
    matched_instruction_trace: bool,
    capability_evidence: &'a [BinaryMachineReplayCapabilityEvidence],
    matched_capability_evidence: bool,
    effect_evidence: &'a [BinaryMachineReplayEffectEvidence],
    effect_diagnostics: &'a [BinaryMachineReplayEffectDiagnostic],
    matched_effect_evidence: bool,
    byte_range_evidence: &'a [BinaryMachineReplayByteRangeEvidence],
    byte_range_diagnostics: &'a [BinaryMachineReplayByteRangeDiagnostic],
    boundary_evidence: &'a [BinaryMachineReplayBoundaryEvidence],
    attestation_slices: &'a [BinaryMachineReplayAttestationSlice],
}

impl Default for BinaryMachineReplayReport {
    fn default() -> Self {
        Self::new(
            BinaryMachineReplayStatus::NeedsMachineReplay,
            "unavailable",
            "machine-code replay backend unavailable",
        )
    }
}

/// Assurance required for a binary solver dispatch.
///
/// SAT counterexample witnesses are only release-grade when replayed against
/// original machine code with an exact instruction trace. UNSAT/proved VCs do
/// not carry exploit witnesses; they require checked proof certificates
/// instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryReplayRequirement {
    /// A SAT/failed counterexample witness must be replayed exactly on the
    /// original machine-code provenance.
    ExactMachineWitnessReplay,
    /// A proved UNSAT VC must have a locally checked proof certificate.
    CheckedUnsatCertificate,
    /// The dispatch state or query semantics is not supported by the binary
    /// replay/certificate split.
    UnknownUnsupportedState,
}

impl BinaryReplayRequirement {
    /// True when this requirement is for counterexample machine replay.
    #[must_use]
    pub fn requires_machine_witness_replay(self) -> bool {
        matches!(self, Self::ExactMachineWitnessReplay)
    }

    /// True when this requirement is for a checked UNSAT proof certificate.
    #[must_use]
    pub fn requires_checked_certificate(self) -> bool {
        matches!(self, Self::CheckedUnsatCertificate)
    }
}

impl fmt::Display for BinaryReplayRequirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExactMachineWitnessReplay => f.write_str("exact_machine_witness_replay"),
            Self::CheckedUnsatCertificate => f.write_str("checked_unsat_certificate"),
            Self::UnknownUnsupportedState => f.write_str("unknown_unsupported_state"),
        }
    }
}

/// Conservative replay evidence derived from one binary solver dispatch.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinarySolverDispatchReplayEvidence {
    /// Solver dispatch id.
    pub dispatch_id: String,
    /// Coarse replay status suitable for feeding back into
    /// [`SolverDispatchRecord::replay`].
    #[serde(
        serialize_with = "serialize_replay_status",
        deserialize_with = "deserialize_replay_status"
    )]
    pub replay: ReplayStatus,
    /// Binary replay report when the dispatch carried a SAT counterexample
    /// witness.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay_report: Option<BinaryReplayReport>,
    /// Dispatch-level assurance required before the solver result can be used
    /// as binary release evidence.
    pub replay_requirement: BinaryReplayRequirement,
    /// Whether the required replay/certificate evidence is already satisfied.
    pub requirement_satisfied: bool,
    /// Human-readable conservative classification reason.
    pub reason: String,
}

impl BinarySolverDispatchReplayEvidence {
    fn no_witness(
        dispatch: &SolverDispatchRecord,
        replay_requirement: BinaryReplayRequirement,
        requirement_satisfied: bool,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            dispatch_id: dispatch.id.clone(),
            replay: ReplayStatus::NotAttempted,
            replay_report: None,
            replay_requirement,
            requirement_satisfied,
            reason: reason.into(),
        }
    }

    fn with_report(
        dispatch: &SolverDispatchRecord,
        replay_report: BinaryReplayReport,
        replay_requirement: BinaryReplayRequirement,
        requirement_satisfied: bool,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            dispatch_id: dispatch.id.clone(),
            replay: replay_report.trust_types_status,
            replay_report: Some(replay_report),
            replay_requirement,
            requirement_satisfied,
            reason: reason.into(),
        }
    }

    #[must_use]
    pub fn produced_witness(&self) -> bool {
        self.replay_report.is_some()
    }

    /// True when this dispatch still needs exact machine-code witness replay.
    #[must_use]
    pub fn needs_machine_witness_replay(&self) -> bool {
        self.replay_requirement.requires_machine_witness_replay() && !self.requirement_satisfied
    }

    /// True when this dispatch still needs a checked UNSAT proof certificate.
    #[must_use]
    pub fn needs_checked_certificate(&self) -> bool {
        self.replay_requirement.requires_checked_certificate() && !self.requirement_satisfied
    }
}

/// Request passed to a machine-code replay backend.
pub struct BinaryMachineReplayRequest<'a> {
    pub witness: &'a BinaryWitness,
    pub config: &'a BinaryMachineReplayConfig,
}

/// Machine-code witness replay backend boundary.
///
/// Implementations may execute original machine code, emulators, hardware
/// traces, or independently checked logs. A backend success is still validated
/// against normalized witness instruction provenance before this module reports
/// [`BinaryMachineReplayStatus::Replayed`].
pub trait BinaryMachineReplayBackend {
    fn replay(&self, request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult;
}

/// Architecture selector for bounded machine-code replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BoundedMachineCodeArchitecture {
    Aarch64,
    X86_64,
    Unsupported,
}

fn bounded_architecture_name(architecture: BoundedMachineCodeArchitecture) -> &'static str {
    match architecture {
        BoundedMachineCodeArchitecture::Aarch64 => "AArch64",
        BoundedMachineCodeArchitecture::X86_64 => "x86_64",
        BoundedMachineCodeArchitecture::Unsupported => "unsupported",
    }
}

fn alternate_architecture_decode_name(
    selected: BoundedMachineCodeArchitecture,
    bytes: &[u8],
    address: u64,
) -> Option<&'static str> {
    match selected {
        BoundedMachineCodeArchitecture::Aarch64 => decode_x86_64(bytes, address)
            .ok()
            .filter(|instruction| instruction.bytes == bytes)
            .map(|_| bounded_architecture_name(BoundedMachineCodeArchitecture::X86_64)),
        BoundedMachineCodeArchitecture::X86_64 => decode_aarch64(bytes, address)
            .ok()
            .filter(|instruction| instruction.bytes == bytes)
            .map(|_| bounded_architecture_name(BoundedMachineCodeArchitecture::Aarch64)),
        BoundedMachineCodeArchitecture::Unsupported => None,
    }
}

fn architecture_decode_failure_reason(
    selected: BoundedMachineCodeArchitecture,
    mapped: &BoundedMachineInstructionBytes,
    detail: impl fmt::Display,
) -> String {
    let selected_name = bounded_architecture_name(selected);
    if let Some(alternate_name) =
        alternate_architecture_decode_name(selected, &mapped.bytes, mapped.address)
    {
        return format!(
            "bounded machine replay architecture mismatch: selected image architecture is {selected_name} but instruction bytes at 0x{:x} decode exactly as {alternate_name}; failed to decode {selected_name} instruction: {detail}",
            mapped.address
        );
    }
    format!("failed to decode {selected_name} instruction at 0x{:x}: {detail}", mapped.address)
}

fn bounded_capability_validation(
    architecture: BoundedMachineCodeArchitecture,
    capability: BinaryMachineReplayCapability,
) -> &'static str {
    match (architecture, capability) {
        (_, BinaryMachineReplayCapability::ConditionalBranch) => {
            "decoded machine semantics validated conditional branch PC update"
        }
        (
            BoundedMachineCodeArchitecture::Aarch64,
            BinaryMachineReplayCapability::IndirectBranch,
        ) => "AArch64 register-indirect branch target validated from exact register witness",
        (BoundedMachineCodeArchitecture::Aarch64, BinaryMachineReplayCapability::DirectCall) => {
            "AArch64 direct call target and saved return-address witness context validated"
        }
        (BoundedMachineCodeArchitecture::Aarch64, BinaryMachineReplayCapability::IndirectCall) => {
            "AArch64 register-indirect call target and saved return-address witness context validated"
        }
        (BoundedMachineCodeArchitecture::Aarch64, BinaryMachineReplayCapability::Return) => {
            "AArch64 return target validated from saved return-address stack witness"
        }
        (BoundedMachineCodeArchitecture::X86_64, BinaryMachineReplayCapability::DirectCall) => {
            "x86_64 direct call target, pushed return address, and post-call stack witness context validated"
        }
        (BoundedMachineCodeArchitecture::X86_64, BinaryMachineReplayCapability::IndirectCall) => {
            "x86_64 indirect call target, pushed return address, and post-call stack witness context validated"
        }
        (BoundedMachineCodeArchitecture::X86_64, BinaryMachineReplayCapability::Return) => {
            "x86_64 return target validated from call-frame and stack witness context"
        }
        (_, BinaryMachineReplayCapability::DirectBranch) => {
            "decoded direct branch target validated against following trace step"
        }
        (_, BinaryMachineReplayCapability::IndirectBranch) => "indirect branch target validated",
        (_, BinaryMachineReplayCapability::DirectCall) => "direct call context validated",
        (_, BinaryMachineReplayCapability::IndirectCall) => "indirect call context validated",
        (_, BinaryMachineReplayCapability::Return) => "return context validated",
    }
}

/// Original bytes for one instruction virtual address.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedMachineInstructionBytes {
    pub address: u64,
    pub bytes: Vec<u8>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file_offset: Option<u64>,
}

impl BoundedMachineInstructionBytes {
    #[must_use]
    pub fn new(address: u64, bytes: impl Into<Vec<u8>>) -> Self {
        Self { address, bytes: bytes.into(), file_offset: None }
    }

    #[must_use]
    pub fn with_file_offset(mut self, file_offset: u64) -> Self {
        self.file_offset = Some(file_offset);
        self
    }
}

/// Segment permissions for bounded machine-code replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedMachineCodeSegmentPermissions {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

impl BoundedMachineCodeSegmentPermissions {
    #[must_use]
    pub const fn new(read: bool, write: bool, execute: bool) -> Self {
        Self { read, write, execute }
    }

    #[must_use]
    pub const fn rx() -> Self {
        Self::new(true, false, true)
    }

    #[must_use]
    pub const fn rw() -> Self {
        Self::new(true, true, false)
    }
}

/// Loaded image segment covered by bounded machine-code replay.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedMachineCodeSegment {
    pub start: u64,
    pub size: u64,
    pub permissions: BoundedMachineCodeSegmentPermissions,
}

impl BoundedMachineCodeSegment {
    #[must_use]
    pub const fn new(
        start: u64,
        size: u64,
        permissions: BoundedMachineCodeSegmentPermissions,
    ) -> Self {
        Self { start, size, permissions }
    }

    #[must_use]
    pub fn contains_range(&self, address: u64, size: usize) -> bool {
        if size == 0 || self.size == 0 {
            return false;
        }
        let Ok(size) = u64::try_from(size) else {
            return false;
        };
        let Some(segment_end) = self.start.checked_add(self.size) else {
            return false;
        };
        let Some(range_end) = address.checked_add(size) else {
            return false;
        };
        self.start <= address && range_end <= segment_end
    }
}

/// Address map from instruction virtual addresses to original instruction bytes.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedMachineCodeAddressMap {
    instructions: BTreeMap<u64, BoundedMachineInstructionBytes>,
}

impl BoundedMachineCodeAddressMap {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn from_instructions(
        instructions: impl IntoIterator<Item = BoundedMachineInstructionBytes>,
    ) -> Self {
        let mut map = Self::new();
        for instruction in instructions {
            map.insert(instruction);
        }
        map
    }

    pub fn insert(&mut self, instruction: BoundedMachineInstructionBytes) {
        self.instructions.insert(instruction.address, instruction);
    }

    #[must_use]
    pub fn get(&self, address: u64) -> Option<&BoundedMachineInstructionBytes> {
        self.instructions.get(&address)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.instructions.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }
}

/// Bounded machine-code image used by the first replay backend slice.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedMachineCodeImage {
    pub architecture: BoundedMachineCodeArchitecture,
    pub address_map: BoundedMachineCodeAddressMap,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub image: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_digest: Option<BinaryArtifactDigest>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentity>,
    /// SHA-256 over the loaded selected-image bytes used by this bounded replay.
    ///
    /// When present, replay rejects stale selected-image identities before
    /// executing witness steps.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image_content_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub segments: Vec<BoundedMachineCodeSegment>,
}

impl BoundedMachineCodeImage {
    #[must_use]
    pub fn new(architecture: BoundedMachineCodeArchitecture) -> Self {
        Self {
            architecture,
            address_map: BoundedMachineCodeAddressMap::new(),
            image: None,
            artifact_digest: None,
            selected_image: None,
            selected_image_content_sha256: None,
            segments: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_address_map(
        architecture: BoundedMachineCodeArchitecture,
        address_map: BoundedMachineCodeAddressMap,
    ) -> Self {
        Self {
            architecture,
            address_map,
            image: None,
            artifact_digest: None,
            selected_image: None,
            selected_image_content_sha256: None,
            segments: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_image(mut self, image: impl Into<String>) -> Self {
        self.image = Some(image.into());
        self
    }

    #[must_use]
    pub fn with_artifact_digest(mut self, artifact_digest: BinaryArtifactDigest) -> Self {
        self.artifact_digest = Some(artifact_digest);
        self
    }

    #[must_use]
    pub fn with_selected_image(mut self, selected_image: BinarySelectedImageIdentity) -> Self {
        self.selected_image = Some(selected_image);
        self
    }

    #[must_use]
    pub fn with_selected_image_bytes(mut self, selected_image_bytes: &[u8]) -> Self {
        self.selected_image_content_sha256 = Some(stable_sha256_hex(selected_image_bytes));
        self
    }

    pub fn insert_instruction(&mut self, address: u64, bytes: impl Into<Vec<u8>>) {
        self.address_map.insert(BoundedMachineInstructionBytes::new(address, bytes));
    }

    pub fn insert_instruction_at_file_offset(
        &mut self,
        address: u64,
        file_offset: u64,
        bytes: impl Into<Vec<u8>>,
    ) {
        self.address_map.insert(
            BoundedMachineInstructionBytes::new(address, bytes).with_file_offset(file_offset),
        );
    }

    pub fn insert_segment(
        &mut self,
        start: u64,
        size: u64,
        permissions: BoundedMachineCodeSegmentPermissions,
    ) {
        self.segments.push(BoundedMachineCodeSegment::new(start, size, permissions));
    }

    fn executable_segment_contains(&self, address: u64, size: usize) -> bool {
        self.segments
            .iter()
            .any(|segment| segment.permissions.execute && segment.contains_range(address, size))
    }

    fn any_segment_contains(&self, address: u64, size: usize) -> bool {
        self.segments.iter().any(|segment| segment.contains_range(address, size))
    }
}

/// First bounded machine-code replay backend.
///
/// This backend intentionally accepts only mapped, bounded instruction traces
/// whose witness evidence does not require memory replay. It uses the existing
/// decoder and concrete machine-semantic effect application for fallthrough and
/// conditional-branch PC updates where that path is available, and otherwise
/// returns a closed classification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundedMachineCodeReplayBackend {
    pub image: BoundedMachineCodeImage,
    pub max_instructions: usize,
}

impl BoundedMachineCodeReplayBackend {
    pub const BACKEND_NAME: &'static str = "bounded-machine-code";

    #[must_use]
    pub fn new(image: BoundedMachineCodeImage) -> Self {
        Self { image, max_instructions: 256 }
    }

    #[must_use]
    pub fn with_max_instructions(mut self, max_instructions: usize) -> Self {
        self.max_instructions = max_instructions;
        self
    }

    fn stale_selected_image_digest_result(&self) -> Option<BinaryMachineReplayResult> {
        let selected_image = self.image.selected_image.as_ref()?;
        let loaded_sha256 = self.image.selected_image_content_sha256.as_deref()?;
        if !selected_image.is_canonical_sha256() || !is_stable_sha256_hex(loaded_sha256) {
            return None;
        }
        if selected_image.sha256 == loaded_sha256 {
            return None;
        }

        let diagnostic = BinaryMachineReplayByteRangeDiagnostic::new(
            BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageDigestMismatch,
            format!(
                "bounded machine replay selected-image digest is stale: selected-image identity sha256 {} did not match loaded selected-image bytes sha256 {}",
                selected_image.sha256, loaded_sha256
            ),
        );
        Some(
            machine_result(
                BinaryMachineReplayStatus::Spurious,
                diagnostic.diagnostic.clone(),
                Vec::new(),
            )
            .with_byte_range_diagnostics(vec![diagnostic]),
        )
    }

    fn replay_expected_trace(
        &self,
        witness: &BinaryWitness,
    ) -> Result<
        (
            Vec<BinaryMachineInstructionEvidence>,
            Vec<BinaryMachineReplayCapabilityEvidence>,
            Vec<BinaryMachineReplayEffectEvidence>,
            Vec<BinaryMachineReplayEffectDiagnostic>,
            Vec<BinaryMachineReplayByteRangeEvidence>,
        ),
        BinaryMachineReplayResult,
    > {
        let expected_steps = expected_machine_instruction_steps(witness);
        let expected =
            expected_steps.iter().map(|(origin, _)| (*origin).clone()).collect::<Vec<_>>();
        if expected.is_empty() {
            return Err(machine_result(
                BinaryMachineReplayStatus::NeedsMachineReplay,
                "normalized witness has no instruction-level provenance for bounded machine replay",
                Vec::new(),
            ));
        }
        if expected.len() > self.max_instructions {
            return Err(machine_result(
                BinaryMachineReplayStatus::Unsupported,
                format!(
                    "bounded machine replay trace length {} exceeds configured limit {}",
                    expected.len(),
                    self.max_instructions
                ),
                Vec::new(),
            ));
        }
        if self.image.architecture == BoundedMachineCodeArchitecture::Unsupported {
            return Err(machine_result(
                BinaryMachineReplayStatus::Unsupported,
                "bounded machine replay does not support the selected architecture",
                Vec::new(),
            ));
        }
        if let Some(result) = self.stale_selected_image_digest_result() {
            return Err(result);
        }

        let mut concrete = ConcreteState::new();
        concrete.pc = expected[0].instruction_address;
        let symbolic = MachineState::symbolic();
        let mut observed = Vec::with_capacity(expected.len());
        let mut capability_evidence = Vec::new();
        let mut effect_evidence = Vec::new();
        let mut effect_diagnostics = Vec::new();
        let mut byte_range_evidence = Vec::new();
        let mut call_frames = Vec::new();

        if let Some((_, first_step)) = expected_steps.first()
            && let Err(error) = self.seed_initial_witness_state(&mut concrete, first_step) {
                return Err(error.into_machine_result(Vec::new()));
            }

        for (idx, (origin, step)) in expected_steps.iter().enumerate() {
            if idx > 0
                && let Err(error) = self.validate_witness_trace_state(&concrete, step) {
                    return Err(error.into_machine_result(observed));
                }
            if let Err(error) =
                observe_aarch64_return_address_stack_witness(&mut call_frames, step, &concrete)
            {
                return Err(error.into_machine_result(observed));
            }
            if concrete.pc != origin.instruction_address {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Spurious,
                    format!(
                        "bounded machine replay left straight-line trace at 0x{:x}; expected 0x{:x}",
                        concrete.pc, origin.instruction_address
                    ),
                    observed,
                ));
            }

            let Some(mapped) = self.image.address_map.get(origin.instruction_address) else {
                return Err(machine_result(
                    BinaryMachineReplayStatus::NeedsMachineReplay,
                    format!(
                        "no original instruction bytes mapped for 0x{:x}",
                        origin.instruction_address
                    ),
                    observed,
                ));
            };

            if let Err(result) = self.validate_instruction_fetch(mapped) {
                return Err(result.with_observed_trace(observed));
            }

            let instruction = match self.decode_instruction(mapped, origin) {
                Ok(instruction) => instruction,
                Err(result) => return Err(result.with_observed_trace(observed)),
            };

            let control_flow_capability = match self.validate_bounded_control_flow(
                &instruction,
                step,
                expected_steps.get(idx + 1).map(|(_, next_step)| *next_step),
                idx,
                expected.len(),
                &concrete,
                &call_frames,
            ) {
                Ok(capability) => capability,
                Err(reason) => {
                    observed.push(instruction_evidence(origin, &instruction, mapped, idx));
                    return Err(machine_result(
                        BinaryMachineReplayStatus::Unsupported,
                        reason,
                        observed,
                    ));
                }
            };

            let effects = match self.effects(&symbolic, &instruction) {
                Ok(effects) => effects,
                Err(reason) => {
                    let diagnostic =
                        semantics_unavailable_effect_diagnostic(&instruction, step.step, &reason);
                    return Err(machine_result(
                        BinaryMachineReplayStatus::Unsupported,
                        reason,
                        observed,
                    )
                    .with_effect_diagnostics(vec![diagnostic]));
                }
            };
            let pc_before = concrete.pc;
            let (step_effect_evidence, step_effect_diagnostics) =
                bounded_effect_evidence_for_instruction(
                    bounded_architecture_name(self.image.architecture),
                    &instruction,
                    step.step,
                    expected_steps.get(idx + 1).map(|(_, next_step)| next_step.step),
                    &concrete,
                    &effects,
                );
            if let Err(reason) = self.apply_bounded_effects(&mut concrete, &effects, &instruction) {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Unsupported,
                    reason,
                    observed,
                )
                .with_effect_evidence(step_effect_evidence)
                .with_effect_diagnostics(step_effect_diagnostics));
            }
            if !effects_update_pc(&effects) {
                concrete.pc = pc_before.wrapping_add(u64::from(instruction.size));
            }
            update_call_frames(
                &mut call_frames,
                &instruction,
                pc_before,
                &concrete,
                self.image.architecture,
            );

            let evidence = instruction_evidence(origin, &instruction, mapped, idx);
            if let Some(evidence_range) = instruction_byte_range_evidence(&evidence, mapped) {
                byte_range_evidence.push(evidence_range);
            }
            if let Some(mut capability) = control_flow_capability {
                capability.step = evidence.step;
                capability.instruction_bytes = evidence.origin.instruction_bytes.clone();
                capability_evidence.push(capability);
            }
            effect_evidence.extend(step_effect_evidence);
            effect_diagnostics.extend(step_effect_diagnostics);
            observed.push(evidence);
        }

        Ok((
            observed,
            capability_evidence,
            effect_evidence,
            effect_diagnostics,
            byte_range_evidence,
        ))
    }

    fn decode_instruction(
        &self,
        mapped: &BoundedMachineInstructionBytes,
        origin: &TrustBinaryOrigin,
    ) -> Result<Instruction, BinaryMachineReplayResult> {
        if self.image.architecture == BoundedMachineCodeArchitecture::Unsupported {
            return Err(machine_result(
                BinaryMachineReplayStatus::Unsupported,
                "bounded machine replay does not support the selected architecture",
                Vec::new(),
            ));
        }
        if !origin.instruction_bytes.is_empty() && mapped.bytes != origin.instruction_bytes {
            return Err(machine_result(
                BinaryMachineReplayStatus::Spurious,
                format!(
                    "mapped instruction bytes for 0x{:x} did not match normalized witness provenance",
                    origin.instruction_address
                ),
                Vec::new(),
            ));
        }
        if let Some(size) = origin.instruction_size
            && mapped.bytes.len() != usize::from(size) {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Spurious,
                    format!(
                        "mapped instruction size for 0x{:x} was {}; expected {}",
                        origin.instruction_address,
                        mapped.bytes.len(),
                        size
                    ),
                    Vec::new(),
                ));
            }

        let decoded = match self.image.architecture {
            BoundedMachineCodeArchitecture::Aarch64 => {
                decode_aarch64(&mapped.bytes, mapped.address).map_err(|err| {
                    machine_result(
                        BinaryMachineReplayStatus::Unsupported,
                        architecture_decode_failure_reason(self.image.architecture, mapped, err),
                        Vec::new(),
                    )
                })?
            }
            BoundedMachineCodeArchitecture::X86_64 => decode_x86_64(&mapped.bytes, mapped.address)
                .map_err(|err| {
                    machine_result(
                        BinaryMachineReplayStatus::Unsupported,
                        architecture_decode_failure_reason(self.image.architecture, mapped, err),
                        Vec::new(),
                    )
                })?,
            BoundedMachineCodeArchitecture::Unsupported => {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Unsupported,
                    "bounded machine replay does not support the selected architecture",
                    Vec::new(),
                ));
            }
        };

        if decoded.address != origin.instruction_address {
            return Err(machine_result(
                BinaryMachineReplayStatus::Spurious,
                format!(
                    "decoded instruction address 0x{:x} did not match expected 0x{:x}",
                    decoded.address, origin.instruction_address
                ),
                Vec::new(),
            ));
        }
        if decoded.bytes != mapped.bytes {
            if let Some(alternate_name) = alternate_architecture_decode_name(
                self.image.architecture,
                &mapped.bytes,
                mapped.address,
            ) {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Unsupported,
                    format!(
                        "bounded machine replay architecture mismatch: selected image architecture is {} but instruction bytes at 0x{:x} decode exactly as {alternate_name}; decoded {} instruction did not consume the mapped byte slice",
                        bounded_architecture_name(self.image.architecture),
                        origin.instruction_address,
                        bounded_architecture_name(self.image.architecture)
                    ),
                    Vec::new(),
                ));
            }
            return Err(machine_result(
                BinaryMachineReplayStatus::Spurious,
                format!(
                    "mapped instruction bytes for 0x{:x} were not exactly one decoded instruction",
                    origin.instruction_address
                ),
                Vec::new(),
            ));
        }
        if let Some(size) = origin.instruction_size
            && decoded.size != size {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Spurious,
                    format!(
                        "decoded instruction size for 0x{:x} was {}; expected {}",
                        origin.instruction_address, decoded.size, size
                    ),
                    Vec::new(),
                ));
            }
        if let Some(encoding) = origin.encoding
            && decoded.encoding != encoding {
                return Err(machine_result(
                    BinaryMachineReplayStatus::Spurious,
                    format!(
                        "decoded instruction encoding for 0x{:x} was 0x{:x}; expected 0x{:x}",
                        origin.instruction_address, decoded.encoding, encoding
                    ),
                    Vec::new(),
                ));
            }

        Ok(decoded)
    }

    fn effects(
        &self,
        state: &MachineState,
        instruction: &Instruction,
    ) -> Result<Vec<trust_machine_sem::Effect>, String> {
        match self.image.architecture {
            BoundedMachineCodeArchitecture::Aarch64 => {
                Aarch64Semantics.effects(state, instruction).map_err(|err| {
                    format!("AArch64 semantics unavailable at 0x{:x}: {err}", instruction.address)
                })
            }
            BoundedMachineCodeArchitecture::X86_64 => {
                X86_64Semantics.effects(state, instruction).map_err(|err| {
                    format!("x86_64 semantics unavailable at 0x{:x}: {err}", instruction.address)
                })
            }
            BoundedMachineCodeArchitecture::Unsupported => {
                Err("bounded machine replay does not support the selected architecture".into())
            }
        }
    }

    fn validate_instruction_fetch(
        &self,
        mapped: &BoundedMachineInstructionBytes,
    ) -> Result<(), BinaryMachineReplayResult> {
        if self.image.segments.is_empty() {
            return Ok(());
        }

        if self.image.executable_segment_contains(mapped.address, mapped.bytes.len()) {
            return Ok(());
        }

        if self.image.any_segment_contains(mapped.address, mapped.bytes.len()) {
            return Err(machine_result(
                BinaryMachineReplayStatus::Spurious,
                format!(
                    "mapped instruction at 0x{:x} is covered only by non-executable loaded image segments",
                    mapped.address
                ),
                Vec::new(),
            ));
        }

        Err(machine_result(
            BinaryMachineReplayStatus::Spurious,
            format!(
                "mapped instruction at 0x{:x} is outside loaded image segments",
                mapped.address
            ),
            Vec::new(),
        ))
    }

    fn apply_bounded_effects(
        &self,
        concrete: &mut ConcreteState,
        effects: &[Effect],
        instruction: &Instruction,
    ) -> Result<(), String> {
        let pre_state = concrete.clone();
        for effect in effects {
            if matches!(effect, Effect::Branch { .. } | Effect::Call { .. } | Effect::Return { .. })
            {
                continue;
            }
            self.validate_memory_effect(&pre_state, effect, instruction)?;
            concrete.apply_effect_with_eval_state(&pre_state, effect).map_err(|err| {
                format!(
                    "bounded concrete machine replay unsupported at 0x{:x}: {err}",
                    instruction.address
                )
            })?;
        }
        Ok(())
    }

    fn validate_memory_effect(
        &self,
        concrete: &ConcreteState,
        effect: &Effect,
        instruction: &Instruction,
    ) -> Result<(), String> {
        match effect {
            Effect::MemRead { address, width_bytes } => {
                let address = concrete.eval_bv(address, 64).map_err(|err| {
                    format!(
                        "bounded machine replay could not resolve memory read address at 0x{:x}: {err}",
                        instruction.address
                    )
                })? as u64;
                self.validate_memory_access(address, *width_bytes, MemoryAccessKind::Read)
            }
            Effect::MemWrite { address, width_bytes, .. } => {
                let address = concrete.eval_bv(address, 64).map_err(|err| {
                    format!(
                        "bounded machine replay could not resolve memory write address at 0x{:x}: {err}",
                        instruction.address
                    )
                })? as u64;
                self.validate_memory_access(address, *width_bytes, MemoryAccessKind::Write)
            }
            _ => Ok(()),
        }
    }

    fn validate_memory_access(
        &self,
        address: u64,
        width_bytes: u32,
        kind: MemoryAccessKind,
    ) -> Result<(), String> {
        if width_bytes == 0 {
            return Err(format!(
                "bounded machine replay cannot validate zero-width memory {} at 0x{address:x}",
                kind.name()
            ));
        }
        let Ok(width) = usize::try_from(width_bytes) else {
            return Err(format!(
                "bounded machine replay memory {} width {width_bytes} at 0x{address:x} is too large",
                kind.name()
            ));
        };
        if address.checked_add(u64::from(width_bytes)).is_none() {
            return Err(format!(
                "bounded machine replay memory {} at 0x{address:x} with width {width_bytes} overflows address space",
                kind.name()
            ));
        }
        if self.image.segments.is_empty() {
            return Err(format!(
                "bounded machine replay requires a loaded memory segment for {} at 0x{address:x} with width {width_bytes}",
                kind.name()
            ));
        }

        let covered_segment =
            self.image.segments.iter().find(|segment| segment.contains_range(address, width));
        let Some(segment) = covered_segment else {
            return Err(format!(
                "bounded machine replay has no loaded memory segment covering {} at 0x{address:x} with width {width_bytes}",
                kind.name()
            ));
        };

        let permitted = match kind {
            MemoryAccessKind::Read => segment.permissions.read,
            MemoryAccessKind::Write => segment.permissions.write,
        };
        if permitted {
            Ok(())
        } else {
            Err(format!(
                "bounded machine replay memory {} at 0x{address:x} with width {width_bytes} is not covered by a {} loaded segment",
                kind.name(),
                kind.permission_name()
            ))
        }
    }

    fn seed_initial_witness_state(
        &self,
        concrete: &mut ConcreteState,
        step: &BinaryWitnessTraceStep,
    ) -> Result<(), WitnessStateError> {
        for record in &step.assignments {
            if let Some(register) = concrete_witness_register(record)? {
                seed_concrete_register(concrete, register, record, step.step)?;
            }
        }

        for record in &step.assignments {
            if let Some(memory) = self.concrete_witness_memory(concrete, record, step.step)? {
                self.seed_concrete_memory(concrete, memory, record, step.step)?;
            }
        }

        Ok(())
    }

    fn validate_witness_trace_state(
        &self,
        concrete: &ConcreteState,
        step: &BinaryWitnessTraceStep,
    ) -> Result<(), WitnessStateError> {
        for record in &step.assignments {
            if let Some(register) = concrete_witness_register(record)? {
                validate_concrete_register(concrete, register, record, step.step)?;
                continue;
            }

            if let Some(memory) = self.concrete_witness_memory(concrete, record, step.step)? {
                self.validate_concrete_memory(concrete, memory, record, step.step)?;
            }
        }

        Ok(())
    }

    fn concrete_witness_memory(
        &self,
        concrete: &ConcreteState,
        record: &BinaryWitnessRecord,
        step: u32,
    ) -> Result<Option<ConcreteWitnessMemory>, WitnessStateError> {
        let (address, width_bytes) = match &record.storage {
            BinaryStorageLocation::Memory { address, size_bytes } => {
                let width_bytes = explicit_memory_witness_size(*size_bytes, record, step)?;
                (concrete_address_from_formula(concrete, address, record, step)?, width_bytes)
            }
            BinaryStorageLocation::Stack { base, offset, size_bytes } => {
                let width_bytes = explicit_memory_witness_size(*size_bytes, record, step)?;
                let base_address = match base {
                    BinaryStackBase::StackPointer => concrete.sp,
                    BinaryStackBase::FramePointer => {
                        return Err(WitnessStateError::unsupported(format!(
                            "bounded machine replay cannot validate frame-pointer-relative stack witness `{}` at trace step {step}",
                            record.raw_name
                        )));
                    }
                    BinaryStackBase::CanonicalFrameAddress => {
                        return Err(WitnessStateError::unsupported(format!(
                            "bounded machine replay cannot validate CFA-relative stack witness `{}` at trace step {step}",
                            record.raw_name
                        )));
                    }
                    BinaryStackBase::Unknown => {
                        return Err(WitnessStateError::unsupported(format!(
                            "bounded machine replay cannot validate stack witness `{}` with unknown base at trace step {step}",
                            record.raw_name
                        )));
                    }
                    _ => {
                        return Err(WitnessStateError::unsupported(format!(
                            "bounded machine replay cannot validate stack witness `{}` with unsupported base at trace step {step}",
                            record.raw_name
                        )));
                    }
                };
                let Some(address) = add_stack_offset(base_address, *offset) else {
                    return Err(WitnessStateError::unsupported(format!(
                        "bounded machine replay stack witness `{}` at trace step {step} overflows address space from SP 0x{base_address:x} with offset {offset}",
                        record.raw_name
                    )));
                };
                (address, width_bytes)
            }
            BinaryStorageLocation::Global {
                address: Some(address),
                size_bytes: Some(size_bytes),
                ..
            } => {
                let Ok(width_bytes) = u32::try_from(*size_bytes) else {
                    return Err(WitnessStateError::unsupported(format!(
                        "bounded machine replay global witness `{}` at trace step {step} has unsupported size {size_bytes}",
                        record.raw_name
                    )));
                };
                (*address, width_bytes)
            }
            BinaryStorageLocation::Register { .. }
            | BinaryStorageLocation::RegisterPair { .. }
            | BinaryStorageLocation::Immediate { .. }
            | BinaryStorageLocation::Unknown => return Ok(None),
            BinaryStorageLocation::Global { .. } => {
                return Err(WitnessStateError::unsupported(format!(
                    "bounded machine replay requires an address and size for global witness `{}` at trace step {step}",
                    record.raw_name
                )));
            }
            BinaryStorageLocation::Split(_) => {
                return Err(WitnessStateError::unsupported(format!(
                    "bounded machine replay cannot validate split witness storage `{}` at trace step {step}",
                    record.raw_name
                )));
            }
            _ => {
                return Err(WitnessStateError::unsupported(format!(
                    "bounded machine replay cannot validate witness storage `{}` at trace step {step}",
                    record.raw_name
                )));
            }
        };

        if let Err(reason) =
            self.validate_memory_access(address, width_bytes, MemoryAccessKind::Read)
        {
            return Err(WitnessStateError::unsupported(format!(
                "bounded machine replay cannot validate memory witness `{}` at trace step {step}: {reason}",
                record.raw_name
            )));
        }

        Ok(Some(ConcreteWitnessMemory { address, width_bytes }))
    }

    fn seed_concrete_memory(
        &self,
        concrete: &mut ConcreteState,
        memory: ConcreteWitnessMemory,
        record: &BinaryWitnessRecord,
        step: u32,
    ) -> Result<(), WitnessStateError> {
        let width_bits = memory_width_bits(memory.width_bytes, record, step)?;
        let value = witness_value_u128(record, width_bits, step)?;
        for offset in 0..memory.width_bytes {
            let Some(address) = memory.address.checked_add(u64::from(offset)) else {
                return Err(WitnessStateError::unsupported(format!(
                    "bounded machine replay memory witness `{}` at trace step {step} overflows address space at 0x{:x}",
                    record.raw_name, memory.address
                )));
            };
            let byte = ((value >> (offset * 8)) & 0xff) as u8;
            if let Some(existing) = concrete.memory.get(&address)
                && *existing != byte {
                    return Err(WitnessStateError::spurious(format!(
                        "bounded machine replay conflicting initial memory witness byte for `{}` at trace step {step}: address 0x{address:x} expected 0x{byte:02x}, already seeded 0x{existing:02x}",
                        record.raw_name
                    )));
                }
        }

        concrete.store_memory_le(memory.address, memory.width_bytes, value).map_err(|err| {
            WitnessStateError::unsupported(format!(
                "bounded machine replay could not seed memory witness `{}` at trace step {step}: {err}",
                record.raw_name
            ))
        })
    }

    fn validate_concrete_memory(
        &self,
        concrete: &ConcreteState,
        memory: ConcreteWitnessMemory,
        record: &BinaryWitnessRecord,
        step: u32,
    ) -> Result<(), WitnessStateError> {
        let width_bits = memory_width_bits(memory.width_bytes, record, step)?;
        let expected = witness_value_u128(record, width_bits, step)?;
        let observed = concrete.load_memory_le(memory.address, memory.width_bytes).map_err(|err| {
            WitnessStateError::spurious(format!(
                "bounded machine replay memory witness `{}` at trace step {step} could not be read at 0x{:x}: {err}",
                record.raw_name, memory.address
            ))
        })?;
        if observed == expected {
            return Ok(());
        }

        Err(WitnessStateError::spurious(format!(
            "bounded machine replay memory witness mismatch for `{}` at trace step {step}: address 0x{:x} width {} expected 0x{:x}, observed 0x{:x}",
            record.raw_name, memory.address, memory.width_bytes, expected, observed
        )))
    }

    fn validate_bounded_control_flow(
        &self,
        instruction: &Instruction,
        step: &BinaryWitnessTraceStep,
        next_step: Option<&BinaryWitnessTraceStep>,
        step_index: usize,
        expected_trace_len: usize,
        concrete: &ConcreteState,
        call_frames: &[CallFrame],
    ) -> Result<Option<BinaryMachineReplayCapabilityEvidence>, String> {
        match instruction.flow {
            ControlFlow::Fallthrough => Ok(None),
            ControlFlow::ConditionalBranch => Ok(Some(self.control_flow_capability_evidence(
                instruction,
                BinaryMachineReplayCapability::ConditionalBranch,
            ))),
            ControlFlow::Branch if instruction.branch_target().is_some() => {
                validate_direct_branch_witness_context(
                    instruction,
                    next_step,
                    step_index,
                    expected_trace_len,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::DirectBranch,
                )))
            }
            ControlFlow::Call
                if self.image.architecture == BoundedMachineCodeArchitecture::X86_64
                    && instruction.branch_target().is_some() =>
            {
                validate_x86_direct_call_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::DirectCall,
                )))
            }
            ControlFlow::Call
                if self.image.architecture == BoundedMachineCodeArchitecture::X86_64 =>
            {
                validate_x86_indirect_call_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                    concrete,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::IndirectCall,
                )))
            }
            ControlFlow::Call
                if self.image.architecture == BoundedMachineCodeArchitecture::Aarch64
                    && instruction.branch_target().is_some() =>
            {
                validate_aarch64_direct_call_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::DirectCall,
                )))
            }
            ControlFlow::Call
                if self.image.architecture == BoundedMachineCodeArchitecture::Aarch64 =>
            {
                validate_aarch64_indirect_call_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::IndirectCall,
                )))
            }
            ControlFlow::Branch
                if self.image.architecture == BoundedMachineCodeArchitecture::Aarch64
                    && instruction.branch_target().is_none() =>
            {
                validate_aarch64_indirect_branch_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::IndirectBranch,
                )))
            }
            ControlFlow::Return
                if self.image.architecture == BoundedMachineCodeArchitecture::X86_64 =>
            {
                validate_x86_return_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                    concrete,
                    call_frames,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::Return,
                )))
            }
            ControlFlow::Return
                if self.image.architecture == BoundedMachineCodeArchitecture::Aarch64 =>
            {
                validate_aarch64_return_witness_context(
                    instruction,
                    step,
                    next_step,
                    step_index,
                    expected_trace_len,
                    concrete,
                    call_frames,
                )?;
                Ok(Some(self.control_flow_capability_evidence(
                    instruction,
                    BinaryMachineReplayCapability::Return,
                )))
            }
            _ => Err(boundary_diagnostic_from_instruction(
                bounded_architecture_name(self.image.architecture),
                instruction,
                Some(step.step),
            )
            .map(|diagnostic| boundary_reason_from_diagnostic(&diagnostic))
            .unwrap_or_else(|| {
                unsupported_control_flow_reason(instruction, step_index, expected_trace_len)
            })),
        }
    }

    fn control_flow_capability_evidence(
        &self,
        instruction: &Instruction,
        capability: BinaryMachineReplayCapability,
    ) -> BinaryMachineReplayCapabilityEvidence {
        BinaryMachineReplayCapabilityEvidence::new(
            capability,
            bounded_architecture_name(self.image.architecture),
            instruction.address,
            bounded_capability_validation(self.image.architecture, capability),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ConcreteWitnessMemory {
    address: u64,
    width_bytes: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CallFrame {
    architecture: BoundedMachineCodeArchitecture,
    call_site: u64,
    return_address: u64,
    stack_address: u64,
    stack_witness: Option<ReturnAddressStackWitness>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReturnAddressStackWitness {
    trace_step: u32,
    address: u64,
    offset: i64,
    size_bytes: u32,
    value: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteWitnessRegister {
    Gpr { name: &'static str, index: u8, width: u32 },
    Sp { name: &'static str, width: u32 },
    Pc { name: &'static str, width: u32 },
    Flag { name: &'static str, flag: ConcreteWitnessFlag },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteWitnessFlag {
    N,
    Z,
    C,
    V,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WitnessStateError {
    status: BinaryMachineReplayStatus,
    reason: String,
}

impl WitnessStateError {
    fn spurious(reason: impl Into<String>) -> Self {
        Self { status: BinaryMachineReplayStatus::Spurious, reason: reason.into() }
    }

    fn unsupported(reason: impl Into<String>) -> Self {
        Self { status: BinaryMachineReplayStatus::Unsupported, reason: reason.into() }
    }

    fn into_machine_result(
        self,
        instruction_trace: Vec<BinaryMachineInstructionEvidence>,
    ) -> BinaryMachineReplayResult {
        machine_result(self.status, self.reason, instruction_trace)
    }
}

fn concrete_witness_register(
    record: &BinaryWitnessRecord,
) -> Result<Option<ConcreteWitnessRegister>, WitnessStateError> {
    let BinaryStorageLocation::Register { name, bit_width } = &record.storage else {
        return Ok(None);
    };

    let upper = name.to_ascii_uppercase();
    let parsed = match upper.as_str() {
        "SP" | "RSP" => {
            Some(ConcreteWitnessRegister::Sp { name: "RSP", width: bit_width.unwrap_or(64) })
        }
        "ESP" => Some(ConcreteWitnessRegister::Sp { name: "ESP", width: bit_width.unwrap_or(32) }),
        "SPL" => Some(ConcreteWitnessRegister::Sp { name: "SPL", width: bit_width.unwrap_or(8) }),
        "LR" => Some(ConcreteWitnessRegister::Gpr {
            name: "LR",
            index: 30,
            width: bit_width.unwrap_or(64),
        }),
        "PC" | "RIP" => {
            Some(ConcreteWitnessRegister::Pc { name: "PC", width: bit_width.unwrap_or(64) })
        }
        "EIP" => Some(ConcreteWitnessRegister::Pc { name: "EIP", width: bit_width.unwrap_or(32) }),
        "N" | "SF" => {
            Some(ConcreteWitnessRegister::Flag { name: "N", flag: ConcreteWitnessFlag::N })
        }
        "Z" | "ZF" => {
            Some(ConcreteWitnessRegister::Flag { name: "Z", flag: ConcreteWitnessFlag::Z })
        }
        "C" | "CF" => {
            Some(ConcreteWitnessRegister::Flag { name: "C", flag: ConcreteWitnessFlag::C })
        }
        "V" | "OF" => {
            Some(ConcreteWitnessRegister::Flag { name: "V", flag: ConcreteWitnessFlag::V })
        }
        _ => parse_aarch64_gpr(&upper, *bit_width).or_else(|| parse_x86_gpr(&upper, *bit_width)),
    };

    parsed.map_or_else(
        || {
            Err(WitnessStateError::unsupported(format!(
                "bounded machine replay cannot map register witness `{}` to a concrete register",
                record.raw_name
            )))
        },
        |register| Ok(Some(register)),
    )
}

fn parse_aarch64_gpr(name: &str, bit_width: Option<u32>) -> Option<ConcreteWitnessRegister> {
    let (prefix, default_width) = if let Some(rest) = name.strip_prefix('X') {
        (rest, 64)
    } else if let Some(rest) = name.strip_prefix('W') {
        (rest, 32)
    } else {
        return None;
    };
    let index = prefix.parse::<u8>().ok()?;
    (index <= 30).then_some(ConcreteWitnessRegister::Gpr {
        name: "GPR",
        index,
        width: bit_width.unwrap_or(default_width),
    })
}

fn parse_x86_gpr(name: &str, bit_width: Option<u32>) -> Option<ConcreteWitnessRegister> {
    let (index, default_width) = match name {
        "RAX" => (0, 64),
        "EAX" => (0, 32),
        "AX" => (0, 16),
        "AL" => (0, 8),
        "RCX" => (1, 64),
        "ECX" => (1, 32),
        "CX" => (1, 16),
        "CL" => (1, 8),
        "RDX" => (2, 64),
        "EDX" => (2, 32),
        "DX" => (2, 16),
        "DL" => (2, 8),
        "RBX" => (3, 64),
        "EBX" => (3, 32),
        "BX" => (3, 16),
        "BL" => (3, 8),
        "RBP" => (5, 64),
        "EBP" => (5, 32),
        "BP" => (5, 16),
        "BPL" => (5, 8),
        "RSI" => (6, 64),
        "ESI" => (6, 32),
        "SI" => (6, 16),
        "SIL" => (6, 8),
        "RDI" => (7, 64),
        "EDI" => (7, 32),
        "DI" => (7, 16),
        "DIL" => (7, 8),
        _ => {
            let rest = name.strip_prefix('R')?;
            let digits_len = rest.chars().take_while(|ch| ch.is_ascii_digit()).count();
            if digits_len == 0 {
                return None;
            }
            let (digits, suffix) = rest.split_at(digits_len);
            let index = digits.parse::<u8>().ok()?;
            if !(8..=15).contains(&index) {
                return None;
            }
            let width = match suffix {
                "" => 64,
                "D" => 32,
                "W" => 16,
                "B" => 8,
                _ => return None,
            };
            (index, width)
        }
    };

    Some(ConcreteWitnessRegister::Gpr {
        name: "GPR",
        index,
        width: bit_width.unwrap_or(default_width),
    })
}

fn seed_concrete_register(
    concrete: &mut ConcreteState,
    register: ConcreteWitnessRegister,
    record: &BinaryWitnessRecord,
    step: u32,
) -> Result<(), WitnessStateError> {
    match register {
        ConcreteWitnessRegister::Gpr { index, width, .. } => {
            validate_register_width(width, record, step)?;
            let value = witness_value_u128(record, width, step)?;
            concrete.write_gpr(index, width, value).map_err(|err| {
                WitnessStateError::unsupported(format!(
                    "bounded machine replay could not seed register witness `{}` at trace step {step}: {err}",
                    record.raw_name
                ))
            })
        }
        ConcreteWitnessRegister::Sp { width, .. } => {
            validate_register_width(width, record, step)?;
            let value = witness_value_u128(record, width, step)?;
            concrete.sp = truncate_width(value, width).ok_or_else(|| {
                WitnessStateError::unsupported(format!(
                    "bounded machine replay stack-pointer witness `{}` at trace step {step} has invalid width {width}",
                    record.raw_name
                ))
            })? as u64;
            Ok(())
        }
        ConcreteWitnessRegister::Pc { .. } => {
            validate_concrete_register(concrete, register, record, step)
        }
        ConcreteWitnessRegister::Flag { flag, .. } => {
            let value = witness_value_bool(record, step)?;
            match flag {
                ConcreteWitnessFlag::N => concrete.flags.n = value,
                ConcreteWitnessFlag::Z => concrete.flags.z = value,
                ConcreteWitnessFlag::C => concrete.flags.c = value,
                ConcreteWitnessFlag::V => concrete.flags.v = value,
            }
            Ok(())
        }
    }
}

fn validate_concrete_register(
    concrete: &ConcreteState,
    register: ConcreteWitnessRegister,
    record: &BinaryWitnessRecord,
    step: u32,
) -> Result<(), WitnessStateError> {
    match register {
        ConcreteWitnessRegister::Gpr { name, index, width } => {
            validate_register_width(width, record, step)?;
            let expected = witness_value_u128(record, width, step)?;
            let observed = concrete.read_gpr(index, width);
            compare_witness_value(name, &record.raw_name, step, width, expected, observed)
        }
        ConcreteWitnessRegister::Sp { name, width } => {
            validate_register_width(width, record, step)?;
            let expected = witness_value_u128(record, width, step)?;
            let observed = truncate_width(u128::from(concrete.sp), width).ok_or_else(|| {
                WitnessStateError::unsupported(format!(
                    "bounded machine replay stack-pointer witness `{}` at trace step {step} has invalid width {width}",
                    record.raw_name
                ))
            })?;
            compare_witness_value(name, &record.raw_name, step, width, expected, observed)
        }
        ConcreteWitnessRegister::Pc { name, width } => {
            validate_register_width(width, record, step)?;
            let expected = witness_value_u128(record, width, step)?;
            let observed = truncate_width(u128::from(concrete.pc), width).ok_or_else(|| {
                WitnessStateError::unsupported(format!(
                    "bounded machine replay PC witness `{}` at trace step {step} has invalid width {width}",
                    record.raw_name
                ))
            })?;
            compare_witness_value(name, &record.raw_name, step, width, expected, observed)
        }
        ConcreteWitnessRegister::Flag { name, flag } => {
            let expected = witness_value_bool(record, step)?;
            let observed = match flag {
                ConcreteWitnessFlag::N => concrete.flags.n,
                ConcreteWitnessFlag::Z => concrete.flags.z,
                ConcreteWitnessFlag::C => concrete.flags.c,
                ConcreteWitnessFlag::V => concrete.flags.v,
            };
            if expected == observed {
                Ok(())
            } else {
                Err(WitnessStateError::spurious(format!(
                    "bounded machine replay flag {name} mismatch for `{}` at trace step {step}: expected {expected}, observed {observed}",
                    record.raw_name
                )))
            }
        }
    }
}

fn validate_register_width(
    width: u32,
    record: &BinaryWitnessRecord,
    step: u32,
) -> Result<(), WitnessStateError> {
    if (1..=64).contains(&width) {
        Ok(())
    } else {
        Err(WitnessStateError::unsupported(format!(
            "bounded machine replay register witness `{}` at trace step {step} has unsupported width {width}",
            record.raw_name
        )))
    }
}

fn compare_witness_value(
    register: &str,
    raw_name: &str,
    step: u32,
    width: u32,
    expected: u128,
    observed: u128,
) -> Result<(), WitnessStateError> {
    if expected == observed {
        Ok(())
    } else {
        Err(WitnessStateError::spurious(format!(
            "bounded machine replay register {register} mismatch for `{raw_name}` at trace step {step}: width {width} expected 0x{expected:x}, observed 0x{observed:x}"
        )))
    }
}

fn explicit_memory_witness_size(
    size_bytes: Option<u32>,
    record: &BinaryWitnessRecord,
    step: u32,
) -> Result<u32, WitnessStateError> {
    size_bytes.ok_or_else(|| {
        WitnessStateError::unsupported(format!(
            "bounded machine replay requires explicit size_bytes for memory witness `{}` at trace step {step}",
            record.raw_name
        ))
    })
}

fn concrete_address_from_formula(
    concrete: &ConcreteState,
    formula: &Formula,
    record: &BinaryWitnessRecord,
    step: u32,
) -> Result<u64, WitnessStateError> {
    match formula {
        Formula::UInt(value) => u64::try_from(*value).map_err(|_| {
            WitnessStateError::unsupported(format!(
                "bounded machine replay memory witness `{}` at trace step {step} has address outside u64 range",
                record.raw_name
            ))
        }),
        Formula::Int(value) if *value >= 0 => u64::try_from(*value as u128).map_err(|_| {
            WitnessStateError::unsupported(format!(
                "bounded machine replay memory witness `{}` at trace step {step} has address outside u64 range",
                record.raw_name
            ))
        }),
        Formula::BitVec { value, width } if *width <= 64 && *value >= 0 => {
            Ok(truncate_width(*value as u128, *width).unwrap_or_default() as u64)
        }
        _ => concrete.eval_bv(formula, 64).map(|value| value as u64).map_err(|err| {
            WitnessStateError::unsupported(format!(
                "bounded machine replay could not resolve memory witness address for `{}` at trace step {step}: {err}",
                record.raw_name
            ))
        }),
    }
}

fn add_stack_offset(base: u64, offset: i64) -> Option<u64> {
    if offset >= 0 {
        base.checked_add(offset as u64)
    } else {
        base.checked_sub(offset.unsigned_abs())
    }
}

fn memory_width_bits(
    width_bytes: u32,
    record: &BinaryWitnessRecord,
    step: u32,
) -> Result<u32, WitnessStateError> {
    width_bytes.checked_mul(8).filter(|width| (1..=128).contains(width)).ok_or_else(|| {
        WitnessStateError::unsupported(format!(
            "bounded machine replay memory witness `{}` at trace step {step} has unsupported width {width_bytes}",
            record.raw_name
        ))
    })
}

fn witness_value_u128(
    record: &BinaryWitnessRecord,
    width: u32,
    step: u32,
) -> Result<u128, WitnessStateError> {
    let value = record
        .value
        .typed
        .clone()
        .or_else(|| parse_raw_counterexample_value(&record.value.raw))
        .ok_or_else(|| {
            WitnessStateError::unsupported(format!(
                "bounded machine replay could not parse witness value `{}` for `{}` at trace step {step}",
                record.value.raw, record.raw_name
            ))
        })?;
    concrete_value_for_width(&value, width).ok_or_else(|| {
        WitnessStateError::unsupported(format!(
            "bounded machine replay witness value `{}` for `{}` at trace step {step} does not fit width {width}",
            record.value.raw, record.raw_name
        ))
    })
}

fn witness_value_bool(record: &BinaryWitnessRecord, step: u32) -> Result<bool, WitnessStateError> {
    let value = record
        .value
        .typed
        .clone()
        .or_else(|| parse_raw_counterexample_value(&record.value.raw))
        .ok_or_else(|| {
            WitnessStateError::unsupported(format!(
                "bounded machine replay could not parse flag witness value `{}` for `{}` at trace step {step}",
                record.value.raw, record.raw_name
            ))
        })?;
    match value {
        CounterexampleValue::Bool(value) => Ok(value),
        CounterexampleValue::Int(0) | CounterexampleValue::Uint(0) => Ok(false),
        CounterexampleValue::Int(1) | CounterexampleValue::Uint(1) => Ok(true),
        _ => Err(WitnessStateError::unsupported(format!(
            "bounded machine replay flag witness value `{}` for `{}` at trace step {step} is not boolean",
            record.value.raw, record.raw_name
        ))),
    }
}

fn concrete_value_for_width(value: &CounterexampleValue, width: u32) -> Option<u128> {
    let mask = bit_mask(width)?;
    match value {
        CounterexampleValue::Bool(value) => Some(u128::from(*value) & mask),
        CounterexampleValue::Uint(value) if *value <= mask => Some(*value),
        CounterexampleValue::Int(value) if *value >= 0 => {
            let value = *value as u128;
            (value <= mask).then_some(value)
        }
        CounterexampleValue::Int(value) => signed_value_for_width(*value, width),
        CounterexampleValue::Float(_) => None,
        _ => None,
    }
}

fn signed_value_for_width(value: i128, width: u32) -> Option<u128> {
    if width == 0 || width > 128 {
        return None;
    }
    if width == 128 {
        return Some(value as u128);
    }

    let min = -(1i128 << (width - 1));
    if value < min {
        return None;
    }
    let modulus = 1i128 << width;
    Some((modulus + value) as u128)
}

fn truncate_width(value: u128, width: u32) -> Option<u128> {
    Some(value & bit_mask(width)?)
}

fn bit_mask(width: u32) -> Option<u128> {
    match width {
        1..=127 => Some((1u128 << width) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MemoryAccessKind {
    Read,
    Write,
}

impl MemoryAccessKind {
    fn name(self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Write => "write",
        }
    }

    fn permission_name(self) -> &'static str {
        match self {
            Self::Read => "readable",
            Self::Write => "writable",
        }
    }
}

impl BinaryMachineReplayBackend for BoundedMachineCodeReplayBackend {
    fn replay(&self, request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
        match self.replay_expected_trace(request.witness) {
            Ok((
                instruction_trace,
                capability_evidence,
                effect_evidence,
                effect_diagnostics,
                byte_range_evidence,
            )) => BinaryMachineReplayResult::replayed(Self::BACKEND_NAME, instruction_trace)
                .with_capability_evidence(capability_evidence)
                .with_effect_evidence(effect_evidence)
                .with_effect_diagnostics(effect_diagnostics)
                .with_byte_range_evidence(byte_range_evidence)
                .with_optional_artifact_digest(self.image.artifact_digest.clone())
                .with_optional_selected_image(self.image.selected_image.clone()),
            Err(result) => result
                .with_optional_artifact_digest(self.image.artifact_digest.clone())
                .with_optional_selected_image(self.image.selected_image.clone()),
        }
    }
}

fn machine_result(
    status: BinaryMachineReplayStatus,
    reason: impl Into<String>,
    instruction_trace: Vec<BinaryMachineInstructionEvidence>,
) -> BinaryMachineReplayResult {
    BinaryMachineReplayResult {
        status,
        backend: BoundedMachineCodeReplayBackend::BACKEND_NAME.into(),
        reason: reason.into(),
        artifact_digest: None,
        selected_image: None,
        instruction_trace,
        capability_evidence: Vec::new(),
        effect_evidence: Vec::new(),
        effect_diagnostics: Vec::new(),
        byte_range_evidence: Vec::new(),
        byte_range_diagnostics: Vec::new(),
    }
}

fn instruction_evidence(
    origin: &TrustBinaryOrigin,
    instruction: &Instruction,
    mapped: &BoundedMachineInstructionBytes,
    step: usize,
) -> BinaryMachineInstructionEvidence {
    let mut origin = origin.clone();
    origin.instruction_size = Some(instruction.size);
    origin.encoding = Some(instruction.encoding);
    origin.instruction_bytes = mapped.bytes.clone();
    BinaryMachineInstructionEvidence { origin, step: u32::try_from(step).ok() }
}

fn instruction_byte_range_evidence(
    evidence: &BinaryMachineInstructionEvidence,
    mapped: &BoundedMachineInstructionBytes,
) -> Option<BinaryMachineReplayByteRangeEvidence> {
    let file_offset = mapped.file_offset?;
    Some(BinaryMachineReplayByteRangeEvidence::new(
        evidence.origin.instruction_address,
        evidence.step,
        file_offset,
        mapped.bytes.len() as u64,
        mapped.bytes.clone(),
    ))
}

fn bounded_effect_evidence_for_instruction(
    architecture: &'static str,
    instruction: &Instruction,
    step: u32,
    next_witness_step: Option<u32>,
    pre_state: &ConcreteState,
    effects: &[Effect],
) -> (Vec<BinaryMachineReplayEffectEvidence>, Vec<BinaryMachineReplayEffectDiagnostic>) {
    if effects.is_empty() {
        return (
            vec![
                BinaryMachineReplayEffectEvidence::new(
                    BinaryMachineReplayEffectKind::NoStateChange,
                    architecture,
                    instruction.address,
                    "bounded machine replay consumed decoded no-state-change instruction step",
                )
                .with_step(Some(step))
                .with_witness_step(Some(step))
                .with_subject("instruction"),
            ],
            Vec::new(),
        );
    }

    let mut evidence = Vec::new();
    let mut diagnostics = Vec::new();
    let mut seen = BTreeSet::new();
    let mut scalar_memory_effect_index = 0usize;
    for effect in effects {
        let memory_index = next_scalar_memory_effect_index(effect, &mut scalar_memory_effect_index);
        if let Some(diagnostic) =
            unsupported_effect_witness_diagnostic(architecture, instruction, Some(step), effect)
        {
            diagnostics.push(diagnostic.with_witness_step(next_witness_step));
            continue;
        }
        let Some(required) = required_effect_evidence_from_effect(
            architecture,
            instruction.address,
            Some(step),
            effect,
            memory_index,
        ) else {
            continue;
        };
        let key = (
            required.kind,
            required.architecture,
            required.instruction_address,
            required.step,
            required.subject.clone(),
            required.memory_access,
        );
        if !seen.insert(key) {
            continue;
        }
        let mut item = BinaryMachineReplayEffectEvidence::new(
            required.kind,
            architecture,
            instruction.address,
            format!(
                "bounded machine replay consumed {} machine effect for decoded instruction step",
                required.kind
            ),
        )
        .with_step(Some(step))
        .with_witness_step(next_witness_step);
        if let Some(subject) = required.subject {
            item = item.with_subject(subject);
        }
        if required.memory_access.is_some() {
            match concrete_scalar_memory_access_evidence(pre_state, effect, instruction) {
                Ok(Some(memory_access)) => {
                    item = item.with_memory_access(memory_access);
                }
                Ok(None) => {}
                Err(reason) => {
                    diagnostics.push(scalar_memory_effect_witness_diagnostic(
                        architecture,
                        instruction,
                        Some(step),
                        required.kind,
                        &reason,
                    ));
                    continue;
                }
            }
        }
        evidence.push(item);
    }

    if evidence.is_empty() && diagnostics.is_empty() {
        evidence.push(
            BinaryMachineReplayEffectEvidence::new(
                BinaryMachineReplayEffectKind::NoStateChange,
                architecture,
                instruction.address,
                "bounded machine replay consumed instruction step with no supported state effect",
            )
            .with_step(Some(step))
            .with_witness_step(Some(step))
            .with_subject("instruction"),
        );
    }
    (evidence, diagnostics)
}

fn next_scalar_memory_effect_index(effect: &Effect, next: &mut usize) -> Option<usize> {
    if matches!(effect, Effect::MemRead { .. } | Effect::MemWrite { .. }) {
        let index = *next;
        *next += 1;
        Some(index)
    } else {
        None
    }
}

fn concrete_scalar_memory_access_evidence(
    pre_state: &ConcreteState,
    effect: &Effect,
    instruction: &Instruction,
) -> Result<Option<BinaryMachineReplayMemoryAccessEvidence>, String> {
    match effect {
        Effect::MemRead { address, width_bytes } => {
            let address = pre_state.eval_bv(address, 64).map_err(|err| {
                format!(
                    "bounded machine replay could not resolve concrete scalar memory read witness address at 0x{:x}: {err}",
                    instruction.address
                )
            })? as u64;
            Ok(Some(BinaryMachineReplayMemoryAccessEvidence::new(address, *width_bytes)))
        }
        Effect::MemWrite { address, width_bytes, .. } => {
            let address = pre_state.eval_bv(address, 64).map_err(|err| {
                format!(
                    "bounded machine replay could not resolve concrete scalar memory write witness address at 0x{:x}: {err}",
                    instruction.address
                )
            })? as u64;
            Ok(Some(BinaryMachineReplayMemoryAccessEvidence::new(address, *width_bytes)))
        }
        _ => Ok(None),
    }
}

fn scalar_memory_effect_witness_diagnostic(
    architecture: &'static str,
    instruction: &Instruction,
    step: Option<u32>,
    kind: BinaryMachineReplayEffectKind,
    reason: &str,
) -> BinaryMachineReplayEffectDiagnostic {
    let step_text = step.map(|step| format!(" at machine trace step {step}")).unwrap_or_default();
    BinaryMachineReplayEffectDiagnostic::new(
        BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass,
        format!(
            "bounded machine replay could not produce concrete scalar {kind} effect witness for {architecture} instruction 0x{:x}{step_text}: {reason}; concrete scalar memory address/width evidence is required for source backprop",
            instruction.address
        ),
    )
    .with_effect_kind(kind)
    .with_instruction(instruction.address, step)
}

fn semantics_unavailable_effect_diagnostic(
    instruction: &Instruction,
    step: u32,
    reason: &str,
) -> BinaryMachineReplayEffectDiagnostic {
    BinaryMachineReplayEffectDiagnostic::new(
        BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass,
        format!(
            "bounded machine replay could not produce machine-effect witnesses for instruction 0x{:x} at machine trace step {step}: {reason}; exact effect witness semantics are required for source backprop",
            instruction.address
        ),
    )
    .with_instruction(instruction.address, Some(step))
}

fn effects_update_pc(effects: &[trust_machine_sem::Effect]) -> bool {
    effects.iter().any(|effect| {
        matches!(
            effect,
            trust_machine_sem::Effect::PcUpdate { .. }
                | trust_machine_sem::Effect::ConditionalBranch { .. }
        )
    })
}

fn validate_direct_branch_witness_context(
    instruction: &Instruction,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(target) = instruction.branch_target() else {
        return Err(format!(
            "{unsupported}; direct branch replay requires a decoded direct target"
        ));
    };
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; direct branch replay requires a following trace step so the branch target is checked"
        ));
    };
    let Some(next_address) = trace_step_instruction_address(next_step) else {
        return Err(format!(
            "{unsupported}; direct branch replay requires the following trace step {} to carry instruction provenance for the decoded target",
            next_step.step
        ));
    };
    if target != next_address {
        return Err(format!(
            "{unsupported}; direct branch target 0x{target:x} does not match following trace instruction 0x{next_address:x} at trace step {}",
            next_step.step
        ));
    }

    Ok(())
}

fn validate_x86_direct_call_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; x86_64 direct call replay requires a following trace step so the call target, pushed return address, and post-call RSP are checked with stack witness context"
        ));
    };
    if !has_exact_stack_pointer_witness(step) {
        return Err(format!(
            "{unsupported}; x86_64 direct call replay requires an exact 64-bit RSP witness at trace step {} before pushing the return address",
            step.step
        ));
    }
    if !has_exact_stack_pointer_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 direct call replay requires an exact post-call 64-bit RSP witness at trace step {}",
            next_step.step
        ));
    }
    if !has_return_address_stack_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 direct call replay requires a return-address stack witness at trace step {} for stack:sp+0 width 8",
            next_step.step
        ));
    }

    Ok(())
}

fn validate_x86_indirect_call_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
    concrete: &ConcreteState,
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay requires a following trace step so the resolved target, pushed return address, and post-call RSP are checked"
        ));
    };
    if let Some(target_memory) = x86_memory_indirect_call_target(instruction) {
        return validate_x86_memory_indirect_call_witness_context(
            instruction,
            step,
            next_step,
            concrete,
            target_memory,
            &unsupported,
        );
    }
    let Some(target_register) = x86_register_indirect_call_target(instruction) else {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay requires target-memory load witness and exact loaded-target provenance"
        ));
    };
    let Some(target) = exact_x86_register_witness_value(step, target_register) else {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay requires an exact 64-bit {target_register} witness at trace step {} to resolve the call target",
            step.step
        ));
    };
    let Some(next_address) = trace_step_instruction_address(next_step) else {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay requires the following trace step {} to carry instruction provenance for the resolved target",
            next_step.step
        ));
    };
    if target != u128::from(next_address) {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay target witness {target_register}=0x{target:x} at trace step {} does not match following trace instruction 0x{next_address:x}",
            step.step
        ));
    }
    if !has_exact_stack_pointer_witness(step) {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay requires an exact 64-bit RSP witness at trace step {} before pushing the return address",
            step.step
        ));
    }
    if !has_exact_stack_pointer_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay requires an exact post-call 64-bit RSP witness at trace step {}",
            next_step.step
        ));
    }
    if !has_return_address_stack_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 register-indirect call replay requires a return-address stack witness at trace step {} for stack:sp+0 width 8",
            next_step.step
        ));
    }

    Ok(())
}

fn validate_x86_memory_indirect_call_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: &BinaryWitnessTraceStep,
    concrete: &ConcreteState,
    target_memory: &MemoryOperand,
    unsupported: &str,
) -> Result<(), String> {
    let operand = x86_memory_operand_label(target_memory);
    let target_address =
        x86_memory_operand_address(concrete, target_memory, instruction.address).map_err(|reason| {
            format!(
                "{unsupported}; x86_64 memory-indirect call replay for target-memory operand {operand} requires exact address provenance at trace step {}: {reason}",
                step.step
            )
        })?;
    let Some(target) = exact_memory_witness_value(step, concrete, target_address, 8) else {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay for target-memory operand {operand} resolved target load address 0x{target_address:x} at trace step {} but requires an exact 8-byte target-memory load witness at that address before establishing a call frame",
            step.step
        ));
    };
    let Some(next_address) = trace_step_instruction_address(next_step) else {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay for target-memory operand {operand} loaded target 0x{target:x} from 0x{target_address:x}, but following trace step {} lacks loaded-target instruction provenance",
            next_step.step
        ));
    };
    if target != u128::from(next_address) {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay target-memory witness for {operand} loaded 0x{target:x} from 0x{target_address:x} at trace step {}, but following trace instruction is 0x{next_address:x}",
            step.step
        ));
    }
    if !has_exact_stack_pointer_witness(step) {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay requires an exact 64-bit RSP witness at trace step {} before pushing the return address",
            step.step
        ));
    }
    if !has_exact_stack_pointer_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay requires an exact post-call 64-bit RSP witness at trace step {}",
            next_step.step
        ));
    }
    if !has_return_address_stack_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 memory-indirect call replay requires a return-address stack witness at trace step {} for stack:sp+0 width 8",
            next_step.step
        ));
    }

    Ok(())
}

fn validate_x86_return_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
    concrete: &ConcreteState,
    call_frames: &[CallFrame],
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; x86_64 return replay requires a following trace step so the popped return address and post-return RSP are checked"
        ));
    };
    if !has_exact_stack_pointer_witness(step) {
        return Err(format!(
            "{unsupported}; x86_64 return replay requires an exact 64-bit RSP witness at trace step {} before popping the return address",
            step.step
        ));
    }
    if !has_return_address_stack_witness(step) {
        return Err(format!(
            "{unsupported}; x86_64 return replay requires a return-address stack witness at trace step {} for stack:sp+0 width 8",
            step.step
        ));
    }
    if !has_exact_stack_pointer_witness(next_step) {
        return Err(format!(
            "{unsupported}; x86_64 return replay requires an exact post-return 64-bit RSP witness at trace step {}",
            next_step.step
        ));
    }

    let Some(frame) = call_frames.last() else {
        return Err(format!(
            "{unsupported}; x86_64 return replay requires an active call frame established by a replayed direct call with stack witness context"
        ));
    };
    if frame.stack_address != concrete.sp {
        return Err(format!(
            "{unsupported}; x86_64 return replay active frame from call 0x{:x} uses stack slot 0x{:x}, but current RSP is 0x{:x}",
            frame.call_site, frame.stack_address, concrete.sp
        ));
    }

    let observed_return = concrete.load_memory_le(concrete.sp, 8).map_err(|err| {
        format!(
            "{unsupported}; x86_64 return replay could not read return-address stack witness at 0x{:x}: {err}",
            concrete.sp
        )
    })?;
    if observed_return != u128::from(frame.return_address) {
        return Err(format!(
            "{unsupported}; x86_64 return replay active frame from call 0x{:x} expected return address 0x{:x} at stack slot 0x{:x}, observed 0x{:x}",
            frame.call_site, frame.return_address, frame.stack_address, observed_return
        ));
    }

    Ok(())
}

fn validate_aarch64_direct_call_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; AArch64 direct call replay requires a following trace step so LR, SP, and the call target are checked"
        ));
    };
    let Some(call_sp) = exact_aarch64_stack_pointer_witness_value(step) else {
        return Err(format!(
            "{unsupported}; AArch64 direct call replay requires an exact 64-bit SP witness at trace step {} to anchor stack context",
            step.step
        ));
    };
    let Some(post_call_sp) = exact_aarch64_stack_pointer_witness_value(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 direct call replay requires an exact post-call 64-bit SP witness at trace step {}",
            next_step.step
        ));
    };
    if post_call_sp != call_sp {
        return Err(format!(
            "{unsupported}; AArch64 direct call replay expected BL to preserve SP 0x{call_sp:x}, observed post-call SP witness 0x{post_call_sp:x} at trace step {}",
            next_step.step
        ));
    }

    let return_address = instruction.address.wrapping_add(u64::from(instruction.size));
    let Some(lr) = exact_aarch64_link_register_witness_value(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 direct call replay requires an exact post-call X30/LR witness at trace step {} containing return address 0x{return_address:x}",
            next_step.step
        ));
    };
    if lr != u128::from(return_address) {
        return Err(format!(
            "{unsupported}; AArch64 direct call replay expected post-call X30/LR witness 0x{return_address:x} at trace step {}, observed 0x{lr:x}",
            next_step.step
        ));
    }

    Ok(())
}

fn validate_aarch64_indirect_call_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires a following trace step so the resolved target, LR, and SP are checked"
        ));
    };
    let Some(target_register) = aarch64_register_indirect_target(instruction) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires a GPR target operand with exact target-register provenance"
        ));
    };
    let Some(target) = exact_aarch64_register_witness_value(step, &target_register) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires an exact 64-bit {target_register} witness at trace step {} to resolve the call target",
            step.step
        ));
    };
    let Some(next_address) = trace_step_instruction_address(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires the following trace step {} to carry instruction provenance for the resolved target",
            next_step.step
        ));
    };
    if target != u128::from(next_address) {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay target witness {target_register}=0x{target:x} at trace step {} does not match following trace instruction 0x{next_address:x}",
            step.step
        ));
    }

    let Some(call_sp) = exact_aarch64_stack_pointer_witness_value(step) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires an exact 64-bit SP witness at trace step {} to anchor stack context",
            step.step
        ));
    };
    let Some(post_call_sp) = exact_aarch64_stack_pointer_witness_value(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires an exact post-call 64-bit SP witness at trace step {}",
            next_step.step
        ));
    };
    if post_call_sp != call_sp {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay expected BLR to preserve SP 0x{call_sp:x}, observed post-call SP witness 0x{post_call_sp:x} at trace step {}",
            next_step.step
        ));
    }

    let return_address = instruction.address.wrapping_add(u64::from(instruction.size));
    let Some(lr) = exact_aarch64_link_register_witness_value(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay requires an exact post-call X30/LR witness at trace step {} containing return address 0x{return_address:x}",
            next_step.step
        ));
    };
    if lr != u128::from(return_address) {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect call replay expected post-call X30/LR witness 0x{return_address:x} at trace step {}, observed 0x{lr:x}",
            next_step.step
        ));
    }

    Ok(())
}

fn validate_aarch64_indirect_branch_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect branch replay requires a following trace step so the resolved target is checked"
        ));
    };
    let Some(target_register) = aarch64_register_indirect_target(instruction) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect branch replay requires a GPR target operand with exact target-register provenance"
        ));
    };
    let Some(target) = exact_aarch64_register_witness_value(step, &target_register) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect branch replay requires an exact 64-bit {target_register} witness at trace step {} to resolve the branch target",
            step.step
        ));
    };
    let Some(next_address) = trace_step_instruction_address(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect branch replay requires the following trace step {} to carry instruction provenance for the resolved target",
            next_step.step
        ));
    };
    if target != u128::from(next_address) {
        return Err(format!(
            "{unsupported}; AArch64 register-indirect branch replay target witness {target_register}=0x{target:x} at trace step {} does not match following trace instruction 0x{next_address:x}",
            step.step
        ));
    }

    Ok(())
}

fn validate_aarch64_return_witness_context(
    instruction: &Instruction,
    step: &BinaryWitnessTraceStep,
    next_step: Option<&BinaryWitnessTraceStep>,
    step_index: usize,
    expected_trace_len: usize,
    concrete: &ConcreteState,
    call_frames: &[CallFrame],
) -> Result<(), String> {
    let unsupported = unsupported_control_flow_reason(instruction, step_index, expected_trace_len);
    let Some(next_step) = next_step else {
        return Err(format!(
            "{unsupported}; AArch64 return replay requires a following trace step so the LR target and restored SP are checked"
        ));
    };
    let Some(frame) = call_frames.last() else {
        return Err(format!(
            "{unsupported}; AArch64 return replay requires an active direct-call frame with exact LR/SP provenance"
        ));
    };
    if frame.architecture != BoundedMachineCodeArchitecture::Aarch64 {
        return Err(format!(
            "{unsupported}; AArch64 return replay active frame from call 0x{:x} was established for {:?}",
            frame.call_site, frame.architecture
        ));
    }

    let Some(current_sp) = exact_aarch64_stack_pointer_witness_value(step) else {
        return Err(format!(
            "{unsupported}; AArch64 return replay requires an exact 64-bit SP witness at trace step {} before returning",
            step.step
        ));
    };
    if current_sp != u128::from(frame.stack_address) {
        return Err(format!(
            "{unsupported}; AArch64 return replay active frame from call 0x{:x} expected restored SP 0x{:x} at trace step {}, observed 0x{current_sp:x}",
            frame.call_site, frame.stack_address, step.step
        ));
    }

    let Some(lr) = exact_aarch64_link_register_witness_value(step) else {
        return Err(format!(
            "{unsupported}; AArch64 return replay requires an exact X30/LR witness at trace step {} before returning",
            step.step
        ));
    };
    if lr != u128::from(frame.return_address) {
        return Err(format!(
            "{unsupported}; AArch64 return replay active frame from call 0x{:x} expected X30/LR return address 0x{:x}, observed 0x{lr:x} at trace step {}",
            frame.call_site, frame.return_address, step.step
        ));
    }
    if concrete.gpr[30] != frame.return_address {
        return Err(format!(
            "{unsupported}; AArch64 return replay active frame from call 0x{:x} expected concrete X30/LR 0x{:x}, observed 0x{:x}",
            frame.call_site, frame.return_address, concrete.gpr[30]
        ));
    }

    let Some(stack_witness) = frame.stack_witness else {
        return Err(format!(
            "{unsupported}; AArch64 return replay requires a saved return-address stack witness for call 0x{:x}: stack-pointer-relative width 8 containing 0x{:x}",
            frame.call_site, frame.return_address
        ));
    };

    let Some(post_return_sp) = exact_aarch64_stack_pointer_witness_value(next_step) else {
        return Err(format!(
            "{unsupported}; AArch64 return replay requires an exact post-return 64-bit SP witness at trace step {}",
            next_step.step
        ));
    };
    if post_return_sp != u128::from(frame.stack_address) {
        return Err(format!(
            "{unsupported}; AArch64 return replay expected post-return SP 0x{:x} at trace step {}, observed 0x{post_return_sp:x}",
            frame.stack_address, next_step.step
        ));
    }

    if stack_witness.value != frame.return_address {
        return Err(format!(
            "{unsupported}; AArch64 return replay stack witness at trace step {} address 0x{:x} offset {} width {} expected return address 0x{:x}, observed 0x{:x}",
            stack_witness.trace_step,
            stack_witness.address,
            stack_witness.offset,
            stack_witness.size_bytes,
            frame.return_address,
            stack_witness.value
        ));
    }

    Ok(())
}

fn has_exact_stack_pointer_witness(step: &BinaryWitnessTraceStep) -> bool {
    step.assignments.iter().any(|record| {
        let BinaryStorageLocation::Register { name, bit_width } = &record.storage else {
            return false;
        };
        matches!(name.to_ascii_uppercase().as_str(), "SP" | "RSP") && bit_width.unwrap_or(64) == 64
    })
}

fn has_return_address_stack_witness(step: &BinaryWitnessTraceStep) -> bool {
    step.assignments.iter().any(|record| {
        matches!(
            &record.storage,
            BinaryStorageLocation::Stack {
                base: BinaryStackBase::StackPointer,
                offset: 0,
                size_bytes: Some(8),
            }
        )
    })
}

fn exact_aarch64_stack_pointer_witness_value(step: &BinaryWitnessTraceStep) -> Option<u128> {
    step.assignments.iter().find_map(|record| {
        let BinaryStorageLocation::Register { name, bit_width } = &record.storage else {
            return None;
        };
        (name.eq_ignore_ascii_case("SP") && bit_width.unwrap_or(64) == 64)
            .then(|| witness_value_u128(record, 64, step.step).ok())
            .flatten()
    })
}

fn exact_aarch64_link_register_witness_value(step: &BinaryWitnessTraceStep) -> Option<u128> {
    step.assignments.iter().find_map(|record| {
        let BinaryStorageLocation::Register { name, bit_width } = &record.storage else {
            return None;
        };
        (matches!(name.to_ascii_uppercase().as_str(), "X30" | "LR")
            && bit_width.unwrap_or(64) == 64)
            .then(|| witness_value_u128(record, 64, step.step).ok())
            .flatten()
    })
}

fn exact_aarch64_register_witness_value(
    step: &BinaryWitnessTraceStep,
    register_name: &str,
) -> Option<u128> {
    step.assignments.iter().find_map(|record| {
        let BinaryStorageLocation::Register { name, bit_width } = &record.storage else {
            return None;
        };
        (aarch64_register_names_match(name, register_name) && bit_width.unwrap_or(64) == 64)
            .then(|| witness_value_u128(record, 64, step.step).ok())
            .flatten()
    })
}

fn exact_x86_register_witness_value(
    step: &BinaryWitnessTraceStep,
    register_name: &str,
) -> Option<u128> {
    step.assignments.iter().find_map(|record| {
        let BinaryStorageLocation::Register { name, bit_width } = &record.storage else {
            return None;
        };
        (name.eq_ignore_ascii_case(register_name) && bit_width.unwrap_or(64) == 64)
            .then(|| witness_value_u128(record, 64, step.step).ok())
            .flatten()
    })
}

fn trace_step_instruction_address(step: &BinaryWitnessTraceStep) -> Option<u64> {
    step.program_point.as_ref()?.origin.as_ref().map(|origin| origin.instruction_address)
}

fn x86_memory_indirect_call_target(instruction: &Instruction) -> Option<&MemoryOperand> {
    let Some(DisasmOperand::Mem(memory)) = instruction.operand(0) else {
        return None;
    };
    Some(memory)
}

fn x86_register_indirect_call_target(instruction: &Instruction) -> Option<&'static str> {
    let Some(DisasmOperand::Reg(register)) = instruction.operand(0) else {
        return None;
    };
    if register.kind == RegKind::Sp || (register.kind == RegKind::Gpr && register.index == 4) {
        return Some("RSP");
    }
    if register.kind != RegKind::Gpr {
        return None;
    }
    x86_gpr64_name(register.index)
}

fn aarch64_register_indirect_target(instruction: &Instruction) -> Option<String> {
    let Some(DisasmOperand::Reg(register)) = instruction.operand(0) else {
        return None;
    };
    aarch64_register_label(register)
}

fn aarch64_register_label(register: &Register) -> Option<String> {
    if register.kind == RegKind::Sp {
        return Some("SP".to_owned());
    }
    if register.kind != RegKind::Gpr || register.index >= 31 {
        return None;
    }
    Some(format!("X{}", register.index))
}

fn aarch64_register_names_match(actual: &str, expected: &str) -> bool {
    let actual = actual.to_ascii_uppercase();
    let expected = expected.to_ascii_uppercase();
    actual == expected
        || (actual == "LR" && expected == "X30")
        || (actual == "X30" && expected == "LR")
}

fn x86_memory_operand_address(
    concrete: &ConcreteState,
    memory: &MemoryOperand,
    instruction_address: u64,
) -> Result<u64, String> {
    match memory {
        MemoryOperand::Base { base } => x86_concrete_register_value(concrete, base),
        MemoryOperand::BaseOffset { base, offset } => {
            add_signed_u64(x86_concrete_register_value(concrete, base)?, *offset)
        }
        MemoryOperand::BaseRegister { base, index, shift, .. } => {
            let base = x86_concrete_register_value(concrete, base)?;
            let index = x86_concrete_register_value(concrete, index)?;
            let shifted = index.checked_shl(u32::from(*shift)).ok_or_else(|| {
                format!("index register shift {shift} overflows target-memory address")
            })?;
            base.checked_add(shifted).ok_or_else(|| {
                format!(
                    "base/index target-memory address overflows: 0x{base:x} + (0x{index:x} << {shift})"
                )
            })
        }
        MemoryOperand::PcRelative { offset } => add_signed_u64(instruction_address, *offset),
        MemoryOperand::PreIndex { base, offset } => {
            add_signed_u64(x86_concrete_register_value(concrete, base)?, *offset)
        }
        MemoryOperand::PostIndex { base, .. } => x86_concrete_register_value(concrete, base),
        _ => Err(format!("unsupported target-memory operand {}", x86_memory_operand_label(memory))),
    }
}

fn x86_concrete_register_value(
    concrete: &ConcreteState,
    register: &Register,
) -> Result<u64, String> {
    if register.kind == RegKind::Sp || (register.kind == RegKind::Gpr && register.index == 4) {
        return Ok(concrete.sp);
    }
    if register.kind != RegKind::Gpr {
        return Err(format!("unsupported target-memory address register {register:?}"));
    }
    if usize::from(register.index) >= concrete.gpr.len() {
        return Err(format!(
            "target-memory address register index {} is outside concrete register file",
            register.index
        ));
    }
    Ok(concrete.gpr[usize::from(register.index)])
}

fn add_signed_u64(base: u64, offset: i64) -> Result<u64, String> {
    if offset >= 0 {
        base.checked_add(offset as u64)
            .ok_or_else(|| format!("target-memory address 0x{base:x}+0x{offset:x} overflows"))
    } else {
        base.checked_sub(offset.unsigned_abs()).ok_or_else(|| {
            format!("target-memory address 0x{base:x}-0x{:x} underflows", offset.unsigned_abs())
        })
    }
}

fn exact_memory_witness_value(
    step: &BinaryWitnessTraceStep,
    concrete: &ConcreteState,
    address: u64,
    width_bytes: u32,
) -> Option<u128> {
    step.assignments.iter().find_map(|record| {
        if !memory_record_covers_address(record, concrete, address, width_bytes) {
            return None;
        }
        witness_value_u128(record, width_bytes.checked_mul(8)?, step.step).ok()
    })
}

fn memory_record_covers_address(
    record: &BinaryWitnessRecord,
    concrete: &ConcreteState,
    address: u64,
    width_bytes: u32,
) -> bool {
    match &record.storage {
        BinaryStorageLocation::Memory { address: formula, size_bytes } => {
            *size_bytes == Some(width_bytes) && formula_concrete_address(formula) == Some(address)
        }
        BinaryStorageLocation::Global {
            address: Some(global_address),
            size_bytes: Some(size),
            ..
        } => *global_address == address && u32::try_from(*size).ok() == Some(width_bytes),
        BinaryStorageLocation::Stack {
            base: BinaryStackBase::StackPointer,
            offset,
            size_bytes: Some(size),
        } => *size == width_bytes && add_stack_offset(concrete.sp, *offset) == Some(address),
        _ => false,
    }
}

fn formula_concrete_address(formula: &Formula) -> Option<u64> {
    let Formula::BitVec { value, width: 64 } = formula else {
        return None;
    };
    u64::try_from(*value).ok()
}

fn x86_memory_operand_label(memory: &MemoryOperand) -> String {
    match memory {
        MemoryOperand::Base { base } => {
            format!("[{}]", x86_register_label(base))
        }
        MemoryOperand::BaseOffset { base, offset } => {
            format!("[{}{}]", x86_register_label(base), signed_offset_label(*offset))
        }
        MemoryOperand::BaseRegister { base, index, shift, .. } => {
            if *shift == 0 {
                format!("[{}+{}]", x86_register_label(base), x86_register_label(index))
            } else {
                format!("[{}+{}<<{}]", x86_register_label(base), x86_register_label(index), shift)
            }
        }
        MemoryOperand::PcRelative { offset } => format!("[RIP{}]", signed_offset_label(*offset)),
        MemoryOperand::PreIndex { base, offset } => {
            format!("[{}{}]!", x86_register_label(base), signed_offset_label(*offset))
        }
        MemoryOperand::PostIndex { base, offset } => {
            format!("[{}],{}", x86_register_label(base), signed_offset_label(*offset))
        }
        _ => format!("{memory:?}"),
    }
}

fn signed_offset_label(offset: i64) -> String {
    if offset < 0 { format!("-0x{:x}", offset.unsigned_abs()) } else { format!("+0x{offset:x}") }
}

fn x86_register_label(register: &Register) -> String {
    if register.kind == RegKind::Sp || (register.kind == RegKind::Gpr && register.index == 4) {
        return "RSP".to_owned();
    }
    if register.kind == RegKind::Gpr {
        return x86_gpr64_name(register.index).unwrap_or("UNKNOWN").to_owned();
    }
    format!("{register:?}")
}

fn x86_gpr64_name(index: u8) -> Option<&'static str> {
    match index {
        0 => Some("RAX"),
        1 => Some("RCX"),
        2 => Some("RDX"),
        3 => Some("RBX"),
        4 => Some("RSP"),
        5 => Some("RBP"),
        6 => Some("RSI"),
        7 => Some("RDI"),
        8 => Some("R8"),
        9 => Some("R9"),
        10 => Some("R10"),
        11 => Some("R11"),
        12 => Some("R12"),
        13 => Some("R13"),
        14 => Some("R14"),
        15 => Some("R15"),
        _ => None,
    }
}

fn observe_aarch64_return_address_stack_witness(
    call_frames: &mut [CallFrame],
    step: &BinaryWitnessTraceStep,
    concrete: &ConcreteState,
) -> Result<(), WitnessStateError> {
    let Some(frame) = call_frames.last_mut() else {
        return Ok(());
    };
    if frame.architecture != BoundedMachineCodeArchitecture::Aarch64
        || frame.stack_witness.is_some()
    {
        return Ok(());
    }

    for record in &step.assignments {
        let BinaryStorageLocation::Stack {
            base: BinaryStackBase::StackPointer,
            offset,
            size_bytes: Some(8),
        } = &record.storage
        else {
            continue;
        };
        let Some(address) = add_stack_offset(concrete.sp, *offset) else {
            return Err(WitnessStateError::unsupported(format!(
                "bounded machine replay stack witness `{}` at trace step {} overflows address space from SP 0x{:x} with offset {offset}",
                record.raw_name, step.step, concrete.sp
            )));
        };
        let value = witness_value_u128(record, 64, step.step)?;
        if value == u128::from(frame.return_address) {
            frame.stack_witness = Some(ReturnAddressStackWitness {
                trace_step: step.step,
                address,
                offset: *offset,
                size_bytes: 8,
                value: frame.return_address,
            });
            break;
        }
    }

    Ok(())
}

fn update_call_frames(
    call_frames: &mut Vec<CallFrame>,
    instruction: &Instruction,
    pc_before: u64,
    concrete: &ConcreteState,
    architecture: BoundedMachineCodeArchitecture,
) {
    match instruction.flow {
        ControlFlow::Call => {
            call_frames.push(CallFrame {
                architecture,
                call_site: instruction.address,
                return_address: pc_before.wrapping_add(u64::from(instruction.size)),
                stack_address: concrete.sp,
                stack_witness: None,
            });
        }
        ControlFlow::Return => {
            call_frames.pop();
        }
        _ => {}
    }
}

fn unsupported_control_flow_reason(
    instruction: &Instruction,
    step: usize,
    expected_trace_len: usize,
) -> String {
    let detail = match instruction.flow {
        ControlFlow::Branch if instruction.branch_target().is_some() => "direct branch",
        ControlFlow::Branch => "indirect branch",
        ControlFlow::Call if instruction.branch_target().is_some() => "direct call",
        ControlFlow::Call => "indirect call",
        ControlFlow::Return => "return",
        ControlFlow::Exception => "exception",
        ControlFlow::Fallthrough => "fallthrough should have been replayable",
        ControlFlow::ConditionalBranch => "conditional branch should have been replayable",
        _ => "unknown",
    };
    format!(
        "bounded machine replay supports fallthrough, conditional branches, direct unconditional branches, proof-context x86_64 call/return, proof-context AArch64 direct/register-indirect call/return, and proof-context AArch64 register-indirect branch only; unsupported control flow: {detail} at 0x{:x} is {:?} (step {} of expected trace length {})",
        instruction.address, instruction.flow, step, expected_trace_len
    )
}

trait MachineResultTraceExt {
    fn with_observed_trace(self, observed: Vec<BinaryMachineInstructionEvidence>) -> Self;
}

impl MachineResultTraceExt for BinaryMachineReplayResult {
    fn with_observed_trace(mut self, observed: Vec<BinaryMachineInstructionEvidence>) -> Self {
        self.instruction_trace = observed;
        self
    }
}

/// Default backend used when no machine-code replay implementation is wired in.
#[derive(Debug, Clone, Copy, Default)]
pub struct UnavailableMachineReplayBackend;

impl BinaryMachineReplayBackend for UnavailableMachineReplayBackend {
    fn replay(&self, _request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
        BinaryMachineReplayResult::default()
    }
}

/// Binary replay classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryReplayStatus {
    /// The witness was confirmed at the binary replay boundary.
    ///
    /// For binary witnesses this requires machine replay evidence. Lifted-only
    /// replay remains [`BinaryReplayStatus::NeedsMachineReplay`].
    Confirmed,
    /// The witness trace contradicts lifted replay.
    Spurious,
    /// The available data is plausible but requires machine-code replay or
    /// richer witness data before confirmation.
    NeedsMachineReplay,
    /// Replay is not supported for this witness or lifted construct.
    Unsupported,
    /// Replay was attempted but failed before checked evidence could be
    /// produced.
    Failed,
}

impl BinaryReplayStatus {
    /// Project to the coarse `trust-types` replay status before validated
    /// machine replay is attached.
    ///
    /// [`BinaryReplayReport`] overrides this to [`ReplayStatus::Replayed`]
    /// only after a machine backend returns matching instruction evidence.
    #[must_use]
    pub fn as_trust_types_status(self) -> ReplayStatus {
        match self {
            Self::Confirmed => ReplayStatus::NotAttempted,
            Self::Spurious => ReplayStatus::Spurious,
            Self::NeedsMachineReplay => ReplayStatus::NotAttempted,
            Self::Unsupported => ReplayStatus::Failed,
            Self::Failed => ReplayStatus::Failed,
        }
    }
}

impl fmt::Display for BinaryReplayStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Confirmed => f.write_str("confirmed"),
            Self::Spurious => f.write_str("spurious"),
            Self::NeedsMachineReplay => f.write_str("needs_machine_replay"),
            Self::Unsupported => f.write_str("unsupported"),
            Self::Failed => f.write_str("failed"),
        }
    }
}

fn replay_status_name(status: ReplayStatus) -> &'static str {
    match status {
        ReplayStatus::NotAttempted => "not_attempted",
        ReplayStatus::Replayed => "replayed",
        ReplayStatus::Spurious => "spurious",
        ReplayStatus::Failed => "failed",
        _ => "failed",
    }
}

fn parse_replay_status(value: &str) -> Option<ReplayStatus> {
    match value {
        "not_attempted" | "NotAttempted" => Some(ReplayStatus::NotAttempted),
        "replayed" | "Replayed" => Some(ReplayStatus::Replayed),
        "spurious" | "Spurious" => Some(ReplayStatus::Spurious),
        "failed" | "Failed" => Some(ReplayStatus::Failed),
        _ => None,
    }
}

fn serialize_replay_status<S>(status: &ReplayStatus, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_str(replay_status_name(*status))
}

fn deserialize_replay_status<'de, D>(deserializer: D) -> Result<ReplayStatus, D::Error>
where
    D: Deserializer<'de>,
{
    let value = String::deserialize(deserializer)?;
    parse_replay_status(&value).ok_or_else(|| {
        serde::de::Error::unknown_variant(
            &value,
            &["not_attempted", "replayed", "spurious", "failed"],
        )
    })
}

/// Configuration for binary replay classification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReplayConfig {
    /// Maximum number of lifted blocks to execute.
    pub depth_limit: usize,
    /// Entry block index.
    pub entry_block: usize,
    /// Require counterexample trace program points before lifted replay can
    /// satisfy the expected outcome.
    pub require_trace_for_confirmation: bool,
}

impl Default for BinaryReplayConfig {
    fn default() -> Self {
        Self { depth_limit: 1000, entry_block: 0, require_trace_for_confirmation: true }
    }
}

impl From<&BinaryReplayConfig> for AdapterConfig {
    fn from(config: &BinaryReplayConfig) -> Self {
        Self {
            depth_limit: config.depth_limit,
            entry_block: config.entry_block,
            capture_per_statement: true,
        }
    }
}

/// Result of a binary replay classification.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryReplayReport {
    /// Fine-grained status for binary replay.
    pub status: BinaryReplayStatus,
    /// Coarse status compatible with `trust-types::ReplayStatus`.
    #[serde(
        serialize_with = "serialize_replay_status",
        deserialize_with = "deserialize_replay_status"
    )]
    pub trust_types_status: ReplayStatus,
    /// Solver/counterexample data normalized into structured binary witness
    /// records.
    pub normalized_witness: BinaryWitness,
    /// Machine-code replay evidence for the normalized witness.
    pub machine_replay: BinaryMachineReplayReport,
    /// Human-readable reason for the status.
    pub reason: String,
    /// Lifted block trace observed during replay, if replay ran.
    pub block_trace: Vec<usize>,
    /// Counterexample trace blocks extracted from witness program points.
    pub witness_trace: Vec<usize>,
    /// Whether lifted replay terminated normally.
    pub terminated_normally: Option<bool>,
    /// Whether original machine-code replay is still required before the
    /// binary witness can be treated as confirmed.
    #[serde(default)]
    pub needs_machine_replay: bool,
}

impl BinaryReplayReport {
    fn new(status: BinaryReplayStatus, reason: impl Into<String>) -> Self {
        Self {
            status,
            trust_types_status: status.as_trust_types_status(),
            normalized_witness: BinaryWitness::default(),
            machine_replay: BinaryMachineReplayReport::default(),
            reason: reason.into(),
            block_trace: Vec::new(),
            witness_trace: Vec::new(),
            terminated_normally: None,
            needs_machine_replay: matches!(
                status,
                BinaryReplayStatus::Confirmed | BinaryReplayStatus::NeedsMachineReplay
            ),
        }
    }

    fn with_replay(mut self, replay: &AdapterResult) -> Self {
        self.block_trace = compact_blocks(&replay.block_trace);
        self.terminated_normally = Some(replay.terminated_normally);
        self
    }

    fn with_witness_trace(mut self, witness_trace: Vec<usize>) -> Self {
        self.witness_trace = compact_blocks(&witness_trace);
        self
    }

    fn with_normalized_witness(mut self, witness: BinaryWitness) -> Self {
        self.normalized_witness = witness;
        self
    }

    fn with_machine_replay(mut self, machine_replay: BinaryMachineReplayReport) -> Self {
        match machine_replay.status {
            BinaryMachineReplayStatus::Replayed => {
                if self.status == BinaryReplayStatus::Confirmed
                    || (self.status == BinaryReplayStatus::NeedsMachineReplay
                        && !self.block_trace.is_empty())
                {
                    self.status = BinaryReplayStatus::Confirmed;
                    self.trust_types_status = ReplayStatus::Replayed;
                    self.needs_machine_replay = false;
                    self.reason = format!(
                        "{}; machine-code replay confirmed matching instruction provenance",
                        self.reason
                    );
                } else {
                    self.reason = format!(
                        "{}; machine-code replay matched instruction provenance but prior replay status remains {}",
                        self.reason, self.status
                    );
                }
            }
            BinaryMachineReplayStatus::Spurious => {
                self.status = BinaryReplayStatus::Spurious;
                self.trust_types_status = ReplayStatus::Spurious;
                self.needs_machine_replay = false;
                self.reason = format!("{}; {}", self.reason, machine_replay.reason);
            }
            BinaryMachineReplayStatus::NeedsMachineReplay => {
                if self.status == BinaryReplayStatus::Confirmed {
                    self.status = BinaryReplayStatus::NeedsMachineReplay;
                    self.trust_types_status = ReplayStatus::NotAttempted;
                    self.reason = format!(
                        "{}; machine-code replay is still required: {}",
                        self.reason, machine_replay.reason
                    );
                }
                self.needs_machine_replay = matches!(
                    self.status,
                    BinaryReplayStatus::Confirmed | BinaryReplayStatus::NeedsMachineReplay
                );
            }
            BinaryMachineReplayStatus::Unsupported => {
                if self.status != BinaryReplayStatus::Spurious {
                    self.status = BinaryReplayStatus::Unsupported;
                    self.trust_types_status = ReplayStatus::Failed;
                    self.needs_machine_replay = false;
                    self.reason = format!("{}; {}", self.reason, machine_replay.reason);
                }
            }
            BinaryMachineReplayStatus::Failed => {
                if self.status != BinaryReplayStatus::Spurious {
                    self.status = BinaryReplayStatus::Failed;
                    self.trust_types_status = ReplayStatus::Failed;
                    self.needs_machine_replay = false;
                    self.reason = format!(
                        "{}; machine-code replay failed: {}",
                        self.reason, machine_replay.reason
                    );
                }
            }
        }
        self.machine_replay = machine_replay;
        self
    }
}

/// Normalize solver/counterexample-like data into structured binary witness
/// records.
#[must_use]
pub fn normalize_binary_witness(
    target: BinaryReplayTarget<'_>,
    input: &BinaryReplayInput,
) -> BinaryWitness {
    match target {
        BinaryReplayTarget::LiftedFunction(function) => {
            normalize_lifted_binary_witness(function, input)
        }
        BinaryReplayTarget::BinaryOrigin(origin) => normalize_binary_origin_witness(&origin, input),
    }
}

/// Normalize a witness using lifted TrustIr local metadata.
#[must_use]
pub fn normalize_lifted_binary_witness(
    function: &VerifiableFunction,
    input: &BinaryReplayInput,
) -> BinaryWitness {
    let origin = lifted_function_origin(function);
    let context = WitnessNormalizationContext {
        function: Some(function.def_path.as_str()),
        origin,
        artifact_digest: input.artifact_digest.clone(),
        selected_image: input.selected_image.clone(),
        verification_context: input
            .verification_condition
            .as_ref()
            .and_then(binary_witness_verification_context),
        requires_selected_image_identity: input.requires_selected_image_identity,
        instruction_provenance: &input.instruction_provenance,
        locals: &function.body.locals,
    };
    normalize_counterexample_witness(input, &context)
}

/// Normalize a witness using binary-origin metadata only.
#[must_use]
pub fn normalize_binary_origin_witness(
    origin: &BinaryOrigin,
    input: &BinaryReplayInput,
) -> BinaryWitness {
    let trust_origin = trust_origin_from_binary_origin(origin);
    let context = WitnessNormalizationContext {
        function: origin.function.as_deref(),
        origin: trust_origin,
        artifact_digest: input.artifact_digest.clone(),
        selected_image: input.selected_image.clone(),
        verification_context: input
            .verification_condition
            .as_ref()
            .and_then(binary_witness_verification_context),
        requires_selected_image_identity: input.requires_selected_image_identity,
        instruction_provenance: &input.instruction_provenance,
        locals: &[],
    };
    normalize_counterexample_witness(input, &context)
}

/// Replay a normalized binary witness through a machine-code backend.
///
/// A backend-reported replay success is accepted only when the backend returns
/// instruction evidence matching the normalized witness instruction
/// provenance.
#[must_use]
pub fn replay_machine_witness<B: BinaryMachineReplayBackend + ?Sized>(
    witness: &BinaryWitness,
    config: &BinaryMachineReplayConfig,
    backend: &B,
) -> BinaryMachineReplayReport {
    let request = BinaryMachineReplayRequest { witness, config };
    let result = backend.replay(&request);
    validate_machine_replay_result(witness, config, result)
}

/// Build conservative binary replay evidence from a solver dispatch.
///
/// Only SAT-as-counterexample dispatches carrying a structured
/// [`Counterexample`] produce a witness report. UNSAT/proved dispatches do not
/// produce exploit witnesses.
#[must_use]
pub fn replay_solver_dispatch_counterexample(
    dispatch: &SolverDispatchRecord,
    function: Option<&VerifiableFunction>,
    config: &BinaryReplayConfig,
) -> BinarySolverDispatchReplayEvidence {
    replay_solver_dispatch_counterexample_with_machine_replay(
        dispatch,
        function,
        config,
        &BinaryMachineReplayConfig::default(),
        &UnavailableMachineReplayBackend,
    )
}

/// Build conservative binary replay evidence from a solver dispatch using an
/// explicit machine-code replay backend.
#[must_use]
pub fn replay_solver_dispatch_counterexample_with_machine_replay<
    B: BinaryMachineReplayBackend + ?Sized,
>(
    dispatch: &SolverDispatchRecord,
    function: Option<&VerifiableFunction>,
    config: &BinaryReplayConfig,
    machine_config: &BinaryMachineReplayConfig,
    backend: &B,
) -> BinarySolverDispatchReplayEvidence {
    let replay_requirement = dispatch_replay_requirement(dispatch);
    let Some(counterexample) = dispatch_counterexample(dispatch) else {
        let requirement_satisfied =
            dispatch_requirement_satisfied_without_witness(dispatch, replay_requirement);
        let reason = no_witness_requirement_reason(
            dispatch_no_witness_reason(dispatch),
            replay_requirement,
            requirement_satisfied,
        );
        return BinarySolverDispatchReplayEvidence::no_witness(
            dispatch,
            replay_requirement,
            requirement_satisfied,
            reason,
        );
    };

    let mut input = BinaryReplayInput::new(counterexample);
    if let Some(vc) = dispatch.vc.clone() {
        input = input.with_verification_condition(vc.into_vc());
    }
    if let Some(origin) = dispatch.origin.clone() {
        input = input.with_instruction_provenance(vec![origin]);
    }
    if let Some(identity) = dispatch.replay_artifact_digest_identity() {
        if let Some(artifact_digest) = identity.root_artifact_digest.clone() {
            input = input.with_artifact_digest(artifact_digest);
        }
        if let Some(selected_image) = identity.selected_image.clone() {
            input = input.with_selected_image(selected_image);
        }
    }
    if replay_requirement.requires_machine_witness_replay() {
        input = input.require_selected_image_identity();
    }

    let exact_machine_config;
    let effective_machine_config = if replay_requirement.requires_machine_witness_replay()
        && (!machine_config.require_exact_instruction_trace
            || !machine_config.require_exact_artifact_digest)
    {
        exact_machine_config = BinaryMachineReplayConfig {
            require_exact_instruction_trace: true,
            require_exact_artifact_digest: true,
        };
        &exact_machine_config
    } else {
        machine_config
    };
    let target = function.map_or_else(
        || BinaryReplayTarget::binary_origin(binary_origin_from_dispatch(dispatch)),
        BinaryReplayTarget::lifted,
    );
    let report = replay_binary_counterexample_with_machine_replay(
        target,
        &input,
        config,
        effective_machine_config,
        backend,
    );
    let requirement_satisfied =
        dispatch_requirement_satisfied_by_report(replay_requirement, &report);
    let reason = if requirement_satisfied {
        "SAT counterexample replayed with exact matching machine-code instruction evidence".into()
    } else if replay_requirement.requires_machine_witness_replay() {
        report_requirement_failure_reason(
            "SAT counterexample requires exact machine witness replay before release",
            &report,
        )
    } else {
        report_requirement_failure_reason(
            "SAT counterexample normalized, but binary replay remains unconfirmed",
            &report,
        )
    };
    BinarySolverDispatchReplayEvidence::with_report(
        dispatch,
        report,
        replay_requirement,
        requirement_satisfied,
        reason,
    )
}

fn report_requirement_failure_reason(base_reason: &str, report: &BinaryReplayReport) -> String {
    let mut details = Vec::new();
    if !report.reason.is_empty() {
        details.push(report.reason.clone());
    }
    if !report.machine_replay.reason.is_empty() && report.machine_replay.reason != report.reason {
        details.push(report.machine_replay.reason.clone());
    }
    if let Some(blocker) = report.machine_replay.source_backprop_replay_blocker_reason()
        && !details.iter().any(|detail| detail == &blocker) {
            details.push(blocker);
        }

    if details.is_empty() {
        base_reason.into()
    } else {
        format!("{base_reason}: {}", details.join("; "))
    }
}

/// Replay and classify a binary counterexample witness.
///
/// The API accepts either a lifted function or binary origin metadata. Lifted
/// functions are replayed through existing `trust-symex` block execution.
/// Binary-origin-only targets return [`BinaryReplayStatus::NeedsMachineReplay`]
/// because this crate does not execute machine code.
#[must_use]
pub fn replay_binary_counterexample(
    target: BinaryReplayTarget<'_>,
    input: &BinaryReplayInput,
    config: &BinaryReplayConfig,
) -> BinaryReplayReport {
    let report = replay_binary_counterexample_without_machine(target, input, config);
    let machine_replay = replay_machine_witness(
        &report.normalized_witness,
        &BinaryMachineReplayConfig::default(),
        &UnavailableMachineReplayBackend,
    );
    report.with_machine_replay(machine_replay)
}

/// Replay and classify a binary counterexample using an explicit machine-code
/// replay backend.
#[must_use]
pub fn replay_binary_counterexample_with_machine_replay<B: BinaryMachineReplayBackend + ?Sized>(
    target: BinaryReplayTarget<'_>,
    input: &BinaryReplayInput,
    config: &BinaryReplayConfig,
    machine_config: &BinaryMachineReplayConfig,
    backend: &B,
) -> BinaryReplayReport {
    let report = replay_binary_counterexample_without_machine(target, input, config);
    let machine_replay =
        replay_machine_witness(&report.normalized_witness, machine_config, backend);
    report.with_machine_replay(machine_replay)
}

fn replay_binary_counterexample_without_machine(
    target: BinaryReplayTarget<'_>,
    input: &BinaryReplayInput,
    config: &BinaryReplayConfig,
) -> BinaryReplayReport {
    match &target {
        BinaryReplayTarget::LiftedFunction(function) => {
            replay_lifted_function_without_machine(function, input, config)
        }
        BinaryReplayTarget::BinaryOrigin(origin) => {
            let mut reason =
                "binary-origin replay requires a machine-code replay backend".to_owned();
            if let Some(entry) = origin.entry {
                reason.push_str(&format!(" for entry 0x{entry:x}"));
            }
            BinaryReplayReport::new(BinaryReplayStatus::NeedsMachineReplay, reason)
                .with_normalized_witness(normalize_binary_origin_witness(origin, input))
        }
    }
}

/// Replay and classify a counterexample against a lifted function.
#[must_use]
pub fn replay_lifted_function(
    function: &VerifiableFunction,
    input: &BinaryReplayInput,
    config: &BinaryReplayConfig,
) -> BinaryReplayReport {
    let report = replay_lifted_function_without_machine(function, input, config);
    let machine_replay = replay_machine_witness(
        &report.normalized_witness,
        &BinaryMachineReplayConfig::default(),
        &UnavailableMachineReplayBackend,
    );
    report.with_machine_replay(machine_replay)
}

fn replay_lifted_function_without_machine(
    function: &VerifiableFunction,
    input: &BinaryReplayInput,
    config: &BinaryReplayConfig,
) -> BinaryReplayReport {
    replay_lifted_function_inner(function, input, config)
        .with_normalized_witness(normalize_lifted_binary_witness(function, input))
}

fn replay_lifted_function_inner(
    function: &VerifiableFunction,
    input: &BinaryReplayInput,
    config: &BinaryReplayConfig,
) -> BinaryReplayReport {
    if let Some(reason) = unsupported_counterexample_value(&input.counterexample) {
        return BinaryReplayReport::new(BinaryReplayStatus::Unsupported, reason);
    }

    if let Some((status, reason)) = lifted_replay_precheck(function, config) {
        return BinaryReplayReport::new(status, reason);
    }

    let adapter_config = AdapterConfig::from(config);
    let Some(vc) = &input.verification_condition else {
        return BinaryReplayReport::new(
            BinaryReplayStatus::NeedsMachineReplay,
            "original verification condition was not supplied; refusing lifted replay confirmation for SAT witness",
        );
    };
    let replay = match replay_with_trace(
        &input.counterexample,
        vc,
        &function.body.blocks,
        &adapter_config,
    ) {
        Ok(replay) => replay,
        Err(err) => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::Unsupported,
                format!("lifted replay failed: {err}"),
            );
        }
    };

    if replay_ended_on_spurious_path(&replay) {
        return BinaryReplayReport::new(
            BinaryReplayStatus::Spurious,
            "lifted replay could not select a feasible branch from the witness",
        )
        .with_replay(&replay);
    }

    let trace_blocks = match extract_witness_blocks(&input.counterexample) {
        WitnessBlocks::Blocks(blocks) => blocks,
        WitnessBlocks::NoTrace if config.require_trace_for_confirmation => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::NeedsMachineReplay,
                "raw solver model has no execution trace; refusing to confirm without replay detail",
            )
            .with_replay(&replay);
        }
        WitnessBlocks::NoTrace => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::NeedsMachineReplay,
                "raw solver model has no execution trace; refusing to confirm without replay detail",
            )
            .with_replay(&replay);
        }
        WitnessBlocks::EmptyTrace if config.require_trace_for_confirmation => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::NeedsMachineReplay,
                "counterexample trace is empty; refusing to confirm without replay detail",
            )
            .with_replay(&replay);
        }
        WitnessBlocks::EmptyTrace => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::NeedsMachineReplay,
                "counterexample trace is empty; refusing to confirm without replay detail",
            )
            .with_replay(&replay);
        }
        WitnessBlocks::MissingProgramPoint if config.require_trace_for_confirmation => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::NeedsMachineReplay,
                "counterexample trace lacks lifted program points; machine replay or richer trace is needed",
            )
            .with_replay(&replay);
        }
        WitnessBlocks::MissingProgramPoint => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::NeedsMachineReplay,
                "counterexample trace lacks lifted program points; machine replay or richer trace is needed",
            )
            .with_replay(&replay);
        }
        WitnessBlocks::InvalidProgramPoint(label) => {
            return BinaryReplayReport::new(
                BinaryReplayStatus::Unsupported,
                format!("unsupported counterexample program point '{label}'"),
            )
            .with_replay(&replay);
        }
    };

    let compact_witness = compact_blocks(&trace_blocks);
    let compact_replay = compact_blocks(&replay.block_trace);
    if config.require_trace_for_confirmation && compact_witness != compact_replay {
        return BinaryReplayReport::new(
            BinaryReplayStatus::Spurious,
            "counterexample trace does not match lifted replay block trace",
        )
        .with_replay(&replay)
        .with_witness_trace(compact_witness);
    }

    let Some(expectation) = &input.expectation else {
        return BinaryReplayReport::new(
            BinaryReplayStatus::NeedsMachineReplay,
            "lifted trace replay matched, but no replay expectation was supplied for confirmation",
        )
        .with_replay(&replay)
        .with_witness_trace(compact_witness);
    };

    if expectation_satisfied(expectation, &replay, &function.body.blocks) {
        BinaryReplayReport::new(
            BinaryReplayStatus::Confirmed,
            "witness trace and expected outcome matched lifted IR; original machine-code replay was not attempted",
        )
        .with_replay(&replay)
        .with_witness_trace(compact_witness)
    } else {
        BinaryReplayReport::new(
            BinaryReplayStatus::Spurious,
            "lifted replay did not satisfy the expected witness outcome",
        )
        .with_replay(&replay)
        .with_witness_trace(compact_witness)
    }
}

/// Status for deterministic counterexample minimization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryMinimizationStatus {
    /// The scaffold removed syntactically redundant trace detail.
    Minimized,
    /// The witness was already unchanged by supported deterministic passes.
    Unchanged,
    /// No honest minimization pass is available for this witness shape.
    Unsupported,
}

/// Configuration for deterministic minimization scaffolding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMinimizationConfig {
    /// Remove consecutive duplicate trace steps with identical program point
    /// and assignments. Solver assignments are never removed by this scaffold.
    pub remove_consecutive_duplicate_trace_steps: bool,
}

impl Default for BinaryMinimizationConfig {
    fn default() -> Self {
        Self { remove_consecutive_duplicate_trace_steps: true }
    }
}

/// Result of deterministic witness minimization.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryMinimizationResult {
    /// Outcome of the minimization scaffold.
    pub status: BinaryMinimizationStatus,
    /// Resulting counterexample. Assignments are unchanged.
    pub counterexample: Counterexample,
    /// Number of trace steps removed.
    pub removed_trace_steps: usize,
    /// Number of model assignments removed. Always zero for now.
    pub removed_assignments: usize,
    /// Machine-checkable metadata about the deterministic minimization pass.
    pub metadata: BinaryTraceMinimizationMetadata,
    /// Human-readable reason for the outcome.
    pub reason: String,
}

/// Metadata describing a deterministic trace minimization pass.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryTraceMinimizationMetadata {
    /// Trace length before minimization, if trace detail was present.
    pub original_trace_steps: Option<usize>,
    /// Trace length after minimization, if trace detail was present.
    pub minimized_trace_steps: Option<usize>,
    /// Model assignment count before minimization.
    pub original_model_assignments: usize,
    /// Model assignment count after minimization.
    pub minimized_model_assignments: usize,
    /// Original BMC step indices removed by the deterministic pass.
    pub removed_trace_step_indices: Vec<u32>,
    /// True when every top-level model assignment was retained.
    pub assignments_preserved: bool,
}

/// Deterministically minimize binary counterexample trace detail when safe.
///
/// This scaffold only removes consecutive duplicate trace steps with identical
/// program point and assignments. It does not attempt semantic delta debugging
/// of solver assignments because `trust-symex` cannot yet re-check binary
/// counterexample predicates independently.
#[must_use]
pub fn minimize_binary_counterexample(
    input: &BinaryReplayInput,
    config: &BinaryMinimizationConfig,
) -> BinaryMinimizationResult {
    let mut counterexample = input.counterexample.clone();
    let base_metadata = BinaryTraceMinimizationMetadata {
        original_trace_steps: input.counterexample.trace.as_ref().map(|trace| trace.steps.len()),
        minimized_trace_steps: input.counterexample.trace.as_ref().map(|trace| trace.steps.len()),
        original_model_assignments: input.counterexample.assignments.len(),
        minimized_model_assignments: input.counterexample.assignments.len(),
        removed_trace_step_indices: Vec::new(),
        assignments_preserved: true,
    };
    let Some(trace) = &input.counterexample.trace else {
        return BinaryMinimizationResult {
            status: BinaryMinimizationStatus::Unsupported,
            counterexample,
            removed_trace_steps: 0,
            removed_assignments: 0,
            metadata: base_metadata,
            reason: "no trace detail is available for deterministic minimization".into(),
        };
    };

    if trace.is_empty() || !config.remove_consecutive_duplicate_trace_steps {
        return BinaryMinimizationResult {
            status: BinaryMinimizationStatus::Unchanged,
            counterexample,
            removed_trace_steps: 0,
            removed_assignments: 0,
            metadata: base_metadata,
            reason: "no supported minimization changed the witness".into(),
        };
    }

    let mut retained = Vec::with_capacity(trace.steps.len());
    let mut removed_trace_step_indices = Vec::new();
    for step in &trace.steps {
        if retained.last().is_some_and(|prev| same_trace_payload(prev, step)) {
            removed_trace_step_indices.push(step.step);
        } else {
            retained.push(step.clone());
        }
    }

    if removed_trace_step_indices.is_empty() {
        BinaryMinimizationResult {
            status: BinaryMinimizationStatus::Unchanged,
            counterexample,
            removed_trace_steps: 0,
            removed_assignments: 0,
            metadata: base_metadata,
            reason: "trace has no consecutive duplicate steps to remove".into(),
        }
    } else {
        let metadata = BinaryTraceMinimizationMetadata {
            minimized_trace_steps: Some(retained.len()),
            removed_trace_step_indices: removed_trace_step_indices.clone(),
            ..base_metadata
        };
        counterexample.trace = Some(CounterexampleTrace::new(retained));
        BinaryMinimizationResult {
            status: BinaryMinimizationStatus::Minimized,
            counterexample,
            removed_trace_steps: removed_trace_step_indices.len(),
            removed_assignments: 0,
            metadata,
            reason: "removed only consecutive duplicate trace steps; model assignments unchanged"
                .into(),
        }
    }
}

fn validate_machine_replay_result(
    witness: &BinaryWitness,
    config: &BinaryMachineReplayConfig,
    result: BinaryMachineReplayResult,
) -> BinaryMachineReplayReport {
    let expected_instruction_trace = expected_machine_instruction_trace(witness);
    let expected_artifact_digest = witness.provenance.artifact_digest.clone();
    let expected_selected_image = witness.provenance.selected_image.clone();
    let boundary_evidence = replay_boundary_evidence(&expected_instruction_trace, &result);
    match result.status {
        BinaryMachineReplayStatus::Replayed => {
            if expected_instruction_trace.is_empty() {
                return BinaryMachineReplayReport::from_backend_result(
                    BinaryMachineReplayStatus::NeedsMachineReplay,
                    result,
                    expected_artifact_digest,
                    false,
                    expected_selected_image,
                    false,
                    expected_instruction_trace,
                    false,
                    "normalized witness has no instruction-level provenance for machine replay validation",
                );
            }

            match machine_instruction_trace_validation(&expected_instruction_trace, &result, config)
            {
                MachineInstructionTraceValidation::Matched => {
                    let artifact_digest_validation = machine_artifact_digest_validation(
                        expected_artifact_digest.as_ref(),
                        result.artifact_digest.as_ref(),
                        config,
                    );
                    let matched_artifact_digest = artifact_digest_validation.allows_replay();
                    if let Some(reason) = artifact_digest_validation.fail_closed_reason() {
                        let status = match artifact_digest_validation {
                            MachineArtifactDigestValidation::Mismatched => {
                                BinaryMachineReplayStatus::Spurious
                            }
                            MachineArtifactDigestValidation::Matched
                            | MachineArtifactDigestValidation::NotRequired => {
                                BinaryMachineReplayStatus::Replayed
                            }
                            MachineArtifactDigestValidation::MissingExpected
                            | MachineArtifactDigestValidation::MissingObserved
                            | MachineArtifactDigestValidation::InvalidExpected
                            | MachineArtifactDigestValidation::InvalidObserved => {
                                BinaryMachineReplayStatus::NeedsMachineReplay
                            }
                        };
                        return BinaryMachineReplayReport::from_backend_result(
                            status,
                            result,
                            expected_artifact_digest,
                            matched_artifact_digest,
                            expected_selected_image,
                            false,
                            expected_instruction_trace,
                            true,
                            reason,
                        );
                    }
                    let selected_image_validation = machine_selected_image_validation(
                        expected_selected_image.as_ref(),
                        result.selected_image.as_ref(),
                        witness.provenance.requires_selected_image_identity,
                        config,
                    );
                    let matched_selected_image = selected_image_validation.allows_replay();
                    let selected_image_byte_range_diagnostic = selected_image_validation
                        .byte_range_diagnostic(
                            expected_selected_image.as_ref(),
                            result.selected_image.as_ref(),
                        );
                    if let Some(reason) = selected_image_validation.fail_closed_reason() {
                        let status = match selected_image_validation {
                            MachineSelectedImageValidation::Mismatched => {
                                BinaryMachineReplayStatus::Spurious
                            }
                            MachineSelectedImageValidation::Matched
                            | MachineSelectedImageValidation::NotRequired => {
                                BinaryMachineReplayStatus::Replayed
                            }
                            MachineSelectedImageValidation::MissingExpected
                            | MachineSelectedImageValidation::MissingObserved
                            | MachineSelectedImageValidation::InvalidExpected
                            | MachineSelectedImageValidation::InvalidObserved => {
                                BinaryMachineReplayStatus::NeedsMachineReplay
                            }
                        };
                        let report_reason = selected_image_byte_range_diagnostic
                            .as_ref()
                            .map(|diagnostic| diagnostic.diagnostic.as_str())
                            .unwrap_or(reason);
                        let mut report = BinaryMachineReplayReport::from_backend_result(
                            status,
                            result,
                            expected_artifact_digest,
                            matched_artifact_digest,
                            expected_selected_image,
                            matched_selected_image,
                            expected_instruction_trace,
                            true,
                            report_reason,
                        );
                        if let Some(diagnostic) = selected_image_byte_range_diagnostic {
                            report = report.ensure_byte_range_diagnostic(diagnostic);
                        }
                        return report;
                    }
                    if witness.provenance.requires_selected_image_identity
                        && let Some(reason) = machine_model_trace_binding_reason(witness) {
                            return BinaryMachineReplayReport::from_backend_result(
                                BinaryMachineReplayStatus::NeedsMachineReplay,
                                result,
                                expected_artifact_digest,
                                matched_artifact_digest,
                                expected_selected_image,
                                matched_selected_image,
                                expected_instruction_trace,
                                true,
                                reason,
                            );
                        }
                    if let Some(diagnostic) = machine_byte_range_attestation_diagnostic(
                        expected_selected_image.as_ref(),
                        &result,
                        witness.provenance.requires_selected_image_identity,
                        config,
                    ) {
                        let status = byte_range_diagnostic_status(&diagnostic);
                        let reason = diagnostic.diagnostic.clone();
                        return BinaryMachineReplayReport::from_backend_result(
                            status,
                            result,
                            expected_artifact_digest,
                            matched_artifact_digest,
                            expected_selected_image,
                            matched_selected_image,
                            expected_instruction_trace,
                            true,
                            reason,
                        )
                        .ensure_byte_range_diagnostic(diagnostic);
                    }
                    if let Some(reason) = unchecked_control_flow_boundary_reason(&boundary_evidence)
                    {
                        return BinaryMachineReplayReport::from_backend_result(
                            BinaryMachineReplayStatus::Unsupported,
                            result,
                            expected_artifact_digest,
                            matched_artifact_digest,
                            expected_selected_image,
                            matched_selected_image,
                            expected_instruction_trace,
                            true,
                            reason,
                        )
                        .with_boundary_evidence(boundary_evidence);
                    }
                    if let Some(reason) = missing_control_flow_capability_evidence_reason(&result) {
                        return BinaryMachineReplayReport::from_backend_result(
                            BinaryMachineReplayStatus::NeedsMachineReplay,
                            result,
                            expected_artifact_digest,
                            matched_artifact_digest,
                            expected_selected_image,
                            matched_selected_image,
                            expected_instruction_trace,
                            true,
                            reason,
                        );
                    }
                    let effect_diagnostic = machine_effect_evidence_diagnostic_from_parts(
                        &result.instruction_trace,
                        &result.effect_evidence,
                        &result.effect_diagnostics,
                    );
                    if witness.provenance.requires_selected_image_identity
                        && let Some(diagnostic) = effect_diagnostic.clone() {
                            let status = effect_diagnostic_status(&diagnostic);
                            let reason = diagnostic.diagnostic.clone();
                            return BinaryMachineReplayReport::from_backend_result(
                                status,
                                result,
                                expected_artifact_digest,
                                matched_artifact_digest,
                                expected_selected_image,
                                matched_selected_image,
                                expected_instruction_trace,
                                true,
                                reason,
                            )
                            .ensure_effect_diagnostic(diagnostic);
                        }
                    BinaryMachineReplayReport::from_backend_result(
                        BinaryMachineReplayStatus::Replayed,
                        result,
                        expected_artifact_digest,
                        matched_artifact_digest,
                        expected_selected_image,
                        matched_selected_image,
                        expected_instruction_trace,
                        true,
                        "machine-code replay evidence matched normalized witness instruction provenance, root artifact digest, selected-image identity, and explicit backend control-flow capability evidence",
                    )
                    .with_matched_capability_evidence(true)
                    .with_matched_effect_evidence(effect_diagnostic.is_none())
                }
                MachineInstructionTraceValidation::MissingExpectedBytes { address } => {
                    BinaryMachineReplayReport::from_backend_result(
                        BinaryMachineReplayStatus::NeedsMachineReplay,
                        result,
                        expected_artifact_digest,
                        false,
                        expected_selected_image,
                        false,
                        expected_instruction_trace,
                        false,
                        format!(
                            "normalized witness provenance for 0x{address:x} omitted original instruction bytes; exact normalized instruction-byte provenance is required before machine replay can satisfy proof-grade evidence"
                        ),
                    )
                }
                MachineInstructionTraceValidation::MissingObservedBytes { address } => {
                    BinaryMachineReplayReport::from_backend_result(
                        BinaryMachineReplayStatus::NeedsMachineReplay,
                        result,
                        expected_artifact_digest,
                        false,
                        expected_selected_image,
                        false,
                        expected_instruction_trace,
                        false,
                        format!(
                            "machine-code replay evidence for 0x{address:x} omitted exact observed instruction bytes; exact observed instruction bytes are required before replay can satisfy proof-grade evidence"
                        ),
                    )
                }
                MachineInstructionTraceValidation::Mismatched => {
                    BinaryMachineReplayReport::from_backend_result(
                        BinaryMachineReplayStatus::Spurious,
                        result,
                        expected_artifact_digest,
                        false,
                        expected_selected_image,
                        false,
                        expected_instruction_trace,
                        false,
                        "machine-code replay instruction trace did not match normalized witness provenance",
                    )
                }
            }
        }
        BinaryMachineReplayStatus::Spurious => {
            let reason = result.reason.clone();
            BinaryMachineReplayReport::from_backend_result(
                BinaryMachineReplayStatus::Spurious,
                result,
                expected_artifact_digest,
                false,
                expected_selected_image,
                false,
                expected_instruction_trace,
                false,
                reason,
            )
            .with_boundary_evidence(boundary_evidence)
        }
        BinaryMachineReplayStatus::NeedsMachineReplay => {
            let reason = result.reason.clone();
            BinaryMachineReplayReport::from_backend_result(
                BinaryMachineReplayStatus::NeedsMachineReplay,
                result,
                expected_artifact_digest,
                false,
                expected_selected_image,
                false,
                expected_instruction_trace,
                false,
                reason,
            )
            .with_boundary_evidence(boundary_evidence)
        }
        BinaryMachineReplayStatus::Unsupported => {
            let reason = result.reason.clone();
            BinaryMachineReplayReport::from_backend_result(
                BinaryMachineReplayStatus::Unsupported,
                result,
                expected_artifact_digest,
                false,
                expected_selected_image,
                false,
                expected_instruction_trace,
                false,
                reason,
            )
            .with_boundary_evidence(boundary_evidence)
        }
        BinaryMachineReplayStatus::Failed => {
            let reason = result.reason.clone();
            BinaryMachineReplayReport::from_backend_result(
                BinaryMachineReplayStatus::Failed,
                result,
                expected_artifact_digest,
                false,
                expected_selected_image,
                false,
                expected_instruction_trace,
                false,
                reason,
            )
            .with_boundary_evidence(boundary_evidence)
        }
    }
}

fn machine_model_trace_binding_reason(witness: &BinaryWitness) -> Option<String> {
    if !witness.has_execution_trace {
        return Some(
            "model-to-witness reconstruction missing: normalized SAT witness has no execution trace, so replayed machine bytes cannot be bound back to the solver model"
                .into(),
        );
    }
    if witness.trace.is_empty() {
        return Some(
            "model-to-witness reconstruction missing: normalized SAT witness execution trace is empty, so replayed machine bytes cannot be bound back to the solver model"
                .into(),
        );
    }

    for step in &witness.trace {
        if step.program_point.as_ref().and_then(|point| point.origin.as_ref()).is_none() {
            return Some(format!(
                "model-to-witness reconstruction missing: trace step {} lacks instruction provenance, so replayed machine bytes cannot be bound back to the solver model",
                step.step
            ));
        }
    }

    let model_records = witness
        .records
        .iter()
        .filter(|record| record.source == BinaryWitnessRecordSource::ModelAssignment)
        .collect::<Vec<_>>();
    if model_records.is_empty() {
        return Some(
            "model-to-witness reconstruction missing: normalized SAT witness has no top-level model assignments to bind into the replay trace"
                .into(),
        );
    }

    let trace_records = witness
        .records
        .iter()
        .filter(|record| record.source == BinaryWitnessRecordSource::TraceAssignment)
        .collect::<Vec<_>>();
    if trace_records.is_empty() {
        return Some(
            "model-to-witness reconstruction missing: execution trace contains no per-step model assignment bindings, so SAT cannot be promoted by replayed bytes alone"
                .into(),
        );
    }

    let explicit_bindings = match validated_explicit_model_trace_bindings(witness, &model_records) {
        Ok(bindings) => bindings,
        Err(reason) => return Some(reason),
    };

    for model_record in model_records {
        if explicit_bindings.contains(model_record.raw_name.as_str()) {
            continue;
        }
        if trace_records.iter().any(|trace_record| {
            trace_record.raw_name == model_record.raw_name
                && witness_values_equivalent(&model_record.value, &trace_record.value)
        }) {
            continue;
        }
        if trace_records.iter().any(|trace_record| trace_record.raw_name == model_record.raw_name) {
            return Some(format!(
                "model-to-witness reconstruction missing: model assignment `{}` appears in the instruction trace but no trace value matches the top-level model value, so SAT cannot be promoted by replayed bytes alone",
                model_record.raw_name
            ));
        }
        let ssa_candidates = ssa_renamed_trace_candidates(&model_record.raw_name, &trace_records);
        if !ssa_candidates.is_empty() {
            return Some(format!(
                "model-to-witness reconstruction missing: model assignment `{}` appears to be SSA-renamed in the instruction trace as `{}` but no explicit binding_map entry connects them, so SAT cannot be promoted by replayed bytes alone",
                model_record.raw_name,
                ssa_candidates.join("`, `")
            ));
        }
        return Some(format!(
            "model-to-witness reconstruction missing: model assignment `{}` is not bound to any instruction trace step, so SAT cannot be promoted by replayed bytes alone",
            model_record.raw_name
        ));
    }

    None
}

fn validated_explicit_model_trace_bindings(
    witness: &BinaryWitness,
    model_records: &[&BinaryWitnessRecord],
) -> Result<BTreeSet<String>, String> {
    let model_by_name = model_records
        .iter()
        .map(|record| (record.raw_name.as_str(), *record))
        .collect::<BTreeMap<_, _>>();
    let mut bound_model_names = BTreeSet::new();

    for binding in &witness.provenance.binding_map {
        let Some(model_record) = model_by_name.get(binding.model_name.as_str()) else {
            return Err(format!(
                "model-to-witness reconstruction missing: binding_map references unknown model assignment `{}`, so replayed machine bytes cannot be bound back to the solver model",
                binding.model_name
            ));
        };
        let Some((trace_step, trace_record)) = trace_binding_record(witness, binding) else {
            return Err(format!(
                "model-to-witness reconstruction missing: binding_map maps model assignment `{}` to trace assignment `{}`{} but that trace assignment was not present",
                binding.model_name,
                binding.trace_name,
                binding.trace_step.map(|step| format!(" at trace step {step}")).unwrap_or_default()
            ));
        };
        if !witness_values_equivalent(&model_record.value, &trace_record.value) {
            return Err(format!(
                "model-to-witness reconstruction missing: binding_map maps model assignment `{}` to trace assignment `{}` at trace step {trace_step}, but their values differ",
                binding.model_name, binding.trace_name
            ));
        }
        bound_model_names.insert(model_record.raw_name.clone());
    }

    Ok(bound_model_names)
}

fn trace_binding_record<'a>(
    witness: &'a BinaryWitness,
    binding: &BinaryWitnessBinding,
) -> Option<(u32, &'a BinaryWitnessRecord)> {
    witness.trace.iter().find_map(|step| {
        if binding.trace_step.is_some_and(|binding_step| binding_step != step.step) {
            return None;
        }
        step.assignments
            .iter()
            .find(|record| record.raw_name == binding.trace_name)
            .map(|record| (step.step, record))
    })
}

fn witness_values_equivalent(lhs: &BinaryWitnessValue, rhs: &BinaryWitnessValue) -> bool {
    match (&lhs.typed, &rhs.typed) {
        (Some(lhs), Some(rhs)) => counterexample_values_equivalent(lhs, rhs),
        _ => lhs.raw.trim() == rhs.raw.trim(),
    }
}

fn counterexample_values_equivalent(lhs: &CounterexampleValue, rhs: &CounterexampleValue) -> bool {
    match (lhs, rhs) {
        (CounterexampleValue::Bool(lhs), CounterexampleValue::Bool(rhs)) => lhs == rhs,
        (CounterexampleValue::Int(lhs), CounterexampleValue::Int(rhs)) => lhs == rhs,
        (CounterexampleValue::Uint(lhs), CounterexampleValue::Uint(rhs)) => lhs == rhs,
        (CounterexampleValue::Int(lhs), CounterexampleValue::Uint(rhs)) => {
            u128::try_from(*lhs).ok() == Some(*rhs)
        }
        (CounterexampleValue::Uint(lhs), CounterexampleValue::Int(rhs)) => {
            u128::try_from(*rhs).ok() == Some(*lhs)
        }
        (CounterexampleValue::Float(lhs), CounterexampleValue::Float(rhs)) => lhs == rhs,
        _ => false,
    }
}

fn ssa_renamed_trace_candidates(
    model_name: &str,
    trace_records: &[&BinaryWitnessRecord],
) -> Vec<String> {
    let mut candidates = trace_records
        .iter()
        .filter(|&record| is_ssa_renamed_binding(model_name, &record.raw_name)).map(|record| record.raw_name.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    candidates.truncate(3);
    candidates
}

fn is_ssa_renamed_binding(model_name: &str, trace_name: &str) -> bool {
    let model_name = trim_smt_symbol_quotes(model_name.trim());
    let trace_name = trim_smt_symbol_quotes(trace_name.trim());
    if model_name.is_empty() || trace_name == model_name {
        return false;
    }
    let Some(suffix) = trace_name.strip_prefix(model_name) else {
        return false;
    };
    matches!(suffix.as_bytes().first(), Some(b'!') | Some(b'@') | Some(b'#') | Some(b'$'))
        || suffix.starts_with(".ssa")
}

fn trim_smt_symbol_quotes(name: &str) -> &str {
    name.strip_prefix('|').and_then(|name| name.strip_suffix('|')).unwrap_or(name)
}

fn dispatch_replay_requirement(dispatch: &SolverDispatchRecord) -> BinaryReplayRequirement {
    if dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
        && dispatch.status == SolverDispatchStatus::Sat
    {
        return BinaryReplayRequirement::ExactMachineWitnessReplay;
    }

    if dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
        && matches!(&dispatch.result, Some(VerificationResult::Failed { .. }))
    {
        return BinaryReplayRequirement::ExactMachineWitnessReplay;
    }

    if dispatch.status == SolverDispatchStatus::Unsat
        || matches!(&dispatch.result, Some(VerificationResult::Proved { .. }))
    {
        return BinaryReplayRequirement::CheckedUnsatCertificate;
    }

    BinaryReplayRequirement::UnknownUnsupportedState
}

fn dispatch_requirement_satisfied_without_witness(
    dispatch: &SolverDispatchRecord,
    requirement: BinaryReplayRequirement,
) -> bool {
    match requirement {
        BinaryReplayRequirement::CheckedUnsatCertificate => dispatch.certificate.is_checked(),
        BinaryReplayRequirement::ExactMachineWitnessReplay
        | BinaryReplayRequirement::UnknownUnsupportedState => false,
    }
}

fn dispatch_requirement_satisfied_by_report(
    requirement: BinaryReplayRequirement,
    report: &BinaryReplayReport,
) -> bool {
    match requirement {
        BinaryReplayRequirement::ExactMachineWitnessReplay => {
            report.trust_types_status == ReplayStatus::Replayed
                && !report.needs_machine_replay
                && report.machine_replay.source_backprop_replay_ready()
        }
        BinaryReplayRequirement::CheckedUnsatCertificate
        | BinaryReplayRequirement::UnknownUnsupportedState => false,
    }
}

fn no_witness_requirement_reason(
    base_reason: String,
    requirement: BinaryReplayRequirement,
    requirement_satisfied: bool,
) -> String {
    match requirement {
        BinaryReplayRequirement::CheckedUnsatCertificate if requirement_satisfied => {
            format!(
                "{base_reason}; checked proof certificate satisfies UNSAT certificate requirement"
            )
        }
        BinaryReplayRequirement::CheckedUnsatCertificate => {
            format!("{base_reason}; checked proof certificate is required for proved UNSAT VC")
        }
        BinaryReplayRequirement::ExactMachineWitnessReplay => {
            format!("{base_reason}; exact machine witness replay is required for SAT witness")
        }
        BinaryReplayRequirement::UnknownUnsupportedState => {
            format!("{base_reason}; dispatch state is unsupported for binary release evidence")
        }
    }
}

fn dispatch_counterexample(dispatch: &SolverDispatchRecord) -> Option<Counterexample> {
    if dispatch.query_semantics != SolverQuerySemantics::SatIsCounterexample {
        return None;
    }
    if dispatch.status != SolverDispatchStatus::Sat {
        return None;
    }
    match &dispatch.result {
        Some(VerificationResult::Failed { counterexample: Some(counterexample), .. }) => {
            Some(counterexample.clone())
        }
        _ => None,
    }
}

fn dispatch_no_witness_reason(dispatch: &SolverDispatchRecord) -> String {
    match (&dispatch.status, &dispatch.result, dispatch.query_semantics) {
        (SolverDispatchStatus::Unsat, _, SolverQuerySemantics::SatIsCounterexample)
        | (_, Some(VerificationResult::Proved { .. }), _) => {
            "UNSAT/proved dispatch has no counterexample witness".into()
        }
        (SolverDispatchStatus::Sat, _, semantics)
            if semantics != SolverQuerySemantics::SatIsCounterexample =>
        {
            format!(
                "SAT dispatch uses {semantics:?} semantics; refusing to treat it as an exploit witness"
            )
        }
        (
            SolverDispatchStatus::Sat,
            Some(VerificationResult::Failed { counterexample: None, .. }),
            _,
        ) => "SAT dispatch did not include a structured counterexample model".into(),
        (SolverDispatchStatus::Sat, None, _) => {
            "SAT dispatch did not include a solver result with a structured counterexample model"
                .into()
        }
        (status, _, _) => format!("dispatch status {status:?} does not carry a binary witness"),
    }
}

fn binary_origin_from_dispatch(dispatch: &SolverDispatchRecord) -> BinaryOrigin {
    let origin = dispatch.origin.as_ref();
    BinaryOrigin {
        image: origin.and_then(|origin| origin.binary_path.clone()),
        architecture: None,
        function: dispatch.function.clone(),
        entry: origin.and_then(|origin| origin.function_entry.or(Some(origin.instruction_address))),
    }
}

fn expected_machine_instruction_trace(witness: &BinaryWitness) -> Vec<TrustBinaryOrigin> {
    witness
        .trace
        .iter()
        .filter_map(|step| step.program_point.as_ref())
        .filter_map(|program_point| program_point.origin.clone())
        .collect()
}

fn expected_machine_instruction_steps(
    witness: &BinaryWitness,
) -> Vec<(&TrustBinaryOrigin, &BinaryWitnessTraceStep)> {
    witness
        .trace
        .iter()
        .filter_map(|step| {
            step.program_point
                .as_ref()
                .and_then(|program_point| program_point.origin.as_ref())
                .map(|origin| (origin, step))
        })
        .collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MachineInstructionTraceValidation {
    Matched,
    MissingExpectedBytes { address: u64 },
    MissingObservedBytes { address: u64 },
    Mismatched,
}

fn machine_instruction_trace_validation(
    expected: &[TrustBinaryOrigin],
    result: &BinaryMachineReplayResult,
    config: &BinaryMachineReplayConfig,
) -> MachineInstructionTraceValidation {
    let observed =
        result.instruction_trace.iter().map(|instruction| &instruction.origin).collect::<Vec<_>>();
    if config.require_exact_instruction_trace {
        if observed.len() != expected.len() {
            return MachineInstructionTraceValidation::Mismatched;
        }

        let mut missing_expected_bytes = None;
        let mut missing_observed_bytes = None;
        for (observed, expected) in observed.iter().zip(expected) {
            match validate_machine_instruction_origin(observed, expected) {
                MachineInstructionTraceValidation::Matched => {}
                MachineInstructionTraceValidation::MissingExpectedBytes { address } => {
                    missing_expected_bytes.get_or_insert(address);
                }
                MachineInstructionTraceValidation::MissingObservedBytes { address } => {
                    missing_observed_bytes.get_or_insert(address);
                }
                MachineInstructionTraceValidation::Mismatched => {
                    return MachineInstructionTraceValidation::Mismatched;
                }
            }
        }

        if let Some(address) = missing_expected_bytes {
            MachineInstructionTraceValidation::MissingExpectedBytes { address }
        } else {
            missing_observed_bytes.map_or(MachineInstructionTraceValidation::Matched, |address| {
                MachineInstructionTraceValidation::MissingObservedBytes { address }
            })
        }
    } else {
        let mut missing_expected_bytes = None;
        let mut missing_observed_bytes = None;
        for expected in expected {
            if expected.instruction_bytes.is_empty() {
                missing_expected_bytes.get_or_insert(expected.instruction_address);
                continue;
            }
            let mut matching_origin_without_bytes = None;
            let mut matched = false;
            for observed in &observed {
                match validate_machine_instruction_origin(observed, expected) {
                    MachineInstructionTraceValidation::Matched => {
                        matched = true;
                        break;
                    }
                    MachineInstructionTraceValidation::MissingExpectedBytes { address } => {
                        missing_expected_bytes.get_or_insert(address);
                    }
                    MachineInstructionTraceValidation::MissingObservedBytes { address } => {
                        matching_origin_without_bytes.get_or_insert(address);
                    }
                    MachineInstructionTraceValidation::Mismatched => {}
                }
            }

            if matched {
                continue;
            }
            if let Some(address) = matching_origin_without_bytes {
                missing_observed_bytes.get_or_insert(address);
            } else {
                return MachineInstructionTraceValidation::Mismatched;
            }
        }

        if let Some(address) = missing_expected_bytes {
            MachineInstructionTraceValidation::MissingExpectedBytes { address }
        } else {
            missing_observed_bytes.map_or(MachineInstructionTraceValidation::Matched, |address| {
                MachineInstructionTraceValidation::MissingObservedBytes { address }
            })
        }
    }
}

fn validate_machine_instruction_origin(
    observed: &TrustBinaryOrigin,
    expected: &TrustBinaryOrigin,
) -> MachineInstructionTraceValidation {
    if observed.instruction_address != expected.instruction_address
        || observed.function_entry != expected.function_entry
        || !origins_have_compatible_paths(observed, expected)
        || !optional_origin_field_matches(observed.instruction_size, expected.instruction_size)
        || !optional_origin_field_matches(observed.encoding, expected.encoding)
    {
        return MachineInstructionTraceValidation::Mismatched;
    }

    if expected.instruction_bytes.is_empty() {
        return MachineInstructionTraceValidation::MissingExpectedBytes {
            address: expected.instruction_address,
        };
    }

    if observed.instruction_bytes.is_empty() {
        return MachineInstructionTraceValidation::MissingObservedBytes {
            address: observed.instruction_address,
        };
    }

    if observed.instruction_bytes != expected.instruction_bytes {
        return MachineInstructionTraceValidation::Mismatched;
    }

    MachineInstructionTraceValidation::Matched
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MachineArtifactDigestValidation {
    Matched,
    NotRequired,
    MissingExpected,
    MissingObserved,
    InvalidExpected,
    InvalidObserved,
    Mismatched,
}

impl MachineArtifactDigestValidation {
    fn allows_replay(self) -> bool {
        matches!(self, Self::Matched | Self::NotRequired)
    }

    fn fail_closed_reason(self) -> Option<&'static str> {
        match self {
            Self::Matched | Self::NotRequired => None,
            Self::MissingExpected => Some(
                "normalized witness omitted root binary artifact digest; exact binary artifact digest identity is required before machine replay can satisfy proof-grade evidence",
            ),
            Self::MissingObserved => Some(
                "machine-code replay evidence omitted root binary artifact digest; exact binary artifact digest identity is required before replay can satisfy proof-grade evidence",
            ),
            Self::InvalidExpected => Some(
                "normalized witness root binary artifact digest is not canonical SHA-256; exact binary artifact digest identity is required before machine replay can satisfy proof-grade evidence",
            ),
            Self::InvalidObserved => Some(
                "machine-code replay evidence root binary artifact digest is not canonical SHA-256; exact binary artifact digest identity is required before replay can satisfy proof-grade evidence",
            ),
            Self::Mismatched => Some(
                "machine-code replay artifact digest did not match normalized witness artifact digest",
            ),
        }
    }
}

fn machine_artifact_digest_validation(
    expected: Option<&BinaryArtifactDigest>,
    observed: Option<&BinaryArtifactDigest>,
    config: &BinaryMachineReplayConfig,
) -> MachineArtifactDigestValidation {
    if !config.require_exact_artifact_digest {
        return MachineArtifactDigestValidation::NotRequired;
    }

    let Some(expected) = expected else {
        return MachineArtifactDigestValidation::MissingExpected;
    };
    let Some(observed) = observed else {
        return MachineArtifactDigestValidation::MissingObserved;
    };

    if !expected.is_canonical_sha256() {
        return MachineArtifactDigestValidation::InvalidExpected;
    }
    if !observed.is_canonical_sha256() {
        return MachineArtifactDigestValidation::InvalidObserved;
    }
    if expected == observed {
        MachineArtifactDigestValidation::Matched
    } else {
        MachineArtifactDigestValidation::Mismatched
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MachineSelectedImageValidation {
    Matched,
    NotRequired,
    MissingExpected,
    MissingObserved,
    InvalidExpected,
    InvalidObserved,
    Mismatched,
}

impl MachineSelectedImageValidation {
    fn allows_replay(self) -> bool {
        matches!(self, Self::Matched | Self::NotRequired)
    }

    fn fail_closed_reason(self) -> Option<&'static str> {
        match self {
            Self::Matched | Self::NotRequired => None,
            Self::MissingExpected => Some(
                "normalized witness selected-image digest/range is absent or ambiguous; exact selected-image identity from the solver dispatch is required before machine replay can satisfy proof-grade evidence",
            ),
            Self::MissingObserved => Some(
                "machine-code replay evidence omitted selected-image digest/range; exact selected-image identity for the replayed bytes is required before replay can satisfy proof-grade evidence",
            ),
            Self::InvalidExpected => Some(
                "normalized witness selected-image digest/range is not canonical; exact selected-image identity from the solver dispatch is required before machine replay can satisfy proof-grade evidence",
            ),
            Self::InvalidObserved => Some(
                "machine-code replay evidence selected-image digest/range is not canonical; exact selected-image identity for the replayed bytes is required before replay can satisfy proof-grade evidence",
            ),
            Self::Mismatched => Some(
                "machine-code replay selected-image digest/range did not match normalized witness selected-image identity",
            ),
        }
    }

    fn byte_range_diagnostic(
        self,
        expected: Option<&BinarySelectedImageIdentity>,
        observed: Option<&BinarySelectedImageIdentity>,
    ) -> Option<BinaryMachineReplayByteRangeDiagnostic> {
        if self != Self::Mismatched {
            return None;
        }
        let (Some(expected), Some(observed)) = (expected, observed) else {
            return None;
        };
        let ranges_match = expected.file_offset == observed.file_offset
            && expected.file_size == observed.file_size;
        if ranges_match {
            return Some(BinaryMachineReplayByteRangeDiagnostic::new(
                BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageDigestMismatch,
                "machine-code replay selected-image digest/range did not match normalized witness selected-image identity: selected-image digest did not match",
            ));
        }
        Some(BinaryMachineReplayByteRangeDiagnostic::new(
            BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageByteRangeMismatch,
            format!(
                "machine-code replay selected-image digest/range did not match normalized witness selected-image identity: selected-image byte range did not match normalized witness range: expected [0x{:x}..0x{:x}), observed [0x{:x}..0x{:x})",
                expected.file_offset,
                expected.end_offset().unwrap_or(expected.file_offset),
                observed.file_offset,
                observed.end_offset().unwrap_or(observed.file_offset)
            ),
        ))
    }
}

fn machine_selected_image_validation(
    expected: Option<&BinarySelectedImageIdentity>,
    observed: Option<&BinarySelectedImageIdentity>,
    required: bool,
    config: &BinaryMachineReplayConfig,
) -> MachineSelectedImageValidation {
    if !config.require_exact_artifact_digest {
        return MachineSelectedImageValidation::NotRequired;
    }
    if !required && (expected.is_none() || observed.is_none()) {
        return MachineSelectedImageValidation::NotRequired;
    }

    let Some(expected) = expected else {
        return MachineSelectedImageValidation::MissingExpected;
    };
    let Some(observed) = observed else {
        return MachineSelectedImageValidation::MissingObserved;
    };

    if !selected_image_identity_is_replay_grade(expected) {
        return MachineSelectedImageValidation::InvalidExpected;
    }
    if !selected_image_identity_is_replay_grade(observed) {
        return MachineSelectedImageValidation::InvalidObserved;
    }
    if expected == observed {
        MachineSelectedImageValidation::Matched
    } else {
        MachineSelectedImageValidation::Mismatched
    }
}

fn selected_image_identity_is_replay_grade(selected: &BinarySelectedImageIdentity) -> bool {
    selected.file_size != 0 && selected.is_canonical_sha256() && selected.end_offset().is_some()
}

fn machine_byte_range_attestation_diagnostic(
    expected_selected_image: Option<&BinarySelectedImageIdentity>,
    result: &BinaryMachineReplayResult,
    required: bool,
    config: &BinaryMachineReplayConfig,
) -> Option<BinaryMachineReplayByteRangeDiagnostic> {
    if !config.require_exact_artifact_digest {
        return None;
    }
    if let Some(diagnostic) = result.byte_range_diagnostics.first() {
        return Some(diagnostic.clone());
    }
    let selected_image = expected_selected_image?;
    result.selected_image.as_ref()?;
    let selected_end = selected_image.end_offset()?;

    if result.byte_range_evidence.is_empty() && !required {
        return None;
    }

    for instruction in &result.instruction_trace {
        let address = instruction.origin.instruction_address;
        let step = if required {
            let Some(step) = instruction.step else {
                return Some(
                    BinaryMachineReplayByteRangeDiagnostic::new(
                        BinaryMachineReplayByteRangeDiagnosticKind::MissingOriginalByteRangeAttestation,
                        format!(
                            "machine-code replay evidence for 0x{address:x} omitted machine trace step binding for original byte/range attestation"
                        ),
                    )
                    .with_instruction(address, None),
                );
            };
            Some(step)
        } else {
            instruction.step
        };
        let Some(evidence) = result
            .byte_range_evidence
            .iter()
            .find(|evidence| evidence.instruction_address == address && evidence.step == step)
        else {
            return Some(
                BinaryMachineReplayByteRangeDiagnostic::new(
                    BinaryMachineReplayByteRangeDiagnosticKind::MissingOriginalByteRangeAttestation,
                    format!(
                        "machine-code replay evidence for 0x{address:x} omitted original byte/range attestation bound to the replayed machine step for the selected image"
                    ),
                )
                .with_instruction(address, step),
            );
        };

        if evidence.size != instruction.origin.instruction_bytes.len() as u64
            || evidence.instruction_bytes != instruction.origin.instruction_bytes
        {
            return Some(
                BinaryMachineReplayByteRangeDiagnostic::new(
                    BinaryMachineReplayByteRangeDiagnosticKind::MismatchedOriginalByteRangeAttestation,
                    format!(
                        "machine-code replay original byte/range attestation for 0x{address:x} did not match replayed instruction bytes"
                    ),
                )
                .with_instruction(address, step)
                .with_file_range(evidence.file_offset, evidence.size),
            );
        }

        let Some(evidence_end) = evidence.end_offset() else {
            return Some(
                BinaryMachineReplayByteRangeDiagnostic::new(
                    BinaryMachineReplayByteRangeDiagnosticKind::MismatchedOriginalByteRangeAttestation,
                    format!(
                        "machine-code replay original byte/range attestation for 0x{address:x} overflows root artifact offsets"
                    ),
                )
                .with_instruction(address, step)
                .with_file_range(evidence.file_offset, evidence.size),
            );
        };
        if evidence.file_offset < selected_image.file_offset || evidence_end > selected_end {
            return Some(
                BinaryMachineReplayByteRangeDiagnostic::new(
                    BinaryMachineReplayByteRangeDiagnosticKind::OriginalByteRangeOutsideSelectedImage,
                    format!(
                        "machine-code replay original byte/range attestation for 0x{address:x} covers [0x{:x}..0x{:x}), outside selected-image byte range [0x{:x}..0x{:x})",
                        evidence.file_offset,
                        evidence_end,
                        selected_image.file_offset,
                        selected_end
                    ),
                )
                .with_instruction(address, step)
                .with_file_range(evidence.file_offset, evidence.size),
            );
        }
    }
    None
}

fn machine_attestation_slices_from_report(
    report: &BinaryMachineReplayReport,
) -> Vec<BinaryMachineReplayAttestationSlice> {
    report
        .observed_instruction_trace
        .iter()
        .map(|instruction| machine_attestation_slice_from_report(report, instruction))
        .collect()
}

fn machine_attestation_slice_from_report(
    report: &BinaryMachineReplayReport,
    instruction: &BinaryMachineInstructionEvidence,
) -> BinaryMachineReplayAttestationSlice {
    let address = instruction.origin.instruction_address;
    let selected_image =
        report.observed_selected_image.clone().or_else(|| report.expected_selected_image.clone());
    let byte_range = matching_byte_range_evidence(report, instruction).cloned();
    let mut effect_identities = Vec::new();

    if let Some(boundary) =
        report.boundary_evidence.iter().find(|boundary| boundary.instruction_address == address)
    {
        return BinaryMachineReplayAttestationSlice::rejected(
            instruction,
            selected_image,
            byte_range,
            effect_identities,
            boundary_reason_from_evidence(boundary),
        );
    }

    if let Some(diagnostic) = instruction_trace_attestation_diagnostic(report, instruction) {
        return BinaryMachineReplayAttestationSlice::rejected(
            instruction,
            selected_image,
            byte_range,
            effect_identities,
            diagnostic,
        );
    }

    let selected_image = match exact_slice_selected_image(report, address) {
        Ok(selected_image) => selected_image,
        Err(diagnostic) => {
            return BinaryMachineReplayAttestationSlice::rejected(
                instruction,
                selected_image,
                byte_range,
                effect_identities,
                diagnostic,
            );
        }
    };

    if instruction.origin.instruction_bytes.is_empty() {
        return BinaryMachineReplayAttestationSlice::rejected(
            instruction,
            Some(selected_image),
            byte_range,
            effect_identities,
            format!(
                "source-backprop attestation slice for instruction 0x{address:x} omitted original instruction bytes"
            ),
        );
    }

    let Some(step) = instruction.step else {
        return BinaryMachineReplayAttestationSlice::rejected(
            instruction,
            Some(selected_image),
            byte_range,
            effect_identities,
            format!(
                "source-backprop attestation slice for instruction 0x{address:x} omitted machine trace step binding"
            ),
        );
    };

    let byte_range = match byte_range {
        Some(byte_range) => byte_range,
        None => {
            return BinaryMachineReplayAttestationSlice::rejected(
                instruction,
                Some(selected_image),
                None,
                effect_identities,
                format!(
                    "source-backprop attestation slice for instruction 0x{address:x} at machine trace step {step} omitted original byte/range attestation"
                ),
            );
        }
    };

    if let Some(diagnostic) =
        byte_range_slice_attestation_diagnostic(instruction, &byte_range, &selected_image)
    {
        return BinaryMachineReplayAttestationSlice::rejected(
            instruction,
            Some(selected_image),
            Some(byte_range),
            effect_identities,
            diagnostic,
        );
    }

    if let Some(diagnostic) = report.effect_diagnostics.iter().find(|diagnostic| {
        diagnostic.instruction_address == Some(address)
            && (diagnostic.step == instruction.step || diagnostic.step.is_none())
    }) {
        return BinaryMachineReplayAttestationSlice::rejected(
            instruction,
            Some(selected_image),
            Some(byte_range),
            effect_identities,
            diagnostic.diagnostic.clone(),
        );
    }

    for required in required_effect_witnesses(instruction) {
        match required {
            RequiredEffectWitness::Evidence(required) => {
                let Some(evidence) = report
                    .effect_evidence
                    .iter()
                    .find(|evidence| effect_evidence_matches(evidence, &required))
                else {
                    let diagnostic = missing_effect_witness_diagnostic(&required);
                    return BinaryMachineReplayAttestationSlice::rejected(
                        instruction,
                        Some(selected_image),
                        Some(byte_range),
                        effect_identities,
                        diagnostic.diagnostic,
                    );
                };
                effect_identities.push(BinaryMachineReplayEffectIdentity::from_evidence(evidence));
            }
            RequiredEffectWitness::Diagnostic(diagnostic) => {
                return BinaryMachineReplayAttestationSlice::rejected(
                    instruction,
                    Some(selected_image),
                    Some(byte_range),
                    effect_identities,
                    diagnostic.diagnostic,
                );
            }
        }
    }

    BinaryMachineReplayAttestationSlice::accepted(
        instruction,
        selected_image,
        byte_range,
        effect_identities,
    )
}

fn matching_byte_range_evidence<'a>(
    report: &'a BinaryMachineReplayReport,
    instruction: &BinaryMachineInstructionEvidence,
) -> Option<&'a BinaryMachineReplayByteRangeEvidence> {
    let address = instruction.origin.instruction_address;
    report.byte_range_evidence.iter().find(|evidence| {
        evidence.instruction_address == address && evidence.step == instruction.step
    })
}

fn instruction_trace_attestation_diagnostic(
    report: &BinaryMachineReplayReport,
    instruction: &BinaryMachineInstructionEvidence,
) -> Option<String> {
    if report.matched_instruction_trace {
        return None;
    }

    let address = instruction.origin.instruction_address;
    let Some(expected) = report
        .expected_instruction_trace
        .iter()
        .find(|expected| expected.instruction_address == address)
    else {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} did not match normalized witness instruction address identity"
        ));
    };

    if expected.instruction_bytes.is_empty() {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} cannot be accepted because normalized witness omitted original instruction bytes"
        ));
    }
    if instruction.origin.instruction_bytes.is_empty() {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} cannot be accepted because machine replay omitted observed instruction bytes"
        ));
    }
    if expected.instruction_bytes != instruction.origin.instruction_bytes {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: instruction bytes did not match normalized witness original bytes"
        ));
    }
    if expected.instruction_size != instruction.origin.instruction_size {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: instruction size did not match normalized witness"
        ));
    }
    if expected.encoding != instruction.origin.encoding {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: instruction encoding did not match normalized witness"
        ));
    }

    Some(format!(
        "source-backprop attestation slice for instruction 0x{address:x} rejected: instruction trace identity did not match normalized witness"
    ))
}

fn exact_slice_selected_image(
    report: &BinaryMachineReplayReport,
    instruction_address: u64,
) -> Result<BinarySelectedImageIdentity, String> {
    let Some(expected) = report.expected_selected_image.as_ref() else {
        return Err(format!(
            "source-backprop attestation slice for instruction 0x{instruction_address:x} omitted expected selected-image digest/range identity"
        ));
    };
    let Some(observed) = report.observed_selected_image.as_ref() else {
        return Err(format!(
            "source-backprop attestation slice for instruction 0x{instruction_address:x} omitted observed selected-image digest/range identity"
        ));
    };
    if !selected_image_identity_is_replay_grade(expected) {
        return Err(format!(
            "source-backprop attestation slice for instruction 0x{instruction_address:x} has non-canonical expected selected-image digest/range identity"
        ));
    }
    if !selected_image_identity_is_replay_grade(observed) {
        return Err(format!(
            "source-backprop attestation slice for instruction 0x{instruction_address:x} has non-canonical observed selected-image digest/range identity"
        ));
    }
    if expected != observed {
        return Err(format!(
            "source-backprop attestation slice for instruction 0x{instruction_address:x} rejected: selected-image digest/range did not match normalized witness"
        ));
    }
    Ok(observed.clone())
}

fn byte_range_slice_attestation_diagnostic(
    instruction: &BinaryMachineInstructionEvidence,
    byte_range: &BinaryMachineReplayByteRangeEvidence,
    selected_image: &BinarySelectedImageIdentity,
) -> Option<String> {
    let address = instruction.origin.instruction_address;
    if byte_range.size != instruction.origin.instruction_bytes.len() as u64
        || byte_range.instruction_bytes != instruction.origin.instruction_bytes
    {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: original byte/range attestation did not match replayed instruction bytes"
        ));
    }
    let Some(range_end) = byte_range.end_offset() else {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: original byte/range attestation overflows root artifact offsets"
        ));
    };
    let Some(selected_end) = selected_image.end_offset() else {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: selected-image byte range overflows root artifact offsets"
        ));
    };
    if byte_range.file_offset < selected_image.file_offset || range_end > selected_end {
        return Some(format!(
            "source-backprop attestation slice for instruction 0x{address:x} rejected: original byte/range attestation lies outside selected-image byte range"
        ));
    }
    None
}

fn accepted_attestation_slice_blocker_reason(
    slice: &BinaryMachineReplayAttestationSlice,
    instruction: &BinaryMachineInstructionEvidence,
) -> Option<String> {
    let address = instruction.origin.instruction_address;
    if slice.instruction_bytes.is_empty() {
        return Some(format!(
            "source-backprop accepted attestation slice for instruction 0x{address:x} dropped original instruction bytes required for source-backprop readiness"
        ));
    }
    if slice.instruction_bytes != instruction.origin.instruction_bytes {
        return Some(format!(
            "source-backprop accepted attestation slice for instruction 0x{address:x} no longer matches replayed original instruction bytes"
        ));
    }
    let Some(selected_image) = slice.selected_image.as_ref() else {
        return Some(format!(
            "source-backprop accepted attestation slice for instruction 0x{address:x} dropped selected-image binding required for source-backprop readiness"
        ));
    };
    let Some(byte_range) = slice.byte_range.as_ref() else {
        return Some(format!(
            "source-backprop accepted attestation slice for instruction 0x{address:x} dropped original byte/range binding required for source-backprop readiness; minimized replay witnesses must retain byte-range bindings"
        ));
    };
    if byte_range.instruction_address != address || byte_range.step != instruction.step {
        return Some(format!(
            "source-backprop accepted attestation slice for instruction 0x{address:x} no longer binds byte/range evidence to the replayed machine step"
        ));
    }
    if let Some(diagnostic) =
        byte_range_slice_attestation_diagnostic(instruction, byte_range, selected_image)
    {
        return Some(diagnostic);
    }

    for required in required_effect_witnesses(instruction) {
        match required {
            RequiredEffectWitness::Evidence(required) => {
                if !slice
                    .effect_identities
                    .iter()
                    .any(|identity| effect_identity_matches_required(identity, &required))
                {
                    return Some(missing_attestation_effect_identity_reason(&required));
                }
            }
            RequiredEffectWitness::Diagnostic(diagnostic) => {
                return Some(format!("source-backprop blocked: {}", diagnostic.diagnostic));
            }
        }
    }
    None
}

fn effect_identity_matches_required(
    identity: &BinaryMachineReplayEffectIdentity,
    required: &RequiredEffectEvidence,
) -> bool {
    identity.kind == required.kind
        && identity.architecture == required.architecture
        && identity.instruction_address == required.instruction_address
        && identity.step == required.step
        && required
            .subject
            .as_ref()
            .is_none_or(|subject| identity.subject.as_ref() == Some(subject))
        && effect_identity_memory_access_matches(identity, required)
}

fn effect_identity_memory_access_matches(
    identity: &BinaryMachineReplayEffectIdentity,
    required: &RequiredEffectEvidence,
) -> bool {
    match required.memory_access {
        Some(required_memory_access) => identity.memory_access.is_some_and(|memory_access| {
            memory_access.width_bytes == required_memory_access.width_bytes
                && memory_access.end_address().is_some()
        }),
        None => identity.memory_access.is_none(),
    }
}

fn missing_attestation_effect_identity_reason(required: &RequiredEffectEvidence) -> String {
    let step = required
        .step
        .map(|step| format!(" at machine trace step {step}"))
        .unwrap_or_else(|| " without a machine trace step".to_owned());
    let subject =
        required.subject.as_ref().map(|subject| format!(" for {subject}")).unwrap_or_default();
    let memory_access = required
        .memory_access
        .map(|memory_access| {
            format!(
                " with concrete scalar memory address and {}-byte width",
                memory_access.width_bytes
            )
        })
        .unwrap_or_default();
    format!(
        "source-backprop accepted attestation slice for instruction 0x{:x}{step} dropped {} effect identity{subject}{memory_access}; minimized replay witnesses must retain machine-effect bindings required for source-backprop readiness",
        required.instruction_address, required.kind
    )
}

fn byte_range_diagnostic_status(
    diagnostic: &BinaryMachineReplayByteRangeDiagnostic,
) -> BinaryMachineReplayStatus {
    match diagnostic.kind {
        BinaryMachineReplayByteRangeDiagnosticKind::MissingOriginalByteRangeAttestation => {
            BinaryMachineReplayStatus::NeedsMachineReplay
        }
        BinaryMachineReplayByteRangeDiagnosticKind::MismatchedOriginalByteRangeAttestation
        | BinaryMachineReplayByteRangeDiagnosticKind::OriginalByteRangeOutsideSelectedImage
        | BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageByteRangeMismatch
        | BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageDigestMismatch => {
            BinaryMachineReplayStatus::Spurious
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RequiredEffectEvidence {
    kind: BinaryMachineReplayEffectKind,
    architecture: &'static str,
    instruction_address: u64,
    step: Option<u32>,
    subject: Option<String>,
    memory_access: Option<RequiredScalarMemoryAccessEvidence>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct RequiredScalarMemoryAccessEvidence {
    width_bytes: u32,
}

enum RequiredEffectWitness {
    Evidence(RequiredEffectEvidence),
    Diagnostic(BinaryMachineReplayEffectDiagnostic),
}

fn machine_effect_evidence_diagnostic_from_parts(
    instruction_trace: &[BinaryMachineInstructionEvidence],
    effect_evidence: &[BinaryMachineReplayEffectEvidence],
    effect_diagnostics: &[BinaryMachineReplayEffectDiagnostic],
) -> Option<BinaryMachineReplayEffectDiagnostic> {
    if let Some(diagnostic) = effect_diagnostics.first() {
        return Some(diagnostic.clone());
    }

    instruction_trace.iter().find_map(|instruction| {
        required_effect_witnesses(instruction).into_iter().find_map(|required| match required {
            RequiredEffectWitness::Evidence(required) => {
                if effect_evidence
                    .iter()
                    .any(|evidence| effect_evidence_matches(evidence, &required))
                {
                    None
                } else {
                    Some(missing_effect_witness_diagnostic(&required))
                }
            }
            RequiredEffectWitness::Diagnostic(diagnostic) => Some(diagnostic),
        })
    })
}

fn machine_effect_evidence_blocker_reason_from_parts(
    instruction_trace: &[BinaryMachineInstructionEvidence],
    effect_evidence: &[BinaryMachineReplayEffectEvidence],
    effect_diagnostics: &[BinaryMachineReplayEffectDiagnostic],
) -> Option<String> {
    machine_effect_evidence_diagnostic_from_parts(
        instruction_trace,
        effect_evidence,
        effect_diagnostics,
    )
    .map(|diagnostic| diagnostic.diagnostic)
}

fn effect_evidence_matches(
    evidence: &BinaryMachineReplayEffectEvidence,
    required: &RequiredEffectEvidence,
) -> bool {
    evidence.kind == required.kind
        && evidence.architecture == required.architecture
        && evidence.instruction_address == required.instruction_address
        && evidence.step == required.step
        && required
            .subject
            .as_ref()
            .is_none_or(|subject| evidence.subject.as_ref() == Some(subject))
        && effect_memory_access_matches(evidence, required)
        && !evidence.validation.is_empty()
}

fn effect_memory_access_matches(
    evidence: &BinaryMachineReplayEffectEvidence,
    required: &RequiredEffectEvidence,
) -> bool {
    match required.memory_access {
        Some(required_memory_access) => evidence.memory_access.is_some_and(|memory_access| {
            memory_access.width_bytes == required_memory_access.width_bytes
                && memory_access.end_address().is_some()
        }),
        None => evidence.memory_access.is_none(),
    }
}

fn missing_effect_witness_diagnostic(
    required: &RequiredEffectEvidence,
) -> BinaryMachineReplayEffectDiagnostic {
    let step = required
        .step
        .map(|step| format!(" at machine trace step {step}"))
        .unwrap_or_else(|| " without a machine trace step".to_owned());
    let subject =
        required.subject.as_ref().map(|subject| format!(" for {subject}")).unwrap_or_default();
    let memory_access = required
        .memory_access
        .map(|memory_access| {
            format!(
                " with concrete scalar memory address and {}-byte width",
                memory_access.width_bytes
            )
        })
        .unwrap_or_default();
    BinaryMachineReplayEffectDiagnostic::new(
        BinaryMachineReplayEffectDiagnosticKind::MissingMachineEffectWitness,
        format!(
            "machine-code replay backend omitted {} effect witness{}{} for instruction 0x{:x}{} on {}; proof-grade source backprop requires machine-effect witnesses consumed for every replayed instruction step",
            required.kind,
            subject,
            memory_access,
            required.instruction_address,
            step,
            required.architecture
        ),
    )
    .with_effect_kind(required.kind)
    .with_instruction(required.instruction_address, required.step)
}

fn effect_diagnostic_status(
    diagnostic: &BinaryMachineReplayEffectDiagnostic,
) -> BinaryMachineReplayStatus {
    match diagnostic.kind {
        BinaryMachineReplayEffectDiagnosticKind::MissingMachineEffectWitness => {
            BinaryMachineReplayStatus::NeedsMachineReplay
        }
        BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass => {
            BinaryMachineReplayStatus::Unsupported
        }
    }
}

fn required_effect_witnesses(
    evidence: &BinaryMachineInstructionEvidence,
) -> Vec<RequiredEffectWitness> {
    let Some((architecture, instruction)) = decode_exact_instruction_origin(&evidence.origin)
    else {
        return vec![RequiredEffectWitness::Diagnostic(
            BinaryMachineReplayEffectDiagnostic::new(
                BinaryMachineReplayEffectDiagnosticKind::MissingMachineEffectWitness,
                format!(
                    "machine-code replay cannot derive machine-effect witnesses for instruction 0x{:x}: exact decoded instruction semantics are unavailable",
                    evidence.origin.instruction_address
                ),
            )
            .with_instruction(evidence.origin.instruction_address, evidence.step),
        )];
    };
    let effects = match exact_instruction_effects(architecture, &instruction) {
        Ok(effects) => effects,
        Err(reason) => {
            return vec![RequiredEffectWitness::Diagnostic(
                BinaryMachineReplayEffectDiagnostic::new(
                    BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass,
                    format!(
                        "machine-code replay cannot proof-consume machine effects for {} instruction 0x{:x}: {reason}; exact effect witness semantics are required for source backprop",
                        architecture, instruction.address
                    ),
                )
                .with_instruction(instruction.address, evidence.step),
            )];
        }
    };

    if effects.is_empty() {
        return vec![RequiredEffectWitness::Evidence(RequiredEffectEvidence {
            kind: BinaryMachineReplayEffectKind::NoStateChange,
            architecture,
            instruction_address: instruction.address,
            step: evidence.step,
            subject: Some("instruction".to_owned()),
            memory_access: None,
        })];
    }

    let mut required = Vec::new();
    let mut seen = BTreeSet::new();
    let mut scalar_memory_effect_index = 0usize;
    for effect in &effects {
        let memory_index = next_scalar_memory_effect_index(effect, &mut scalar_memory_effect_index);
        if let Some(diagnostic) =
            unsupported_effect_witness_diagnostic(architecture, &instruction, evidence.step, effect)
        {
            required.push(RequiredEffectWitness::Diagnostic(diagnostic));
            continue;
        }
        let Some(requirement) = required_effect_evidence_from_effect(
            architecture,
            instruction.address,
            evidence.step,
            effect,
            memory_index,
        ) else {
            continue;
        };
        let key = (
            requirement.kind,
            requirement.architecture,
            requirement.instruction_address,
            requirement.step,
            requirement.subject.clone(),
            requirement.memory_access,
        );
        if seen.insert(key) {
            required.push(RequiredEffectWitness::Evidence(requirement));
        }
    }

    if required.is_empty() {
        required.push(RequiredEffectWitness::Evidence(RequiredEffectEvidence {
            kind: BinaryMachineReplayEffectKind::NoStateChange,
            architecture,
            instruction_address: instruction.address,
            step: evidence.step,
            subject: Some("instruction".to_owned()),
            memory_access: None,
        }));
    }
    required
}

fn exact_instruction_effects(
    architecture: &'static str,
    instruction: &Instruction,
) -> Result<Vec<Effect>, String> {
    let state = MachineState::symbolic();
    match architecture {
        "AArch64" => Aarch64Semantics
            .effects(&state, instruction)
            .map_err(|err| format!("AArch64 semantics unavailable: {err}")),
        "x86_64" => X86_64Semantics
            .effects(&state, instruction)
            .map_err(|err| format!("x86_64 semantics unavailable: {err}")),
        _ => Err(format!("{architecture} semantics unavailable")),
    }
}

fn required_effect_evidence_from_effect(
    architecture: &'static str,
    instruction_address: u64,
    step: Option<u32>,
    effect: &Effect,
    scalar_memory_effect_index: Option<usize>,
) -> Option<RequiredEffectEvidence> {
    let (kind, subject, memory_access) = match effect {
        Effect::RegWrite { index, width, .. } => (
            BinaryMachineReplayEffectKind::RegisterWrite,
            Some(format!("GPR{index}:{width}")),
            None,
        ),
        Effect::SpWrite { .. } => {
            (BinaryMachineReplayEffectKind::StackPointerWrite, Some("SP".to_owned()), None)
        }
        Effect::MemRead { width_bytes, .. } => {
            let memory_access = RequiredScalarMemoryAccessEvidence { width_bytes: *width_bytes };
            (
                BinaryMachineReplayEffectKind::MemoryRead,
                scalar_memory_effect_subject(scalar_memory_effect_index, *width_bytes),
                Some(memory_access),
            )
        }
        Effect::MemWrite { width_bytes, .. } => {
            let memory_access = RequiredScalarMemoryAccessEvidence { width_bytes: *width_bytes };
            (
                BinaryMachineReplayEffectKind::MemoryWrite,
                scalar_memory_effect_subject(scalar_memory_effect_index, *width_bytes),
                Some(memory_access),
            )
        }
        Effect::FlagUpdate { .. } => {
            (BinaryMachineReplayEffectKind::FlagUpdate, Some("NZCV".to_owned()), None)
        }
        Effect::PcUpdate { .. } => {
            (BinaryMachineReplayEffectKind::ProgramCounterUpdate, Some("PC".to_owned()), None)
        }
        Effect::Branch { .. }
        | Effect::ConditionalBranch { .. }
        | Effect::Call { .. }
        | Effect::Return { .. } => {
            (BinaryMachineReplayEffectKind::ControlFlow, Some("PC".to_owned()), None)
        }
        Effect::FpRegWrite { .. }
        | Effect::Aarch64SyncBoundary { .. }
        | Effect::Aarch64AtomicAccess { .. } => return None,
        _ => return None,
    };
    Some(RequiredEffectEvidence {
        kind,
        architecture,
        instruction_address,
        step,
        subject,
        memory_access,
    })
}

fn scalar_memory_effect_subject(index: Option<usize>, width_bytes: u32) -> Option<String> {
    index.map(|index| format!("memory_access#{index}:{width_bytes}B"))
}

fn unsupported_effect_witness_diagnostic(
    architecture: &'static str,
    instruction: &Instruction,
    step: Option<u32>,
    effect: &Effect,
) -> Option<BinaryMachineReplayEffectDiagnostic> {
    let (kind, missing_witnesses) = match effect {
        Effect::FpRegWrite { .. } => (
            BinaryMachineReplayEffectKind::FloatingPointRegisterWrite,
            "FP/SIMD local layout, IEEE-754 value semantics, FPCR/FPSR state, rounding mode and exception flags",
        ),
        Effect::Aarch64SyncBoundary { .. } => (
            BinaryMachineReplayEffectKind::Aarch64SyncBoundary,
            "barrier ordering event, shareability scope propagation, memory-system visibility/completion, happens-before witness",
        ),
        Effect::Aarch64AtomicAccess { .. } => (
            BinaryMachineReplayEffectKind::Aarch64AtomicAccess,
            "atomic ordering event, synchronization edge, monitor/thread identity, happens-before witness",
        ),
        _ => return None,
    };
    let step_text = step.map(|step| format!(" at machine trace step {step}")).unwrap_or_default();
    Some(
        BinaryMachineReplayEffectDiagnostic::new(
            BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass,
            format!(
                "machine-code replay reached unsupported machine-effect witness class {kind} for {} instruction 0x{:x}{}: {effect:?}; missing_witnesses={missing_witnesses}; exact effect witness semantics are not represented, so proof-grade source backprop must fail closed",
                architecture, instruction.address, step_text
            ),
        )
        .with_effect_kind(kind)
        .with_instruction(instruction.address, step),
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RequiredCapabilityEvidence {
    capability: BinaryMachineReplayCapability,
    architecture: &'static str,
    instruction_address: u64,
    step: Option<u32>,
    instruction_bytes: Vec<u8>,
}

fn missing_control_flow_capability_evidence_reason(
    result: &BinaryMachineReplayResult,
) -> Option<String> {
    missing_control_flow_capability_evidence_reason_from_parts(
        &result.instruction_trace,
        &result.capability_evidence,
    )
}

fn missing_control_flow_capability_evidence_reason_from_parts(
    instruction_trace: &[BinaryMachineInstructionEvidence],
    capability_evidence: &[BinaryMachineReplayCapabilityEvidence],
) -> Option<String> {
    instruction_trace
        .iter()
        .filter_map(required_capability_evidence)
        .find(|required| {
            !capability_evidence.iter().any(|evidence| {
                evidence.capability == required.capability
                    && evidence.architecture == required.architecture
                    && evidence.instruction_address == required.instruction_address
                    && evidence.step == required.step
                    && evidence.instruction_bytes == required.instruction_bytes
                    && !evidence.validation.is_empty()
            })
        })
        .map(|required| {
            let step = required
                .step
                .map(|step| format!(" at backend step {step}"))
                .unwrap_or_default();
            format!(
                "machine-code replay backend omitted explicit capability evidence for validated {} control flow at 0x{:x}{} on {}; proof-grade replay requires structured backend capability evidence for branch/call/return validation",
                required.capability,
                required.instruction_address,
                step,
                required.architecture
            )
        })
}

fn required_capability_evidence(
    evidence: &BinaryMachineInstructionEvidence,
) -> Option<RequiredCapabilityEvidence> {
    let (architecture, instruction) = decode_exact_instruction_origin(&evidence.origin)?;
    let capability = instruction_capability(instruction.flow, &instruction)?;
    Some(RequiredCapabilityEvidence {
        capability,
        architecture,
        instruction_address: instruction.address,
        step: evidence.step,
        instruction_bytes: instruction.bytes,
    })
}

fn decode_exact_instruction_origin(
    origin: &TrustBinaryOrigin,
) -> Option<(&'static str, Instruction)> {
    let bytes = origin.instruction_bytes.as_slice();
    if bytes.len() == 4
        && let Some(instruction) =
            decode_exact_instruction(bytes, origin.instruction_address, decode_aarch64)
        {
            return Some(("AArch64", instruction));
        }
    if !bytes.is_empty()
        && let Some(instruction) =
            decode_exact_instruction(bytes, origin.instruction_address, decode_x86_64)
        {
            return Some(("x86_64", instruction));
        }
    if origin.instruction_bytes.is_empty() && origin.instruction_size == Some(4)
        && let Some(encoding) = origin.encoding
            && let Some(instruction) = decode_exact_instruction(
                &encoding.to_le_bytes(),
                origin.instruction_address,
                decode_aarch64,
            ) {
                return Some(("AArch64", instruction));
            }
    None
}

fn decode_exact_instruction(
    bytes: &[u8],
    address: u64,
    decode: fn(&[u8], u64) -> Result<Instruction, trust_disasm::DisasmError>,
) -> Option<Instruction> {
    let instruction = decode(bytes, address).ok()?;
    if instruction.bytes == bytes { Some(instruction) } else { None }
}

fn instruction_capability(
    flow: ControlFlow,
    instruction: &Instruction,
) -> Option<BinaryMachineReplayCapability> {
    match flow {
        ControlFlow::ConditionalBranch => Some(BinaryMachineReplayCapability::ConditionalBranch),
        ControlFlow::Branch if instruction.branch_target().is_some() => {
            Some(BinaryMachineReplayCapability::DirectBranch)
        }
        ControlFlow::Branch => Some(BinaryMachineReplayCapability::IndirectBranch),
        ControlFlow::Call if instruction.branch_target().is_some() => {
            Some(BinaryMachineReplayCapability::DirectCall)
        }
        ControlFlow::Call => Some(BinaryMachineReplayCapability::IndirectCall),
        ControlFlow::Return => Some(BinaryMachineReplayCapability::Return),
        ControlFlow::Fallthrough | ControlFlow::Exception => None,
        _ => None,
    }
}

fn unchecked_control_flow_boundary_reason(
    boundary_evidence: &[BinaryMachineReplayBoundaryEvidence],
) -> Option<String> {
    boundary_evidence.first().map(boundary_reason_from_evidence)
}

fn replay_boundary_evidence(
    expected: &[TrustBinaryOrigin],
    result: &BinaryMachineReplayResult,
) -> Vec<BinaryMachineReplayBoundaryEvidence> {
    let mut evidence = result
        .instruction_trace
        .iter()
        .filter_map(|instruction| {
            decoded_boundary_diagnostic(&instruction.origin, instruction.step)
                .map(BinaryMachineReplayBoundaryEvidence::from)
        })
        .collect::<Vec<_>>();
    if !evidence.is_empty() {
        return evidence;
    }

    evidence.extend(expected.iter().enumerate().filter_map(|(idx, origin)| {
        decoded_boundary_diagnostic(origin, u32::try_from(idx).ok())
            .map(BinaryMachineReplayBoundaryEvidence::from)
    }));
    evidence
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundaryDiagnostic {
    kind: BinaryMachineReplayBoundaryKind,
    architecture: &'static str,
    address: u64,
    step: Option<u32>,
    opcode: String,
    flow: ControlFlow,
    encoding: u32,
    bytes: Vec<u8>,
    immediate: Option<u64>,
}

impl From<BoundaryDiagnostic> for BinaryMachineReplayBoundaryEvidence {
    fn from(diagnostic: BoundaryDiagnostic) -> Self {
        let diagnostic_text = boundary_reason_from_diagnostic(&diagnostic);
        Self {
            kind: diagnostic.kind,
            architecture: diagnostic.architecture.to_owned(),
            instruction_address: diagnostic.address,
            step: diagnostic.step,
            instruction_bytes: diagnostic.bytes,
            opcode: diagnostic.opcode,
            encoding: diagnostic.encoding,
            immediate: diagnostic.immediate,
            semantics: BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness,
            diagnostic: diagnostic_text,
        }
    }
}

fn decoded_boundary_diagnostic(
    origin: &TrustBinaryOrigin,
    step: Option<u32>,
) -> Option<BoundaryDiagnostic> {
    let bytes = origin.instruction_bytes.as_slice();
    if bytes.len() == 4
        && let Some(diagnostic) = decode_exact_boundary(
            "AArch64",
            bytes,
            origin.instruction_address,
            step,
            decode_aarch64,
        ) {
            return Some(diagnostic);
        }
    if !bytes.is_empty()
        && let Some(diagnostic) =
            decode_exact_boundary("x86_64", bytes, origin.instruction_address, step, decode_x86_64)
        {
            return Some(diagnostic);
        }
    if origin.instruction_bytes.is_empty() && origin.instruction_size == Some(4)
        && let Some(encoding) = origin.encoding {
            return decode_exact_boundary(
                "AArch64",
                &encoding.to_le_bytes(),
                origin.instruction_address,
                step,
                decode_aarch64,
            );
        }
    None
}

fn boundary_diagnostic_from_instruction(
    architecture: &'static str,
    instruction: &Instruction,
    step: Option<u32>,
) -> Option<BoundaryDiagnostic> {
    let kind = boundary_kind(architecture, instruction)?;
    Some(BoundaryDiagnostic {
        kind,
        architecture,
        address: instruction.address,
        step,
        opcode: instruction.opcode.to_string(),
        flow: instruction.flow,
        encoding: instruction.encoding,
        bytes: instruction.bytes.clone(),
        immediate: instruction.operand(0).and_then(|operand| match operand {
            DisasmOperand::Imm(value) => Some(*value),
            _ => None,
        }),
    })
}

fn boundary_kind(
    architecture: &str,
    instruction: &Instruction,
) -> Option<BinaryMachineReplayBoundaryKind> {
    let opcode = instruction.opcode.to_string().to_ascii_uppercase();
    match architecture {
        "AArch64" => match opcode.as_str() {
            "SVC" => Some(BinaryMachineReplayBoundaryKind::Syscall),
            "HVC" | "SMC" => Some(BinaryMachineReplayBoundaryKind::Exception),
            "BRK" | "HLT" => Some(BinaryMachineReplayBoundaryKind::Trap),
            _ => None,
        },
        "x86_64" => match opcode.as_str() {
            "SYSCALL" | "SYSENTER" => Some(BinaryMachineReplayBoundaryKind::Syscall),
            "INT3" => Some(BinaryMachineReplayBoundaryKind::Trap),
            "INT" => Some(BinaryMachineReplayBoundaryKind::Exception),
            _ => None,
        },
        _ => None,
    }
}

fn decode_exact_boundary(
    architecture: &'static str,
    bytes: &[u8],
    address: u64,
    step: Option<u32>,
    decode: fn(&[u8], u64) -> Result<Instruction, trust_disasm::DisasmError>,
) -> Option<BoundaryDiagnostic> {
    let instruction = decode(bytes, address).ok()?;
    if instruction.bytes != bytes {
        return None;
    }
    boundary_diagnostic_from_instruction(architecture, &instruction, step)
}

fn boundary_reason_from_evidence(evidence: &BinaryMachineReplayBoundaryEvidence) -> String {
    let step = evidence.step.map(|step| format!(", step {step}")).unwrap_or_default();
    let immediate = evidence.immediate.map(|imm| format!(", immediate #{imm}")).unwrap_or_default();
    format!(
        "machine-code replay instruction trace reached unchecked {} {} boundary at 0x{:x}: {} (encoding 0x{:x}, bytes [{}]{}{}); exact boundary witness semantics are not represented ({}) so this replay cannot satisfy proof-grade evidence",
        evidence.architecture,
        evidence.kind,
        evidence.instruction_address,
        evidence.opcode,
        evidence.encoding,
        hex_bytes(&evidence.instruction_bytes),
        immediate,
        step,
        evidence.semantics
    )
}

fn boundary_reason_from_diagnostic(diagnostic: &BoundaryDiagnostic) -> String {
    let step = diagnostic.step.map(|step| format!(", step {step}")).unwrap_or_default();
    format!(
        "machine-code replay instruction trace reached unchecked {} {} boundary at 0x{:x}: {} (flow {:?}, encoding 0x{:x}, bytes [{}]{}{}); exact boundary witness semantics are not represented ({}) so this replay cannot satisfy proof-grade evidence",
        diagnostic.architecture,
        diagnostic.kind,
        diagnostic.address,
        diagnostic.opcode,
        diagnostic.flow,
        diagnostic.encoding,
        hex_bytes(&diagnostic.bytes),
        diagnostic.immediate.map(|imm| format!(", immediate #{imm}")).unwrap_or_default(),
        step,
        BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness
    )
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect::<Vec<_>>().join(" ")
}

fn origins_have_compatible_paths(
    observed: &TrustBinaryOrigin,
    expected: &TrustBinaryOrigin,
) -> bool {
    match (&observed.binary_path, &expected.binary_path) {
        (Some(observed), Some(expected)) => observed == expected,
        _ => true,
    }
}

fn optional_origin_field_matches<T: PartialEq>(observed: Option<T>, expected: Option<T>) -> bool {
    expected.is_none() || observed == expected
}

struct WitnessNormalizationContext<'a> {
    function: Option<&'a str>,
    origin: Option<TrustBinaryOrigin>,
    artifact_digest: Option<BinaryArtifactDigest>,
    selected_image: Option<BinarySelectedImageIdentity>,
    verification_context: Option<BinaryWitnessVerificationContext>,
    requires_selected_image_identity: bool,
    instruction_provenance: &'a [TrustBinaryOrigin],
    locals: &'a [trust_types::LocalDecl],
}

fn normalize_counterexample_witness(
    input: &BinaryReplayInput,
    context: &WitnessNormalizationContext<'_>,
) -> BinaryWitness {
    let trace_steps = input.counterexample.trace.as_ref().map_or(0, |trace| trace.steps.len());
    let mut witness = BinaryWitness {
        function: context.function.map(ToOwned::to_owned),
        origin: context.origin.clone(),
        records: Vec::new(),
        trace: Vec::new(),
        raw_model_assignments: input.counterexample.assignments.len(),
        raw_trace_steps: trace_steps,
        has_execution_trace: input.counterexample.trace.is_some(),
        provenance: BinaryWitnessProvenance {
            function: context.function.map(ToOwned::to_owned),
            origin: context.origin.clone(),
            artifact_digest: context.artifact_digest.clone(),
            selected_image: context.selected_image.clone(),
            verification_context: context.verification_context.clone(),
            requires_selected_image_identity: context.requires_selected_image_identity,
            model_assignment_names: input
                .counterexample
                .assignments
                .iter()
                .map(|(name, _)| name.clone())
                .collect(),
            trace_program_points: input
                .counterexample
                .trace
                .as_ref()
                .map_or_else(Vec::new, |trace| {
                    trace.steps.iter().map(|step| step.program_point.clone()).collect()
                }),
            trace_instruction_origins: Vec::new(),
            binding_map: input.binding_map.clone(),
        },
    };

    for (name, value) in &input.counterexample.assignments {
        witness.records.push(normalize_witness_record(
            name,
            BinaryWitnessValue::typed(value),
            BinaryWitnessRecordSource::ModelAssignment,
            None,
            context,
        ));
    }

    if let Some(trace) = &input.counterexample.trace {
        for step in &trace.steps {
            let program_point =
                step.program_point.as_ref().map(|label| normalize_program_point(label, context));
            let assignments = step
                .assignments
                .iter()
                .map(|(name, value)| {
                    normalize_witness_record(
                        name,
                        BinaryWitnessValue::raw(value),
                        BinaryWitnessRecordSource::TraceAssignment,
                        program_point.clone(),
                        context,
                    )
                })
                .collect::<Vec<_>>();
            witness.records.extend(assignments.iter().cloned());
            if let Some(origin) = program_point.as_ref().and_then(|point| point.origin.clone()) {
                witness.provenance.trace_instruction_origins.push(origin);
            }
            witness.trace.push(BinaryWitnessTraceStep {
                step: step.step,
                program_point,
                assignments,
            });
        }
    }

    witness
}

fn normalize_witness_record(
    name: &str,
    value: BinaryWitnessValue,
    source: BinaryWitnessRecordSource,
    program_point: Option<BinaryWitnessProgramPoint>,
    context: &WitnessNormalizationContext<'_>,
) -> BinaryWitnessRecord {
    let classification = classify_witness_name(name, context);
    BinaryWitnessRecord {
        source,
        raw_name: name.to_owned(),
        value,
        subject: classification.subject,
        storage: classification.storage,
        function: context.function.map(ToOwned::to_owned),
        local_index: classification.local_index,
        program_point,
    }
}

struct WitnessNameClassification {
    subject: BinaryFactSubject,
    storage: BinaryStorageLocation,
    local_index: Option<usize>,
}

fn classify_witness_name(
    name: &str,
    context: &WitnessNormalizationContext<'_>,
) -> WitnessNameClassification {
    if let Some(register) = parse_prefixed_register_name(name) {
        return register_classification(register, None, context, None);
    }

    if let Some(memory) = parse_memory_name(name) {
        return memory;
    }

    if let Some(stack) = parse_stack_name(name) {
        return stack;
    }

    if let Some(index) = parse_local_index(name) {
        if let Some(local) = context.locals.iter().find(|local| local.index == index) {
            return local_classification(local, context);
        }
        return WitnessNameClassification {
            subject: BinaryFactSubject::Local {
                function: function_label(context),
                name: format!("_local{index}"),
            },
            storage: BinaryStorageLocation::Unknown,
            local_index: Some(index),
        };
    }

    if let Some(local) = context
        .locals
        .iter()
        .find(|local| local.name.as_deref().is_some_and(|local_name| local_name == name))
    {
        return local_classification(local, context);
    }

    if let Some(register) = parse_register_name(name) {
        return register_classification(register, None, context, None);
    }

    if let Some(global) = parse_global_name(name) {
        return global;
    }

    WitnessNameClassification {
        subject: BinaryFactSubject::Unknown,
        storage: BinaryStorageLocation::Unknown,
        local_index: None,
    }
}

fn local_classification(
    local: &trust_types::LocalDecl,
    context: &WitnessNormalizationContext<'_>,
) -> WitnessNameClassification {
    let local_name = local.name.as_deref().unwrap_or("");
    if let Some(register) = parse_register_name(local_name) {
        return register_classification(
            register,
            ty_bit_width(&local.ty),
            context,
            Some(local.index),
        );
    }

    if is_memory_state_name(local_name) {
        return WitnessNameClassification {
            subject: BinaryFactSubject::Memory { name: Some(local_name.to_owned()), address: None },
            storage: BinaryStorageLocation::Unknown,
            local_index: Some(local.index),
        };
    }

    WitnessNameClassification {
        subject: BinaryFactSubject::Local {
            function: function_label(context),
            name: if local_name.is_empty() {
                format!("_local{}", local.index)
            } else {
                local_name.to_owned()
            },
        },
        storage: BinaryStorageLocation::Unknown,
        local_index: Some(local.index),
    }
}

fn register_classification(
    register: String,
    bit_width: Option<u32>,
    context: &WitnessNormalizationContext<'_>,
    local_index: Option<usize>,
) -> WitnessNameClassification {
    WitnessNameClassification {
        subject: BinaryFactSubject::Register {
            function: function_label(context),
            register: register.clone(),
        },
        storage: BinaryStorageLocation::Register { name: register, bit_width },
        local_index,
    }
}

fn parse_memory_name(name: &str) -> Option<WitnessNameClassification> {
    let trimmed = name.trim();
    if is_memory_state_name(trimmed) {
        return Some(WitnessNameClassification {
            subject: BinaryFactSubject::Memory { name: Some(trimmed.to_owned()), address: None },
            storage: BinaryStorageLocation::Unknown,
            local_index: None,
        });
    }

    let body = if let Some(body) = trimmed.strip_prefix("mem[") {
        body.strip_suffix(']')?
    } else if let Some(body) = trimmed.strip_prefix("memory[") {
        body.strip_suffix(']')?
    } else if let Some(body) = trimmed.strip_prefix('[') {
        body.strip_suffix(']')?
    } else if let Some(body) = trimmed.strip_prefix("mem:") {
        body
    } else { trimmed.strip_prefix("memory:")? };

    let (address_text, size_bytes) =
        body.split_once(':').map_or((body, None), |(addr, size)| (addr, parse_u32_literal(size)));
    let address = parse_u64_literal(address_text.trim())?;
    Some(WitnessNameClassification {
        subject: BinaryFactSubject::Memory { name: None, address: Some(address) },
        storage: BinaryStorageLocation::Memory {
            address: Formula::UInt(u128::from(address)),
            size_bytes,
        },
        local_index: None,
    })
}

fn parse_stack_name(name: &str) -> Option<WitnessNameClassification> {
    let trimmed = name.trim();
    let body = if let Some(body) = trimmed.strip_prefix("stack:") {
        body
    } else if let Some(body) = trimmed.strip_prefix("stack[") {
        body.strip_suffix(']')?
    } else {
        return None;
    };
    let (base_offset, size_bytes) = body.rsplit_once(':')?;
    let size_bytes = parse_u32_literal(size_bytes.trim())?;
    let (base, offset) = parse_stack_base_offset(base_offset.trim())?;
    Some(WitnessNameClassification {
        subject: BinaryFactSubject::Memory { name: Some(trimmed.to_owned()), address: None },
        storage: BinaryStorageLocation::Stack { base, offset, size_bytes: Some(size_bytes) },
        local_index: None,
    })
}

fn parse_stack_base_offset(value: &str) -> Option<(BinaryStackBase, i64)> {
    let compact = value.chars().filter(|ch| !ch.is_whitespace()).collect::<String>();
    let lower = compact.to_ascii_lowercase();
    for (label, base) in [
        ("rsp", BinaryStackBase::StackPointer),
        ("sp", BinaryStackBase::StackPointer),
        ("rbp", BinaryStackBase::FramePointer),
        ("fp", BinaryStackBase::FramePointer),
        ("cfa", BinaryStackBase::CanonicalFrameAddress),
    ] {
        if lower == label {
            return Some((base, 0));
        }
        if let Some(offset) = lower.strip_prefix(label)
            && offset.starts_with(['+', '-']) {
                return Some((base, parse_i64_literal(offset)?));
            }
    }
    None
}

fn parse_global_name(name: &str) -> Option<WitnessNameClassification> {
    let trimmed = name.trim();
    let body = trimmed.strip_prefix("global:").or_else(|| trimmed.strip_prefix("global["))?;
    let body = body.strip_suffix(']').unwrap_or(body);
    let address = parse_u64_literal(body);
    Some(WitnessNameClassification {
        subject: BinaryFactSubject::Memory {
            name: address.is_none().then(|| body.to_owned()),
            address,
        },
        storage: BinaryStorageLocation::Global {
            name: address.is_none().then(|| body.to_owned()),
            address,
            size_bytes: None,
        },
        local_index: None,
    })
}

fn normalize_program_point(
    program_point: &str,
    context: &WitnessNormalizationContext<'_>,
) -> BinaryWitnessProgramPoint {
    let parsed = parse_program_point(program_point);
    BinaryWitnessProgramPoint {
        raw: program_point.to_owned(),
        block: parsed.block,
        origin: parsed
            .address
            .map(|address| trust_origin_for_instruction(address, context))
            .or_else(|| context.origin.clone()),
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ParsedProgramPoint {
    block: Option<usize>,
    address: Option<u64>,
}

fn parse_program_point(program_point: &str) -> ParsedProgramPoint {
    ParsedProgramPoint {
        block: parse_block_program_point(program_point),
        address: parse_address_from_program_point(program_point),
    }
}

fn lifted_function_origin(function: &VerifiableFunction) -> Option<TrustBinaryOrigin> {
    let address = function.span.binary_address_value()?;
    Some(TrustBinaryOrigin {
        binary_path: None,
        function_entry: Some(address),
        instruction_address: address,
        instruction_size: None,
        encoding: None,
        instruction_bytes: vec![],
        source: Some(function.span.clone()),
    })
}

fn trust_origin_from_binary_origin(origin: &BinaryOrigin) -> Option<TrustBinaryOrigin> {
    let entry = origin.entry?;
    Some(TrustBinaryOrigin {
        binary_path: origin.image.clone(),
        function_entry: Some(entry),
        instruction_address: entry,
        instruction_size: None,
        encoding: None,
        instruction_bytes: vec![],
        source: Some(SourceSpan::binary_address(entry)),
    })
}

fn trust_origin_for_instruction(
    address: u64,
    context: &WitnessNormalizationContext<'_>,
) -> TrustBinaryOrigin {
    if let Some(origin) =
        context.instruction_provenance.iter().find(|origin| origin.instruction_address == address)
    {
        let mut origin = origin.clone();
        if origin.binary_path.is_none() {
            origin.binary_path =
                context.origin.as_ref().and_then(|origin| origin.binary_path.clone());
        }
        if origin.function_entry.is_none() {
            origin.function_entry =
                context.origin.as_ref().and_then(|origin| origin.function_entry).or(Some(address));
        }
        if origin.source.is_none() {
            origin.source = Some(SourceSpan::binary_address(address));
        }
        return origin;
    }

    TrustBinaryOrigin {
        binary_path: context.origin.as_ref().and_then(|origin| origin.binary_path.clone()),
        function_entry: context
            .origin
            .as_ref()
            .and_then(|origin| origin.function_entry)
            .or(Some(address)),
        instruction_address: address,
        instruction_size: None,
        encoding: None,
        instruction_bytes: vec![],
        source: Some(SourceSpan::binary_address(address)),
    }
}

fn parse_raw_counterexample_value(value: &str) -> Option<CounterexampleValue> {
    let trimmed = value.trim();
    match trimmed {
        "true" => return Some(CounterexampleValue::Bool(true)),
        "false" => return Some(CounterexampleValue::Bool(false)),
        _ => {}
    }

    if let Some(n) = parse_u128_hex(trimmed) {
        return Some(CounterexampleValue::Uint(n));
    }
    if let Ok(n) = trimmed.parse::<i128>() {
        return Some(CounterexampleValue::Int(n));
    }
    if let Ok(n) = trimmed.parse::<u128>() {
        return Some(CounterexampleValue::Uint(n));
    }
    if trimmed.contains('.')
        && let Ok(n) = trimmed.parse::<f64>() {
            return Some(CounterexampleValue::Float(n));
        }
    None
}

fn parse_prefixed_register_name(name: &str) -> Option<String> {
    let trimmed = name.trim();
    let body = trimmed
        .strip_prefix("reg:")
        .or_else(|| trimmed.strip_prefix("register:"))
        .or_else(|| trimmed.strip_prefix('%'))
        .or_else(|| trimmed.strip_prefix('$'))?;
    parse_register_name(body)
}

fn parse_register_name(name: &str) -> Option<String> {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return None;
    }
    let lower = trimmed.to_ascii_lowercase();
    if is_x86_register(&lower) || is_aarch64_register(&lower) || is_flag_register(&lower) {
        Some(trimmed.to_ascii_uppercase())
    } else {
        None
    }
}

fn is_x86_register(lower: &str) -> bool {
    matches!(
        lower,
        "rax"
            | "eax"
            | "ax"
            | "al"
            | "rbx"
            | "ebx"
            | "bx"
            | "bl"
            | "rcx"
            | "ecx"
            | "cx"
            | "cl"
            | "rdx"
            | "edx"
            | "dx"
            | "dl"
            | "rsi"
            | "esi"
            | "si"
            | "sil"
            | "rdi"
            | "edi"
            | "di"
            | "dil"
            | "rbp"
            | "ebp"
            | "bp"
            | "bpl"
            | "rsp"
            | "esp"
            | "sp"
            | "spl"
            | "rip"
            | "eip"
            | "cf"
            | "zf"
            | "sf"
            | "of"
    ) || parse_numbered_x86_register(lower)
}

fn parse_numbered_x86_register(lower: &str) -> bool {
    let Some(rest) = lower.strip_prefix('r') else {
        return false;
    };
    let digits_len = rest.chars().take_while(|ch| ch.is_ascii_digit()).count();
    if digits_len == 0 {
        return false;
    }
    let (digits, suffix) = rest.split_at(digits_len);
    let Ok(index) = digits.parse::<u8>() else {
        return false;
    };
    (8..=15).contains(&index) && matches!(suffix, "" | "d" | "w" | "b")
}

fn is_aarch64_register(lower: &str) -> bool {
    matches!(lower, "sp" | "pc" | "xzr" | "wzr" | "nzcv")
        || lower
            .strip_prefix('x')
            .and_then(|digits| digits.parse::<u8>().ok())
            .is_some_and(|index| index <= 30)
        || lower
            .strip_prefix('w')
            .and_then(|digits| digits.parse::<u8>().ok())
            .is_some_and(|index| index <= 30)
}

fn is_flag_register(lower: &str) -> bool {
    matches!(lower, "n" | "z" | "c" | "v")
}

fn is_memory_state_name(name: &str) -> bool {
    name.eq_ignore_ascii_case("mem") || name.eq_ignore_ascii_case("memory")
}

fn parse_local_index(name: &str) -> Option<usize> {
    let trimmed = name.trim();
    let digits = trimmed
        .strip_prefix("_local")
        .or_else(|| trimmed.strip_prefix("local"))
        .or_else(|| trimmed.strip_prefix('_'))?;
    if digits.is_empty() || !digits.chars().all(|ch| ch.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn ty_bit_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::Bool => Some(1),
        Ty::Int { width, .. } | Ty::Float { width } | Ty::Bv(width) => Some(*width),
        _ => None,
    }
}

fn function_label(context: &WitnessNormalizationContext<'_>) -> String {
    context.function.unwrap_or("unknown").to_owned()
}

fn parse_address_from_program_point(program_point: &str) -> Option<u64> {
    let bytes = program_point.as_bytes();
    let mut idx = 0;
    while idx + 2 <= bytes.len() {
        if bytes[idx] == b'0' && matches!(bytes.get(idx + 1), Some(b'x' | b'X')) {
            let start = idx + 2;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_hexdigit() {
                end += 1;
            }
            if end > start {
                return u64::from_str_radix(&program_point[start..end], 16).ok();
            }
        }
        idx += 1;
    }
    None
}

fn parse_u32_literal(value: &str) -> Option<u32> {
    parse_u64_literal(value).and_then(|n| u32::try_from(n).ok())
}

fn parse_i64_literal(value: &str) -> Option<i64> {
    let trimmed = value.trim();
    if let Some(unsigned) = trimmed.strip_prefix('-') {
        let value = parse_u64_literal(unsigned)?;
        if value == (i64::MAX as u64) + 1 {
            return Some(i64::MIN);
        }
        return i64::try_from(value).ok()?.checked_neg();
    }
    let unsigned = trimmed.strip_prefix('+').unwrap_or(trimmed);
    parse_u64_literal(unsigned).and_then(|n| i64::try_from(n).ok())
}

fn parse_u64_literal(value: &str) -> Option<u64> {
    let trimmed = value.trim();
    if let Some(n) = parse_u128_hex(trimmed) {
        return u64::try_from(n).ok();
    }
    trimmed.parse::<u64>().ok()
}

fn parse_u128_hex(value: &str) -> Option<u128> {
    value
        .strip_prefix("0x")
        .or_else(|| value.strip_prefix("0X"))
        .and_then(|hex| u128::from_str_radix(hex, 16).ok())
}

fn unsupported_counterexample_value(counterexample: &Counterexample) -> Option<String> {
    for (name, value) in &counterexample.assignments {
        match value {
            CounterexampleValue::Bool(_) | CounterexampleValue::Int(_) => {}
            CounterexampleValue::Uint(n) if *n <= i128::MAX as u128 => {}
            CounterexampleValue::Uint(_) => {
                return Some(format!(
                    "uint assignment for '{name}' exceeds current i128 replay domain"
                ));
            }
            CounterexampleValue::Float(_) => {
                return Some(format!(
                    "float assignment for '{name}' is unsupported by lifted integer replay"
                ));
            }
            _ => {
                return Some(format!(
                    "counterexample assignment for '{name}' uses an unsupported value kind"
                ));
            }
        }
    }
    None
}

fn lifted_replay_precheck(
    function: &VerifiableFunction,
    config: &BinaryReplayConfig,
) -> Option<(BinaryReplayStatus, String)> {
    if function.body.blocks.is_empty() {
        return Some((
            BinaryReplayStatus::Unsupported,
            "lifted function has no basic blocks".into(),
        ));
    }
    if config.entry_block >= function.body.blocks.len() {
        return Some((
            BinaryReplayStatus::Unsupported,
            format!(
                "entry block {} out of range for {} lifted blocks",
                config.entry_block,
                function.body.blocks.len()
            ),
        ));
    }

    for block in &function.body.blocks {
        for stmt in &block.stmts {
            if let Some(issue) = unsupported_statement(stmt) {
                return Some(issue);
            }
        }
        if let Some(issue) = unsupported_terminator(&block.terminator) {
            return Some(issue);
        }
    }

    None
}

fn unsupported_statement(stmt: &Statement) -> Option<(BinaryReplayStatus, String)> {
    match stmt {
        Statement::Assign { rvalue, .. } => unsupported_rvalue(rvalue),
        Statement::Nop
        | Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter => None,
        Statement::SetDiscriminant { .. }
        | Statement::Deinit { .. }
        | Statement::Retag { .. }
        | Statement::Intrinsic { .. } => Some((
            BinaryReplayStatus::NeedsMachineReplay,
            format!("lifted statement requires machine replay or richer semantics: {stmt:?}"),
        )),
        _ => Some((
            BinaryReplayStatus::Unsupported,
            format!("unsupported lifted statement for replay: {stmt:?}"),
        )),
    }
}

fn unsupported_terminator(term: &Terminator) -> Option<(BinaryReplayStatus, String)> {
    match term {
        Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => None,
        Terminator::SwitchInt { discr, .. } => unsupported_operand(discr),
        Terminator::Assert { cond, .. } => unsupported_operand(cond),
        Terminator::Drop { .. } => None,
        Terminator::Call { .. } => Some((
            BinaryReplayStatus::NeedsMachineReplay,
            "lifted call terminator requires machine replay or a call summary".into(),
        )),
        Terminator::Opaque { kind, targets, .. } => Some((
            BinaryReplayStatus::NeedsMachineReplay,
            format!("opaque lifted terminator `{kind}` requires replay; targets={targets:?}"),
        )),
        _ => Some((
            BinaryReplayStatus::Unsupported,
            format!("unsupported lifted terminator for replay: {term:?}"),
        )),
    }
}

fn unsupported_rvalue(rvalue: &Rvalue) -> Option<(BinaryReplayStatus, String)> {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            unsupported_operand(op)
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            unsupported_operand(lhs).or_else(|| unsupported_operand(rhs))
        }
        Rvalue::CopyForDeref(place) if place.projections.is_empty() => None,
        Rvalue::Ref { .. }
        | Rvalue::Aggregate(_, _)
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::AddressOf(_, _)
        | Rvalue::CopyForDeref(_) => Some((
            BinaryReplayStatus::NeedsMachineReplay,
            format!("lifted rvalue requires machine replay or richer memory semantics: {rvalue:?}"),
        )),
        _ => Some((
            BinaryReplayStatus::Unsupported,
            format!("unsupported lifted rvalue for replay: {rvalue:?}"),
        )),
    }
}

fn unsupported_operand(op: &Operand) -> Option<(BinaryReplayStatus, String)> {
    match op {
        Operand::Copy(_) | Operand::Move(_) => None,
        Operand::Constant(ConstValue::Bool(_))
        | Operand::Constant(ConstValue::Int(_))
        | Operand::Constant(ConstValue::Unit) => None,
        Operand::Constant(ConstValue::CallableItem { .. }) => Some((
            BinaryReplayStatus::Unsupported,
            "callable-item constants require identity-aware replay".into(),
        )),
        Operand::Constant(ConstValue::Uint(n, _)) if *n <= i128::MAX as u128 => None,
        Operand::Constant(ConstValue::Uint(_, _)) => Some((
            BinaryReplayStatus::Unsupported,
            "uint constant exceeds current i128 replay domain".into(),
        )),
        Operand::Constant(ConstValue::Float(_)) => Some((
            BinaryReplayStatus::Unsupported,
            "float constants are unsupported by lifted integer replay".into(),
        )),
        Operand::Symbolic(_) => Some((
            BinaryReplayStatus::NeedsMachineReplay,
            "SMT-level symbolic operand cannot be replayed concretely in trust-symex".into(),
        )),
        _ => Some((
            BinaryReplayStatus::Unsupported,
            format!("unsupported lifted operand for replay: {op:?}"),
        )),
    }
}

fn replay_ended_on_spurious_path(replay: &AdapterResult) -> bool {
    replay.trace.last().is_some_and(|step| step.description.contains("no feasible branch"))
}

fn expectation_satisfied(
    expectation: &BinaryReplayExpectation,
    replay: &AdapterResult,
    blocks: &[BasicBlock],
) -> bool {
    match expectation {
        BinaryReplayExpectation::Terminates => replay.terminated_normally,
        BinaryReplayExpectation::ReachesUnreachable => {
            let Some(last_block) = replay.block_trace.last() else {
                return false;
            };
            blocks
                .get(*last_block)
                .is_some_and(|block| matches!(block.terminator, Terminator::Unreachable))
        }
        BinaryReplayExpectation::VisitsBlock(block) => replay.block_trace.contains(block),
        BinaryReplayExpectation::EndsAtBlock(block) => replay.block_trace.last() == Some(block),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum WitnessBlocks {
    Blocks(Vec<usize>),
    NoTrace,
    EmptyTrace,
    MissingProgramPoint,
    InvalidProgramPoint(String),
}

fn extract_witness_blocks(counterexample: &Counterexample) -> WitnessBlocks {
    let Some(trace) = &counterexample.trace else {
        return WitnessBlocks::NoTrace;
    };
    if trace.steps.is_empty() {
        return WitnessBlocks::EmptyTrace;
    }

    let mut blocks = Vec::with_capacity(trace.steps.len());
    for step in &trace.steps {
        let Some(program_point) = &step.program_point else {
            return WitnessBlocks::MissingProgramPoint;
        };
        let Some(block) = parse_block_program_point(program_point) else {
            return WitnessBlocks::InvalidProgramPoint(program_point.clone());
        };
        blocks.push(block);
    }

    WitnessBlocks::Blocks(blocks)
}

fn parse_block_program_point(program_point: &str) -> Option<usize> {
    let trimmed = program_point.trim();
    if let Some(digits) = trimmed.strip_prefix("bb") {
        let digits: String = digits.chars().take_while(|ch| ch.is_ascii_digit()).collect();
        if !digits.is_empty() {
            return digits.parse().ok();
        }
    }

    let bytes = trimmed.as_bytes();
    let mut idx = 0;
    while idx + 2 <= bytes.len() {
        if bytes[idx] == b'b' && bytes.get(idx + 1) == Some(&b'b') {
            let start = idx + 2;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > start {
                return trimmed[start..end].parse().ok();
            }
        }
        idx += 1;
    }
    None
}

fn compact_blocks(blocks: &[usize]) -> Vec<usize> {
    let mut compacted = Vec::with_capacity(blocks.len());
    for block in blocks {
        if compacted.last() != Some(block) {
            compacted.push(*block);
        }
    }
    compacted
}

fn same_trace_payload(lhs: &trust_types::TraceStep, rhs: &trust_types::TraceStep) -> bool {
    lhs.program_point == rhs.program_point && lhs.assignments == rhs.assignments
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use serde_json::json;
    use trust_types::{
        BinOp, BinaryArtifactDigestIdentity, BinarySelectedImageIdentity, BlockId, Formula,
        FunctionSpec, LocalDecl, Place, ProofStrength, SerializableVc, SolverDispatchRecord,
        SolverDispatchStatus, Sort, SourceSpan, TraceStep, Ty, VcKind, VerifiableBody,
        VerificationResult,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn callable_constants_fail_closed_in_binary_replay() {
        let operand = Operand::Constant(ConstValue::CallableItem {
            def_path: "fixture::callback".to_string(),
            kind: trust_types::CallableKind::FnDef,
            def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
        });
        let (status, detail) =
            unsupported_operand(&operand).expect("binary replay cannot encode callables");
        assert_eq!(status, BinaryReplayStatus::Unsupported);
        assert!(detail.contains("callable-item constants"));
    }

    fn vc(function: &VerifiableFunction) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Unreachable,
            function: function.def_path.clone().into(),
            location: function.span.clone(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn function(blocks: Vec<BasicBlock>) -> VerifiableFunction {
        VerifiableFunction {
            name: "lifted_test".into(),
            def_path: "binary::lifted_test".into(),
            span: span(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                blocks,
                arg_count: 1,
                return_ty: Ty::unit_ty(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: FunctionSpec::default(),
        }
    }

    fn traced_counterexample(
        assignments: Vec<(String, CounterexampleValue)>,
        blocks: &[usize],
    ) -> Counterexample {
        let steps = blocks
            .iter()
            .enumerate()
            .map(|(idx, block)| TraceStep {
                step: idx as u32,
                assignments: BTreeMap::new(),
                program_point: Some(format!("bb{block}")),
            })
            .collect();
        Counterexample::with_trace(assignments, CounterexampleTrace::new(steps))
    }

    fn return_function() -> VerifiableFunction {
        function(vec![BasicBlock {
            id: BlockId(0),
            stmts: Vec::new(),
            terminator: Terminator::Return,
        }])
    }

    fn branch_function() -> VerifiableFunction {
        function(vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: span(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
            BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
        ])
    }

    const AARCH64_NOP_ENCODING: u32 = 0xd503_201f;
    const AARCH64_NOP_BYTES: [u8; 4] = [0x1f, 0x20, 0x03, 0xd5];
    const AARCH64_B_PLUS_8_ENCODING: u32 = 0x1400_0002;
    const AARCH64_B_PLUS_8_BYTES: [u8; 4] = [0x02, 0x00, 0x00, 0x14];
    const AARCH64_BL_PLUS_8_ENCODING: u32 = 0x9400_0002;
    const AARCH64_BL_PLUS_8_BYTES: [u8; 4] = [0x02, 0x00, 0x00, 0x94];
    const AARCH64_RET_ENCODING: u32 = 0xd65f_03c0;
    const AARCH64_RET_BYTES: [u8; 4] = [0xc0, 0x03, 0x5f, 0xd6];
    const AARCH64_SVC0_ENCODING: u32 = 0xd400_0001;
    const AARCH64_SVC0_BYTES: [u8; 4] = [0x01, 0x00, 0x00, 0xd4];
    const AARCH64_SVC1_ENCODING: u32 = 0xd400_0021;
    const AARCH64_SVC1_BYTES: [u8; 4] = [0x21, 0x00, 0x00, 0xd4];
    const AARCH64_BRK1_ENCODING: u32 = 0xd420_0020;
    const AARCH64_BRK1_BYTES: [u8; 4] = [0x20, 0x00, 0x20, 0xd4];
    const AARCH64_YIELD_ENCODING: u32 = 0xd503_203f;
    const AARCH64_YIELD_BYTES: [u8; 4] = [0x3f, 0x20, 0x03, 0xd5];
    const AARCH64_LDAXR_X0_X1_BYTES: [u8; 4] = [0x20, 0xfc, 0x5f, 0xc8];
    const X86_64_SYSCALL_ENCODING: u32 = 0x0f05;
    const X86_64_SYSCALL_BYTES: [u8; 2] = [0x0f, 0x05];
    const X86_64_INT3_ENCODING: u32 = 0xcc;
    const X86_64_INT3_BYTES: [u8; 1] = [0xcc];
    const X86_64_CALL_0X401020_BYTES: [u8; 5] = [0xe8, 0x0b, 0x00, 0x00, 0x00];
    const X86_64_RET_BYTES: [u8; 1] = [0xc3];
    const X86_64_NOP_BYTES: [u8; 1] = [0x90];
    const TEST_ARTIFACT_SHA256: &str =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    const OTHER_TEST_ARTIFACT_SHA256: &str =
        "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789";
    const TEST_SELECTED_IMAGE_SHA256: &str =
        "04ca88f2b88d606239021d6eb03752f117e3f73fb022df93dbe99ab93edf368b";
    const OTHER_TEST_SELECTED_IMAGE_SHA256: &str =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    fn test_artifact_digest() -> BinaryArtifactDigest {
        BinaryArtifactDigest::sha256(TEST_ARTIFACT_SHA256)
    }

    fn test_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
        BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(test_artifact_digest()),
            selected_image: Some(test_selected_image()),
        }
    }

    fn test_selected_image() -> BinarySelectedImageIdentity {
        BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 0x1000,
            sha256: TEST_SELECTED_IMAGE_SHA256.to_string(),
        }
    }

    fn other_test_selected_image() -> BinarySelectedImageIdentity {
        BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 4,
            sha256: OTHER_TEST_SELECTED_IMAGE_SHA256.to_string(),
        }
    }

    fn offset_test_selected_image() -> BinarySelectedImageIdentity {
        BinarySelectedImageIdentity {
            file_offset: 4,
            file_size: 0x1000,
            sha256: TEST_SELECTED_IMAGE_SHA256.to_string(),
        }
    }

    fn test_instruction_file_offset(address: u64) -> u64 {
        address.saturating_sub(0x401000)
    }

    fn test_byte_range_evidence(
        instruction_trace: &[BinaryMachineInstructionEvidence],
    ) -> Vec<BinaryMachineReplayByteRangeEvidence> {
        instruction_trace
            .iter()
            .map(|evidence| {
                BinaryMachineReplayByteRangeEvidence::new(
                    evidence.origin.instruction_address,
                    evidence.step,
                    test_instruction_file_offset(evidence.origin.instruction_address),
                    evidence.origin.instruction_bytes.len() as u64,
                    evidence.origin.instruction_bytes.clone(),
                )
            })
            .collect()
    }

    fn test_effect_evidence(
        instruction_trace: &[BinaryMachineInstructionEvidence],
    ) -> Vec<BinaryMachineReplayEffectEvidence> {
        instruction_trace
            .iter()
            .flat_map(|instruction| {
                required_effect_witnesses(instruction).into_iter().filter_map(|required| {
                    let RequiredEffectWitness::Evidence(required) = required else {
                        return None;
                    };
                    let mut evidence = BinaryMachineReplayEffectEvidence::new(
                        required.kind,
                        required.architecture,
                        required.instruction_address,
                        format!("mock backend consumed {} effect witness", required.kind),
                    )
                    .with_step(required.step)
                    .with_witness_step(required.step);
                    if let Some(subject) = required.subject {
                        evidence = evidence.with_subject(subject);
                    }
                    if let Some(memory_access) = required.memory_access {
                        evidence = evidence.with_memory_access(
                            BinaryMachineReplayMemoryAccessEvidence::new(
                                0,
                                memory_access.width_bytes,
                            ),
                        );
                    }
                    Some(evidence)
                })
            })
            .collect()
    }

    fn root_only_test_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
        BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(test_artifact_digest()),
            selected_image: None,
        }
    }

    fn other_test_artifact_digest() -> BinaryArtifactDigest {
        BinaryArtifactDigest::sha256(OTHER_TEST_ARTIFACT_SHA256)
    }

    fn instruction_origin(address: u64, function_entry: u64) -> TrustBinaryOrigin {
        TrustBinaryOrigin {
            binary_path: None,
            function_entry: Some(function_entry),
            instruction_address: address,
            instruction_size: Some(4),
            encoding: None,
            instruction_bytes: vec![],
            source: Some(SourceSpan::binary_address(address)),
        }
    }

    fn instruction_origin_with_bytes(
        address: u64,
        function_entry: u64,
        size: u8,
        encoding: u32,
        bytes: impl Into<Vec<u8>>,
    ) -> TrustBinaryOrigin {
        TrustBinaryOrigin {
            instruction_size: Some(size),
            encoding: Some(encoding),
            instruction_bytes: bytes.into(),
            ..instruction_origin(address, function_entry)
        }
    }

    fn instruction_origin_with_encoding(
        address: u64,
        function_entry: u64,
        encoding: u32,
    ) -> TrustBinaryOrigin {
        TrustBinaryOrigin {
            encoding: Some(encoding),
            ..instruction_origin(address, function_entry)
        }
    }

    fn instruction_origin_with_exact_bytes(
        address: u64,
        function_entry: u64,
        bytes: impl Into<Vec<u8>>,
    ) -> TrustBinaryOrigin {
        let bytes = bytes.into();
        TrustBinaryOrigin {
            instruction_size: Some(bytes.len() as u8),
            instruction_bytes: bytes,
            ..instruction_origin(address, function_entry)
        }
    }

    fn binary_witness_with_origin(origin: TrustBinaryOrigin) -> BinaryWitness {
        binary_witness_with_origins(vec![origin])
    }

    fn binary_witness_with_origins(origins: Vec<TrustBinaryOrigin>) -> BinaryWitness {
        let trace = origins
            .into_iter()
            .enumerate()
            .map(|(step, origin)| BinaryWitnessTraceStep {
                step: step as u32,
                program_point: Some(BinaryWitnessProgramPoint {
                    raw: format!("bb{step}@0x{:x}", origin.instruction_address),
                    block: Some(step),
                    origin: Some(origin),
                }),
                assignments: Vec::new(),
            })
            .collect::<Vec<_>>();
        let raw_trace_steps = trace.len();
        BinaryWitness {
            trace,
            raw_trace_steps,
            has_execution_trace: true,
            provenance: BinaryWitnessProvenance {
                artifact_digest: Some(test_artifact_digest()),
                ..BinaryWitnessProvenance::default()
            },
            ..BinaryWitness::default()
        }
    }

    fn source_backprop_replay_witness(origins: Vec<TrustBinaryOrigin>) -> BinaryWitness {
        let steps = origins
            .iter()
            .enumerate()
            .map(|(step, origin)| {
                let mut assignments = BTreeMap::new();
                if step == 0 {
                    assignments.insert("_local0".to_owned(), "1".to_owned());
                }
                TraceStep {
                    step: step as u32,
                    assignments,
                    program_point: Some(format!("bb{step}@0x{:x}", origin.instruction_address)),
                }
            })
            .collect::<Vec<_>>();
        let input = BinaryReplayInput::new(Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(steps),
        ))
        .with_instruction_provenance(origins.clone())
        .with_artifact_digest(test_artifact_digest())
        .with_selected_image(test_selected_image())
        .require_selected_image_identity();
        let origin = BinaryOrigin {
            function: Some("binary::source_backprop_fixture".into()),
            entry: origins
                .first()
                .and_then(|origin| origin.function_entry)
                .or_else(|| origins.first().map(|origin| origin.instruction_address)),
            ..BinaryOrigin::default()
        };

        normalize_binary_origin_witness(&origin, &input)
    }

    fn aarch64_nop_image(address: u64) -> BoundedMachineCodeImage {
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(address, AARCH64_NOP_BYTES);
        image
    }

    fn aarch64_ldaxr_image(address: u64) -> BoundedMachineCodeImage {
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(address, AARCH64_LDAXR_X0_X1_BYTES);
        image
    }

    fn x86_64_nop_image(address: u64) -> BoundedMachineCodeImage {
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::X86_64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(address, [0x90]);
        image
    }

    fn trace_step_with_assignments(
        step: u32,
        address: u64,
        assignments: impl IntoIterator<Item = (&'static str, &'static str)>,
    ) -> TraceStep {
        TraceStep {
            step,
            assignments: assignments
                .into_iter()
                .map(|(name, value)| (name.to_owned(), value.to_owned()))
                .collect(),
            program_point: Some(format!("bb0@0x{address:x}")),
        }
    }

    fn traced_counterexample_with_instruction(address: u64) -> Counterexample {
        Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![TraceStep {
                step: 0,
                assignments: BTreeMap::new(),
                program_point: Some(format!("bb0@0x{address:x}")),
            }]),
        )
    }

    fn traced_counterexample_with_bound_instruction(address: u64) -> Counterexample {
        let mut assignments = BTreeMap::new();
        assignments.insert("_local0".to_owned(), "1".to_owned());
        Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![TraceStep {
                step: 0,
                assignments,
                program_point: Some(format!("bb0@0x{address:x}")),
            }]),
        )
    }

    fn traced_counterexample_with_ssa_renamed_instruction(address: u64) -> Counterexample {
        let mut assignments = BTreeMap::new();
        assignments.insert("_local0!7".to_owned(), "1".to_owned());
        Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![TraceStep {
                step: 0,
                assignments,
                program_point: Some(format!("bb0@0x{address:x}")),
            }]),
        )
    }

    fn traced_counterexample_with_instruction_assignment(address: u64) -> Counterexample {
        let mut assignments = BTreeMap::new();
        assignments.insert("%rax".to_owned(), "0x2a".to_owned());
        Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![TraceStep {
                step: 0,
                assignments,
                program_point: Some(format!("bb0@0x{address:x}")),
            }]),
        )
    }

    fn sat_dispatch_with_counterexample(
        function: &VerifiableFunction,
        counterexample: Counterexample,
    ) -> SolverDispatchRecord {
        let vc = vc(function);
        SolverDispatchRecord {
            id: "sat-dispatch".into(),
            function: Some(function.def_path.clone()),
            origin: Some(instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )),
            vc: Some(SerializableVc::from_vc(&vc)),
            solver: "constant-folder".into(),
            status: SolverDispatchStatus::Sat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            result: Some(VerificationResult::Failed {
                solver: "constant-folder".into(),
                time_ms: 1,
                counterexample: Some(counterexample),
            }),
            ..SolverDispatchRecord::default()
        }
    }

    fn unsat_dispatch(function: &VerifiableFunction) -> SolverDispatchRecord {
        let vc = vc(function);
        SolverDispatchRecord {
            id: "unsat-dispatch".into(),
            function: Some(function.def_path.clone()),
            origin: Some(instruction_origin(0x401010, 0x401000)),
            vc: Some(SerializableVc::from_vc(&vc)),
            solver: "constant-folder".into(),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            result: Some(VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }),
            ..SolverDispatchRecord::default()
        }
    }

    #[derive(Debug, Clone)]
    struct MockMachineReplayBackend {
        result: BinaryMachineReplayResult,
    }

    impl BinaryMachineReplayBackend for MockMachineReplayBackend {
        fn replay(&self, request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
            assert!(request.config.require_exact_instruction_trace);
            assert!(request.config.require_exact_artifact_digest);
            assert!(request.witness.has_execution_trace);
            let mut result = self.result.clone();
            if result.selected_image.is_some() && result.byte_range_evidence.is_empty() {
                result.byte_range_evidence = test_byte_range_evidence(&result.instruction_trace);
            }
            if result.effect_evidence.is_empty() && result.effect_diagnostics.is_empty() {
                result.effect_evidence = test_effect_evidence(&result.instruction_trace);
            }
            result
        }
    }

    #[test]
    fn bounded_machine_code_address_map_returns_original_bytes_by_va() {
        let mut map = BoundedMachineCodeAddressMap::new();
        map.insert(BoundedMachineInstructionBytes::new(0x401010, [0x1f, 0x20, 0x03, 0xd5]));

        let mapped = map.get(0x401010).expect("mapped instruction bytes");

        assert_eq!(mapped.address, 0x401010);
        assert_eq!(mapped.bytes, vec![0x1f, 0x20, 0x03, 0xd5]);
        assert!(map.get(0x401014).is_none());
    }

    #[test]
    fn bounded_machine_backend_classifies_unmapped_expected_va_as_needs_machine_replay() {
        let witness = binary_witness_with_origin(instruction_origin(0x401010, 0x401000));
        let backend = BoundedMachineCodeReplayBackend::new(BoundedMachineCodeImage::new(
            BoundedMachineCodeArchitecture::Aarch64,
        ));

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.reason.contains("no original instruction bytes mapped"));
        assert_eq!(report.expected_instruction_trace[0].instruction_address, 0x401010);
    }

    #[test]
    fn bounded_machine_backend_classifies_encoding_mismatch_as_spurious() {
        let witness = binary_witness_with_origin(instruction_origin_with_encoding(
            0x401010,
            0x401000,
            0xffff_ffff,
        ));
        let backend = BoundedMachineCodeReplayBackend::new(aarch64_nop_image(0x401010));

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(report.reason.contains("decoded instruction encoding"));
        assert!(!report.matched_instruction_trace);
    }

    #[test]
    fn bounded_machine_backend_classifies_instruction_bytes_mismatch_as_spurious() {
        let witness = binary_witness_with_origin(instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        ));
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(0x401010, AARCH64_YIELD_BYTES);
        let backend = BoundedMachineCodeReplayBackend::new(image);

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(report.reason.contains("instruction bytes"));
        assert!(!report.matched_instruction_trace);
    }

    #[test]
    fn bounded_machine_backend_classifies_instruction_size_mismatch_as_spurious() {
        let witness = binary_witness_with_origin(instruction_origin(0x401010, 0x401000));
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(0x401010, [0x1f, 0x20, 0x03, 0xd5, 0x00]);
        let backend = BoundedMachineCodeReplayBackend::new(image);

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(report.reason.contains("mapped instruction size"));
        assert!(!report.matched_instruction_trace);
    }

    #[test]
    fn bounded_machine_backend_classifies_unsupported_architecture_as_unsupported() {
        let witness = binary_witness_with_origin(instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        ));
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Unsupported);
        image.insert_instruction(0x401010, AARCH64_NOP_BYTES);
        let backend = BoundedMachineCodeReplayBackend::new(image);

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(report.reason.contains("selected architecture"));
        assert!(!report.matched_instruction_trace);
    }

    #[test]
    fn bounded_machine_backend_reports_selected_architecture_mismatch() {
        let witness = binary_witness_with_origin(instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        ));
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::X86_64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(0x401010, AARCH64_NOP_BYTES);
        let backend = BoundedMachineCodeReplayBackend::new(image);

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(
            report.reason.contains("architecture mismatch"),
            "unexpected reason: {}",
            report.reason
        );
        assert!(report.reason.contains("x86_64"), "unexpected reason: {}", report.reason);
        assert!(report.reason.contains("AArch64"), "unexpected reason: {}", report.reason);
    }

    #[test]
    fn bounded_machine_backend_confirms_mapped_straight_line_aarch64_original_bytes() {
        let witness = binary_witness_with_origins(vec![
            instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            ),
            instruction_origin_with_bytes(
                0x401014,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            ),
        ]);
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
            .with_artifact_digest(test_artifact_digest());
        image.insert_instruction(0x401010, AARCH64_NOP_BYTES);
        image.insert_instruction(0x401014, AARCH64_NOP_BYTES);
        let backend = BoundedMachineCodeReplayBackend::new(image);

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert!(report.matched_instruction_trace);
        assert_eq!(report.observed_instruction_trace.len(), 2);
        assert_eq!(
            report.observed_instruction_trace[1].origin.instruction_bytes,
            AARCH64_NOP_BYTES.to_vec()
        );
        assert_eq!(report.observed_instruction_trace[1].step, Some(1));
    }

    #[test]
    fn bounded_machine_backend_confirms_mapped_straight_line_aarch64_nop() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = BoundedMachineCodeReplayBackend::new(aarch64_nop_image(0x401010));

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert_eq!(
            report.machine_replay.observed_instruction_trace[0].origin.instruction_address,
            0x401010
        );
    }

    #[test]
    fn bounded_machine_backend_keeps_aarch64_ldaxr_fail_closed_at_lift_boundary() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                0xc85f_fc20,
                AARCH64_LDAXR_X0_X1_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = BoundedMachineCodeReplayBackend::new(aarch64_ldaxr_image(0x401010));

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.block_trace, vec![0]);
        assert_eq!(report.witness_trace, vec![0]);
        assert_eq!(report.status, BinaryReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(!report.needs_machine_replay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.machine_replay.trust_types_status, ReplayStatus::Failed);
        assert_ne!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert_ne!(report.machine_replay.status, BinaryMachineReplayStatus::Spurious);
        assert!(!report.machine_replay.matched_instruction_trace);
        assert_eq!(
            report.machine_replay.expected_instruction_trace[0].instruction_address,
            0x401010
        );
        assert!(
            report
                .machine_replay
                .reason
                .contains("LDAXR exclusive monitor semantics are fail-closed"),
            "unexpected reason: {}",
            report.machine_replay.reason
        );
        assert!(
            report.machine_replay.reason.contains("monitor reservation state"),
            "unexpected reason: {}",
            report.machine_replay.reason
        );
    }

    #[test]
    fn bounded_machine_backend_confirms_mapped_straight_line_x86_64_nop() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                1,
                0x90,
                [0x90],
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = BoundedMachineCodeReplayBackend::new(x86_64_nop_image(0x401010));

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert_eq!(
            report.machine_replay.observed_instruction_trace[0].origin.instruction_address,
            0x401010
        );
        assert_eq!(report.machine_replay.observed_instruction_trace.len(), 1);
    }

    #[test]
    fn bounded_machine_backend_replays_x86_64_call_return_with_exact_attestation() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401010);
        let origins = vec![
            instruction_origin_with_exact_bytes(0x401010, 0x401010, X86_64_CALL_0X401020_BYTES),
            instruction_origin_with_exact_bytes(0x401020, 0x401010, X86_64_RET_BYTES),
            instruction_origin_with_exact_bytes(0x401015, 0x401010, X86_64_NOP_BYTES),
        ];
        let counterexample = Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![
                trace_step_with_assignments(0, 0x401010, [("_local0", "1"), ("RSP", "0x8000")]),
                trace_step_with_assignments(
                    1,
                    0x401020,
                    [("RSP", "0x7ff8"), ("stack:sp+0:8", "0x401015")],
                ),
                trace_step_with_assignments(2, 0x401015, [("RSP", "0x8000")]),
            ]),
        );
        let input = BinaryReplayInput::new(counterexample)
            .with_instruction_provenance(origins.clone())
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates)
            .require_selected_image_identity();
        let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::X86_64)
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image());
        image.insert_instruction_at_file_offset(0x401010, 0, X86_64_CALL_0X401020_BYTES);
        image.insert_instruction_at_file_offset(0x401020, 0x10, X86_64_RET_BYTES);
        image.insert_instruction_at_file_offset(0x401015, 0x05, X86_64_NOP_BYTES);
        image.insert_segment(0x401010, 0x11, BoundedMachineCodeSegmentPermissions::rx());
        image.insert_segment(0x7000, 0x2000, BoundedMachineCodeSegmentPermissions::rw());
        let backend = BoundedMachineCodeReplayBackend::new(image);

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::Confirmed, "{report:#?}");
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert!(!report.needs_machine_replay);
        let machine = &report.machine_replay;
        assert_eq!(machine.status, BinaryMachineReplayStatus::Replayed);
        assert!(machine.source_backprop_replay_ready(), "{machine:#?}");
        assert_eq!(machine.source_backprop_replay_blocker_reason(), None);
        assert!(machine.matched_instruction_trace);
        assert!(machine.matched_artifact_digest);
        assert!(machine.matched_selected_image);
        assert!(machine.matched_capability_evidence);
        assert!(machine.matched_effect_evidence);
        assert_eq!(machine.expected_instruction_trace, origins);
        assert_eq!(
            machine
                .observed_instruction_trace
                .iter()
                .map(|instruction| instruction.origin.instruction_address)
                .collect::<Vec<_>>(),
            vec![0x401010, 0x401020, 0x401015]
        );
        assert_eq!(machine.byte_range_evidence.len(), 3);
        assert!(
            machine
                .byte_range_evidence
                .iter()
                .any(|evidence| evidence.instruction_address == 0x401020
                    && evidence.file_offset == 0x10
                    && evidence.instruction_bytes.as_slice() == X86_64_RET_BYTES.as_slice())
        );
        assert!(machine.capability_evidence.iter().any(|evidence| {
            evidence.capability == BinaryMachineReplayCapability::DirectCall
                && evidence.instruction_address == 0x401010
                && evidence.instruction_bytes.as_slice() == X86_64_CALL_0X401020_BYTES.as_slice()
        }));
        assert!(machine.capability_evidence.iter().any(|evidence| {
            evidence.capability == BinaryMachineReplayCapability::Return
                && evidence.instruction_address == 0x401020
                && evidence.instruction_bytes.as_slice() == X86_64_RET_BYTES.as_slice()
        }));
        assert!(machine.effect_evidence.iter().any(|evidence| {
            evidence.instruction_address == 0x401010
                && evidence.kind == BinaryMachineReplayEffectKind::ControlFlow
        }));
        assert!(machine.effect_evidence.iter().any(|evidence| {
            evidence.instruction_address == 0x401010
                && evidence.kind == BinaryMachineReplayEffectKind::MemoryWrite
                && evidence
                    .memory_access
                    .is_some_and(|access| access.address == 0x7ff8 && access.width_bytes == 8)
        }));
        assert!(machine.effect_evidence.iter().any(|evidence| {
            evidence.instruction_address == 0x401020
                && evidence.kind == BinaryMachineReplayEffectKind::MemoryRead
                && evidence
                    .memory_access
                    .is_some_and(|access| access.address == 0x7ff8 && access.width_bytes == 8)
        }));
        assert_eq!(machine.attestation_slices.len(), 3);
        assert!(
            machine.attestation_slices.iter().all(BinaryMachineReplayAttestationSlice::is_accepted)
        );
        assert!(machine.boundary_evidence.is_empty());
        assert!(machine.effect_diagnostics.is_empty());
        assert!(machine.byte_range_diagnostics.is_empty());
    }

    #[test]
    fn raw_solver_model_is_not_confirmed() {
        let function = return_function();
        let input = BinaryReplayInput::new(Counterexample::new(vec![(
            "_local0".into(),
            CounterexampleValue::Int(1),
        )]))
        .with_verification_condition(vc(&function))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_ne!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.needs_machine_replay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_ne!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
    }

    #[test]
    fn raw_solver_model_is_not_confirmed_even_when_trace_requirement_is_disabled() {
        let function = return_function();
        let input = BinaryReplayInput::new(Counterexample::new(vec![(
            "_local0".into(),
            CounterexampleValue::Int(1),
        )]))
        .with_verification_condition(vc(&function))
        .with_expectation(BinaryReplayExpectation::Terminates);
        let config =
            BinaryReplayConfig { require_trace_for_confirmation: false, ..Default::default() };

        let report =
            replay_binary_counterexample(BinaryReplayTarget::lifted(&function), &input, &config);

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_ne!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.normalized_witness.trace.is_empty());
        assert!(!report.normalized_witness.has_execution_trace);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    }

    #[test]
    fn lifted_trace_with_expectation_still_needs_machine_replay_by_default() {
        let function = return_function();
        let input = BinaryReplayInput::new(traced_counterexample(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            &[0],
        ))
        .with_verification_condition(vc(&function))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.needs_machine_replay);
        assert!(report.reason.contains("lifted IR"));
        assert!(report.reason.contains("machine-code replay is still required"));
        assert_eq!(report.block_trace, vec![0]);
        assert_eq!(report.witness_trace, vec![0]);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_ne!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
    }

    #[test]
    fn replay_status_json_uses_snake_case_names() {
        assert_eq!(
            serde_json::to_value(BinaryReplayStatus::NeedsMachineReplay).unwrap(),
            json!("needs_machine_replay")
        );
        assert_eq!(serde_json::to_value(BinaryReplayStatus::Spurious).unwrap(), json!("spurious"));
        assert_eq!(
            serde_json::to_value(BinaryMachineReplayStatus::NeedsMachineReplay).unwrap(),
            json!("needs_machine_replay")
        );
        assert_eq!(
            serde_json::to_value(BinaryMachineReplayStatus::Spurious).unwrap(),
            json!("spurious")
        );
        assert_eq!(serde_json::to_value(BinaryReplayStatus::Failed).unwrap(), json!("failed"));
        assert_eq!(
            serde_json::to_value(BinaryMachineReplayStatus::Failed).unwrap(),
            json!("failed")
        );
        assert_eq!(
            serde_json::to_value(BinaryWitnessRecordSource::TraceAssignment).unwrap(),
            json!("trace_assignment")
        );

        let replayed_evidence = BinarySolverDispatchReplayEvidence {
            dispatch_id: "dispatch".into(),
            replay: ReplayStatus::Replayed,
            replay_report: None,
            replay_requirement: BinaryReplayRequirement::ExactMachineWitnessReplay,
            requirement_satisfied: true,
            reason: "serialization fixture".into(),
        };
        assert_eq!(serde_json::to_value(&replayed_evidence).unwrap()["replay"], json!("replayed"));
    }

    #[test]
    fn replay_report_json_serializes_spurious_status_as_snake_case() {
        let function = branch_function();
        let input = BinaryReplayInput::new(traced_counterexample(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            &[0, 2],
        ))
        .with_verification_condition(vc(&function))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );
        let json = serde_json::to_value(&report).unwrap();

        assert_eq!(json["status"], json!("spurious"));
        assert_eq!(json["trust_types_status"], json!("spurious"));
        assert_eq!(json["machine_replay"]["status"], json!("needs_machine_replay"));
        assert_eq!(json["machine_replay"]["trust_types_status"], json!("not_attempted"));
    }

    #[test]
    fn replay_report_json_includes_normalized_witness_provenance() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input =
            BinaryReplayInput::new(traced_counterexample_with_instruction_assignment(0x401010))
                .with_verification_condition(vc(&function))
                .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );
        let json = serde_json::to_value(&report).unwrap();
        let witness = &json["normalized_witness"];
        let trace_point = &witness["trace"][0]["program_point"];
        let trace_record = &witness["trace"][0]["assignments"][0];

        assert_eq!(json["status"], json!("needs_machine_replay"));
        assert_eq!(json["machine_replay"]["status"], json!("needs_machine_replay"));
        assert_eq!(witness["function"], json!("binary::lifted_test"));
        assert_eq!(witness["origin"]["instruction_address"], json!(0x401000));
        assert_eq!(trace_point["raw"], json!("bb0@0x401010"));
        assert_eq!(trace_point["block"], json!(0));
        assert_eq!(trace_point["origin"]["instruction_address"], json!(0x401010));
        assert_eq!(trace_point["origin"]["function_entry"], json!(0x401000));
        assert_eq!(trace_record["source"], json!("trace_assignment"));
        assert_eq!(trace_record["program_point"]["origin"]["instruction_address"], json!(0x401010));
        assert_eq!(witness["provenance"]["model_assignment_names"], json!(["_local0"]));
        assert_eq!(witness["provenance"]["trace_program_points"], json!(["bb0@0x401010"]));
        assert_eq!(
            witness["provenance"]["trace_instruction_origins"][0]["instruction_address"],
            json!(0x401010)
        );
    }

    #[test]
    fn lifted_only_evidence_json_never_serializes_replay_status_as_replayed() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );

        let evidence = replay_solver_dispatch_counterexample(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
        );
        let json = serde_json::to_value(&evidence).unwrap();
        let report = &json["replay_report"];
        let serialized = serde_json::to_string(&evidence).unwrap();

        assert_eq!(json["replay"], json!("not_attempted"));
        assert_eq!(report["status"], json!("needs_machine_replay"));
        assert_eq!(report["trust_types_status"], json!("not_attempted"));
        assert_eq!(report["machine_replay"]["status"], json!("needs_machine_replay"));
        assert_eq!(report["machine_replay"]["trust_types_status"], json!("not_attempted"));
        assert_ne!(json["replay"], json!("replayed"));
        assert_ne!(report["trust_types_status"], json!("replayed"));
        assert_ne!(report["machine_replay"]["trust_types_status"], json!("replayed"));
        assert!(!serialized.contains("\"Replayed\""));
        assert!(!serialized.contains("\"replayed\""));
    }

    #[test]
    fn unavailable_machine_backend_preserves_needs_machine_replay() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.needs_machine_replay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.trust_types_status, ReplayStatus::NotAttempted);
        assert_eq!(
            report.machine_replay.expected_instruction_trace[0].instruction_address,
            0x401010
        );
    }

    #[test]
    fn mock_machine_backend_confirms_when_instruction_provenance_matches() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence {
                    origin: instruction_origin_with_bytes(
                        0x401010,
                        0x401000,
                        4,
                        AARCH64_NOP_ENCODING,
                        AARCH64_NOP_BYTES,
                    ),
                    step: Some(0),
                }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert!(!report.needs_machine_replay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert!(report.machine_replay.matched_instruction_trace);
        assert_eq!(
            report.machine_replay.observed_instruction_trace[0].origin.instruction_address,
            0x401010
        );
    }

    #[test]
    fn machine_replay_rejects_replayed_trace_without_witness_artifact_digest() {
        let expected = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let mut witness = binary_witness_with_origin(expected.clone());
        witness.provenance.artifact_digest = None;
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(expected)],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.matched_instruction_trace);
        assert!(!report.matched_artifact_digest);
        assert!(report.reason.contains("normalized witness omitted root binary artifact digest"));
        assert!(report.reason.contains("proof-grade"));
    }

    #[test]
    fn machine_replay_rejects_mismatched_artifact_digest_as_spurious() {
        let expected = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let witness = binary_witness_with_origin(expected.clone());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(expected)],
            )
            .with_artifact_digest(other_test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(report.matched_instruction_trace);
        assert!(!report.matched_artifact_digest);
        assert!(report.reason.contains("artifact digest did not match"));
        assert_eq!(report.expected_artifact_digest, Some(test_artifact_digest()));
        assert_eq!(report.observed_artifact_digest, Some(other_test_artifact_digest()));
    }

    #[test]
    fn matching_machine_trace_does_not_confirm_unreplayed_memory_provenance() {
        let mut function = function(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Ref { mutable: false, place: Place::local(0) },
                span: span(),
            }],
            terminator: Terminator::Return,
        }]);
        function.span = SourceSpan::binary_address(0x401000);
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: Some("value".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                name: Some("value_ref".into()),
            },
        ];
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence {
                    origin: instruction_origin_with_bytes(
                        0x401010,
                        0x401000,
                        4,
                        AARCH64_NOP_ENCODING,
                        AARCH64_NOP_BYTES,
                    ),
                    step: Some(0),
                }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert_ne!(report.trust_types_status, ReplayStatus::Replayed);
        assert!(report.needs_machine_replay);
        assert!(report.block_trace.is_empty());
        assert!(report.reason.contains("richer memory semantics"));
        assert!(report.reason.contains("prior replay status remains needs_machine_replay"));
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert!(report.machine_replay.matched_instruction_trace);
    }

    #[test]
    fn mock_machine_backend_is_spurious_when_instruction_provenance_mismatches() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_artifact_digest(test_artifact_digest())
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401014,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(!report.needs_machine_replay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Spurious);
        assert!(!report.machine_replay.matched_instruction_trace);
        assert_eq!(
            report.machine_replay.expected_instruction_trace[0].instruction_address,
            0x401010
        );
    }

    #[test]
    fn bounded_machine_validation_rejects_replayed_evidence_with_provenance_mismatch() {
        let expected = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let observed = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_YIELD_ENCODING,
            AARCH64_YIELD_BYTES,
        );
        let witness = binary_witness_with_origin(expected);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(observed)],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(!report.matched_instruction_trace);
        assert!(report.reason.contains("instruction trace"));
    }

    #[test]
    fn machine_replay_rejects_replayed_trace_without_instruction_bytes() {
        let expected = instruction_origin(0x401010, 0x401000);
        let witness = binary_witness_with_origin(expected.clone());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(expected)],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(!report.matched_instruction_trace);
        assert!(report.reason.contains("omitted original instruction bytes"));
        assert!(report.reason.contains("proof-grade"));
    }

    #[test]
    fn machine_replay_rejects_backend_supplied_bytes_without_witness_identity() {
        let expected = instruction_origin(0x401010, 0x401000);
        let observed = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let witness = binary_witness_with_origin(expected);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(observed)],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(!report.matched_instruction_trace);
        assert!(report.reason.contains("normalized witness provenance"));
        assert!(report.reason.contains("exact normalized instruction-byte provenance"));
        assert!(report.reason.contains("proof-grade"));
    }

    #[test]
    fn machine_replay_rejects_replayed_aarch64_exception_boundary() {
        let svc = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_SVC0_ENCODING,
            AARCH64_SVC0_BYTES,
        );
        let witness = binary_witness_with_origin(svc.clone());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(svc)],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(report.matched_instruction_trace);
        assert!(!report.matched_capability_evidence);
        assert!(report.capability_evidence.is_empty());
        assert_eq!(report.boundary_evidence.len(), 1);
        let boundary = &report.boundary_evidence[0];
        assert_eq!(boundary.kind, BinaryMachineReplayBoundaryKind::Syscall);
        assert_eq!(boundary.architecture, "AArch64");
        assert_eq!(boundary.instruction_address, 0x401010);
        assert_eq!(boundary.step, None);
        assert_eq!(boundary.instruction_bytes, AARCH64_SVC0_BYTES);
        assert_eq!(boundary.opcode.to_ascii_uppercase(), "SVC");
        assert_eq!(boundary.encoding, AARCH64_SVC0_ENCODING);
        assert_eq!(boundary.immediate, Some(0));
        assert_eq!(
            boundary.semantics,
            BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness
        );
        assert!(boundary.diagnostic.contains("unsupported_no_exact_witness"));
        assert!(report.reason.contains("unchecked AArch64 syscall boundary"));
        assert!(report.reason.to_ascii_lowercase().contains("svc"));
        assert!(report.reason.contains("immediate #0"));
        assert!(report.reason.contains("unsupported_no_exact_witness"));
        assert!(report.reason.contains("proof-grade"));
    }

    #[test]
    fn machine_replay_rejects_replayed_x86_64_syscall_boundary_without_witness_semantics() {
        let expected = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            2,
            X86_64_SYSCALL_ENCODING,
            X86_64_SYSCALL_BYTES,
        );
        let observed = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            2,
            X86_64_SYSCALL_ENCODING,
            X86_64_SYSCALL_BYTES,
        );
        let witness = binary_witness_with_origin(expected);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(observed)],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(report.matched_instruction_trace);
        assert!(!report.matched_capability_evidence);
        assert!(report.capability_evidence.is_empty());
        assert_eq!(report.boundary_evidence.len(), 1);
        let boundary = &report.boundary_evidence[0];
        assert_eq!(boundary.kind, BinaryMachineReplayBoundaryKind::Syscall);
        assert_eq!(boundary.architecture, "x86_64");
        assert_eq!(boundary.instruction_address, 0x401010);
        assert_eq!(boundary.step, None);
        assert_eq!(boundary.instruction_bytes, X86_64_SYSCALL_BYTES);
        assert_eq!(boundary.opcode.to_ascii_uppercase(), "SYSCALL");
        assert_eq!(boundary.encoding, X86_64_SYSCALL_ENCODING);
        assert_eq!(
            boundary.semantics,
            BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness
        );
        assert!(boundary.diagnostic.contains("unchecked x86_64 syscall boundary"));
        assert!(report.reason.contains("unchecked x86_64 syscall boundary"));
        assert!(report.reason.to_ascii_lowercase().contains("syscall"));
        assert!(report.reason.contains("proof-grade"));
    }

    #[test]
    fn machine_replay_reports_structured_x86_64_trap_boundary_without_proof_grade() {
        let int3 = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            1,
            X86_64_INT3_ENCODING,
            X86_64_INT3_BYTES,
        );
        let witness = binary_witness_with_origin(int3.clone());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence { origin: int3, step: Some(7) }],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(report.matched_instruction_trace);
        assert_eq!(report.boundary_evidence.len(), 1);
        let boundary = &report.boundary_evidence[0];
        assert_eq!(boundary.kind, BinaryMachineReplayBoundaryKind::Trap);
        assert_eq!(boundary.architecture, "x86_64");
        assert_eq!(boundary.instruction_address, 0x401010);
        assert_eq!(boundary.step, Some(7));
        assert_eq!(boundary.instruction_bytes, X86_64_INT3_BYTES);
        assert_eq!(
            boundary.semantics,
            BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness
        );
        assert!(report.reason.contains("unchecked x86_64 trap boundary"));
        assert!(report.reason.contains("step 7"));
        assert!(report.reason.contains("proof-grade"));
    }

    #[test]
    fn machine_replay_reports_structured_aarch64_trap_boundary_without_proof_grade() {
        let brk = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_BRK1_ENCODING,
            AARCH64_BRK1_BYTES,
        );
        let witness = binary_witness_with_origin(brk.clone());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence { origin: brk, step: Some(3) }],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(report.matched_instruction_trace);
        assert_eq!(report.boundary_evidence.len(), 1);
        let boundary = &report.boundary_evidence[0];
        assert_eq!(boundary.kind, BinaryMachineReplayBoundaryKind::Trap);
        assert_eq!(boundary.architecture, "AArch64");
        assert_eq!(boundary.instruction_address, 0x401010);
        assert_eq!(boundary.step, Some(3));
        assert_eq!(boundary.instruction_bytes, AARCH64_BRK1_BYTES);
        assert_eq!(boundary.immediate, Some(1));
        assert_eq!(
            boundary.semantics,
            BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness
        );
        assert!(report.reason.contains("unchecked AArch64 trap boundary"));
        assert!(report.reason.contains("immediate #1"));
        assert!(report.reason.contains("step 3"));
    }

    #[test]
    fn machine_replay_rejects_mismatched_aarch64_exception_boundary_as_spurious() {
        let expected = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_SVC0_ENCODING,
            AARCH64_SVC0_BYTES,
        );
        let observed = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_SVC1_ENCODING,
            AARCH64_SVC1_BYTES,
        );
        let witness = binary_witness_with_origin(expected);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(observed)],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(!report.matched_instruction_trace);
        assert!(report.reason.contains("instruction trace"));
    }

    #[test]
    fn mock_machine_backend_failure_is_failed_not_replay_required_or_spurious() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_verification_condition(vc(&function))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::failed("mock", "emulator crashed"),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );
        let json = serde_json::to_value(&report).unwrap();

        assert_eq!(report.status, BinaryReplayStatus::Failed);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(!report.needs_machine_replay);
        assert_ne!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_ne!(report.status, BinaryReplayStatus::Spurious);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Failed);
        assert_eq!(json["status"], json!("failed"));
        assert_eq!(json["machine_replay"]["status"], json!("failed"));
        assert_eq!(
            report.machine_replay.expected_instruction_trace[0].instruction_address,
            0x401010
        );
    }

    #[test]
    fn solver_dispatch_sat_with_model_needs_machine_replay_by_default() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );

        let evidence = replay_solver_dispatch_counterexample(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
        );

        assert!(evidence.produced_witness());
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert_eq!(report.block_trace, vec![0]);
        assert_eq!(
            report.machine_replay.expected_instruction_trace[0].instruction_address,
            0x401010
        );
    }

    #[test]
    fn solver_dispatch_sat_with_matching_machine_replay_without_digest_stays_unreplayed() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_bound_instruction(0x401010),
        );
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert!(report.machine_replay.matched_instruction_trace);
        assert!(!report.machine_replay.matched_artifact_digest);
        assert!(report.machine_replay.reason.contains("artifact digest"));
    }

    #[test]
    fn solver_dispatch_sat_rejects_backend_trace_without_original_bytes() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_bound_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_encoding(
                    0x401010,
                    0x401000,
                    AARCH64_NOP_ENCODING,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert!(!report.machine_replay.matched_instruction_trace);
        assert!(report.machine_replay.reason.contains("exact observed instruction bytes"));
        assert!(report.machine_replay.reason.contains("proof-grade"));
    }

    #[test]
    fn solver_dispatch_sat_consumes_dispatch_digest_identity_for_machine_replay() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_bound_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence {
                    origin: instruction_origin_with_bytes(
                        0x401010,
                        0x401000,
                        4,
                        AARCH64_NOP_ENCODING,
                        AARCH64_NOP_BYTES,
                    ),
                    step: Some(0),
                }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(evidence.requirement_satisfied, "{}", evidence.reason);
        assert_eq!(evidence.replay, ReplayStatus::Replayed);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::Confirmed, "{}", report.reason);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert_eq!(
            report.normalized_witness.provenance.artifact_digest,
            Some(test_artifact_digest())
        );
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert_eq!(report.machine_replay.expected_artifact_digest, Some(test_artifact_digest()));
        assert_eq!(report.machine_replay.observed_artifact_digest, Some(test_artifact_digest()));
        assert!(report.machine_replay.matched_artifact_digest);
        assert_eq!(report.machine_replay.expected_selected_image, Some(test_selected_image()));
        assert_eq!(report.machine_replay.observed_selected_image, Some(test_selected_image()));
        assert!(report.machine_replay.matched_selected_image);
    }

    #[test]
    fn dispatch_requirement_uses_canonical_source_backprop_readiness_identity_gate() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input = BinaryReplayInput::new(traced_counterexample_with_instruction(0x401010))
            .with_verification_condition(vc(&function))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );
        let blocker = report
            .machine_replay
            .source_backprop_replay_blocker_reason()
            .expect("missing selected-image identity must block release-grade replay");
        let reason = report_requirement_failure_reason(
            "SAT counterexample requires exact machine witness replay before release",
            &report,
        );

        assert_eq!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert!(report.machine_replay.matched_instruction_trace);
        assert!(report.machine_replay.matched_artifact_digest);
        assert!(report.machine_replay.matched_selected_image);
        assert_eq!(report.machine_replay.expected_selected_image, None);
        assert_eq!(report.machine_replay.observed_selected_image, None);
        assert!(blocker.contains("expected selected-image digest/range"), "{blocker}");
        assert!(!dispatch_requirement_satisfied_by_report(
            BinaryReplayRequirement::ExactMachineWitnessReplay,
            &report
        ));
        assert!(reason.contains("expected selected-image digest/range"), "{reason}");
    }

    #[test]
    fn source_backprop_replay_ready_requires_byte_ranges_bound_to_machine_steps() {
        let origin = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let witness = source_backprop_replay_witness(vec![origin.clone()]);
        let stepped_backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence { origin: origin.clone(), step: Some(0) }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let stepped_report = replay_machine_witness(
            &witness,
            &BinaryMachineReplayConfig::default(),
            &stepped_backend,
        );

        assert_eq!(stepped_report.status, BinaryMachineReplayStatus::Replayed);
        assert!(stepped_report.source_backprop_replay_ready(), "{stepped_report:?}");
        assert_eq!(stepped_report.byte_range_evidence[0].step, Some(0));

        let mut address_only_report = stepped_report.clone();
        address_only_report.observed_instruction_trace[0].step = None;
        address_only_report.byte_range_evidence[0].step = None;
        let blocker = address_only_report
            .source_backprop_replay_blocker_reason()
            .expect("address-only instruction evidence must not be source-backprop ready");
        assert!(!address_only_report.source_backprop_replay_ready());
        assert!(blocker.contains("machine trace step"), "{blocker}");

        let address_only_backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(origin.clone())],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let source_report = replay_machine_witness(
            &witness,
            &BinaryMachineReplayConfig::default(),
            &address_only_backend,
        );

        assert_eq!(source_report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(source_report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(!source_report.source_backprop_replay_ready());
        assert_eq!(
            source_report.byte_range_diagnostics[0].kind,
            BinaryMachineReplayByteRangeDiagnosticKind::MissingOriginalByteRangeAttestation
        );
        assert_eq!(source_report.byte_range_evidence[0].step, None);
        assert!(source_report.reason.contains("machine trace step binding"));

        let mut exploratory_witness = binary_witness_with_origin(origin);
        exploratory_witness.provenance.selected_image = Some(test_selected_image());
        let exploratory_report = replay_machine_witness(
            &exploratory_witness,
            &BinaryMachineReplayConfig::default(),
            &address_only_backend,
        );

        assert_eq!(exploratory_report.status, BinaryMachineReplayStatus::Replayed);
        assert_eq!(exploratory_report.trust_types_status, ReplayStatus::Replayed);
        assert!(exploratory_report.matched_instruction_trace);
        assert!(exploratory_report.matched_selected_image);
        assert!(!exploratory_report.source_backprop_replay_ready());
        let exploratory_blocker = exploratory_report
            .source_backprop_replay_blocker_reason()
            .expect("exploratory replay must not imply source-backprop readiness");
        assert!(exploratory_blocker.contains("machine trace step"), "{exploratory_blocker}");
    }

    #[test]
    fn source_backprop_replay_report_json_carries_exact_identity_and_capability_evidence() {
        let branch = instruction_origin_with_bytes(
            0x401000,
            0x401000,
            4,
            AARCH64_B_PLUS_8_ENCODING,
            AARCH64_B_PLUS_8_BYTES,
        );
        let target = instruction_origin_with_bytes(
            0x401008,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let witness = source_backprop_replay_witness(vec![branch.clone(), target.clone()]);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![
                    BinaryMachineInstructionEvidence { origin: branch.clone(), step: Some(0) },
                    BinaryMachineInstructionEvidence { origin: target.clone(), step: Some(1) },
                ],
            )
            .with_capability_evidence(vec![
                BinaryMachineReplayCapabilityEvidence::new(
                    BinaryMachineReplayCapability::DirectBranch,
                    "AArch64",
                    0x401000,
                    "decoded direct branch target validated against following trace step",
                )
                .with_step(Some(0))
                .with_instruction_bytes(AARCH64_B_PLUS_8_BYTES),
            ])
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);
        let json = serde_json::to_value(&report).expect("serialize machine replay report");

        assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
        assert!(report.source_backprop_replay_ready(), "{:?}", report);
        assert_eq!(report.source_backprop_replay_blocker_reason(), None);
        assert!(report.matched_instruction_trace);
        assert!(report.matched_artifact_digest);
        assert!(report.matched_selected_image);
        assert!(report.matched_capability_evidence);
        assert_eq!(report.byte_range_evidence.len(), 2);
        assert!(report.byte_range_diagnostics.is_empty());
        assert!(report.boundary_evidence.is_empty());
        assert_eq!(report.expected_instruction_trace, vec![branch.clone(), target.clone()]);
        assert_eq!(report.observed_instruction_trace.len(), 2);

        assert_eq!(json["status"], json!("replayed"));
        assert_eq!(json["trust_types_status"], json!("replayed"));
        assert_eq!(json["matched_instruction_trace"], json!(true));
        assert_eq!(json["matched_artifact_digest"], json!(true));
        assert_eq!(json["matched_selected_image"], json!(true));
        assert_eq!(json["matched_capability_evidence"], json!(true));
        assert_eq!(json["byte_range_evidence"][0]["instruction_address"], json!(0x401000));
        assert_eq!(json["byte_range_evidence"][0]["file_offset"], json!(0));
        assert_eq!(json["byte_range_evidence"][1]["file_offset"], json!(8));
        assert!(json["boundary_evidence"].is_null());
        assert_eq!(json["expected_instruction_trace"][0]["instruction_address"], json!(0x401000));
        assert_eq!(
            json["observed_instruction_trace"][0]["origin"]["instruction_bytes"],
            json!(AARCH64_B_PLUS_8_BYTES)
        );
        assert_eq!(json["observed_instruction_trace"][0]["step"], json!(0));
        assert_eq!(json["capability_evidence"][0]["capability"], json!("direct_branch"));
        assert_eq!(json["capability_evidence"][0]["architecture"], json!("AArch64"));
        assert_eq!(json["capability_evidence"][0]["instruction_address"], json!(0x401000));
        assert_eq!(json["capability_evidence"][0]["step"], json!(0));
        assert_eq!(
            json["capability_evidence"][0]["instruction_bytes"],
            json!(AARCH64_B_PLUS_8_BYTES)
        );
    }

    #[test]
    fn source_backprop_replay_ready_requires_exact_identity_capabilities_and_clean_boundaries() {
        fn assert_blocked(report: &BinaryMachineReplayReport, needle: &str) {
            let blocker = report
                .source_backprop_replay_blocker_reason()
                .expect("report should be blocked from source backprop");
            assert!(!report.source_backprop_replay_ready());
            assert!(blocker.contains(needle), "{blocker}");
        }

        let branch = instruction_origin_with_bytes(
            0x401000,
            0x401000,
            4,
            AARCH64_B_PLUS_8_ENCODING,
            AARCH64_B_PLUS_8_BYTES,
        );
        let call = instruction_origin_with_bytes(
            0x401008,
            0x401000,
            4,
            AARCH64_BL_PLUS_8_ENCODING,
            AARCH64_BL_PLUS_8_BYTES,
        );
        let ret = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_RET_ENCODING,
            AARCH64_RET_BYTES,
        );
        let witness =
            source_backprop_replay_witness(vec![branch.clone(), call.clone(), ret.clone()]);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![
                    BinaryMachineInstructionEvidence { origin: branch.clone(), step: Some(0) },
                    BinaryMachineInstructionEvidence { origin: call.clone(), step: Some(1) },
                    BinaryMachineInstructionEvidence { origin: ret.clone(), step: Some(2) },
                ],
            )
            .with_capability_evidence(vec![
                BinaryMachineReplayCapabilityEvidence::new(
                    BinaryMachineReplayCapability::DirectBranch,
                    "AArch64",
                    0x401000,
                    "decoded direct branch target validated against following trace step",
                )
                .with_step(Some(0))
                .with_instruction_bytes(AARCH64_B_PLUS_8_BYTES),
                BinaryMachineReplayCapabilityEvidence::new(
                    BinaryMachineReplayCapability::DirectCall,
                    "AArch64",
                    0x401008,
                    "decoded direct call target and return context validated",
                )
                .with_step(Some(1))
                .with_instruction_bytes(AARCH64_BL_PLUS_8_BYTES),
                BinaryMachineReplayCapabilityEvidence::new(
                    BinaryMachineReplayCapability::Return,
                    "AArch64",
                    0x401010,
                    "decoded return target validated from call context",
                )
                .with_step(Some(2))
                .with_instruction_bytes(AARCH64_RET_BYTES),
            ])
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

        assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
        assert!(report.source_backprop_replay_ready(), "{:?}", report);
        assert!(report.matched_instruction_trace);
        assert_eq!(report.expected_artifact_digest, Some(test_artifact_digest()));
        assert_eq!(report.observed_artifact_digest, Some(test_artifact_digest()));
        assert!(report.matched_artifact_digest);
        assert_eq!(report.expected_selected_image, Some(test_selected_image()));
        assert_eq!(report.observed_selected_image, Some(test_selected_image()));
        assert!(report.matched_selected_image);
        assert!(report.matched_capability_evidence);
        assert_eq!(report.capability_evidence.len(), 3);
        assert!(report.boundary_evidence.is_empty());

        let mut mismatched_trace = report.clone();
        mismatched_trace.matched_instruction_trace = false;
        assert_blocked(&mismatched_trace, "instruction trace");

        let mut missing_expected_artifact = report.clone();
        missing_expected_artifact.expected_artifact_digest = None;
        assert_blocked(&missing_expected_artifact, "root binary artifact digest");

        let mut missing_observed_artifact = report.clone();
        missing_observed_artifact.observed_artifact_digest = None;
        assert_blocked(&missing_observed_artifact, "root binary artifact digest");

        let mut missing_expected_selected_image = report.clone();
        missing_expected_selected_image.expected_selected_image = None;
        assert_blocked(&missing_expected_selected_image, "selected-image digest/range");

        let mut missing_observed_selected_image = report.clone();
        missing_observed_selected_image.observed_selected_image = None;
        assert_blocked(&missing_observed_selected_image, "selected-image digest/range");

        for capability in [
            BinaryMachineReplayCapability::DirectBranch,
            BinaryMachineReplayCapability::DirectCall,
            BinaryMachineReplayCapability::Return,
        ] {
            let mut missing_capability = report.clone();
            missing_capability
                .capability_evidence
                .retain(|evidence| evidence.capability != capability);
            assert_blocked(&missing_capability, &capability.to_string());
        }

        let mut unchecked_boundary = report.clone();
        unchecked_boundary.boundary_evidence.push(BinaryMachineReplayBoundaryEvidence {
            kind: BinaryMachineReplayBoundaryKind::Trap,
            architecture: "AArch64".to_owned(),
            instruction_address: 0x401018,
            step: Some(3),
            instruction_bytes: AARCH64_BRK1_BYTES.to_vec(),
            opcode: "BRK".to_owned(),
            encoding: AARCH64_BRK1_ENCODING,
            immediate: Some(1),
            semantics: BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness,
            diagnostic: "unchecked AArch64 trap boundary".to_owned(),
        });
        assert_blocked(&unchecked_boundary, "unchecked AArch64 trap boundary");
    }

    #[test]
    fn source_backprop_replay_report_blocks_when_capability_evidence_is_lost() {
        let branch = instruction_origin_with_bytes(
            0x401000,
            0x401000,
            4,
            AARCH64_B_PLUS_8_ENCODING,
            AARCH64_B_PLUS_8_BYTES,
        );
        let target = instruction_origin_with_bytes(
            0x401008,
            0x401000,
            4,
            AARCH64_NOP_ENCODING,
            AARCH64_NOP_BYTES,
        );
        let witness = source_backprop_replay_witness(vec![branch.clone(), target.clone()]);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![
                    BinaryMachineInstructionEvidence { origin: branch, step: Some(0) },
                    BinaryMachineInstructionEvidence { origin: target, step: Some(1) },
                ],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);
        let blocker = report
            .source_backprop_replay_blocker_reason()
            .expect("missing capability should block source backprop");

        assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(!report.source_backprop_replay_ready());
        assert!(report.matched_instruction_trace);
        assert!(report.matched_artifact_digest);
        assert!(report.matched_selected_image);
        assert!(!report.matched_capability_evidence);
        assert!(report.capability_evidence.is_empty());
        assert!(blocker.contains("capability evidence"), "{blocker}");
        assert!(blocker.contains("source-backprop blocked"), "{blocker}");
    }

    #[test]
    fn source_backprop_replay_report_preserves_boundary_evidence_as_blocker() {
        let svc = instruction_origin_with_bytes(
            0x401010,
            0x401000,
            4,
            AARCH64_SVC0_ENCODING,
            AARCH64_SVC0_BYTES,
        );
        let witness = source_backprop_replay_witness(vec![svc.clone()]);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence { origin: svc, step: Some(0) }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);
        let json = serde_json::to_value(&report).expect("serialize machine replay report");
        let blocker = report
            .source_backprop_replay_blocker_reason()
            .expect("unchecked boundary should block source backprop");

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
        assert!(!report.source_backprop_replay_ready());
        assert_eq!(report.boundary_evidence.len(), 1);
        assert_eq!(report.boundary_evidence[0].kind, BinaryMachineReplayBoundaryKind::Syscall);
        assert_eq!(report.boundary_evidence[0].step, Some(0));
        assert!(blocker.contains("unchecked AArch64 syscall boundary"), "{blocker}");
        assert_eq!(json["boundary_evidence"][0]["kind"], json!("syscall"));
        assert_eq!(json["boundary_evidence"][0]["step"], json!(0));
        assert_eq!(
            json["boundary_evidence"][0]["semantics"],
            json!("unsupported_no_exact_witness")
        );
        assert!(
            json["boundary_evidence"][0]["diagnostic"]
                .as_str()
                .expect("boundary diagnostic")
                .contains("cannot satisfy proof-grade evidence")
        );
    }

    #[test]
    fn solver_dispatch_sat_rejects_unbound_model_trace_after_machine_attestation() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence {
                    origin: instruction_origin_with_bytes(
                        0x401010,
                        0x401000,
                        4,
                        AARCH64_NOP_ENCODING,
                        AARCH64_NOP_BYTES,
                    ),
                    step: Some(0),
                }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert!(report.machine_replay.matched_instruction_trace);
        assert!(report.machine_replay.matched_artifact_digest);
        assert!(report.machine_replay.matched_selected_image);
        assert!(report.machine_replay.reason.contains("model-to-witness reconstruction"));
        assert!(report.machine_replay.reason.contains("per-step model assignment bindings"));
        assert_ne!(report.trust_types_status, ReplayStatus::Replayed);
    }

    #[test]
    fn machine_replay_accepts_explicit_binding_map_for_ssa_renamed_trace() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input =
            BinaryReplayInput::new(traced_counterexample_with_ssa_renamed_instruction(0x401010))
                .with_verification_condition(vc(&function))
                .with_instruction_provenance(vec![instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                )])
                .with_artifact_digest(test_artifact_digest())
                .with_selected_image(test_selected_image())
                .require_selected_image_identity()
                .with_binding(BinaryWitnessBinding::new("_local0", "_local0!7").at_trace_step(0))
                .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence {
                    origin: instruction_origin_with_bytes(
                        0x401010,
                        0x401000,
                        4,
                        AARCH64_NOP_ENCODING,
                        AARCH64_NOP_BYTES,
                    ),
                    step: Some(0),
                }],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::Confirmed);
        assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
        assert!(!report.needs_machine_replay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Replayed);
        assert!(report.machine_replay.matched_instruction_trace);
        assert!(report.machine_replay.matched_artifact_digest);
        assert!(report.machine_replay.matched_selected_image);
        assert_eq!(
            report.normalized_witness.provenance.binding_map,
            vec![BinaryWitnessBinding::new("_local0", "_local0!7").at_trace_step(0)]
        );

        let json = serde_json::to_value(&report).expect("serialize replay report");
        assert_eq!(json["status"], json!("confirmed"));
        assert_eq!(json["trust_types_status"], json!("replayed"));
        assert_eq!(
            json["normalized_witness"]["provenance"]["binding_map"],
            json!([{
                "model_name": "_local0",
                "trace_name": "_local0!7",
                "trace_step": 0
            }])
        );
    }

    #[test]
    fn machine_replay_diagnoses_ssa_renamed_trace_without_binding_map() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let input =
            BinaryReplayInput::new(traced_counterexample_with_ssa_renamed_instruction(0x401010))
                .with_verification_condition(vc(&function))
                .with_instruction_provenance(vec![instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                )])
                .with_artifact_digest(test_artifact_digest())
                .with_selected_image(test_selected_image())
                .require_selected_image_identity()
                .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert!(report.machine_replay.matched_instruction_trace);
        assert!(report.machine_replay.matched_artifact_digest);
        assert!(report.machine_replay.matched_selected_image);
        assert!(report.machine_replay.reason.contains("SSA-renamed"));
        assert!(report.machine_replay.reason.contains("_local0!7"));
        assert!(report.machine_replay.reason.contains("binding_map"));
    }

    #[test]
    fn machine_replay_rejects_binding_map_with_mismatched_trace_value() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut trace_assignments = BTreeMap::new();
        trace_assignments.insert("_local0!7".to_owned(), "2".to_owned());
        let counterexample = Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![TraceStep {
                step: 0,
                assignments: trace_assignments,
                program_point: Some("bb0@0x401010".to_owned()),
            }]),
        );
        let input = BinaryReplayInput::new(counterexample)
            .with_verification_condition(vc(&function))
            .with_instruction_provenance(vec![instruction_origin_with_bytes(
                0x401010,
                0x401000,
                4,
                AARCH64_NOP_ENCODING,
                AARCH64_NOP_BYTES,
            )])
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image())
            .require_selected_image_identity()
            .with_binding(BinaryWitnessBinding::new("_local0", "_local0!7").at_trace_step(0))
            .with_expectation(BinaryReplayExpectation::Terminates);
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let report = replay_binary_counterexample_with_machine_replay(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );
        let json = serde_json::to_value(&report).expect("serialize replay report");

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert!(report.machine_replay.reason.contains("binding_map maps model assignment"));
        assert!(report.machine_replay.reason.contains("values differ"));
        assert_eq!(
            json["normalized_witness"]["provenance"]["binding_map"],
            json!([{
                "model_name": "_local0",
                "trace_name": "_local0!7",
                "trace_step": 0
            }])
        );
        assert!(
            json["machine_replay"]["reason"]
                .as_str()
                .expect("machine replay reason")
                .contains("values differ")
        );
    }

    #[test]
    fn solver_dispatch_evidence_surfaces_missing_ssa_binding_map_reason() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_ssa_renamed_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );
        let json = serde_json::to_value(&evidence).expect("serialize replay evidence");

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        assert!(evidence.needs_machine_witness_replay());
        assert!(evidence.reason.contains("binding_map"));
        assert!(evidence.reason.contains("SSA-renamed"));
        assert!(evidence.reason.contains("_local0!7"));
        assert!(json["reason"].as_str().expect("evidence reason").contains("binding_map"));
        assert!(
            json["replay_report"]["machine_replay"]["reason"]
                .as_str()
                .expect("machine replay reason")
                .contains("binding_map")
        );
    }

    #[test]
    fn solver_dispatch_sat_rejects_mismatched_dispatch_digest_identity() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(other_test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::Spurious);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::Spurious);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.machine_replay.expected_artifact_digest, Some(test_artifact_digest()));
        assert_eq!(
            report.machine_replay.observed_artifact_digest,
            Some(other_test_artifact_digest())
        );
        assert!(!report.machine_replay.matched_artifact_digest);
        assert!(report.machine_replay.reason.contains("artifact digest did not match"));
    }

    #[test]
    fn solver_dispatch_sat_rejects_missing_selected_image_identity_for_proof_grade_replay() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(root_only_test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.expected_selected_image, None);
        assert_eq!(report.machine_replay.observed_selected_image, Some(test_selected_image()));
        assert!(!report.machine_replay.matched_selected_image);
        assert!(report.machine_replay.reason.contains("selected-image digest/range"));
        assert!(report.machine_replay.reason.contains("absent or ambiguous"));
    }

    #[test]
    fn solver_dispatch_sat_rejects_missing_backend_selected_image_identity() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
        assert_eq!(report.machine_replay.expected_selected_image, Some(test_selected_image()));
        assert_eq!(report.machine_replay.observed_selected_image, None);
        assert!(!report.machine_replay.matched_selected_image);
        assert!(report.machine_replay.reason.contains("replay evidence omitted selected-image"));
    }

    #[test]
    fn solver_dispatch_sat_rejects_mismatched_selected_image_identity() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(other_test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::Spurious);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.status, BinaryReplayStatus::Spurious);
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.machine_replay.expected_selected_image, Some(test_selected_image()));
        assert_eq!(
            report.machine_replay.observed_selected_image,
            Some(other_test_selected_image())
        );
        assert!(report.machine_replay.matched_artifact_digest);
        assert!(!report.machine_replay.matched_selected_image);
        assert!(report.machine_replay.reason.contains("selected-image digest/range did not match"));
    }

    #[test]
    fn solver_dispatch_sat_rejects_mismatched_selected_image_range() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let mut dispatch = sat_dispatch_with_counterexample(
            &function,
            traced_counterexample_with_instruction(0x401010),
        );
        dispatch.binary_artifact_digest_identity = Some(test_artifact_digest_identity());
        let backend = MockMachineReplayBackend {
            result: BinaryMachineReplayResult::replayed(
                "mock",
                vec![BinaryMachineInstructionEvidence::new(instruction_origin_with_bytes(
                    0x401010,
                    0x401000,
                    4,
                    AARCH64_NOP_ENCODING,
                    AARCH64_NOP_BYTES,
                ))],
            )
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(offset_test_selected_image()),
        };

        let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
            &BinaryMachineReplayConfig::default(),
            &backend,
        );

        assert!(evidence.produced_witness());
        assert!(!evidence.requirement_satisfied);
        assert_eq!(evidence.replay, ReplayStatus::Spurious);
        let report = evidence.replay_report.as_ref().expect("SAT model should produce report");
        assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Spurious);
        assert_eq!(report.machine_replay.expected_selected_image, Some(test_selected_image()));
        assert_eq!(
            report.machine_replay.observed_selected_image,
            Some(offset_test_selected_image())
        );
        assert!(report.machine_replay.matched_artifact_digest);
        assert!(!report.machine_replay.matched_selected_image);
        assert!(report.machine_replay.reason.contains("selected-image digest/range did not match"));
    }

    #[test]
    fn solver_dispatch_unsat_produces_no_witness() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        let dispatch = unsat_dispatch(&function);

        let evidence = replay_solver_dispatch_counterexample(
            &dispatch,
            Some(&function),
            &BinaryReplayConfig::default(),
        );

        assert!(!evidence.produced_witness());
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        assert!(evidence.replay_report.is_none());
        assert!(evidence.reason.contains("UNSAT"));
    }

    #[test]
    fn normalizes_register_memory_local_and_instruction_witness_records() {
        let mut function = return_function();
        function.span = SourceSpan::binary_address(0x401000);
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::unit_ty(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("RAX".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("tmp".into()) },
        ];

        let mut trace_assignments = BTreeMap::new();
        trace_assignments.insert("%rcx".to_owned(), "0x2a".to_owned());
        trace_assignments.insert("memory:0x2000".to_owned(), "255".to_owned());
        let trace = CounterexampleTrace::new(vec![TraceStep {
            step: 0,
            assignments: trace_assignments,
            program_point: Some("bb0@0x401010".into()),
        }]);
        let input = BinaryReplayInput::new(Counterexample::with_trace(
            vec![
                ("_local1".into(), CounterexampleValue::Uint(42)),
                ("mem[0x1000:4]".into(), CounterexampleValue::Uint(7)),
                ("tmp".into(), CounterexampleValue::Int(-1)),
            ],
            trace,
        ));

        let witness = normalize_lifted_binary_witness(&function, &input);

        assert_eq!(witness.function.as_deref(), Some("binary::lifted_test"));
        assert_eq!(
            witness.origin.as_ref().map(|origin| origin.instruction_address),
            Some(0x401000)
        );
        assert_eq!(witness.raw_model_assignments, 3);
        assert_eq!(witness.raw_trace_steps, 1);
        assert!(witness.has_execution_trace);

        let rax = witness.records.iter().find(|record| record.raw_name == "_local1").unwrap();
        assert!(matches!(
            &rax.subject,
            BinaryFactSubject::Register { function, register }
                if function == "binary::lifted_test" && register == "RAX"
        ));
        assert!(matches!(
            &rax.storage,
            BinaryStorageLocation::Register { name, bit_width }
                if name == "RAX" && *bit_width == Some(64)
        ));
        assert_eq!(rax.local_index, Some(1));

        let memory =
            witness.records.iter().find(|record| record.raw_name == "mem[0x1000:4]").unwrap();
        assert!(matches!(
            &memory.storage,
            BinaryStorageLocation::Memory { address, size_bytes }
                if *address == Formula::UInt(0x1000) && *size_bytes == Some(4)
        ));

        let local = witness.records.iter().find(|record| record.raw_name == "tmp").unwrap();
        assert!(matches!(
            &local.subject,
            BinaryFactSubject::Local { function, name }
                if function == "binary::lifted_test" && name == "tmp"
        ));
        assert_eq!(local.local_index, Some(2));

        let trace_point = witness.trace[0].program_point.as_ref().unwrap();
        assert_eq!(trace_point.block, Some(0));
        assert_eq!(
            trace_point.origin.as_ref().map(|origin| origin.instruction_address),
            Some(0x401010)
        );
        assert_eq!(
            trace_point.origin.as_ref().and_then(|origin| origin.function_entry),
            Some(0x401000)
        );
        let rcx = witness
            .trace
            .first()
            .unwrap()
            .assignments
            .iter()
            .find(|record| record.raw_name == "%rcx")
            .unwrap();
        assert!(matches!(
            &rcx.storage,
            BinaryStorageLocation::Register { name, bit_width }
                if name == "RCX" && bit_width.is_none()
        ));
        assert_eq!(rcx.value.typed, Some(CounterexampleValue::Uint(0x2a)));
    }

    #[test]
    fn lifted_trace_without_original_vc_is_not_confirmed() {
        let function = return_function();
        let input = BinaryReplayInput::new(traced_counterexample(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            &[0],
        ))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.needs_machine_replay);
        assert!(report.reason.contains("original verification condition"));
        assert!(report.block_trace.is_empty());
    }

    #[test]
    fn lifted_trace_mismatch_is_spurious() {
        let function = branch_function();
        let input = BinaryReplayInput::new(traced_counterexample(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            &[0, 2],
        ))
        .with_verification_condition(vc(&function))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::Spurious);
        assert_eq!(report.status.to_string(), "spurious");
        assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
        assert!(!report.needs_machine_replay);
        assert_eq!(report.block_trace, vec![0, 1]);
        assert_eq!(report.witness_trace, vec![0, 2]);
    }

    #[test]
    fn binary_origin_requires_machine_replay() {
        let input = BinaryReplayInput::new(Counterexample::new(vec![(
            "rax".into(),
            CounterexampleValue::Int(7),
        )]));

        let report = replay_binary_counterexample(
            BinaryReplayTarget::binary_origin(BinaryOrigin::new(0x401000)),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
        assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
        assert!(report.needs_machine_replay);
        assert_eq!(report.status.to_string(), "needs_machine_replay");
        assert!(report.reason.contains("0x401000"));
        assert_eq!(
            report.normalized_witness.origin.as_ref().map(|origin| origin.instruction_address),
            Some(0x401000)
        );
        assert!(matches!(
            &report.normalized_witness.records[0].subject,
            BinaryFactSubject::Register { register, .. } if register == "RAX"
        ));
    }

    #[test]
    fn unsupported_float_model_value_is_not_replayed() {
        let function = return_function();
        let input = BinaryReplayInput::new(traced_counterexample(
            vec![("_local0".into(), CounterexampleValue::Float(1.5))],
            &[0],
        ))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::Unsupported);
        assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    }

    #[test]
    fn symbolic_operand_needs_machine_replay() {
        let function = function(vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Symbolic(Formula::Var("rax".into(), Sort::Int)),
                    Operand::Constant(ConstValue::Int(1)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        }]);
        let input = BinaryReplayInput::new(traced_counterexample(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            &[0],
        ))
        .with_expectation(BinaryReplayExpectation::Terminates);

        let report = replay_binary_counterexample(
            BinaryReplayTarget::lifted(&function),
            &input,
            &BinaryReplayConfig::default(),
        );

        assert_eq!(report.status, BinaryReplayStatus::NeedsMachineReplay);
    }

    #[test]
    fn minimization_without_trace_is_unsupported() {
        let input = BinaryReplayInput::new(Counterexample::new(vec![(
            "_local0".into(),
            CounterexampleValue::Int(1),
        )]));

        let result = minimize_binary_counterexample(&input, &BinaryMinimizationConfig::default());

        assert_eq!(result.status, BinaryMinimizationStatus::Unsupported);
        assert_eq!(result.removed_trace_steps, 0);
        assert_eq!(result.removed_assignments, 0);
        assert_eq!(result.metadata.original_trace_steps, None);
        assert_eq!(result.metadata.minimized_trace_steps, None);
        assert_eq!(result.metadata.original_model_assignments, 1);
        assert_eq!(result.metadata.minimized_model_assignments, 1);
        assert!(result.metadata.assignments_preserved);
    }

    #[test]
    fn minimization_removes_only_consecutive_duplicate_trace_steps() {
        let mut assignments = BTreeMap::new();
        assignments.insert("_local0".to_owned(), "1".to_owned());
        let trace = CounterexampleTrace::new(vec![
            TraceStep {
                step: 0,
                assignments: assignments.clone(),
                program_point: Some("bb0".into()),
            },
            TraceStep {
                step: 1,
                assignments: assignments.clone(),
                program_point: Some("bb0".into()),
            },
            TraceStep { step: 2, assignments, program_point: Some("bb1".into()) },
        ]);
        let cex = Counterexample::with_trace(
            vec![("_local0".into(), CounterexampleValue::Int(1))],
            trace,
        );
        let input = BinaryReplayInput::new(cex);

        let result = minimize_binary_counterexample(&input, &BinaryMinimizationConfig::default());

        assert_eq!(result.status, BinaryMinimizationStatus::Minimized);
        assert_eq!(result.removed_trace_steps, 1);
        assert_eq!(result.removed_assignments, 0);
        assert_eq!(result.metadata.original_trace_steps, Some(3));
        assert_eq!(result.metadata.minimized_trace_steps, Some(2));
        assert_eq!(result.metadata.original_model_assignments, 1);
        assert_eq!(result.metadata.minimized_model_assignments, 1);
        assert_eq!(result.metadata.removed_trace_step_indices, vec![1]);
        assert!(result.metadata.assignments_preserved);
        let minimized_trace = result.counterexample.trace.expect("trace should remain");
        assert_eq!(minimized_trace.steps.len(), 2);
        assert_eq!(result.counterexample.assignments.len(), 1);
    }
}
