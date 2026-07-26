// trust-types/formula/vc_kind: Verification condition kind classification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::ProofLevel;
use super::temporal::{FairnessConstraint, LivenessProperty};
use crate::Symbol;
use crate::model::{BinOp, Ty};

/// Hardened obligation categories for OS/path, byte/text, error, panic,
/// compatibility, process semantics, unsafe/FFI, and trust-domain boundary checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum HardenedVcCategory {
    RawPathApi,
    PathIdentity,
    PermissionChange,
    PermissionCreate,
    PermissionWindow,
    Utf8Reject,
    ByteLoss,
    ErrorDiscard,
    PanicBoundary,
    CompatObservable,
    ProcessSemantics,
    TrustDomain,
    TrustDomainOrder,
    UnsafeOperation,
    FfiBoundary,
    Unknown(Symbol),
}

impl HardenedVcCategory {
    #[must_use]
    pub fn as_tag(self) -> &'static str {
        match self {
            HardenedVcCategory::RawPathApi => "raw_path_api",
            HardenedVcCategory::PathIdentity => "path_identity",
            HardenedVcCategory::PermissionChange => "permission_change",
            HardenedVcCategory::PermissionCreate => "permission_create",
            HardenedVcCategory::PermissionWindow => "permission_window",
            HardenedVcCategory::Utf8Reject => "utf8_reject",
            HardenedVcCategory::ByteLoss => "byte_loss",
            HardenedVcCategory::ErrorDiscard => "error_discard",
            HardenedVcCategory::PanicBoundary => "panic_boundary",
            HardenedVcCategory::CompatObservable => "compat_observable",
            HardenedVcCategory::ProcessSemantics => "process_semantics",
            HardenedVcCategory::TrustDomain => "trust_domain",
            HardenedVcCategory::TrustDomainOrder => "trust_domain_order",
            HardenedVcCategory::UnsafeOperation => "unsafe_operation",
            HardenedVcCategory::FfiBoundary => "ffi_boundary",
            HardenedVcCategory::Unknown(tag) => tag.as_str(),
        }
    }

    #[must_use]
    pub fn from_tag(tag: &str) -> Option<Self> {
        Some(match tag {
            "raw_path_api" => HardenedVcCategory::RawPathApi,
            "path_identity" => HardenedVcCategory::PathIdentity,
            "permission_change" => HardenedVcCategory::PermissionChange,
            "permission_create" => HardenedVcCategory::PermissionCreate,
            "permission_window" => HardenedVcCategory::PermissionWindow,
            "utf8_reject" => HardenedVcCategory::Utf8Reject,
            "byte_loss" => HardenedVcCategory::ByteLoss,
            "error_discard" => HardenedVcCategory::ErrorDiscard,
            "panic_boundary" => HardenedVcCategory::PanicBoundary,
            "compat_observable" => HardenedVcCategory::CompatObservable,
            "process_semantics" => HardenedVcCategory::ProcessSemantics,
            "trust_domain" => HardenedVcCategory::TrustDomain,
            "trust_domain_order" => HardenedVcCategory::TrustDomainOrder,
            "unsafe_operation" => HardenedVcCategory::UnsafeOperation,
            "ffi_boundary" => HardenedVcCategory::FfiBoundary,
            "" => return None,
            other => HardenedVcCategory::unknown_tag(other),
        })
    }

    #[must_use]
    pub fn unknown_tag(tag: &str) -> Self {
        HardenedVcCategory::Unknown(Symbol::intern(tag))
    }

    #[must_use]
    pub fn is_unknown(self) -> bool {
        matches!(self, HardenedVcCategory::Unknown(_))
    }
}

impl Serialize for HardenedVcCategory {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_tag())
    }
}

impl<'de> Deserialize<'de> for HardenedVcCategory {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let tag = String::deserialize(deserializer)?;
        Ok(HardenedVcCategory::from_tag(&tag)
            .unwrap_or_else(|| HardenedVcCategory::unknown_tag(&tag)))
    }
}

/// What kind of property a VC checks.
///
/// Each variant maps to a specific safety or functional property. The
/// `proof_level()` method classifies VcKinds into `ProofLevel` tiers
/// used by the router for backend selection.
///
/// # Examples
///
/// ```
/// use trust_types::{VcKind, ProofLevel};
///
/// // L0Safety kinds
/// assert_eq!(VcKind::DivisionByZero.proof_level(), ProofLevel::L0Safety);
/// assert_eq!(VcKind::IndexOutOfBounds.proof_level(), ProofLevel::L0Safety);
///
/// // L1Functional kinds
/// assert_eq!(VcKind::Postcondition.proof_level(), ProofLevel::L1Functional);
///
/// // Display shows a human-readable description
/// assert_eq!(format!("{}", VcKind::DivisionByZero), "division by zero");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcKind {
    ArithmeticOverflow {
        op: BinOp,
        operand_tys: (Ty, Ty),
    },
    ShiftOverflow {
        op: BinOp,
        operand_ty: Ty,
        shift_ty: Ty,
    },
    DivisionByZero,
    RemainderByZero,
    IndexOutOfBounds,
    SliceBoundsCheck,
    Assertion {
        message: String,
    },
    Precondition {
        callee: String,
    },
    Postcondition,
    CastOverflow {
        from_ty: Ty,
        to_ty: Ty,
    },
    NegationOverflow {
        ty: Ty,
    },
    Unreachable,
    /// TrustIr preserved valid rustc MIR whose precise semantics are not yet
    /// implemented. This must report as unknown/unsupported, never as proved.
    UnsupportedMir {
        kind: String,
        detail: String,
    },
    // State machine properties (ty)
    DeadState {
        state: String,
    },
    Deadlock,
    Temporal {
        property: String,
        /// Optional state-machine model the temporal backend (`ty`) checks the
        /// property against. When present, `TyBackend::extract_state_machine`
        /// converts it to a `trust_temporal::StateMachine` and model-checks the
        /// property; when absent, the VC stays fail-closed (no machine to check).
        /// Carrying it on this variant (rather than a `VerificationCondition`
        /// field) keeps the change to the few `Temporal` construction sites.
        #[serde(default)]
        machine: Option<crate::formula::contracts::StateMachineMetadata>,
    },
    // Trust: Liveness and fairness properties
    Liveness {
        property: LivenessProperty,
        /// Optional state-machine model, mirroring `Temporal::machine`: when
        /// present, the temporal backend (`ty`) checks the liveness property
        /// against it (SCC/lasso analysis); when absent, the VC stays
        /// fail-closed (no machine to check).
        #[serde(default)]
        machine: Option<crate::formula::contracts::StateMachineMetadata>,
    },
    Fairness {
        constraint: FairnessConstraint,
    },
    TaintViolation {
        source_label: String,
        sink_kind: String,
        path_length: usize,
    },
    RefinementViolation {
        spec_file: String,
        action: String,
    },
    // External dependency resilience
    ResilienceViolation {
        service: String,
        failure_mode: String,
        reason: String,
    },
    // Trust: Cross-service protocol composition
    ProtocolViolation {
        protocol: String,
        violation: String,
    },
    // Termination checking via decreases clauses
    NonTermination {
        /// "loop" or "recursion"
        context: String,
        /// Which measure failed to decrease (e.g., "n", "len - i")
        measure: String,
    },
    // Data race and memory ordering verification
    /// Two threads access the same variable without happens-before ordering,
    /// and at least one access is a write.
    DataRace {
        /// The shared variable being accessed.
        variable: String,
        /// Thread ID of the first access.
        thread_a: String,
        /// Thread ID of the second access.
        thread_b: String,
    },
    /// An atomic access uses an ordering that is insufficient for correctness.
    InsufficientOrdering {
        /// The variable being accessed.
        variable: String,
        /// The ordering actually used (e.g., "Relaxed").
        actual: String,
        /// The minimum ordering required (e.g., "Acquire").
        required: String,
    },
    // Translation validation — compiled code refines source MIR semantics.
    /// Asserts that a post-optimization (or compiled) function refines the
    /// pre-optimization MIR. UNSAT means the transformation is correct.
    TranslationValidation {
        /// Name of the optimization pass (e.g., "constant_folding", "dce").
        pass: String,
        /// Which check category this VC covers.
        check: String,
    },
    // Floating-point operation verification conditions.
    /// Float division where divisor may be zero (produces +/-Inf per IEEE 754).
    FloatDivisionByZero,
    /// Float arithmetic that may overflow to infinity (+/-Inf).
    FloatOverflowToInfinity {
        op: BinOp,
        operand_ty: Ty,
    },
    // Rvalue safety VCs for Discriminant, Aggregate, Ref, and Len.
    /// Discriminant read on a place that does not hold an enum/ADT type.
    InvalidDiscriminant {
        /// Human-readable name of the place whose discriminant was read.
        place_name: String,
    },
    /// Array aggregate constructed with a mismatched element count.
    AggregateArrayLengthMismatch {
        /// Expected number of elements from the array type.
        expected: usize,
        /// Actual number of operands provided.
        actual: usize,
    },
    // Unsafe code VC.
    /// Unsafe operation detected (raw pointer deref, transmute, FFI, etc.).
    UnsafeOperation {
        desc: String,
    },
    /// Binary stack write may overwrite the saved return address.
    SavedReturnAddressOverwrite {
        /// Number of bytes written by the memory access.
        access_width_bytes: u32,
        /// Human-readable stack return slot being protected.
        slot: String,
    },
    /// Binary or FFI printf-family call may use attacker-controlled format text.
    FormatStringViolation {
        /// Name of the printf-family callee.
        callee: String,
        /// Human-readable evidence for the unsafe format argument.
        evidence: String,
    },
    /// Binary indirect control-flow target is unresolved and therefore may be attacker-controlled.
    TaintedIndirectBranch {
        /// Control-flow sink, such as "indirect_branch" or "indirect_call".
        sink_kind: String,
        /// Human-readable target expression or unknown target marker.
        target: String,
        /// Evidence explaining why this is fail-closed rather than proof-grade.
        evidence: String,
    },
    /// Recovered binary ABI metadata contradicts proof-grade storage metadata.
    BinaryAbiContradiction {
        /// Human-readable ABI/storage fact that is contradictory.
        fact: String,
        /// Human-readable evidence for the contradiction.
        evidence: String,
    },
    /// Binary copy/copy-like sink may copy more bytes than the destination can hold.
    BinaryCopySinkLengthViolation {
        /// Name of the recovered copy sink, such as "memcpy" or "strncpy".
        callee: String,
        /// Description of the exact bad length evidence or missing proof facts.
        desc: String,
    },
    // FFI boundary verification with summary-based VCs.
    /// FFI call site where a summary-based contract was checked.
    FfiBoundaryViolation {
        /// Name of the extern callee (e.g., "malloc", "memcpy").
        callee: String,
        /// Description of the specific violation (null, range, alias, etc.).
        desc: String,
    },
    /// A raw bulk copy or pointer→slice construction
    /// (`ptr::copy[_nonoverlapping]`, `slice::from_raw_parts`) may read or write
    /// past the bounds of an allocation: the element/byte count is not provably
    /// `<=` the source (read) or destination (write) allocation size. Distinct
    /// from `IndexOutOfBounds`/`SliceBoundsCheck`, which cover *safe* indexing;
    /// this covers the unchecked raw-pointer count that the language does not
    /// guard. (Closes the gap where `from_raw_parts` only checked `len < 0`.)
    CopyBoundsViolation {
        /// The copy-like operation (e.g. "copy_nonoverlapping", "from_raw_parts").
        callee: String,
        /// Which side is unproven: "src" (read past source) or "dst" (write past destination).
        direction: String,
        /// Human-readable evidence: the bound that could not be discharged.
        detail: String,
    },
    /// A pointer/slice is derived from an allocation whose size can change
    /// *externally* — e.g. an `mmap`'d file another process can truncate, or a
    /// region a second thread can shrink — but the derived length was captured
    /// once and is not re-validated against the allocation's *live* size. A
    /// later access can then read past the valid region (SIGBUS on truncation,
    /// or an out-of-bounds read). The obligation: the captured length must be
    /// proven `<=` the live size at every use, or re-checked on each access.
    ExternallyMutableAllocationBounds {
        /// What kind of externally-mutable allocation (e.g. "mmap_file").
        allocation_kind: String,
        /// The size that may shrink out from under the derived view (e.g. "live_file_len").
        live_size: String,
        /// Human-readable detail / remediation hint.
        detail: String,
    },
    /// A bulk heap allocation (`Vec::with_capacity`/`Vec::reserve`/`<[T]>::resize`
    /// /`vec![_; n]`) is sized by a `count` that is not provably bounded — neither
    /// a constant, nor `<=` a value established by a reaching precondition/check,
    /// nor routed through a budget gateway whose over-budget branch returns
    /// *without* allocating. An adversarial or pathological `count` (e.g. an
    /// untrusted header field, or an unbounded loop-carried size) can then
    /// exhaust memory and OOM the process — an availability/DoS hazard — instead
    /// of failing closed. The obligation: `count` is provably `<= BOUND`, or the
    /// allocation site is dominated by a budget check whose failure path is the
    /// only reachable non-allocating action. This is a SAFETY invariant over the
    /// program text (where allocations sit in the CFG), NOT a termination/total-
    /// memory bound — the latter is undecidable in general. Closes the gap where
    /// `Solver::ensure_num_vars(n)` resized ~25 per-variable `Vec`s from an
    /// unbounded `n` (and computed `n * 2` with no overflow guard), letting a
    /// pathological query grow to 203 GB before the kernel killed it.
    UnboundedAllocation {
        /// The allocating operation (e.g. "Vec::with_capacity", "<[T]>::resize").
        callee: String,
        /// The size/count operand that is not provably bounded (e.g. "num_vars * 2").
        count: String,
        /// Human-readable evidence / remediation hint.
        detail: String,
    },
    // Typed ownership VcKind variants for trust_vc integration.
    /// Accessing memory after it has been freed (use-after-free).
    UseAfterFree,
    /// Freeing the same allocation twice (double-free).
    DoubleFree,
    /// Aliasing violation: &mut coexists with another &/&mut reference.
    AliasingViolation {
        /// true if the conflicting alias is &mut, false if shared &.
        mutable: bool,
    },
    /// Reference outlives its referent (dangling reference).
    LifetimeViolation,
    /// Non-Send type sent across thread boundary.
    SendViolation,
    /// Non-Sync type shared across threads.
    SyncViolation,
    // Functional correctness verification condition.
    /// The function produces an incorrect result (e.g., binary search returns
    /// wrong index on unsorted input). The `property` field describes the
    /// expected property (e.g., "result correctness"), and `context` carries
    /// domain-specific information (e.g., "binary_search: input not sorted").
    FunctionalCorrectness {
        /// High-level property being checked (e.g., "result_correctness").
        property: String,
        /// Domain context explaining the failure (e.g., "input array not sorted").
        context: String,
    },
    /// Hardened profile obligation for OS/path/byte/error/panic/unsafe/FFI/trust-domain
    /// boundary hazards. Older reports serialized these as
    /// `FunctionalCorrectness { property: "hardened::<category>", ... }`; use
    /// `hardened_category()` to classify both encodings.
    HardenedBoundary {
        category: HardenedVcCategory,
        callee: String,
        detail: String,
    },
    // trust-wp-style contract VcKinds for Horn clause lowering.
    /// Loop invariant initiation: the invariant holds on entry to the loop.
    LoopInvariantInitiation {
        /// The invariant expression that must hold at loop entry.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Loop invariant consecution: if the invariant holds before an iteration,
    /// it holds after the iteration (inductive step).
    LoopInvariantConsecution {
        /// The invariant expression being checked inductively.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Loop invariant sufficiency: the invariant implies the postcondition
    /// upon loop exit.
    LoopInvariantSufficiency {
        /// The invariant expression that must imply the post-loop property.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Type refinement violation: a value does not satisfy its refinement predicate.
    TypeRefinementViolation {
        /// The variable or expression being refined.
        variable: String,
        /// The refinement predicate that was violated (e.g., "v > 0").
        predicate: String,
    },
    /// Frame condition violation: a variable not in the modifies set was changed.
    FrameConditionViolation {
        /// The variable that was modified but not in the modifies clause.
        variable: String,
        /// The function whose frame condition was violated.
        function: String,
    },
}

impl VcKind {
    /// Stable family tag for binary copy-sink length obligations.
    pub const BINARY_COPY_SINK_LENGTH_FAMILY: &'static str = "binary_copy_sink_length_violation";
    /// Stable prefix used for machine-readable hardened report tags.
    pub const HARDENED_FAMILY_PREFIX: &'static str = "hardened";
    /// Kind prefix the native full-verification lane stamps onto an
    /// `UnsupportedMir` round-trip row (`FullVerification::<ApiKind>`, built as
    /// `format!("FullVerification::{kind:?}")` from the verifier-API obligation
    /// kind in `trust_verify.rs::legacy_unsupported_kind_detail`).
    pub const FULL_VERIFICATION_KIND_PREFIX: &'static str = "FullVerification::";

    /// Hardened obligation category for typed rows and legacy
    /// `FunctionalCorrectness { property: "hardened::<category>" }` rows.
    #[must_use]
    pub fn hardened_category(&self) -> Option<HardenedVcCategory> {
        match self {
            VcKind::HardenedBoundary { category, .. } => Some(*category),
            VcKind::Assertion { message } if message.starts_with("[unsafe:ffi]") => {
                Some(HardenedVcCategory::FfiBoundary)
            }
            VcKind::Assertion { message } if message.starts_with("[unsafe") => {
                Some(HardenedVcCategory::UnsafeOperation)
            }
            VcKind::UnsafeOperation { .. } => Some(HardenedVcCategory::UnsafeOperation),
            VcKind::FfiBoundaryViolation { desc, .. }
                if !desc.contains(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
                    && !desc.contains("copy sink length") =>
            {
                Some(HardenedVcCategory::FfiBoundary)
            }
            VcKind::FunctionalCorrectness { property, .. } => {
                property.strip_prefix("hardened::").and_then(HardenedVcCategory::from_tag)
            }
            _ => None,
        }
    }

    /// Stable hardened family tag for reports, including legacy rows.
    #[must_use]
    pub fn hardened_family_tag(&self) -> Option<String> {
        self.hardened_category()
            .map(|category| format!("{}_{}", Self::HARDENED_FAMILY_PREFIX, category.as_tag()))
    }

    /// Stable compact tag used by compiler diagnostics and structured
    /// transport.
    ///
    /// This tag is deliberately retained for backward compatibility and human
    /// readability. It is not a lossless serialization: parameterized kinds
    /// must also travel in `TransportObligationResult::typed_kind`.
    #[must_use]
    pub fn transport_tag(&self) -> String {
        if let Some(category) = self.hardened_category() {
            return format!("hardened_{}", category.as_tag());
        }

        let tag = match self {
            VcKind::ArithmeticOverflow { op, .. } => match op {
                BinOp::Add => "overflow:add",
                BinOp::Sub => "overflow:sub",
                BinOp::Mul => "overflow:mul",
                _ => "overflow",
            },
            VcKind::ShiftOverflow { op, .. } => match op {
                BinOp::Shl => "shift:left",
                BinOp::Shr => "shift:right",
                _ => "shift",
            },
            VcKind::DivisionByZero => "divzero",
            VcKind::RemainderByZero => "remzero",
            VcKind::FloatDivisionByZero => "float_division_by_zero",
            VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity",
            VcKind::IndexOutOfBounds => "bounds",
            VcKind::SliceBoundsCheck => "slice",
            VcKind::Assertion { .. } => "assert",
            VcKind::Precondition { .. } => "precond",
            VcKind::Postcondition => "postcond",
            VcKind::Unreachable => "unreach",
            VcKind::DeadState { .. } => "deadstate",
            VcKind::Deadlock => "deadlock",
            VcKind::Temporal { .. } => "temporal",
            VcKind::CastOverflow { .. } => "cast",
            VcKind::NegationOverflow { .. } => "negation",
            VcKind::Liveness { .. } => "liveness",
            VcKind::Fairness { .. } => "fairness",
            VcKind::TaintViolation { .. } => "taint",
            VcKind::RefinementViolation { .. } => "refinement",
            VcKind::ResilienceViolation { .. } => "resilience",
            VcKind::ProtocolViolation { .. } => "protocol",
            VcKind::NonTermination { .. } => "termination",
            VcKind::UnboundedAllocation { .. } => "unbounded_allocation",
            _ => "unknown",
        };
        tag.to_string()
    }

    /// True for typed copy-sink length VCs and legacy FFI-tagged compatibility rows.
    ///
    /// Older artifacts emitted this family as `FfiBoundaryViolation` with a
    /// description containing "copy sink length". Keeping that compatibility
    /// classifier lets reports distinguish this security family even when they
    /// read pre-typed evidence.
    #[must_use]
    pub fn is_binary_copy_sink_length_violation(&self) -> bool {
        match self {
            VcKind::BinaryCopySinkLengthViolation { .. } => true,
            VcKind::FfiBoundaryViolation { desc, .. } => desc.contains("copy sink length"),
            _ => false,
        }
    }

    /// Stable family tag for copy-sink length rows, including legacy rows.
    #[must_use]
    pub fn binary_copy_sink_length_family_tag(&self) -> Option<&'static str> {
        self.is_binary_copy_sink_length_violation().then_some(Self::BINARY_COPY_SINK_LENGTH_FAMILY)
    }

    /// Human-readable description.
    pub fn description(&self) -> String {
        match self {
            VcKind::ArithmeticOverflow { op, .. } => {
                format!("arithmetic overflow ({op:?})")
            }
            VcKind::ShiftOverflow { op, .. } => {
                format!("shift overflow ({op:?})")
            }
            VcKind::DivisionByZero => "division by zero".to_string(),
            VcKind::RemainderByZero => "remainder by zero".to_string(),
            VcKind::IndexOutOfBounds => "index out of bounds".to_string(),
            VcKind::SliceBoundsCheck => "slice bounds check".to_string(),
            VcKind::Assertion { message } => format!("assertion: {message}"),
            VcKind::Precondition { callee } => format!("precondition of `{callee}`"),
            VcKind::Postcondition => "postcondition".to_string(),
            VcKind::CastOverflow { from_ty, to_ty } => {
                format!("cast overflow ({from_ty:?} -> {to_ty:?})")
            }
            VcKind::NegationOverflow { ty } => {
                format!("negation overflow ({ty:?})")
            }
            VcKind::Unreachable => "unreachable code reached".to_string(),
            VcKind::UnsupportedMir { kind, detail } => {
                format!("unsupported MIR `{kind}`: {detail}")
            }
            VcKind::DeadState { state } => format!("dead state `{state}`"),
            VcKind::Deadlock => "deadlock".to_string(),
            VcKind::Temporal { property, .. } => format!("temporal: {property}"),
            VcKind::Liveness { property, .. } => format!("liveness: {}", property.description()),
            VcKind::Fairness { constraint } => {
                format!("fairness: {}", constraint.description())
            }
            VcKind::TaintViolation { source_label, sink_kind, path_length } => {
                format!(
                    "taint violation: {} data reaches {} sink (path length: {})",
                    source_label, sink_kind, path_length
                )
            }
            VcKind::RefinementViolation { spec_file, action } => {
                format!(
                    "refinement violation: action `{action}` does not refine spec `{spec_file}`"
                )
            }
            VcKind::ResilienceViolation { service, failure_mode, reason } => {
                format!("resilience: {service} {failure_mode} - {reason}")
            }
            VcKind::ProtocolViolation { protocol, violation } => {
                format!("protocol `{protocol}`: {violation}")
            }
            VcKind::NonTermination { context, measure } => {
                format!("non-termination: {context} measure `{measure}` may not decrease")
            }
            // Data race and memory ordering descriptions
            VcKind::DataRace { variable, thread_a, thread_b } => {
                format!("data race on `{variable}` between threads {thread_a} and {thread_b}")
            }
            VcKind::InsufficientOrdering { variable, actual, required } => {
                format!(
                    "insufficient memory ordering on `{variable}`: {actual}, requires {required}"
                )
            }
            VcKind::TranslationValidation { pass, check } => {
                format!("translation validation ({pass}): {check}")
            }
            // Floating-point VC descriptions
            VcKind::FloatDivisionByZero => "float division by zero".to_string(),
            VcKind::FloatOverflowToInfinity { op, .. } => {
                format!("float overflow to infinity ({op:?})")
            }
            // Rvalue safety VC descriptions
            VcKind::InvalidDiscriminant { place_name } => {
                format!("invalid discriminant read on `{place_name}` (not an enum)")
            }
            VcKind::AggregateArrayLengthMismatch { expected, actual } => {
                format!(
                    "array aggregate length mismatch: expected {expected} elements, got {actual}"
                )
            }
            // Unsafe operation description.
            VcKind::UnsafeOperation { desc } => format!("unsafe operation: {desc}"),
            VcKind::SavedReturnAddressOverwrite { access_width_bytes, slot } => {
                format!(
                    "binary saved return address overwrite: {access_width_bytes}-byte write may alias {slot}"
                )
            }
            VcKind::FormatStringViolation { callee, evidence } => {
                format!("format string violation in `{callee}`: {evidence}")
            }
            VcKind::TaintedIndirectBranch { sink_kind, target, evidence } => {
                format!("tainted indirect control flow: {target} reaches {sink_kind}: {evidence}")
            }
            VcKind::BinaryAbiContradiction { fact, evidence } => {
                format!("binary ABI contradiction: {fact} ({evidence})")
            }
            VcKind::BinaryCopySinkLengthViolation { callee, desc } => {
                format!("binary copy-sink length violation in `{callee}`: {desc}")
            }
            // FFI boundary verification description.
            VcKind::FfiBoundaryViolation { callee, desc } => {
                format!("FFI boundary violation in `{callee}`: {desc}")
            }
            VcKind::CopyBoundsViolation { callee, direction, detail } => {
                format!("copy bounds violation in `{callee}` ({direction}): {detail}")
            }
            VcKind::ExternallyMutableAllocationBounds { allocation_kind, live_size, detail } => {
                format!(
                    "externally-mutable allocation bounds ({allocation_kind}, live size `{live_size}`): {detail}"
                )
            }
            VcKind::UnboundedAllocation { callee, count, detail } => {
                format!("unbounded allocation in `{callee}` (count `{count}`): {detail}")
            }
            // Ownership VcKind descriptions.
            VcKind::UseAfterFree => "use after free".to_string(),
            VcKind::DoubleFree => "double free".to_string(),
            VcKind::AliasingViolation { mutable } => {
                if *mutable {
                    "aliasing violation: &mut aliases with &mut".to_string()
                } else {
                    "aliasing violation: &mut aliases with &".to_string()
                }
            }
            VcKind::LifetimeViolation => {
                "lifetime violation: reference outlives referent".to_string()
            }
            VcKind::SendViolation => {
                "Send violation: non-Send type sent across threads".to_string()
            }
            VcKind::SyncViolation => {
                "Sync violation: non-Sync type shared across threads".to_string()
            }
            // Functional correctness description.
            VcKind::FunctionalCorrectness { property, context } => {
                format!("functional correctness ({property}): {context}")
            }
            VcKind::HardenedBoundary { category, callee, detail } => {
                format!("hardened boundary ({}): {callee}: {detail}", category.as_tag())
            }
            // trust_wp contract VC descriptions.
            VcKind::LoopInvariantInitiation { invariant, header_block } => {
                format!("loop invariant initiation (bb{header_block}): {invariant}")
            }
            VcKind::LoopInvariantConsecution { invariant, header_block } => {
                format!("loop invariant consecution (bb{header_block}): {invariant}")
            }
            VcKind::LoopInvariantSufficiency { invariant, header_block } => {
                format!("loop invariant sufficiency (bb{header_block}): {invariant}")
            }
            VcKind::TypeRefinementViolation { variable, predicate } => {
                format!("type refinement violation: {variable} does not satisfy {predicate}")
            }
            VcKind::FrameConditionViolation { variable, function } => {
                format!(
                    "frame condition violation: `{variable}` modified outside modifies clause of `{function}`"
                )
            }
        }
    }

    /// Returns the proof level (L0, L1, L2).
    pub fn proof_level(&self) -> ProofLevel {
        match self {
            VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::Assertion { .. }
            | VcKind::CastOverflow { .. }
            | VcKind::NegationOverflow { .. }
            | VcKind::Unreachable
            | VcKind::UnsupportedMir { .. }
            // Discriminant on non-enum and array length mismatch are safety (L0).
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            | VcKind::UnsafeOperation { .. }
            | VcKind::SavedReturnAddressOverwrite { .. }
            | VcKind::FormatStringViolation { .. }
            | VcKind::TaintedIndirectBranch { .. }
            | VcKind::BinaryAbiContradiction { .. }
            | VcKind::BinaryCopySinkLengthViolation { .. }
            // FFI boundary violations are safety (L0).
            | VcKind::FfiBoundaryViolation { .. }
            // Raw-copy bounds and externally-mutable allocation bounds are UB-class (L0).
            | VcKind::CopyBoundsViolation { .. }
            | VcKind::ExternallyMutableAllocationBounds { .. }
            // Unbounded allocation is an availability/DoS safety hazard (L0).
            | VcKind::UnboundedAllocation { .. } => ProofLevel::L0Safety,
            VcKind::Precondition { .. } | VcKind::Postcondition => ProofLevel::L1Functional,
            VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. } => ProofLevel::L2Domain,
            VcKind::TaintViolation { .. } => ProofLevel::L1Functional,
            VcKind::ResilienceViolation { .. } => ProofLevel::L1Functional,
            VcKind::NonTermination { .. } => ProofLevel::L1Functional,
            // Data races are UB (L0 safety), ordering is correctness (L1).
            VcKind::DataRace { .. } => ProofLevel::L0Safety,
            VcKind::InsufficientOrdering { .. } => ProofLevel::L1Functional,
            // Translation validation is functional correctness (L1).
            VcKind::TranslationValidation { .. } => ProofLevel::L1Functional,
            // Trust (DESIGN_PHILOSOPHY §9 — defined behavior is not unsafe):
            // IEEE-754 float division-by-zero and overflow-to-infinity are DEFINED
            // (±inf/NaN, never trap, never UB), so they are NOT L0 safety
            // violations and must never fail-close a build of valid Rust. They are
            // demoted to L1 (functional/numerical-hygiene advisory): a bounded op
            // still proves, an unbounded one surfaces as a non-fatal note rather
            // than an L0 refutation. `FloatDivisionByZero` is additionally not even
            // emitted (division is total — nothing to advise); `FloatOverflowToInfinity`
            // remains emittable as the L1 advisory. See the Div arm in
            // trust-vcgen `generate.rs` and the reference generator.
            VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
                ProofLevel::L1Functional
            }
            // Ownership violations are all UB (L0 safety).
            VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation => ProofLevel::L0Safety,
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::UnsafeOperation | HardenedVcCategory::FfiBoundary,
                ..
            } => ProofLevel::L0Safety,
            // Functional correctness is L1.
            VcKind::FunctionalCorrectness { .. } | VcKind::HardenedBoundary { .. } => {
                ProofLevel::L1Functional
            }
            // trust_wp contract VCs are L1 functional correctness.
            VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
            | VcKind::TypeRefinementViolation { .. }
            | VcKind::FrameConditionViolation { .. } => ProofLevel::L1Functional,
        }
    }

    /// Recovers the real obligation-kind tag of a native full-verification
    /// round-trip row.
    ///
    /// The full lane re-materializes a legacy VC as
    /// `UnsupportedMir { kind: "FullVerification::<ApiKind>", detail }` (see
    /// `legacy_unsupported_kind_detail` in `trust_verify.rs`): the coarse
    /// verifier-API family survives in `kind`, and the ORIGINAL
    /// `VcKind::description()` text survives as the leading segment of `detail`
    /// (optional `; contract_id=` / `; metadata_keys=` suffixes follow it).
    ///
    /// SINGLE SOURCE OF TRUTH for the family/detail → tag mapping: the
    /// transport display recovery in `trust_verify.rs` (`format_vc_kind` /
    /// `recovered_full_lane_vc_tag`) and the effective-kind runtime fallback
    /// ([`VcKind::has_runtime_fallback`]) must both answer from this mapping —
    /// do not fork it. The recovered tag is exactly the tag `format_vc_kind`
    /// gives the pre-round-trip `VcKind` (`overflow:add`, `bounds`, `divzero`,
    /// `assert`, `unreach`, …).
    ///
    /// Each detail prefix is CROSS-CHECKED against the verifier-API family the
    /// original `VcKind` actually routes through (`vc_obligation_kind` in
    /// trust-mir-extract), so a stray description can never relabel a row
    /// across families. Every prefix is anchored at the start of `detail`, so
    /// e.g. `division by zero` can never fire on `float division by zero`.
    /// Anything unrecognized returns `None` — fail-closed.
    #[must_use]
    pub fn recovered_full_lane_vc_tag(kind: &str, detail: &str) -> Option<&'static str> {
        let family = kind.strip_prefix(Self::FULL_VERIFICATION_KIND_PREFIX)?;
        let tag = match family {
            "ArithmeticSafety" => {
                if detail.starts_with("arithmetic overflow (Add)") {
                    "overflow:add"
                } else if detail.starts_with("arithmetic overflow (Sub)") {
                    "overflow:sub"
                } else if detail.starts_with("arithmetic overflow (Mul)") {
                    "overflow:mul"
                } else if detail.starts_with("arithmetic overflow") {
                    "overflow"
                } else if detail.starts_with("shift overflow (Shl)") {
                    "shift:left"
                } else if detail.starts_with("shift overflow (Shr)") {
                    "shift:right"
                } else if detail.starts_with("shift overflow") {
                    "shift"
                } else if detail.starts_with("division by zero") {
                    "divzero"
                } else if detail.starts_with("remainder by zero") {
                    "remzero"
                } else if detail.starts_with("float division by zero") {
                    "float_division_by_zero"
                } else if detail.starts_with("float overflow to infinity") {
                    "float_overflow_to_infinity"
                } else if detail.starts_with("cast overflow") {
                    "cast"
                } else if detail.starts_with("negation overflow") {
                    "negation"
                } else {
                    return None;
                }
            }
            "BoundsCheck" => {
                if detail.starts_with("index out of bounds") {
                    "bounds"
                } else if detail.starts_with("slice bounds check") {
                    "slice"
                } else {
                    return None;
                }
            }
            "Assertion" => {
                if detail.starts_with("assertion: ") {
                    "assert"
                } else if detail.starts_with("unreachable code reached") {
                    "unreach"
                } else {
                    return None;
                }
            }
            "Precondition" if detail.starts_with("precondition of `") => "precond",
            "Postcondition" if detail.starts_with("postcondition") => "postcond",
            "TemporalSafety" => {
                if detail.starts_with("dead state `") {
                    "deadstate"
                } else if detail.starts_with("deadlock") {
                    "deadlock"
                } else if detail.starts_with("temporal: ") {
                    "temporal"
                } else if detail.starts_with("fairness: ") {
                    "fairness"
                } else {
                    return None;
                }
            }
            "Liveness" if detail.starts_with("liveness: ") => "liveness",
            "Protocol" if detail.starts_with("protocol `") => "protocol",
            "Refinement" if detail.starts_with("refinement violation: ") => "refinement",
            "Termination" if detail.starts_with("non-termination: ") => "termination",
            // Custom-routed kinds carry their precise `vc_kind_label` slug INSIDE
            // the round-trip kind string itself (`FullVerification::trust.vc::
            // <label>`) — the strongest survivor; no description cross-check is
            // needed. `trust.vc::unsupported_mir` (a genuine unsupported-MIR VC)
            // deliberately has no arm: it never had a real kind to recover.
            "trust.vc::taint_violation" => "taint",
            "trust.vc::resilience_violation" => "resilience",
            _ => return None,
        };
        Some(tag)
    }

    /// Returns whether Rust has a corresponding runtime check for this VC kind.
    #[must_use]
    pub fn has_runtime_fallback(&self, overflow_checks: bool) -> bool {
        match self {
            VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::NegationOverflow { .. } => overflow_checks,
            VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::Assertion { .. }
            | VcKind::Unreachable => true,
            // Effective-kind runtime fallback: a native full-lane round-trip
            // row (`FullVerification::<ApiKind>`) is an obligation whose
            // underlying operation KEEPS its physical runtime check — checks
            // are elided only for Proved-with-authority obligations, which an
            // `UnsupportedMir` row by construction is not. Recover the
            // effective kind through the same single-sourced mapping the
            // transport display already trusts and answer per that kind's own
            // arm above/below. Fail-closed: a detail that does not map exactly
            // — including every non-`FullVerification::` kind, such as the
            // `assumption:<tag>` rows targo folds into `UnsupportedMir`
            // precisely so they get NO fallback — keeps `false`.
            VcKind::UnsupportedMir { kind, detail } => {
                match Self::recovered_full_lane_vc_tag(kind, detail) {
                    // ArithmeticOverflow / ShiftOverflow / NegationOverflow arms.
                    Some(
                        "overflow:add" | "overflow:sub" | "overflow:mul" | "overflow"
                        | "shift:left" | "shift:right" | "shift" | "negation",
                    ) => overflow_checks,
                    // DivisionByZero / RemainderByZero / IndexOutOfBounds /
                    // SliceBoundsCheck / Assertion / Unreachable arms.
                    Some("divzero" | "remzero" | "bounds" | "slice" | "assert" | "unreach") => true,
                    // Every other recovered family (cast/precond/postcond/
                    // float/temporal/…) answers `false` per its own arm, and an
                    // unrecovered detail stays fail-closed `false`.
                    _ => false,
                }
            }
            VcKind::CastOverflow { .. }
            | VcKind::Precondition { .. }
            | VcKind::Postcondition
            | VcKind::ResilienceViolation { .. }
            | VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::TaintViolation { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. }
            | VcKind::NonTermination { .. }
            // No runtime checks for data races or ordering violations.
            | VcKind::DataRace { .. }
            | VcKind::InsufficientOrdering { .. }
            // Translation validation has no runtime fallback.
            | VcKind::TranslationValidation { .. }
            // Float ops silently produce Inf/NaN per IEEE 754 — no runtime check.
            | VcKind::FloatDivisionByZero
            | VcKind::FloatOverflowToInfinity { .. } => false,
            // No runtime checks for type-level safety VCs.
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            // No runtime check for unsafe operations.
            | VcKind::UnsafeOperation { .. }
            | VcKind::SavedReturnAddressOverwrite { .. }
            | VcKind::FormatStringViolation { .. }
            | VcKind::TaintedIndirectBranch { .. }
            | VcKind::BinaryAbiContradiction { .. }
            | VcKind::BinaryCopySinkLengthViolation { .. }
            // No runtime check for FFI boundary violations.
            | VcKind::FfiBoundaryViolation { .. }
            // The language does not bounds-check raw copies or externally-mutable
            // backing sizes — that absence is exactly why these are obligations.
            | VcKind::CopyBoundsViolation { .. }
            | VcKind::ExternallyMutableAllocationBounds { .. }
            // The language does not bound bulk-allocation sizes — that absence is
            // exactly why an unbounded allocation is an obligation, not a check.
            | VcKind::UnboundedAllocation { .. }
            // Ownership violations have no runtime check (UB in unsafe code).
            | VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation
            // Functional correctness has no runtime fallback.
            | VcKind::FunctionalCorrectness { .. }
            | VcKind::HardenedBoundary { .. }
            // trust_wp contract VCs have no runtime fallback.
            | VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
            | VcKind::TypeRefinementViolation { .. }
            | VcKind::FrameConditionViolation { .. } => false,
        }
    }
}

// Display delegates to description() so `.to_string()` works in tests.
impl std::fmt::Display for VcKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.description())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn saved_return_address_overwrite_is_l0_without_runtime_fallback() {
        let kind = VcKind::SavedReturnAddressOverwrite {
            access_width_bytes: 8,
            slot: "saved_return_address".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("saved return address overwrite"));
    }

    #[test]
    fn format_string_violation_is_l0_without_runtime_fallback() {
        let kind = VcKind::FormatStringViolation {
            callee: "printf".to_string(),
            evidence: "format argument is symbolic".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("format string violation"));
    }

    #[test]
    fn tainted_indirect_branch_is_l0_without_runtime_fallback() {
        let kind = VcKind::TaintedIndirectBranch {
            sink_kind: "indirect_branch".to_string(),
            target: "unresolved_indirect_target".to_string(),
            evidence: "target taint unavailable".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("tainted indirect control flow"));
    }

    #[test]
    fn binary_abi_contradiction_is_l0_without_runtime_fallback() {
        let kind = VcKind::BinaryAbiContradiction {
            fact: "parameter 0 storage".to_string(),
            evidence: "ABI says RDI, storage says RSI".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("binary ABI contradiction"));
    }

    #[test]
    fn binary_copy_sink_length_violation_is_l0_without_runtime_fallback() {
        let kind = VcKind::BinaryCopySinkLengthViolation {
            callee: "memcpy".to_string(),
            desc: "copy sink length may exceed destination capacity".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("binary copy-sink length violation"));
        assert_eq!(
            kind.binary_copy_sink_length_family_tag(),
            Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        );
    }

    #[test]
    fn legacy_ffi_copy_sink_rows_keep_stable_family_classifier() {
        let legacy = VcKind::FfiBoundaryViolation {
            callee: "strncpy".to_string(),
            desc: "copy sink length for `strncpy` lacks destination capacity".to_string(),
        };
        let ordinary_ffi = VcKind::FfiBoundaryViolation {
            callee: "malloc".to_string(),
            desc: "return contract may be null".to_string(),
        };

        assert!(legacy.is_binary_copy_sink_length_violation());
        assert_eq!(
            legacy.binary_copy_sink_length_family_tag(),
            Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        );
        assert!(!ordinary_ffi.is_binary_copy_sink_length_violation());
        assert_eq!(ordinary_ffi.binary_copy_sink_length_family_tag(), None);
    }

    #[test]
    fn hardened_boundary_is_l1_without_runtime_fallback() {
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::RawPathApi,
            callee: "std::fs::remove_file".to_string(),
            detail: "path removal re-resolves a mutable direntry".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
        assert!(!kind.has_runtime_fallback(true));
        assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::RawPathApi));
        assert_eq!(kind.hardened_family_tag().as_deref(), Some("hardened_raw_path_api"));
        assert!(kind.description().contains("hardened boundary"));
    }

    #[test]
    fn all_hardened_categories_roundtrip_and_classify() {
        let cases = [
            (HardenedVcCategory::RawPathApi, "raw_path_api", ProofLevel::L1Functional),
            (HardenedVcCategory::PathIdentity, "path_identity", ProofLevel::L1Functional),
            (HardenedVcCategory::PermissionChange, "permission_change", ProofLevel::L1Functional),
            (HardenedVcCategory::PermissionCreate, "permission_create", ProofLevel::L1Functional),
            (HardenedVcCategory::PermissionWindow, "permission_window", ProofLevel::L1Functional),
            (HardenedVcCategory::Utf8Reject, "utf8_reject", ProofLevel::L1Functional),
            (HardenedVcCategory::ByteLoss, "byte_loss", ProofLevel::L1Functional),
            (HardenedVcCategory::ErrorDiscard, "error_discard", ProofLevel::L1Functional),
            (HardenedVcCategory::PanicBoundary, "panic_boundary", ProofLevel::L1Functional),
            (HardenedVcCategory::CompatObservable, "compat_observable", ProofLevel::L1Functional),
            (HardenedVcCategory::ProcessSemantics, "process_semantics", ProofLevel::L1Functional),
            (HardenedVcCategory::TrustDomain, "trust_domain", ProofLevel::L1Functional),
            (HardenedVcCategory::TrustDomainOrder, "trust_domain_order", ProofLevel::L1Functional),
            (HardenedVcCategory::UnsafeOperation, "unsafe_operation", ProofLevel::L0Safety),
            (HardenedVcCategory::FfiBoundary, "ffi_boundary", ProofLevel::L0Safety),
        ];

        for (category, tag, level) in cases {
            assert_eq!(category.as_tag(), tag);
            assert_eq!(HardenedVcCategory::from_tag(tag), Some(category));

            let kind = VcKind::HardenedBoundary {
                category,
                callee: "fixture".into(),
                detail: "detail".into(),
            };
            assert_eq!(kind.hardened_category(), Some(category));
            assert_eq!(kind.hardened_family_tag(), Some(format!("hardened_{tag}")));
            assert_eq!(kind.proof_level(), level);
            assert!(!kind.has_runtime_fallback(true));
            assert!(!kind.has_runtime_fallback(false));
        }

        assert_eq!(HardenedVcCategory::from_tag(""), None);
    }

    #[test]
    fn future_hardened_category_deserializes_as_unknown() {
        let kind: VcKind = serde_json::from_str(
            r#"{
                "HardenedBoundary": {
                    "category": "future_kernel_object_identity",
                    "callee": "openat2",
                    "detail": "future hardened category should stay fail-closed"
                }
            }"#,
        )
        .expect("future hardened category should deserialize through Unknown");

        match kind {
            VcKind::HardenedBoundary { category, callee, detail } => {
                assert!(category.is_unknown());
                assert_eq!(category.as_tag(), "future_kernel_object_identity");
                assert_eq!(callee, "openat2");
                assert!(detail.contains("future hardened category"));
            }
            other => panic!("expected hardened boundary, got {other:?}"),
        }
    }

    #[test]
    fn legacy_hardened_functional_correctness_rows_classify() {
        let legacy = VcKind::FunctionalCorrectness {
            property: "hardened::byte_loss".to_string(),
            context: "to_string_lossy: lossy OS/path conversion".to_string(),
        };
        let ordinary = VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "binary_search postcondition".to_string(),
        };

        assert_eq!(legacy.hardened_category(), Some(HardenedVcCategory::ByteLoss));
        assert_eq!(legacy.hardened_family_tag().as_deref(), Some("hardened_byte_loss"));
        assert_eq!(ordinary.hardened_category(), None);
        assert_eq!(ordinary.hardened_family_tag(), None);
    }

    #[test]
    fn legacy_future_hardened_functional_correctness_rows_preserve_tag() {
        let legacy = VcKind::FunctionalCorrectness {
            property: "hardened::future_kernel_object_identity".to_string(),
            context: "future hardened row".to_string(),
        };

        let category = legacy.hardened_category().expect("future hardened category");
        assert!(category.is_unknown());
        assert_eq!(category.as_tag(), "future_kernel_object_identity");
        assert_eq!(
            legacy.hardened_family_tag().as_deref(),
            Some("hardened_future_kernel_object_identity")
        );
    }

    #[test]
    fn ffi_boundary_is_native_hardened_category() {
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::FfiBoundary,
            callee: "extern \"C\"::strlen".to_string(),
            detail: "trusted wrapper contract required".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::FfiBoundary));
        assert_eq!(kind.hardened_family_tag().as_deref(), Some("hardened_ffi_boundary"));
        assert!(kind.description().contains("ffi_boundary"));
    }

    #[test]
    fn native_unsafe_and_ffi_kinds_classify_as_hardened_categories_without_losing_l0_or_copy_sink_tags()
     {
        let unsafe_kind = VcKind::UnsafeOperation { desc: "raw pointer deref".to_string() };
        let unsafe_assertion =
            VcKind::Assertion { message: "[unsafe] missing SAFETY comment".to_string() };
        let ffi_assertion =
            VcKind::Assertion { message: "[unsafe:ffi] precondition for getenv".to_string() };
        let ffi_kind = VcKind::FfiBoundaryViolation {
            callee: "strlen".to_string(),
            desc: "trusted wrapper contract required".to_string(),
        };
        let copy_sink = VcKind::FfiBoundaryViolation {
            callee: "memcpy".to_string(),
            desc: "copy sink length may exceed destination capacity".to_string(),
        };

        assert_eq!(unsafe_kind.proof_level(), ProofLevel::L0Safety);
        assert_eq!(unsafe_assertion.proof_level(), ProofLevel::L0Safety);
        assert_eq!(ffi_assertion.proof_level(), ProofLevel::L0Safety);
        assert_eq!(ffi_kind.proof_level(), ProofLevel::L0Safety);
        assert_eq!(unsafe_kind.hardened_category(), Some(HardenedVcCategory::UnsafeOperation));
        assert_eq!(unsafe_assertion.hardened_category(), Some(HardenedVcCategory::UnsafeOperation));
        assert_eq!(ffi_assertion.hardened_category(), Some(HardenedVcCategory::FfiBoundary));
        assert_eq!(ffi_kind.hardened_category(), Some(HardenedVcCategory::FfiBoundary));
        assert_eq!(unsafe_kind.hardened_family_tag().as_deref(), Some("hardened_unsafe_operation"));
        assert_eq!(ffi_kind.hardened_family_tag().as_deref(), Some("hardened_ffi_boundary"));
        assert_eq!(copy_sink.hardened_category(), None);
        assert_eq!(
            copy_sink.binary_copy_sink_length_family_tag(),
            Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        );
    }

    #[test]
    fn legacy_hardened_serialized_vc_kind_still_deserializes() {
        let json = r#"{
            "FunctionalCorrectness": {
                "property": "hardened::panic_boundary",
                "context": "unwrap: success precondition is not proven"
            }
        }"#;

        let kind: VcKind = serde_json::from_str(json).expect("legacy VC kind deserializes");

        assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::PanicBoundary));
        assert_eq!(kind.hardened_family_tag().as_deref(), Some("hardened_panic_boundary"));
    }

    fn full_lane(kind: &str, detail: &str) -> VcKind {
        VcKind::UnsupportedMir { kind: kind.to_string(), detail: detail.to_string() }
    }

    #[test]
    fn recovered_full_lane_vc_tag_matches_transport_tags() {
        // Detail texts mirror captured transport rows: the original
        // `VcKind::description()` prefix survives, with optional
        // `; contract_id=` / `; metadata_keys=` suffixes after it.
        let cases = [
            (
                "FullVerification::ArithmeticSafety",
                "arithmetic overflow (Add); contract_id=contract:trust-mc-typed-chc-public:cf0b9f",
                "overflow:add",
            ),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Sub)", "overflow:sub"),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Mul)", "overflow:mul"),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Div)", "overflow"),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shl)", "shift:left"),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shr)", "shift:right"),
            ("FullVerification::ArithmeticSafety", "negation overflow (i32)", "negation"),
            (
                "FullVerification::ArithmeticSafety",
                "division by zero; contract_id=contract:trust-mc-typed-chc-public:4c7c39",
                "divzero",
            ),
            ("FullVerification::ArithmeticSafety", "remainder by zero", "remzero"),
            ("FullVerification::ArithmeticSafety", "cast overflow (U64 -> U32)", "cast"),
            // Prefix anchoring: the float families never fire the integer arms.
            (
                "FullVerification::ArithmeticSafety",
                "float division by zero",
                "float_division_by_zero",
            ),
            (
                "FullVerification::ArithmeticSafety",
                "float overflow to infinity (Add)",
                "float_overflow_to_infinity",
            ),
            (
                "FullVerification::BoundsCheck",
                "index out of bounds; metadata_keys=[trust.obligation_context.v1]",
                "bounds",
            ),
            ("FullVerification::BoundsCheck", "slice bounds check", "slice"),
            (
                "FullVerification::Assertion",
                "assertion: panic call: std::rt::panic_fmt; contract_id=contract:trust-mc-typed-chc-public:b4cdda",
                "assert",
            ),
            (
                "FullVerification::Assertion",
                "unreachable code reached; contract_id=contract:trust-mc-typed-chc-public:8031b9",
                "unreach",
            ),
            ("FullVerification::Precondition", "precondition of `callee`", "precond"),
            ("FullVerification::Postcondition", "postcondition", "postcond"),
            ("FullVerification::TemporalSafety", "dead state `idle`", "deadstate"),
            ("FullVerification::TemporalSafety", "deadlock", "deadlock"),
            ("FullVerification::TemporalSafety", "temporal: always ready", "temporal"),
            ("FullVerification::TemporalSafety", "fairness: WF_{q}(step)", "fairness"),
            ("FullVerification::Liveness", "liveness: termination: <>done", "liveness"),
            ("FullVerification::Protocol", "protocol `handshake`: out of order", "protocol"),
            (
                "FullVerification::Refinement",
                "refinement violation: action `pop` does not refine spec `stack.tla`",
                "refinement",
            ),
            (
                "FullVerification::Termination",
                "non-termination: loop measure `n` may not decrease",
                "termination",
            ),
            ("FullVerification::trust.vc::taint_violation", "anything", "taint"),
            ("FullVerification::trust.vc::resilience_violation", "anything", "resilience"),
        ];

        for (kind, detail, expected) in cases {
            assert_eq!(
                VcKind::recovered_full_lane_vc_tag(kind, detail),
                Some(expected),
                "kind={kind:?} detail={detail:?}"
            );
        }
    }

    #[test]
    fn recovered_full_lane_vc_tag_fails_closed_on_unmapped_rows() {
        let cases = [
            // Unrecognized detail within a known family.
            ("FullVerification::ArithmeticSafety", "some future obligation text"),
            // Cross-family mismatch: a stray description can never relabel a
            // row across families.
            ("FullVerification::BoundsCheck", "division by zero"),
            ("FullVerification::Assertion", "index out of bounds"),
            // A genuine unsupported-MIR VC never had a real kind to recover.
            ("FullVerification::trust.vc::unsupported_mir", "unsupported MIR `InlineAsm`"),
            // Unknown family.
            ("FullVerification::MemorySafety", "index out of bounds"),
            // Non-round-trip rows: no `FullVerification::` prefix at all.
            ("assumption:native-lowering", "assumption:native-lowering"),
            ("InlineAsm", "inline assembly is not modeled"),
            ("", "division by zero"),
        ];

        for (kind, detail) in cases {
            assert_eq!(
                VcKind::recovered_full_lane_vc_tag(kind, detail),
                None,
                "kind={kind:?} detail={detail:?}"
            );
        }
    }

    #[test]
    fn full_lane_effective_kind_recovers_runtime_fallback_per_family() {
        // (kind, detail, with overflow-checks, without overflow-checks) — each
        // answer matches the recovered effective kind's own arm.
        let cases = [
            // Overflow family → `overflow_checks`, per the
            // ArithmeticOverflow/ShiftOverflow/NegationOverflow arms.
            (
                "FullVerification::ArithmeticSafety",
                "arithmetic overflow (Add); contract_id=contract:trust-mc-typed-chc-public:cf0b9f",
                true,
                false,
            ),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Sub)", true, false),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Mul)", true, false),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Div)", true, false),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shl)", true, false),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shr)", true, false),
            ("FullVerification::ArithmeticSafety", "negation overflow (i32)", true, false),
            // Divzero/bounds/assert families → unconditionally true, per the
            // DivisionByZero/RemainderByZero/IndexOutOfBounds/SliceBoundsCheck/
            // Assertion arms.
            (
                "FullVerification::ArithmeticSafety",
                "division by zero; contract_id=contract:trust-mc-typed-chc-public:4c7c39",
                true,
                true,
            ),
            ("FullVerification::ArithmeticSafety", "remainder by zero", true, true),
            (
                "FullVerification::BoundsCheck",
                "index out of bounds; metadata_keys=[trust.obligation_context.v1]",
                true,
                true,
            ),
            ("FullVerification::BoundsCheck", "slice bounds check", true, true),
            (
                "FullVerification::Assertion",
                "assertion: panic call: std::rt::panic_fmt; contract_id=contract:trust-mc-typed-chc-public:b4cdda",
                true,
                true,
            ),
            // Unreach → whatever the Unreachable arm answers (true).
            (
                "FullVerification::Assertion",
                "unreachable code reached; contract_id=contract:trust-mc-typed-chc-public:8031b9",
                true,
                true,
            ),
            // Recovered families whose own arms answer false stay false.
            ("FullVerification::ArithmeticSafety", "cast overflow (U64 -> U32)", false, false),
            ("FullVerification::ArithmeticSafety", "float division by zero", false, false),
            ("FullVerification::Precondition", "precondition of `callee`", false, false),
            ("FullVerification::Postcondition", "postcondition", false, false),
            ("FullVerification::TemporalSafety", "deadlock", false, false),
        ];

        for (kind, detail, with_oc, without_oc) in cases {
            let vc_kind = full_lane(kind, detail);
            assert_eq!(
                vc_kind.has_runtime_fallback(true),
                with_oc,
                "kind={kind:?} detail={detail:?} overflow_checks=true"
            );
            assert_eq!(
                vc_kind.has_runtime_fallback(false),
                without_oc,
                "kind={kind:?} detail={detail:?} overflow_checks=false"
            );
        }
    }

    #[test]
    fn full_lane_unmapped_detail_keeps_runtime_fallback_fail_closed() {
        let cases = [
            ("FullVerification::ArithmeticSafety", "some future obligation text"),
            ("FullVerification::BoundsCheck", "division by zero"),
            ("FullVerification::trust.vc::unsupported_mir", "unsupported MIR `InlineAsm`"),
            // targo folds `assumption:<tag>` rows into `UnsupportedMir`
            // precisely so they get NO runtime fallback — must stay false.
            ("assumption:native-lowering", "assumption:native-lowering"),
            ("InlineAsm", "inline assembly is not modeled"),
        ];

        for (kind, detail) in cases {
            let vc_kind = full_lane(kind, detail);
            assert!(!vc_kind.has_runtime_fallback(true), "kind={kind:?} detail={detail:?}");
            assert!(!vc_kind.has_runtime_fallback(false), "kind={kind:?} detail={detail:?}");
        }
    }

    #[test]
    fn non_unsupported_mir_runtime_fallback_arms_are_stable() {
        // The effective-kind derivation touches ONLY `UnsupportedMir`; every
        // other family keeps its existing answer.
        let cases: [(VcKind, bool, bool); 8] = [
            (
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
                true,
                false,
            ),
            (VcKind::DivisionByZero, true, true),
            (VcKind::RemainderByZero, true, true),
            (VcKind::IndexOutOfBounds, true, true),
            (VcKind::SliceBoundsCheck, true, true),
            (VcKind::Assertion { message: "invariant holds".into() }, true, true),
            (VcKind::Unreachable, true, true),
            (VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() }, false, false),
        ];

        for (vc_kind, with_oc, without_oc) in cases {
            assert_eq!(vc_kind.has_runtime_fallback(true), with_oc, "{vc_kind:?}");
            assert_eq!(vc_kind.has_runtime_fallback(false), without_oc, "{vc_kind:?}");
        }
    }
}
