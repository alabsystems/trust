// trust-integration-tests/tests/vckind_exhaustiveness.rs: VcKind exhaustiveness guard
//
// THE ENUM IS THE SOURCE OF TRUTH, AND IT IS ENFORCED AT COMPILE TIME.
// Adding a variant to `VcKind` is a compile ERROR in this file until the census
// below names it. There is no variant count to keep in sync, because there is
// no count: `vckind_census!` expands ONE token list into both the constructed
// inventory and a `match` over `VcKind`, and that match is checked against the
// real enum by the compiler.
//
// Why a lint and not a bare `match`: `VcKind` is `#[non_exhaustive]`, so an
// external match is REQUIRED to carry a wildcard arm, and a wildcard silently
// absorbs every future variant. `non_exhaustive_omitted_patterns` closes exactly
// that hole -- the wildcard stays (the language demands it) but the lint reports
// every variant the arms did not name explicitly, and `deny` makes that fatal.
//
// This replaces two hardcoded counts (`EXPECTED_VARIANT_COUNT` and a
// `variants.len()` assertion) that counted the test's OWN hand-written lists
// rather than the enum. Both read 53 while `VcKind` had 56 variants and BOTH
// STILL PASSED: the guard measured itself, so it could not fail for the one
// thing it existed to catch. Do not reintroduce a count -- a count here is
// self-referential by construction.
//
// The unstable lint gate is affordable HERE specifically: this is a `tests/`
// target of a leaf crate that nothing depends on, so unlike trust-machine-sem
// (reachable from `rustc_codegen_trust_cg`) it is not in the compiler's own
// build graph and cannot propagate a feature requirement to it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(non_exhaustive_omitted_patterns_lint)]

use trust_types::*;

/// Entry mapping a VcKind variant to its test coverage location.
struct VcKindCoverage {
    /// Human-readable variant name, from the same token as the constructor.
    variant_name: &'static str,
    /// A representative instance, so every variant reaches the real
    /// `description()` / `proof_level()` matches in trust-types.
    kind: VcKind,
    /// Test file(s) that exercise this variant, or justification if untested.
    coverage: Coverage,
}

enum Coverage {
    /// At least one test exercises this VcKind variant.
    Tested(&'static str),
    /// No end-to-end test yet; documented justification.
    Documented(&'static str),
}

impl Coverage {
    fn detail(&self) -> &'static str {
        match self {
            Coverage::Tested(files) => files,
            Coverage::Documented(reason) => reason,
        }
    }
}

/// Emits the census and its completeness proof from a single token list.
///
/// The constructed inventory and the `match` that certifies it are expanded from
/// the SAME `$variant` tokens, so "the inventory says one thing and the match
/// says another" is not a mistake that can be written down. The match is what
/// the compiler checks against `VcKind`; the inventory is what the tests read.
macro_rules! vckind_census {
    ($( $variant:ident { $($field:tt)* } => $coverage:expr ),+ $(,)?) => {
        fn census() -> Vec<VcKindCoverage> {
            vec![$(
                VcKindCoverage {
                    variant_name: stringify!($variant),
                    kind: VcKind::$variant { $($field)* },
                    coverage: $coverage,
                }
            ),+]
        }

        /// THE GUARD. A `VcKind` variant absent from the census above is not
        /// matched explicitly here, and `deny` turns the lint's report into a
        /// build failure. The wildcard is mandatory (`#[non_exhaustive]`) and is
        /// unreachable in practice precisely because the lint is denied.
        fn census_name_of(kind: &VcKind) -> &'static str {
            #[deny(non_exhaustive_omitted_patterns)]
            match kind {
                $( VcKind::$variant { .. } => stringify!($variant), )+
                _ => unreachable!(
                    "unreachable while non_exhaustive_omitted_patterns is denied: \
                     an unlisted VcKind variant fails to compile above"
                ),
            }
        }
    };
}

/// Representative operand type for variants that carry one.
fn ty() -> Ty {
    Ty::u32()
}

// Listed in `VcKind` declaration order so this census diffs cleanly against the
// enum. Order is a review convenience only -- completeness is the compiler's job.
vckind_census! {
    ArithmeticOverflow { op: BinOp::Add, operand_tys: (ty(), ty()) }
        => Coverage::Tested("error_detection.rs, pipeline.rs, self_verify.rs, ay_phase2_models.rs"),
    ShiftOverflow { op: BinOp::Shl, operand_ty: ty(), shift_ty: ty() }
        => Coverage::Tested("ay_phase2_models.rs"),
    UncheckedArithmeticOverflow { op: BinOp::Add, operand_tys: (ty(), ty()) }
        => Coverage::Tested("overflow_call_tests.rs (unchecked_add/sub/mul)"),
    DivisionByZero {}
        => Coverage::Tested("error_detection.rs, pipeline.rs, real_ay_verification.rs"),
    RemainderByZero {}
        => Coverage::Tested("error_detection.rs, self_verify.rs"),
    IndexOutOfBounds {}
        => Coverage::Tested("error_detection.rs, pipeline.rs, self_verify.rs, self_verify_ay.rs"),
    SliceBoundsCheck {}
        => Coverage::Tested(
            "trust-strengthen/cex_guided.rs (unit), trust-vcgen/tests/slice_bounds_guard_linkage.rs",
        ),
    UncheckedIndexBounds { callee: String::new(), detail: String::new() }
        => Coverage::Tested("sep_engine get_unchecked lane"),
    Assertion { message: String::new() }
        => Coverage::Tested("self_verify_ay.rs, e2e_loop.rs, pipeline.rs, m5_acceptance.rs"),
    ContractInvariant { expression: String::new() }
        => Coverage::Tested("contracts.rs / spec_parser.rs invariant clause"),
    Precondition { callee: String::new() }
        => Coverage::Tested("m4_precondition.rs"),
    Postcondition {}
        => Coverage::Tested("pipeline.rs, m3_acceptance.rs, m3_real_crate.rs"),
    CastOverflow { from_ty: ty(), to_ty: ty() }
        => Coverage::Tested("trust-strengthen/cex_guided.rs, trust-strengthen/counterexample.rs"),
    NegationOverflow { ty: ty() }
        => Coverage::Tested("trust-strengthen/cex_guided.rs, trust-strengthen/proposer.rs"),
    Unreachable {}
        => Coverage::Tested("trust-convergence/integration.rs, trust-strengthen/proposer.rs"),
    UnsupportedMir { kind: String::new(), detail: String::new() }
        => Coverage::Tested("trust-report canonical tags, compiler transport fail-closed tests"),
    DeadState { state: String::new() }
        => Coverage::Documented("State machine property; exercised via TLA+ backend, not ay e2e"),
    Deadlock {}
        => Coverage::Tested("trust-strengthen/cex_guided.rs, trust-strengthen/proposer.rs"),
    Temporal { property: String::new(), machine: None }
        => Coverage::Tested("pipeline.rs"),
    Liveness {
        property: LivenessProperty {
            name: String::new(),
            operator: TemporalOperator::Eventually,
            predicate: String::new(),
            consequent: None,
            fairness: vec![],
        },
        machine: None,
    }
        => Coverage::Tested("trust-router/ty_backend.rs (ty_handles_liveness_vcs)"),
    Fairness { constraint: FairnessConstraint::Weak { action: String::new(), vars: vec![] } }
        => Coverage::Tested(
            "trust-router/ty_backend.rs (ty_handles_fairness_vcs), \
             trust-router/termination_dispatch.rs",
        ),
    TaintViolation { source_label: String::new(), sink_kind: String::new(), path_length: 0 }
        => Coverage::Tested("trust-vcgen/tests/infoflow_leak.rs"),
    RefinementViolation { spec_file: String::new(), action: String::new() }
        => Coverage::Documented("Refinement checking; tested at trust-types description() level"),
    ResilienceViolation {
        service: String::new(),
        failure_mode: String::new(),
        reason: String::new(),
    }
        => Coverage::Tested("misc_vc_pipeline.rs (VC construction + Report)"),
    ProtocolViolation { protocol: String::new(), violation: String::new() }
        => Coverage::Documented("Protocol composition; tested at trust-types description() level"),
    NonTermination { context: String::new(), measure: String::new() }
        => Coverage::Tested(
            "trust-router/tests/full_pipeline.rs, trust-clean/tests/termination_u32_bound.rs, \
             trust-vcgen/tests/checked_loop_contracts.rs",
        ),
    DataRace { variable: String::new(), thread_a: String::new(), thread_b: String::new() }
        => Coverage::Tested("concurrency_e2e.rs"),
    InsufficientOrdering { variable: String::new(), actual: String::new(), required: String::new() }
        => Coverage::Tested("concurrency_e2e.rs"),
    TranslationValidation { pass: String::new(), check: String::new() }
        => Coverage::Tested("misc_vc_pipeline.rs (VC construction + Report)"),
    FloatDivisionByZero {}
        => Coverage::Tested("float_unsafe_e2e.rs (vcgen pipeline)"),
    FloatOverflowToInfinity { op: BinOp::Add, operand_ty: ty() }
        => Coverage::Tested("ay_phase2_models.rs"),
    InvalidDiscriminant { place_name: String::new() }
        => Coverage::Tested("error_detection.rs (vcgen pipeline)"),
    AggregateArrayLengthMismatch { expected: 0, actual: 0 }
        => Coverage::Documented("Rvalue safety; L2 domain, backend-dependent"),
    UnsafeOperation { desc: String::new() }
        => Coverage::Tested("float_unsafe_e2e.rs (direct VC + solver, no vcgen)"),
    SavedReturnAddressOverwrite { access_width_bytes: 8, slot: String::new() }
        => Coverage::Tested("trust-report canonical tag inventory"),
    FormatStringViolation { callee: String::new(), evidence: String::new() }
        => Coverage::Tested("trust-report canonical tag inventory"),
    TaintedIndirectBranch {
        sink_kind: String::new(),
        target: String::new(),
        evidence: String::new(),
    }
        => Coverage::Tested("trust-report canonical tag inventory"),
    BinaryAbiContradiction { fact: String::new(), evidence: String::new() }
        => Coverage::Tested("trust-report canonical tag inventory"),
    BinaryCopySinkLengthViolation { callee: String::new(), desc: String::new() }
        => Coverage::Tested("trust-report canonical tag inventory"),
    FfiBoundaryViolation { callee: String::new(), desc: String::new() }
        => Coverage::Tested("float_unsafe_e2e.rs (vcgen pipeline)"),
    CopyBoundsViolation {
        callee: String::new(),
        direction: String::new(),
        detail: String::new(),
    }
        => Coverage::Tested("trust-report canonical tag inventory"),
    ExternallyMutableAllocationBounds {
        allocation_kind: String::new(),
        live_size: String::new(),
        detail: String::new(),
    }
        => Coverage::Tested("trust-report canonical tag inventory"),
    UnboundedAllocation { callee: String::new(), count: String::new(), detail: String::new() }
        => Coverage::Tested("trust-report canonical tag inventory, vcgen allocation tests"),
    UseAfterFree {}
        => Coverage::Tested("ownership_e2e.rs (provenance tracker + MIR)"),
    DoubleFree {}
        => Coverage::Tested("ownership_e2e.rs (provenance tracker + MIR)"),
    AliasingViolation { mutable: false }
        => Coverage::Tested("ownership_e2e.rs (ownership scan + MIR)"),
    LifetimeViolation {}
        => Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
    SendViolation {}
        => Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
    SyncViolation {}
        => Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
    FunctionalCorrectness { property: String::new(), context: String::new() }
        => Coverage::Tested(
            "contract_e2e.rs, misc_vc_pipeline.rs (vcgen pipeline, partial Router bypass)",
        ),
    HardenedBoundary {
        category: HardenedVcCategory::ByteLoss,
        callee: String::new(),
        detail: String::new(),
    }
        => Coverage::Tested("trust-report hardened category and canonical tag tests"),
    LoopInvariantInitiation { invariant: String::new(), header_block: 0 }
        => Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    LoopInvariantConsecution { invariant: String::new(), header_block: 0 }
        => Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    // Trust: this said `Tested("contract_e2e.rs (vcgen pipeline + ay)")`, which
    // overstated it in the specific way this census exists to prevent. No
    // production path CONSTRUCTS a sufficiency VC: every occurrence in the tree
    // is a test building one by hand (contract_e2e, model_roundtrip,
    // proptest_roundtrip) or a match arm in serialization/reporting. vcgen emits
    // the E4 PAIR -- initiation and consecution -- and nothing else, so no
    // pipeline test could have exercised this variant.
    LoopInvariantSufficiency { invariant: String::new(), header_block: 0 }
        => Coverage::Documented(
            "NOT EMITTED BY vcgen. The wire/serialization shape is round-tripped by \
             model_roundtrip.rs and proptest_roundtrip.rs, so the variant is exercised as \
             DATA. Nothing generates it as an obligation: the 'invariant too weak for the \
             postcondition' check has no producer. Wiring one is the work; until then this \
             row must not read as pipeline coverage.",
        ),
    TypeRefinementViolation { variable: String::new(), predicate: String::new() }
        => Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    FrameConditionViolation { variable: String::new(), function: String::new() }
        => Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
}

/// Exercises the compile-time guard and rejects a census that lists a variant
/// twice (which the lint permits: a duplicate arm is merely unreachable).
#[test]
fn test_vckind_exhaustiveness_guard() {
    let coverage = census();

    // Keeps `census_name_of` live and confirms each instance really is the
    // variant its entry names.
    for entry in &coverage {
        assert_eq!(
            census_name_of(&entry.kind),
            entry.variant_name,
            "census entry constructs a different variant than it names"
        );
    }

    let mut names: Vec<&str> = coverage.iter().map(|e| e.variant_name).collect();
    names.sort_unstable();
    for pair in names.windows(2) {
        assert_ne!(
            pair[0], pair[1],
            "VcKind::{} is listed twice in the census; its coverage is double-counted",
            pair[0]
        );
    }

    let tested = coverage.iter().filter(|e| matches!(e.coverage, Coverage::Tested(_))).count();
    eprintln!("VcKind exhaustiveness guard: {} variants", coverage.len());
    eprintln!("  Tested:     {tested}");
    eprintln!("  Documented: {}", coverage.len() - tested);
    for entry in coverage.iter().filter(|e| matches!(e.coverage, Coverage::Documented(_))) {
        eprintln!("  VcKind::{}: {}", entry.variant_name, entry.coverage.detail());
    }
}

/// Every variant reaches `VcKind::description()` -- the genuinely exhaustive
/// internal match in trust-types -- and yields a non-empty description.
#[test]
fn test_vckind_description_completeness() {
    for entry in &census() {
        assert!(
            !entry.kind.description().is_empty(),
            "VcKind::{} has an empty description()",
            entry.variant_name
        );
        assert!(
            !entry.coverage.detail().is_empty(),
            "VcKind::{} has an empty coverage justification",
            entry.variant_name
        );
    }
}

/// Every variant reaches `VcKind::proof_level()` -- the second exhaustive
/// internal match -- and lands in one of the documented tiers.
#[test]
fn test_vckind_proof_level_completeness() {
    for entry in &census() {
        let level = entry.kind.proof_level();
        assert!(
            matches!(level, ProofLevel::L0Safety | ProofLevel::L1Functional | ProofLevel::L2Domain),
            "VcKind::{} returned an untiered proof level: {level:?}",
            entry.variant_name
        );
    }
}
