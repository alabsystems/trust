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
    /// The `ProofLevel` this census EXPECTS `kind.proof_level()` to return: a
    /// reviewed pin per variant. `filter_vcs_by_level` (trust-vcgen) drops every
    /// VC above the policy's level, so moving a safety kind from L0 to L1 drops
    /// it from an L0 run without a word; here it fails the build's soundness row
    /// (`fast.vckind-exhaustiveness` in tests/run_trust_comprehensive_harness.sh).
    level: ProofLevel,
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
    ($( $variant:ident { $($field:tt)* } => $level:ident, $coverage:expr ),+ $(,)?) => {
        fn census() -> Vec<VcKindCoverage> {
            vec![$(
                VcKindCoverage {
                    variant_name: stringify!($variant),
                    kind: VcKind::$variant { $($field)* },
                    level: ProofLevel::$level,
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
// Each entry is `Variant { fields } => <expected ProofLevel>, <coverage>`; the
// level is what `VcKind::proof_level()` must return for that instance
// (`test_vckind_proof_level_pins`). `HardenedBoundary`'s level depends on its
// category, so its categories are pinned separately (`hardened_census!`).
vckind_census! {
    ArithmeticOverflow { op: BinOp::Add, operand_tys: (ty(), ty()) }
        => L0Safety, Coverage::Tested(
            "error_detection.rs, pipeline.rs, self_verify.rs, ay_phase2_models.rs",
        ),
    ShiftOverflow { op: BinOp::Shl, operand_ty: ty(), shift_ty: ty() }
        => L0Safety, Coverage::Tested("ay_phase2_models.rs"),
    UncheckedArithmeticOverflow { op: BinOp::Add, operand_tys: (ty(), ty()) }
        => L0Safety, Coverage::Tested("overflow_call_tests.rs (unchecked_add/sub/mul)"),
    DivisionByZero {}
        => L0Safety, Coverage::Tested("error_detection.rs, pipeline.rs, real_ay_verification.rs"),
    RemainderByZero {}
        => L0Safety, Coverage::Tested("error_detection.rs, self_verify.rs"),
    IndexOutOfBounds {}
        => L0Safety, Coverage::Tested(
            "error_detection.rs, pipeline.rs, self_verify.rs, self_verify_ay.rs",
        ),
    SliceBoundsCheck {}
        => L0Safety, Coverage::Tested(
            "trust-strengthen/cex_guided.rs (unit), trust-vcgen/tests/slice_bounds_guard_linkage.rs",
        ),
    UncheckedIndexBounds { callee: String::new(), detail: String::new() }
        => L0Safety, Coverage::Tested("sep_engine get_unchecked lane"),
    Assertion { message: String::new() }
        => L0Safety, Coverage::Tested(
            "self_verify_ay.rs, e2e_loop.rs, pipeline.rs, m5_acceptance.rs",
        ),
    ContractInvariant { expression: String::new() }
        => L1Functional, Coverage::Tested("contracts.rs / spec_parser.rs invariant clause"),
    Precondition { callee: String::new() }
        => L1Functional, Coverage::Tested("m4_precondition.rs"),
    Postcondition {}
        => L1Functional, Coverage::Tested("pipeline.rs, m3_acceptance.rs, m3_real_crate.rs"),
    CastOverflow { from_ty: ty(), to_ty: ty() }
        => L0Safety, Coverage::Tested(
            "trust-strengthen/cex_guided.rs, trust-strengthen/counterexample.rs",
        ),
    NegationOverflow { ty: ty() }
        => L0Safety, Coverage::Tested(
            "trust-strengthen/cex_guided.rs, trust-strengthen/proposer.rs",
        ),
    Unreachable {}
        => L0Safety, Coverage::Tested(
            "trust-convergence/integration.rs, trust-strengthen/proposer.rs",
        ),
    UnsupportedMir { kind: String::new(), detail: String::new() }
        => L0Safety, Coverage::Tested(
            "trust-report canonical tags, compiler transport fail-closed tests",
        ),
    DeadState { state: String::new() }
        => L2Domain, Coverage::Documented(
            "State machine property; exercised via TLA+ backend, not ay e2e",
        ),
    Deadlock {}
        => L2Domain, Coverage::Tested(
            "trust-strengthen/cex_guided.rs, trust-strengthen/proposer.rs",
        ),
    Temporal { property: String::new(), machine: None }
        => L2Domain, Coverage::Tested("pipeline.rs"),
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
        => L2Domain, Coverage::Tested("trust-router/ty_backend.rs (ty_handles_liveness_vcs)"),
    Fairness { constraint: FairnessConstraint::Weak { action: String::new(), vars: vec![] } }
        => L2Domain, Coverage::Tested(
            "trust-router/ty_backend.rs (ty_handles_fairness_vcs), \
             trust-router/termination_dispatch.rs",
        ),
    TaintViolation { source_label: String::new(), sink_kind: String::new(), path_length: 0 }
        => L1Functional, Coverage::Tested("trust-vcgen/tests/infoflow_leak.rs"),
    RefinementViolation { spec_file: String::new(), action: String::new() }
        => L2Domain, Coverage::Documented(
            "Refinement checking; tested at trust-types description() level",
        ),
    ResilienceViolation {
        service: String::new(),
        failure_mode: String::new(),
        reason: String::new(),
    }
        => L1Functional, Coverage::Tested("misc_vc_pipeline.rs (VC construction + Report)"),
    ProtocolViolation { protocol: String::new(), violation: String::new() }
        => L2Domain, Coverage::Documented(
            "Protocol composition; tested at trust-types description() level",
        ),
    NonTermination { context: String::new(), measure: String::new() }
        => L1Functional, Coverage::Tested(
            "trust-router/tests/full_pipeline.rs, trust-clean/tests/termination_u32_bound.rs, \
             trust-vcgen/tests/checked_loop_contracts.rs",
        ),
    DataRace { variable: String::new(), thread_a: String::new(), thread_b: String::new() }
        => L0Safety, Coverage::Tested("concurrency_e2e.rs"),
    InsufficientOrdering { variable: String::new(), actual: String::new(), required: String::new() }
        => L1Functional, Coverage::Tested("concurrency_e2e.rs"),
    TranslationValidation { pass: String::new(), check: String::new() }
        => L1Functional, Coverage::Tested("misc_vc_pipeline.rs (VC construction + Report)"),
    FloatDivisionByZero {}
        => L1Functional, Coverage::Tested("float_unsafe_e2e.rs (vcgen pipeline)"),
    FloatOverflowToInfinity { op: BinOp::Add, operand_ty: ty() }
        => L1Functional, Coverage::Tested("ay_phase2_models.rs"),
    InvalidDiscriminant { place_name: String::new() }
        => L0Safety, Coverage::Tested("error_detection.rs (vcgen pipeline)"),
    AggregateArrayLengthMismatch { expected: 0, actual: 0 }
        => L0Safety, Coverage::Documented("Rvalue safety (L0); no e2e test, backend-dependent"),
    UnsafeOperation { desc: String::new() }
        => L0Safety, Coverage::Tested("float_unsafe_e2e.rs (direct VC + solver, no vcgen)"),
    SavedReturnAddressOverwrite { access_width_bytes: 8, slot: String::new() }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    FormatStringViolation { callee: String::new(), evidence: String::new() }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    TaintedIndirectBranch {
        sink_kind: String::new(),
        target: String::new(),
        evidence: String::new(),
    }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    BinaryAbiContradiction { fact: String::new(), evidence: String::new() }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    BinaryCopySinkLengthViolation { callee: String::new(), desc: String::new() }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    FfiBoundaryViolation { callee: String::new(), desc: String::new() }
        => L0Safety, Coverage::Tested("float_unsafe_e2e.rs (vcgen pipeline)"),
    CopyBoundsViolation {
        callee: String::new(),
        direction: String::new(),
        detail: String::new(),
    }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    ExternallyMutableAllocationBounds {
        allocation_kind: String::new(),
        live_size: String::new(),
        detail: String::new(),
    }
        => L0Safety, Coverage::Tested("trust-report canonical tag inventory"),
    UnboundedAllocation { callee: String::new(), count: String::new(), detail: String::new() }
        => L0Safety, Coverage::Tested(
            "trust-report canonical tag inventory, vcgen allocation tests",
        ),
    UseAfterFree {}
        => L0Safety, Coverage::Tested("ownership_e2e.rs (provenance tracker + MIR)"),
    DoubleFree {}
        => L0Safety, Coverage::Tested("ownership_e2e.rs (provenance tracker + MIR)"),
    AliasingViolation { mutable: false }
        => L0Safety, Coverage::Tested("ownership_e2e.rs (ownership scan + MIR)"),
    LifetimeViolation {}
        => L0Safety, Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
    SendViolation {}
        => L0Safety, Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
    SyncViolation {}
        => L0Safety, Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
    FunctionalCorrectness { property: String::new(), context: String::new() }
        => L1Functional, Coverage::Tested(
            "contract_e2e.rs, misc_vc_pipeline.rs (vcgen pipeline, partial Router bypass)",
        ),
    HardenedBoundary {
        category: HardenedVcCategory::ByteLoss,
        callee: String::new(),
        detail: String::new(),
    }
        => L1Functional, Coverage::Tested("trust-report hardened category and canonical tag tests"),
    LoopInvariantInitiation { invariant: String::new(), header_block: 0 }
        => L1Functional, Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    LoopInvariantConsecution { invariant: String::new(), header_block: 0 }
        => L1Functional, Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    // Trust: this said `Tested("contract_e2e.rs (vcgen pipeline + ay)")`, which
    // overstated it in the specific way this census exists to prevent. No
    // production path CONSTRUCTS a sufficiency VC: every occurrence in the tree
    // is a test building one by hand (contract_e2e, model_roundtrip,
    // proptest_roundtrip) or a match arm in serialization/reporting. vcgen emits
    // the E4 PAIR -- initiation and consecution -- and nothing else, so no
    // pipeline test could have exercised this variant.
    LoopInvariantSufficiency { invariant: String::new(), header_block: 0 }
        => L1Functional, Coverage::Documented(
            "NOT EMITTED BY vcgen. The wire/serialization shape is round-tripped by \
             model_roundtrip.rs and proptest_roundtrip.rs, so the variant is exercised as \
             DATA. Nothing generates it as an obligation: the 'invariant too weak for the \
             postcondition' check has no producer. Wiring one is the work; until then this \
             row must not read as pipeline coverage.",
        ),
    TypeRefinementViolation { variable: String::new(), predicate: String::new() }
        => L1Functional, Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    FrameConditionViolation { variable: String::new(), function: String::new() }
        => L1Functional, Coverage::Tested("contract_e2e.rs (vcgen pipeline + ay)"),
    TypeInvariant {
        ty: String::new(),
        point: TypeInvariantPoint::Establish,
        site: TypeInvariantSite { block: 0, statement_index: 0 },
        conjunct: 0,
        ordinal: 0,
        edge: None,
    }
        => L1Functional, Coverage::Documented(
            "Emitted only by trust-vcgen's TINV step-7 pre-pass (type_invariant), which nothing \
             outside tests calls until step 9 (docs/design/2026-10-04-type-invariant-tinv.md \
             §6); kernel authority is admitted by kind since step 7.7, behind the row \
             situatedness gate (TINV-8, TINV-9(j)): trust-vcgen type_invariant/certify_tests.rs, \
             trust-certify kernel_authority_kind_gate.rs.",
        ),
    // A tuple variant: `{ 0: … }` is its brace form, so the same macro constructs
    // and matches it. The level is the one 1007a19e07 pins in trust-types'
    // `contract_decline_never_mints_static_or_language_check_authority`.
    DeclinedContractBody {
        0: Box::new(ContractBodyDecline {
            cause: ContractBodyDeclineCause::UnconstrainedReturnCall,
            source_contract_index: 0,
            source_predicate: Formula::Var("authored_predicate".into(), Sort::Bool),
        }),
    }
        => L1Functional, Coverage::Tested(
            "trust-types formula/contract_decline.rs (unit: no static or language-check \
             authority), trust-vcgen contract_decline_tests.rs (the producer retains the \
             authored predicate at a typed body-lowering decline)",
        ),
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
/// internal match -- and lands on the tier its census entry pins. (This used to
/// assert only that the level was one of `ProofLevel`'s three variants, which
/// every value of the type is: it could not fail.) A change to a kind's tier is
/// a change to what an L0 policy verifies, so it must change this table too.
#[test]
fn test_vckind_proof_level_pins() {
    let mut wrong = Vec::new();
    for entry in &census() {
        let level = entry.kind.proof_level();
        if level != entry.level {
            wrong.push(format!(
                "VcKind::{}: proof_level() is {level:?}, the census pins {:?}",
                entry.variant_name, entry.level
            ));
        }
    }
    assert!(wrong.is_empty(), "proof levels moved:\n{}", wrong.join("\n"));
}

/// `VcKind::HardenedBoundary`'s `proof_level()` arm splits on the category
/// (unsafe operations and FFI boundaries are UB-class, L0; the rest are
/// functional, L1), which the one-instance census row above cannot see. This
/// pins every category's level, from one token list like `vckind_census!`: a
/// `HardenedVcCategory` the list does not name fails to compile.
macro_rules! hardened_census {
    ($( $category:ident $( ($arg:expr) )? => $level:ident ),+ $(,)?) => {
        fn hardened_census() -> Vec<(HardenedVcCategory, ProofLevel)> {
            vec![$( (HardenedVcCategory::$category $( ($arg) )?, ProofLevel::$level) ),+]
        }

        fn hardened_census_name_of(category: &HardenedVcCategory) -> &'static str {
            #[deny(non_exhaustive_omitted_patterns)]
            match category {
                $( HardenedVcCategory::$category { .. } => stringify!($category), )+
                _ => unreachable!(
                    "unreachable while non_exhaustive_omitted_patterns is denied: an \
                     unlisted HardenedVcCategory fails to compile above"
                ),
            }
        }
    };
}

hardened_census! {
    RawPathApi => L1Functional,
    PathIdentity => L1Functional,
    PermissionChange => L1Functional,
    PermissionCreate => L1Functional,
    PermissionWindow => L1Functional,
    Utf8Reject => L1Functional,
    ByteLoss => L1Functional,
    ErrorDiscard => L1Functional,
    PanicBoundary => L1Functional,
    CompatObservable => L1Functional,
    ProcessSemantics => L1Functional,
    TrustDomain => L1Functional,
    TrustDomainOrder => L1Functional,
    UnsafeOperation => L0Safety,
    FfiBoundary => L0Safety,
    Unknown(Symbol::intern("census")) => L1Functional,
}

#[test]
fn test_hardened_boundary_proof_level_pins() {
    let mut wrong = Vec::new();
    let mut names = Vec::new();
    for (category, pinned) in hardened_census() {
        names.push(hardened_census_name_of(&category));
        let kind =
            VcKind::HardenedBoundary { category, callee: String::new(), detail: String::new() };
        let level = kind.proof_level();
        if level != pinned {
            wrong.push(format!("HardenedBoundary {category:?}: {level:?}, pinned {pinned:?}"));
        }
    }
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), hardened_census().len(), "a category is listed twice");
    assert!(wrong.is_empty(), "hardened proof levels moved:\n{}", wrong.join("\n"));
}
