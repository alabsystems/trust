// dead_code audit: crate-level suppression removed
//! trust-clean: Certificate pipeline for clean proof verification
//!
//! Bridges Trust verification conditions to clean proof certificates.
//! The certificate chain is: solver -> certificate -> clean kernel.
//! If clean accepts the certificate, the proof is machine-checked and
//! the result upgrades from Trusted to Certified.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: `clean axioms` instrument — transitive axiom-closure analysis. The
// success metric for the Clean-dependent-types program is "modulo 3 axioms";
// this module computes it. See docs/PLAN-clean-dependent-type-reflection.md.
pub mod axioms;
// Trust: WHOLE-ENVIRONMENT axiom census — the complement to the per-decl residue
// gates: asserts every ConstantKind::Axiom in a pipeline environment is one of the
// 3 foundational axioms + the 4 Quot kernel primitives, catching a 4th axiom even
// under a kernel-whitelisted name the residue filter would hide.
pub mod axiom_census;
pub(crate) mod bundle;
pub(crate) mod canonical;
// Trust: type-reflection functor R (scalar fragment) — Trust types -> Clean
// dependent-type carriers. See docs/PLAN-clean-dependent-type-reflection.md (S0).
pub mod reflect;
// Trust: source-level reflection — parse a function's string form (as the targo
// source extractor yields) into a kernel-checked dependent contract type.
pub mod source_reflect;
// Trust: S1 — ground reflected terms in the REAL clean-kernel (axiom-free
// inductives), discharging the carrier-axiom encoding toward "modulo 3 axioms".
pub mod clean_ground;
// Trust: recognizer-side assignment typing. Public Trust MIR is deserializable and
// therefore adversarial; semantic recognizers must prove that every assignment they
// chase writes a value of the destination place's (projection-aware) type.
pub(crate) mod assignment_types;
// Trust: GOAL-ITEM #4 (FAITHFULNESS) — the MirSem semantic anchor pinned in Clean
// + Lemma 1A (operand adequacy), proving the scalar-operand reflection ADEQUATE to
// the MIR operational semantics. See docs/PLAN-clean-dependent-type-reflection.md §2/§0.
pub mod mirsem;
// Trust: RE-ANCHOR POC (goal item 1) — relocate the faithfulness spec OFF the
// bespoke `Trust.MirSem` model ONTO a Clean denotation KEYED TO trust-ir's
// UNIVERSAL IR syntax (`Trust.TrustIr.BinOp` / `evalBin`). Additive: it pins the
// trust-ir-keyed anchor IN PARALLEL to MirSem and proves a straight-line binary
// refinement RELATIVE TO the trust-ir denotation, kernel-checked modulo 3. See
// the module header + reports/trustir-reanchor-scope-out.md for the gap analysis.
pub mod trustir_anchor;
// Trust: RE-ANCHOR Lane T (MirSem teardown) — the loop RANKING/TERMINATION theory
// (`loopRankTerminates` / composed `loopTotalCorrect` + the pure Int/Nat rank-lemma
// suite) ported byte-for-byte from `Trust.MirSem` onto the trust-ir denotation
// (`Trust.TrustIr.execLoop` / `execLoopS`), registered under `Trust.TrustIr.*` names
// only, modulo exactly 3. Provides the per-function total-correctness instances the §6
// via-trustir gates consume (eliminating the in-path MirSem termination residue).
pub mod trustir_termination;
// Trust: LANE S (MirSem-teardown prerequisite) — the SAFETY-VC adequacy tier
// RELOCATED onto the trust-ir denotation: the 8 safety-VC kinds' machine-semantics
// specs re-pinned under `Trust.TrustIr.*` (same empirically-matched bodies as the
// MirSem Lemmas 2–9), with the formula-aware LIVE-grounder def-eq bridge and the
// via-trustir function-level gate. Additive: zero MirSem declarations in its env.
pub mod trustir_safety;
// Trust: the trust-ir CALL denotation (call-spine residue #1, closed) — the
// inter-procedural `Call` inductive + `callResult`/`callCallee` projections + the
// PROVEN `callRefinesContract` transport lemma + per-call-site instances, ported
// byte-for-byte from `Trust.MirSem` onto the trust-ir env under `Trust.TrustIr.*`
// names only (zero MirSem declarations), modulo exactly 3. Provides the kernel
// evidence for prove.rs's `call_return_fully_faithful_via_trustir` via-path, so a
// call-spine caller certifies trust-ir-PRIMARY (MirSem fallback returns to 0).
pub mod trustir_call;
// Trust: ADT-return leaf (gap-queue #2, 2026-07-07) — the KERNEL-CHECKED witness for
// the Result/Option-ADT AGGREGATE RETURN shape (`if guard { Ok(x) } else { Err(e) }`,
// the CONSTRUCTION dual of the discriminant-guard CONSUMPTION shape). Sibling to
// `trustir_anchor`'s `IrGuardedIndex`/`IrGuardedConstIndex` — same `Bool.rec` +
// `congrArg`-transport recipe, generalized from an `Int` motive to a freshly-
// registered outer ADT carrier (reusing the EXISTING Phase-4 `reflect::reflect_enum`
// / `clean_ground::register_adt_carriers` machinery unchanged). See the module doc.
pub mod trustir_adt;
// Trust: MULTI-VALUE SwitchInt disjunctive-equality guard (2026-07-08) — the
// KERNEL-CHECKED witness for `if discr ∈ {v1,...,vN} { then } else { else }`
// (the `core::u8::is_ascii_whitespace`-class shape: ONE `SwitchInt` whose
// explicit targets all converge on a single arm). Sibling to `trustir_adt`
// (same `Bool.rec` + `congrArg`-transport recipe, generalized to an N-ARY
// `Bool.or` fold over a plain `Int` motive — no ADT carrier registration).
// See the module doc.
pub mod trustir_multieq;
// Trust: FIELDLESS-ENUM Clone/eq lane (2026-07-16) — the KERNEL-CHECKED
// witnesses for the derived `Clone::clone` (deref-copy identity) and
// `PartialEq::eq` (discriminant-compare) of a C-LIKE (fieldless) enum. See the
// module doc for the model + honesty tier.
pub mod trustir_fieldless;
// Trust: structural-fold lane, RUNG A (mini-ADT pilot, 2026-07-10;
// docs/design/2026-07-10-structural-fold-lane.md §5) — the KERNEL-CHECKED
// witness for an Int-valued STRUCTURAL FOLD over an `Arc`-recursive enum:
// recursor-defined-total interpreter (the kernel checks totality by
// type-checking the `<T>.rec` definition), IH-slot mapping (a recursive call
// translates to the recursor's induction-hypothesis slot, never an opaque
// call result), strict-subterm provenance (everything else is a NAMED
// decline: `non_subterm_recursive_arg` et al., design §6). SCC-of-1 only,
// no memo, no accumulator. See the module doc for the honesty tier + named
// premises (P-ACYC, P-ARC-DEREF).
pub mod trustir_fold;
pub mod trustir_fold_expr;
// Trust: structural-fold lane, RUNG E (2026-07-11; design §3.4 + §5 Rung E) —
// the G-FAMILY WRAPPERS over the rung-C/D-certified memoized Expr folds:
// folder-LAUNCH wrappers (build folder + `fold_opt_or_clone`, certified by
// per-wrapper inlining — design §3.4 option (b), structurally forced: the
// generic driver hides the concrete-folder call edge from the registry) and
// pure ADT DELEGATES (certified through the callees-first registry + the
// TExpr-valued `CallE`/`callResultE` transport twin — design §3.4 option (a),
// the growth path). The kernel pieces (wrapAdequate/wrapAdequateD +
// callReturnInstanceE) live in `trustir_fold_expr`'s rung-E section. See the
// module doc for the fail-closed decline vocabulary.
pub mod trustir_fold_wrap;
// Trust: the SHIPPED Lean↔Clean bridge gate — machine-imports trust-ir's REAL
// Lean 4.8 `semIntBinOp` semantics from VENDORED, sha256-manifested `.olean`
// artifacts (fixtures/trustir-oleans + vendor/lean-core-oleans) and proves the
// per-op agreement theorems against trust-clean's denotation constants
// (`Int.add/sub/mul/…`), kernel-checked with axiom_deps = ∅, fail-closed on
// pin drift / tampered artifacts / axiom residue / accepted forgeries. The
// default-on integration test is tests/lean_clean_bridge.rs; the regeneration
// audit lane is scripts/regen-trustir-oleans.sh.
pub mod trustir_bridge;
// Trust: M4 v0 — the general bounded-CFG induction FRAMEWORK. A typed
// `CfgFamilySpec` (~20-40 lines) is planned, statically envelope-checked,
// and emitted into the SAME kernel-checking discipline `trustir_bridge.rs`'s
// hand-written arms use — see the module doc
// (reports/m4-general-cfg-induction-framework-design-2026-07-07.md).
pub mod cfg_family;
// Trust: GOAL-ITEM #3 — the STRUCTURED IEEE-754 float model. The IEEE-754
// classification predicates (isNaN/isInf/isZero/isSubnormal) as Clean defs over the
// `Trust.Float32`/`Trust.Float64` structured carriers (reflect::reflect_float),
// kernel-checked modulo 3. The value/rounding-ops layer is the deferred Phase 2.
pub(crate) mod certificate;
pub mod certification;
pub mod clean_bridge;
pub(crate) mod composition_transfer;
pub mod error;
pub(crate) mod fingerprint;
pub mod float_class;
pub mod integration;
pub(crate) mod kernel_check;
pub(crate) mod logic_classification;
pub(crate) mod obligation;
pub(crate) mod proof_transfer;
// Bridge composition DAG to clean proof transfer (similarity search)
pub(crate) mod ay_proof_bridge;
pub(crate) mod reconstruction;
pub(crate) mod replay;
pub(crate) mod tactic_gen;
pub(crate) mod tactics;
pub(crate) mod transfer_bridge;
pub(crate) mod v1_reuse;

/// Exact compiler lang-item identity for the inherited contract return wrapper.
///
/// This intrinsic is semantically transparent to the Clean return reflection;
/// an arbitrary local function whose name merely contains this substring is
/// not. Accept the canonical def-path itself or that same function followed by
/// one balanced trailing turbofish. Generic-looking segments anywhere else,
/// doubled separators, trailing text, and unbalanced arguments all decline.
pub(crate) fn is_contract_check_ensures_callee(callee: &str) -> bool {
    const BASE: &str = "core::intrinsics::contract_check_ensures";
    if callee == BASE {
        return true;
    }
    let Some(suffix) = callee.strip_prefix(BASE).and_then(|rest| rest.strip_prefix("::<")) else {
        return false;
    };
    if suffix.len() < 2 || !suffix.ends_with('>') {
        return false;
    }

    // The opening `<` was consumed above. Its matching close must be the final
    // byte; nested type arguments are allowed, but an early close followed by
    // another path segment is not the intrinsic's def-path rendering.
    let mut depth = 1usize;
    for (index, ch) in suffix.char_indices() {
        match ch {
            '<' => depth = depth.checked_add(1).unwrap_or(usize::MAX),
            '>' => {
                let Some(next) = depth.checked_sub(1) else { return false };
                depth = next;
                if depth == 0 && index + ch.len_utf8() != suffix.len() {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

#[cfg(test)]
mod contract_intrinsic_identity_tests {
    use super::is_contract_check_ensures_callee;

    #[test]
    fn contract_check_ensures_identity_is_exact() {
        assert!(is_contract_check_ensures_callee("core::intrinsics::contract_check_ensures"));
        assert!(is_contract_check_ensures_callee(
            "core::intrinsics::contract_check_ensures::<Option<Vec<i32>>, i32>"
        ));

        for malformed in [
            "core::<evil>::intrinsics::contract_check_ensures",
            "core::::intrinsics::contract_check_ensures",
            "core::intrinsics::contract_check_ensures<garbage",
            "core::intrinsics::contract_check_ensures::<i32",
            "core::intrinsics::contract_check_ensures::<i32>::forged",
            "crate::contract_check_ensures",
        ] {
            assert!(!is_contract_check_ensures_callee(malformed), "accepted {malformed}");
        }
    }
}

#[cfg(test)]
mod e2e_tests;

// Trust: `clean axioms` instrument — transitive axiom closure + foundational gate
pub use axioms::{
    AxiomReport, AxiomViolation, FOUNDATIONAL_AXIOMS, axiom_closure, is_foundational,
    require_axioms_subset, require_foundational,
};
pub use bundle::{
    TRUST_CERT_BUNDLE_FORMAT_VERSION, TrustProofCertificateBundle,
    TrustProofCertificateBundleMetadata, deserialize_certificate_bundle, read_certificate_bundle,
    serialize_certificate_bundle, write_certificate_bundle,
};
pub use canonical::canonical_vc_bytes;
pub use certificate::{
    TrustProofCertificate, generate_certificate, generate_certificate_unchecked, verify_certificate,
};
// Trust: Certification pipeline — post-verification clean kernel certification
// Enhanced with proof term generation for QF_LIA and QF_UF theories
// Added classify_vc_scope for scope-aware certification
pub use certification::{
    CertificationPipeline, CertificationResult, ProofGeneration, ProofTheory,
    classify_vc_for_certification, classify_vc_scope, generate_proof_term, qf_lia_axiom,
    qf_uf_axiom,
};
// Trust: M4 v0 — the generated-family report surface.
pub use cfg_family::gate::GeneratedFamilyReport;
// Trust: Integration bridge — connects clean pipeline to trust-proof-cert
pub use clean_bridge::{
    deserialize_proof_cert, serialize_proof_cert, translate_formula, translate_vc_to_clean_theorem,
    verify_proof_cert,
};
// Trust: EXPANDED TRUST TYPES — ground a reflected refinement/spec verification
// type (reuses the prelude `Subtype` for the dependent subset; modulo 3, NO 4th axiom).
pub use clean_ground::ground_verification_type;
// Trust: Phase 1 — named-struct inductive registration + structural grounding
pub use clean_ground::{
    AdtRegistry, field_proj_named, reachable_adt_carriers, reachable_structural_container_count,
    register_adt_carriers,
};
// Trust: trait-object existential registration (`dyn Trait` → Sigma + vtable record,
// modulo the 3-axiom gate) + reachability collection.
pub use clean_ground::{DynRegistry, reachable_dyn_carriers, register_dyn_carriers};
// Trust: S1 — real-kernel grounding (modulo-3 verdict via the real clean-kernel)
pub use clean_ground::{GroundOutcome, KernelGroundingSession, ground_contract, to_clean_expr};
// Trust: inhabitation — prove a function SATISFIES its contract (the §6 obligation)
pub use clean_ground::{InhabitOutcome, inhabit_verifiable_function};
// Trust: TYPE-ZOO CLOSE — real-kernel registration for the length-indexed const-generic
// array `Trust.ArrayN` (#1) and the erased lifetime/REGION atom `Trust.Region` (#4),
// both modulo the 3-axiom gate (NO 4th axiom).
pub use clean_ground::{register_arrayn_carrier, register_region_carrier};
// Trust: Clean proof transfer integration with composition DAG
pub use composition_transfer::{
    CleanProofTransfer, ProofStatus, ProofStatusRegistry, TransferObligation,
};
pub use error::CertificateError;
pub use fingerprint::{Fingerprint, compute_vc_fingerprint};
// Trust: GOAL-ITEM #3 — IEEE-754 classification predicates over the structured float
// carriers, pinned in Clean modulo 3 (isNaN/isInf/isZero/isSubnormal), plus the value
// model, the round-to-nearest-even ops, the half-ulp rounding-error bound (universal over
// every binade), the NON-FINITE (±∞/NaN) value+op semantics, and the binade-top carry
// re-encoding / overflow-to-∞ — all proven modulo 3.
pub use float_class::{
    CLASSIFIERS, FloatClassVerdict, ValueLemmaVerdict, all_binade_bound_lemmas, all_carry_lemmas,
    all_fadd_ext_rules, all_fdiv_ext_rules, all_fdiv_finite_lemmas, all_fmul_ext_rules,
    all_ulp_bound_lemmas, binade_env, binade_ulp_bound_status, carry_env, classification_env,
    classifier_name, classifiers_typecheck, ext_env, ext_ops_typecheck, float_env,
    half_ulp_error_bound_status, lemma_carry_is_next_binade_bottom, lemma_carry_overflow_to_inf,
    lemma_fadd_ext_nan_left, lemma_fdiv_ext_finite_is_qdiv, lemma_fdiv_ext_nan_left,
    lemma_fdiv_finite_error_bound, lemma_fdiv_finite_zero_exact, lemma_fmul_ext_nan_left,
    lemma_round_carry_reencodes, lemma_ulp_is_grid_spacing, lemma_ulp_normal_reads_exponent,
    lemma_value_ext_classifies, nonfinite_and_carry, nonfinite_carry_status,
    normal_binade_ulp_bound, pin_float_binade, pin_float_carry, pin_float_classification,
    pin_float_ext, pin_float_ulp, ulp_bound, ulp_bound_universal_status, ulp_env,
    wrong_fdiv_finite_swapped_fails_closed, wrong_qdiv_numerator_swapped_fails_closed,
    wrong_quarter_ulp_fdiv_finite_fails_closed,
};
pub use integration::{CertificationBridge, PipelineOutput, RecordVerification};
// Trust: Clean kernel proof checking interface
pub use kernel_check::{
    ContextEntry, KernelContext, KernelQuery, KernelResult, ProofTerm, check_proof, infer_type,
    is_definitionally_equal, substitute,
};
// Trust: Logic classification for Alethe→clean certification scoping
pub use logic_classification::{
    CertificationScope, CertificationStrategy, SmtLogic, TheoryClassifier, classify_formula,
    degradation_strategy, is_certifiable, scope_from_logic,
};
// Trust: GOAL-ITEM #4 (FAITHFULNESS) — the MirSem semantic anchor + Lemma 1A
// (operand adequacy), Lemma 1B (rvalue adequacy), Lemma 1C (return adequacy), the
// whole-function composition witness, and the §6 faithfulness-certificate hooks.
pub use mirsem::{
    AdequacyCertificate,
    AdequacyVerdict,
    AnchorVerdict,
    // Trust: STEP 6BRK / 6MN — the break/early-exit and monotone-nested loop witnesses,
    // consumed by `prove::extract_break_loop_function` / `extract_monotone_nested_loop_function`.
    BreakLoopCertificate,
    CallReturnAdequacyCertificate,
    // Trust: call-spine increment — the certified-callee registry + the CALL
    // return shape (fourth return shape) + its per-call-instance witness.
    CalleeFact,
    CfReturnAdequacyCertificate,
    FullFaithfulnessCertificate,
    FunctionAdequacyCertificate,
    FunctionSafetyVcCertificates,
    LoopPostcondition,
    LoopPostconditionCertificate,
    LoopRefinementCertificate,
    LoopTotalCorrectCertificate,
    MonotoneNestedLoopCertificate,
    NegationAdequacyCertificate,
    NestedLoopCertificate,
    OverflowAdequacyCertificate,
    RefinementCertificate,
    RefinementVerdict,
    RemByZeroAdequacyCertificate,
    ReturnAdequacyCertificate,
    ReturnCertificate,
    RvalueAdequacyCertificate,
    SWidth,
    SafetyVcCertificate,
    SafetyVcKind,
    SemBinOp,
    SemBreakLoopFunction,
    SemCallReturn,
    SemCfReturn,
    SemCmpOp,
    SemCond,
    SemCondTree,
    SemLoopFunction,
    SemMonotoneNestedLoopFunction,
    SemNestedLoopFunction,
    SemOperand,
    SemReturn,
    SemRvalue,
    SemStmt,
    ShiftAdequacyCertificate,
    ShiftWidth,
    SignedOp,
    SignedOverflowAdequacyCertificate,
    SynthInvariant,
    UWidth,
    UsubUnderflowAdequacyCertificate,
    break_loop_witness,
    call_return_adequacy_witness,
    cf_return_adequacy_witness,
    check_bounds_adequacy,
    check_break_loop_instance,
    check_call_refines_contract,
    check_cf_return_adequacy,
    check_cfg_rank_terminates,
    check_cfg_refinement,
    check_div_adequacy,
    check_higher_order_call,
    check_higher_order_disjunction,
    check_loop_invariant_rule,
    check_loop_rank_terminates,
    check_loop_refinement_instance,
    check_loop_total_correct,
    check_loop_total_correct_instance,
    check_monotone_nested_loop_instance,
    check_mutual_call_contracts,
    check_neg_overflow_adequacy,
    check_nested_loop_instance,
    check_open_world_call,
    check_operand_adequacy,
    check_overflow_adequacy,
    check_refinement,
    check_rem_adequacy,
    check_return_adequacy,
    check_rvalue_adequacy,
    check_shift_oob_adequacy,
    check_signed_overflow_adequacy,
    check_usub_underflow_adequacy,
    function_adequacy_witness,
    function_adequacy_witness_with_callees,
    function_emits_unmodeled_safety_vc_pub,
    function_fully_faithful_witness,
    function_fully_faithful_witness_with_callees,
    function_safety_vc_faithful,
    function_safety_vcs_faithful,
    is_safety_vc_kind_pub,
    loop_postcondition_witness,
    loop_refinement_witness,
    loop_total_correct_witness,
    mirsem_env,
    mirsem_refinement_env,
    mirsem_safety_env,
    mirsem_whole_program_env,
    monotone_nested_loop_witness,
    negation_adequacy_witness,
    nested_loop_witness,
    operand_adequacy_witness,
    overflow_adequacy_witness,
    pin_bounds_div_anchor,
    pin_cf_return_anchor,
    pin_mirsem_anchor,
    pin_mirsem_refinement_anchor,
    pin_mirsem_whole_program_anchor,
    pin_negation_anchor,
    pin_overflow_anchor,
    pin_rem_anchor,
    pin_shift_anchor,
    pin_signed_overflow_anchor,
    pin_usub_underflow_anchor,
    rem_by_zero_adequacy_witness,
    return_adequacy_witness,
    rvalue_adequacy_witness,
    sem_binop_of_mir,
    sem_cmpop_of_mir,
    sem_operand_of_mir,
    sem_rvalue_of_mir,
    shift_adequacy_witness,
    signed_overflow_adequacy_witness,
    usub_underflow_adequacy_witness,
    whole_function_refinement_witness,
};
// Trust: Proof obligation management
pub use obligation::{
    ObligationId, ObligationSet, ObligationSource, ObligationStatus, ProofObligation,
    split_obligation,
};
// Trust: Proof transfer between lemmas
pub use proof_transfer::{
    Adaptation, LemmaSignature, TransferCandidate, TransferResult, adapt_proof, find_transferable,
    similarity_score,
};
// Trust: Proof reconstruction from solver certificates
pub use reconstruction::{
    LeanProofTerm, ProofReconstructor, ProofStep, ReconstructionError, SolverProof, reconstruct,
    validate_reconstruction,
};
// Trust: type-reflection functor R (scalar + product fragment)
pub use reflect::{
    ADT_PREFIX, AdtCarrier, CLOSURE_PREFIX, REFLECTED_BITVEC_WIDTHS, ReflectError, adt_ctor_name,
    adt_inductive_name, carrier_context, closure_inductive_name, is_structural_container,
    reflect_bitvec, reflect_closure, reflect_contract, reflect_fn_sig, reflect_fn_sig_pi,
    reflect_formula, reflect_function_spec, reflect_int_term, reflect_sort, reflect_struct,
    reflect_ty, reflect_verifiable_function,
};
// Trust: TYPE-ZOO CLOSE — the six remaining Rust type families as REAL Clean dependent
// types modulo 3: #1 const generics (length-indexed `Trust.ArrayN`), #2 impl Trait
// (RPIT/TAIT existential), #3 multi-bound trait objects (conjoined-vtable existential),
// #4 HRTBs (`Π(r : Trust.Region)` over the fn arrow), #5 GATs (parameterized
// type-level-function family), #6 coroutines (state record env + resume : S → Y).
pub use reflect::{
    ARRAYN_CONS, ARRAYN_NIL, CARRIER_ARRAYN, CARRIER_REGION, COROUTINE_PREFIX, GAT_PREFIX,
    IMPL_TRAIT_PREFIX, REGION_INDUCTIVE, coroutine_inductive_name, gat_family_name,
    impl_trait_const_name, is_marker_trait, reflect_array_indexed, reflect_coroutine,
    reflect_gat_family, reflect_hrtb_fn, reflect_impl_trait, reflect_multi_dyn, reflect_region,
    split_multi_bound,
};
// Trust: trait objects (`dyn Trait`) as REAL existential dependent types
// (`Trust.Dyn.<trait> := Sigma (T:Type), Vtable_<trait> T`), rooted in the 3 axioms.
pub use reflect::{
    DYN_PREFIX, DYN_VTABLE_PREFIX, DynCarrier, dyn_const_name, dyn_vtable_record_name, reflect_dyn,
};
// Trust: GOAL-ITEM #3 — structured IEEE-754 float carriers (reflect_float) + layout.
pub use reflect::{
    float_ctor_name, float_field_tys, float_inductive_name, ieee754_layout, reflect_float,
};
// Trust: EXPANDED TRUST TYPES — the verification types Trust adds BEYOND Rust as
// REAL Clean DEPENDENT types modulo 3: the refinement / liquid subset `{v:T|φ}` →
// `Σ(v:R T), Proof(φ v)` = the prelude `Subtype` (reflect_refinement /
// reflect_refinement_contract / reflect_invariant_type), and the spec'd dependent
// function `Π(x:T), Proof(pre x) → Σ(r:U), Proof(post x r)` (reflect_spec_function).
pub use reflect::{
    reflect_invariant_type, reflect_refinement, reflect_refinement_contract, reflect_spec_function,
};
// Trust: Proof replay engine for verifying proof certificates
pub use replay::{
    FailureDiagnosis, ProofContext, ProofReplayer, ReplayCertificate, ReplayCheckpoint,
    ReplayDiagnostics, ReplayResult, ReplayRule, ReplayStep, SuggestedFix,
    certificate_from_proof_term, checkpoint_replay, diagnose_failure, suggest_fix,
};
// Trust: source-level reflection bridge (string form -> dependent type)
pub use source_reflect::{parse_rust_type, reflect_source_function};
// Trust: Automated tactic generation from VC structure
pub use tactic_gen::{
    Difficulty, TacticHint, TacticSequence, estimate_difficulty, format_clean_proof,
    generate_tactics, tactic_for_arithmetic, tactic_for_induction,
};
// Trust: Tactic script generation for clean proofs
pub use tactics::{
    Tactic, TacticScript, arithmetic_strategy, case_split_strategy, compose_tactics,
    generate_tactic_script, induction_strategy,
};
// Similarity-based proof transfer search over composition DAG
pub use transfer_bridge::{
    AdaptedObligation, TransferProvenance, apply_transfer, build_transfer_provenance,
    cert_to_lemma_signature, find_transfer_candidates, find_transfer_candidates_from_certs,
};
// Trust: RE-ANCHOR POC (goal item 1) — the trust-ir-keyed faithfulness surface.
// `AnchorVerdict`/`RefinementVerdict` are renamed on export to avoid colliding with
// the MirSem types of the same name (these are the trust-ir-anchored analogues).
pub use trustir_anchor::{
    AnchorVerdict as TrustIrAnchorVerdict,
    // Trust: RE-ANCHOR control-flow increment — the CmpOp/Cond/Term/Block/Cfg denotation
    // keyed to trust-ir's basic-block + terminator vocabulary, executed by `evalCfg`, plus
    // the BRANCH refinement (`Switch`/2-way bool branch) against the live grounder's `Ite`.
    IrBlock,
    // Trust: RE-ANCHOR straight-line increment — the operand/rvalue/stmt/body
    // denotation keyed to trust-ir `Inst` + the body refinement against the live grounder.
    IrBody,
    // Trust: RE-ANCHOR loop-breadth increment — the BREAK / EARLY-EXIT loop class
    // (`while cond { if brk { break } body }`) on the combined-guard while-rule
    // `loopInvariantRuleBrk`, kernel-checked modulo 3 (invariant holds at BOTH exit points)
    // + fail-closed probe. Mirrors the committed MirSem break-loop meta-theory.
    IrBreakLoop,
    IrCfg,
    IrCond,
    // Trust: RE-ANCHOR loop increment — the back-edge fixpoint denotation
    // (`stepLoop`/`execLoop`) + the Hoare while-rule (`stepPreservesInv`/`loopInvariantRule`)
    // mirroring the committed MirSem loop meta-theory, plus the COUNTER-LOOP refinement
    // (`count_to`, invariant `i ≤ n`) kernel-checked modulo 3 against the trust-ir denotation.
    IrLoop,
    IrLoopInvariant,
    // Trust: RE-ANCHOR NESTED-loop increment — the STRATIFIED outer-statement layer
    // (`OStmt`/`execO`/`stepLoopO`/`execLoopO`/`stepPreservesInvO`/`loopInvariantRuleO`) + the
    // per-function nested-loop refinement `while i<n { j:=0; while j<m {j+=1}; i+=1 }` over BOTH
    // the UNTOUCHED-LOCAL (`t==0`) and MONOTONE (`0≤s`, inner-modifies-outer) outer-invariant
    // classes, kernel-checked modulo 3 (the OUTER fixpoint reconstructs the certified fact
    // through the COMPLETED inner loop) + fail-closed probes. Mirrors the committed MirSem
    // Step-6N/6NM nested-loop meta-theory; STRATIFIED (no non-additive `Stmt.Loop`).
    IrNestedInvariant,
    IrNestedLoop,
    IrOperand,
    IrRvalue,
    IrStmt,
    IrTerm,
    RefinementVerdict as TrustIrRefinementVerdict,
    TrustIrBinOp,
    TrustIrCmpOp,
    TrustIrUnOp,
    check_body_refinement,
    check_branch_refinement,
    check_loop_invariant_instance,
    check_operand_refinement,
    check_rvalue_refinement,
    check_rvalue_refinement_model,
    check_trustir_break_loop_instance,
    check_trustir_nested_loop_instance,
    check_trustir_refinement,
    pin_trustir_anchor,
    // Trust: RE-ANCHOR loop-BREADTH increment — the OTHER MirSem loop classes
    // (COUNTDOWN `while i>0 {i:=i-1}` / STRIDE `while i<n {i:=i+k}` / ACCUMULATOR lower bound
    // `0≤s` + relational `s==i ∧ i≤n`) instantiated on the SAME `loopInvariantRule`, each
    // kernel-checked modulo 3 with a GENUINE class-specific preservation + fail-closed probe.
    trustir_accum_eq_refinement_fail_closed,
    trustir_body_refinement_fail_closed,
    trustir_branch_refinement_fail_closed,
    trustir_break_loop_refinement_fail_closed,
    trustir_countdown_refinement_fail_closed,
    trustir_env,
    trustir_loop_refinement_fail_closed,
    trustir_monotone_nested_loop_refinement_fail_closed,
    trustir_nested_loop_refinement_fail_closed,
    trustir_nested_loop_witness,
    trustir_refinement_fail_closed,
    trustir_stride_refinement_fail_closed,
};
// Trust: the Lean↔Clean bridge gate surface (§6 `bridge_agreement` citation).
pub use trustir_bridge::{
    ArmForm, BridgeAgreement, BridgeGateConfig, BridgeGateError, BridgeGateMode, run_bridge_gate,
};
// Trust: §6 driver — run the pipeline over real MIR-extracted VerifiableFunctions
pub mod prove;
// Trust: M6 rung 6 — per-function FULLY_FAITHFUL gate breakdown (shape-adequacy
// vs safety-VC), for the rung-6 diagnosis-first cluster table. Rung B adds the
// sibling-bodies-threaded variant (P-STACK trampoline resolution).
pub use prove::{
    FullyFaithfulDiagnosis, ProveScorecard, diagnose_expr_fold_scc,
    diagnose_expr_fold_scc_for_function, diagnose_fully_faithful_gate,
    diagnose_fully_faithful_gate_with_bodies, prove_dump_dir, prove_dump_dir_with_budget,
    prove_dump_dir_with_budget_and_bodies,
};
// Trust: goal item 4 — the FIRST whole-program / inter-procedural POC. Moves
// composition from the SMT lane INTO the kernel-checked-modulo-3 lane: a
// 2-function compositional proof whose caller obligation is discharged USING a
// Certified callee's rebound `#[ensures]`, kernel-checked modulo 3, fail-closed
// on an absent/unproven callee, trust-ir-keyed (ProofContext + InheritedFromCallee
// + Certified/CleanCic). The first production caller of `composition_transfer`.
pub mod whole_program;
pub use whole_program::{
    CalleeSummary, CompositionVerdict, TrustIrCompositionRecord, WholeProgramPoc,
    build_transfer_obligation, caller_goal_h_plus_one_le_101, certify_callee_summary,
    helper_callee, main_like_caller, prove_caller_obligation, run_poc, trust_ir_record_for_proven,
};
// Trust: WHOLE-PROGRAM Step 3 (goal item 4) — the GENERAL multi-function call-graph
// compositional driver. Verifies an arbitrary acyclic call graph in callee-first
// topological order (consumed from `trust_vcgen::compute_verification_order`),
// threading ONE `ProofStatusRegistry` across the whole graph; each function's ensures
// is kernel-checked modulo 3 UNDER its certified callees' version-pinned ensures.
// Fail-closed + transitive: a mid-graph knockout opens its whole caller cone.
pub use whole_program::{
    FunctionVerdict, WholeProgramGraphResult, diamond_leaf, diamond_left, diamond_program,
    diamond_right, diamond_top, verify_call_graph, verify_call_graph_with_knockout,
};
// Trust: WHOLE-PROGRAM Step 4 (goal item 4) — RECURSION. The well-founded
// inter-procedural meta-theorem, MIRRORING the committed loop-totality meta-theory
// (loopRankDecrease / toNatMono / loopRankTerminates / loopTotalCorrect). A
// self-recursive `#[decreases(measure)]` function is verified compositionally: the
// recursive call's obligation is discharged by ASSUMING the function's OWN ensures
// (the induction hypothesis), JUSTIFIED by the measure STRICTLY DECREASING (and
// staying well-founded ≥ 0) on that call — kernel-checked modulo 3 via the UNCHANGED
// vc_refute engine. Fail-closed: no/bad #[decreases] ⇒ the IH may not be assumed ⇒
// Open. Mutual recursion (an SCC > 1) via a shared decreasing measure (assume-
// guarantee over the SCC). Additive: no change to vc_refute.rs or mirsem.rs.
pub use whole_program::{
    RecursionResult, RecursionVerdict, RecursiveFunction, mutual_recursion_scc,
    prove_mutual_recursion_scc, prove_recursive_function, run_recursion_poc,
    sum_to_n_false_ensures, sum_to_n_non_decreasing, sum_to_n_recursive,
};
// Trust: SMT→CIC reconstruction of safety VCs (guarded-check refutation, modulo 3)
pub mod vc_refute;
// Trust: AY proof bridge — translates ay proof certificates to SolverProof
pub use ay_proof_bridge::translate_ay_proof;
// Trust: v1 clean proof reuse — indexes and matches v1 theorems
pub use v1_reuse::{LoweringError, TheoremCategory, TheoremLibrary, V1Theorem, lower_proof_term};
pub use vc_refute::{RefuteOutcome, StructParams, check_lt_le_contradiction, check_refute_vc_with};
