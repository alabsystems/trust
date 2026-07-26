// trust-certify: CHECKER-CORE functional-correctness re-check lane.
//
// The `inductive_functional` lane certifies a correctness property of the
// kernel's arithmetic (`Nat.add` left identity, `forall n, 0 + n = n`) via a
// genuine `Nat.rec` structural induction. This lane pushes the SAME machinery
// off arithmetic and onto the ACTUAL TYPE-CHECKING CORE: the de Bruijn
// `lift_at` / `instantiate_at` operations the kernel uses to move terms across
// binder levels and substitute under binders.
//
// The property proved is the lift/substitution INTERCHANGE lemma (gap form) —
// the load-bearing commutation the kernel's reduction/confluence machinery
// relies on:
//
//   lift_instantiate_swap :
//     forall (body : KExpr) (val : KExpr) (d : Nat) (k : Nat) (a : Nat),
//       Eq KExpr
//         (lift_at (instantiate_at body val d) (Nat.add d k) a)
//         (instantiate_at (lift_at body (Nat.succ (Nat.add d k)) a)
//                         (lift_at val k a) d)
//
// "Lifting at cutoff (d+k) commutes with a depth-d substitution (with the value
// lifted at the gap cutoff k)." This is a real correctness property of the
// kernel's core `lift_at`/`instantiate_at` de Bruijn operations — NOT of
// arithmetic.
//
// WHERE THE TERM COMES FROM (the "medium wiring"):
//   clean-verify already kernel-checks this lemma as a `DerivedProved`,
//   zero-domain-axiom CIC proof TERM: an explicit `KExpr.rec` structural
//   induction over the 7-constructor `KExpr` model (sort/const by Eq.refl, bvar
//   by a triple-`Nat.rec` convoy, app/lam/pi/let_ by the interchange template) — see
//   clean-verify
//   `crates/clean-verify/src/spec/core_spec/expr_model_lift_instantiate_swap.rs`.
//   When `Specification::new()` builds the spec, it elaborates that lemma's
//   `type_src`/`value_src` and registers it via `Environment::add_decl`, which
//   FULLY kernel-type-checks the proof term against the goal. This lane rebuilds
//   the spec, pins the exact goal source, extracts the registered
//   (elaborated_type, elaborated_value) pair, and INDEPENDENTLY re-runs the
//   clean kernel `TypeChecker::check_type(term, goal, infer_only = false)`,
//   serializes the term, and re-checks the deserialized payload.
//
// The clean CIC kernel (`TypeChecker::check_type`) is the proof-checking TCB —
// the same checker as the QF_LIA / finite_dfa / inductive_functional lanes.
// The theorem remains relative to clean-verify's registered model and
// foundational premises. The inductive-proof SEARCH (banked by clean-verify)
// is outside that proof-checking TCB; the kernel re-checks the resulting term.
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `term : goal`;
//   * the goal is PINNED by this lane (LIFT_INSTANTIATE_SWAP_TYPE_SRC): the mint
//     fails closed unless the spec's registered `type_src` is byte-identical, so
//     we certify exactly the checker-core Prop and not a drifted restatement;
//   * we require the spec's honesty labels (`DerivedProved`, not an axiom, no
//     remaining helper-axiom blockers) — the model-level zero-domain-axiom
//     residual — else fail closed;
//   * the NEGATIVE CONTROL must reject before we mint: a refl-only "proof" of the
//     SAME goal (`Eq.refl KExpr LHS`, which would succeed iff the LHS were
//     def-equal to the RHS) is elaborated in the spec environment and fed to the
//     kernel, which MUST reject it — witnessing that the kernel check is
//     discriminating and the interchange genuinely needs the `KExpr.rec`
//     induction, not mere unfolding;
//   * the term + closed context + goal source are bound into the lineage digest,
//     so a certificate cannot be replayed against another obligation;
//   * `recheck_lift_instantiate_swap` independently rebuilds the spec + goal and
//     re-runs the kernel check on the DESERIALIZED term — a tampered term or a
//     swapped lineage fails closed.
//
// GROUNDING CAVEAT (stated honestly): this is a MODEL-LEVEL result. It proves
// the property about the 7-constructor `KExpr` model's `lift_at`/`instantiate_at`
// — clean-verify's faithful-by-inspection abstraction of the ~20-constructor
// Rust `Expr` and its lift/instantiate — NOT about the literal Rust functions
// extracted from MIR. It is the honest rung ABOVE the arithmetic `zero_add`
// lane: it moves the certified capability from `Nat.add` to the ACTUAL de Bruijn
// machinery of the type-checking core, at model level. Closing the loop to the
// literal Rust kernel fns' functional postcondition additionally requires a
// recursive-spec Formula + functional-VC grounding path that does not yet exist
// (Gaps A/B); this lane does NOT claim that.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{Environment, Expr, TypeChecker};
use sha2::{Digest, Sha256};

/// Lineage domain tag for the checker-core `CleanCic` digest. Distinct from the
/// QF_LIA / finite-sim / inductive-arithmetic lanes so certificates never alias.
const CHECKER_CORE_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.checker-core.v1";

/// Stable obligation label folded into the lineage digest.
const CHECKER_CORE_LABEL: &str = "clean-verify.core_spec.lift_instantiate_swap: \
     lift_at (instantiate_at body val d) (d+k) a = \
     instantiate_at (lift_at body (succ (d+k)) a) (lift_at val k a) d";

/// The clean-verify definition name of the checker-core lemma.
const LEMMA_NAME: &str = "lift_instantiate_swap";

/// The EXACT checker-core goal we certify, pinned as source. Must be
/// byte-identical to the `type_src` clean-verify registers for
/// `lift_instantiate_swap` (expr_model_lift_instantiate_swap.rs); the mint fails
/// closed otherwise, so this lane certifies precisely the checker-core Prop.
const LIFT_INSTANTIATE_SWAP_TYPE_SRC: &str = concat!(
    "forall (body : KExpr) (val : KExpr) (d : Nat) (k : Nat) (a : Nat), ",
    "Eq KExpr ",
    "(lift_at (instantiate_at body val d) (Nat.add d k) a) ",
    "(instantiate_at (lift_at body (Nat.succ (Nat.add d k)) a) ",
    "(lift_at val k a) d)",
);

/// NEGATIVE control source: `fun body val d k a => Eq.refl KExpr LHS`, where LHS
/// is the goal's left-hand side `lift_at (instantiate_at body val d) (d+k) a`.
/// Its type is `Eq KExpr LHS LHS`, which is NOT the goal `Eq KExpr LHS RHS`
/// because the LHS is not def-equal to the RHS (both are stuck on the free
/// `body` — `lift_at`/`instantiate_at` cannot reduce on a variable). The kernel
/// MUST reject it — the witness that this checker-core interchange genuinely
/// requires the `KExpr.rec` induction, not mere unfolding.
const REFL_ONLY_FAKE_SRC: &str = concat!(
    "fun (body : KExpr) (val : KExpr) (d : Nat) (k : Nat) (a : Nat) => ",
    "Eq.refl KExpr (lift_at (instantiate_at body val d) (Nat.add d k) a)",
);

/// Stack for the spec build + kernel re-check. `Specification::new()` elaborates
/// and kernel-checks the full core spec (deep recursion), and the lemma's proof
/// term is a large `KExpr.rec` tree — both blow the default 8 MB thread stack.
const CHECKER_CORE_STACK_BYTES: usize = 512 * 1024 * 1024;

/// Run `f` on a dedicated large-stack thread. `None` if the thread cannot be
/// spawned or panics (fail-closed).
///
/// `pub(crate)` so the sibling checker-core lemma lanes
/// ([`crate::checker_core_lemma`]) run their heavy spec-build + kernel-recheck
/// bodies on the same 512 MB stack.
pub(crate) fn run_on_large_stack<F, T>(f: F) -> Option<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    std::thread::Builder::new().stack_size(CHECKER_CORE_STACK_BYTES).spawn(f).ok()?.join().ok()
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// closed context, in the spec environment's mode.
///
/// `pub(crate)` so the sibling checker-core lemma lanes reuse the exact same
/// kernel-recheck entry point (same TCB).
pub(crate) fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_mode(env, env.mode()).check_type(term, goal).is_ok()
}

/// Elaborate `src` in `env` with full metavariable + universe-level instantiation
/// (the same pipeline clean-verify's `elaborate_source` uses). `None` on any
/// parse/elab failure. Used only to build the negative-control fake term.
///
/// `pub(crate)` so the sibling checker-core lemma lanes build their own
/// negative-control fakes with the identical elaboration pipeline.
pub(crate) fn elaborate_full(env: &Environment, src: &str) -> Option<Expr> {
    let surface = clean_parser::parse_expr(src).ok()?;
    let mut ctx = clean_elab::ElabCtx::new(env);
    let expr = ctx.elaborate(&surface).ok()?;
    let expr = ctx.metas().instantiate(&expr);
    Some(ctx.metas().instantiate_levels(&expr))
}

/// The clean kernel must REJECT the refl-only pseudo-proof against `goal`.
/// Returns `true` iff the fake ELABORATES to a well-formed term AND the kernel
/// rejects it against the goal — i.e. the kernel check is discriminating. If the
/// fake cannot be elaborated we cannot demonstrate a discriminating rejection,
/// so we fail closed (`false`).
fn refl_only_fake_rejected(env: &Environment, goal: &Expr) -> bool {
    match elaborate_full(env, REFL_ONLY_FAKE_SRC) {
        Some(fake) => !kernel_checks_goal(env, &fake, goal),
        None => false,
    }
}

/// SHA-256 lineage digest binding the term, the empty closed context, the
/// obligation label, and the pinned goal source. Position-tagged +
/// length-prefixed => injective.
fn checker_core_lineage_digest(term_bytes: &[u8], context_bytes: &[u8]) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(CHECKER_CORE_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), CHECKER_CORE_LABEL.as_bytes()),
        (b"goal:".as_slice(), LIFT_INSTANTIATE_SWAP_TYPE_SRC.as_bytes()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    trust_ir::ProofDigest::sha256(bytes)
}

/// Recompute authority from the live specification closure.  Hand-maintained
/// status fields are useful diagnostics, but cannot by themselves exclude a
/// newly introduced trust marker or domain axiom from a public recheck lane.
fn lemma_authority_is_clean(spec: &clean_verify::spec::Specification) -> bool {
    let Some(def) = spec.get_definition(LEMMA_NAME) else {
        return false;
    };
    if spec.env().get_const(&clean_kernel::Name::from_string(LEMMA_NAME)).is_none()
        || def.is_axiom
        || def.proof_status != clean_verify::spec::ProofStatus::DerivedProved
        || !def.axiom_deps.is_empty()
    {
        return false;
    }
    let foundational = clean_verify::spec_axiom_closure::foundational_base(spec);
    let closure = clean_verify::spec_axiom_closure::computed_axiom_closure(spec, LEMMA_NAME);
    let (trust_markers, residual) =
        clean_verify::spec_axiom_closure::partition_closure(&closure, &foundational);
    trust_markers.is_empty() && residual.is_empty()
}

/// The heavy body of the mint, run on the large-stack thread.
fn certify_inner() -> Option<trust_ir::ProofEvidence> {
    let spec = clean_verify::spec::Specification::new().ok()?;
    let def = spec.get_definition(LEMMA_NAME)?;

    // Pin the exact checker-core Prop: fail closed if the spec has drifted, so
    // we certify precisely this property and never a silently-changed statement.
    if def.type_src != LIFT_INSTANTIATE_SWAP_TYPE_SRC {
        return None;
    }
    // Honesty residual (model level): a constructive, zero-domain-axiom proof.
    if !lemma_authority_is_clean(&spec) {
        return None;
    }

    let goal = def.elaborated_type.as_ref()?;
    let proof = def.elaborated_value.as_ref()?;

    // 1. The clean kernel independently type-checks the DerivedProved KExpr.rec
    //    proof term against the checker-core goal.
    if !kernel_checks_goal(spec.env(), proof, goal) {
        return None;
    }

    // 2. NO MASQUERADE: the negative control must reject before we mint. If a
    //    refl-only term could pass the same check, the check would be vacuous.
    if !refl_only_fake_rejected(spec.env(), goal) {
        return None;
    }

    // 3. Serialize term + empty closed context via the clean_auto codec, then
    //    re-check the DESERIALIZED payload round-trips to a kernel-valid term
    //    (against the goal we already hold, in the same env — no second spec
    //    build). The consumer-independent re-check that rebuilds the spec from
    //    scratch is `recheck_lift_instantiate_swap`.
    let term_bytes = serialize_term(proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let roundtrip = deserialize_term(&term_bytes).ok()?;
    if !kernel_checks_goal(spec.env(), &roundtrip, goal) {
        return None;
    }
    let lineage = checker_core_lineage_digest(&term_bytes, &context_bytes);

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Mint a kernel-CHECKED `CleanCic` certificate that the clean-verify
/// `DerivedProved` KExpr proof term discharges the checker-core lift/instantiate
/// interchange lemma `lift_instantiate_swap`. Returns `None` (fail-closed) on any
/// spec-build, drift, kernel-check, negative-control, serialization, or
/// round-trip failure.
#[must_use]
pub fn certify_lift_instantiate_swap() -> Option<trust_ir::ProofEvidence> {
    run_on_large_stack(certify_inner).flatten()
}

/// The heavy body of the consumer-side re-check, run on the large-stack thread.
fn recheck_inner(term_bytes: &[u8], context_bytes: &[u8], lineage: &trust_ir::ProofDigest) -> bool {
    let Some(spec) = clean_verify::spec::Specification::new().ok() else {
        return false;
    };
    let Some(def) = spec.get_definition(LEMMA_NAME) else {
        return false;
    };
    // Rebuild the goal independently and pin it.
    if def.type_src != LIFT_INSTANTIATE_SWAP_TYPE_SRC {
        return false;
    }
    if !lemma_authority_is_clean(&spec) {
        return false;
    }
    let (Some(goal), Some(canonical_proof)) =
        (def.elaborated_type.as_ref(), def.elaborated_value.as_ref())
    else {
        return false;
    };
    if !crate::is_canonical_term(term_bytes, canonical_proof) {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(spec.env(), &term, goal) {
        return false;
    }
    &checker_core_lineage_digest(term_bytes, context_bytes) == lineage
}

/// Consumer-side re-check of a checker-core `CleanCic` certificate: independently
/// rebuild the spec + goal, deserialize the term, re-run the clean-kernel
/// `check_type`, and re-bind the lineage digest. Returns `true` ONLY if the
/// kernel accepts the deserialized term against the freshly-rebuilt goal AND the
/// lineage matches — a tampered term or a swapped lineage fails closed.
#[must_use]
pub fn recheck_lift_instantiate_swap(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !crate::is_canonical_empty_context(context_bytes) {
        return false;
    }
    let term = term_bytes.to_vec();
    let context = context_bytes.to_vec();
    let lineage = *lineage;
    run_on_large_stack(move || recheck_inner(&term, &context, &lineage)).unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::ProofEvidence;

    /// THE MILESTONE + the consumer-side fail-closed gates, exercised on a single
    /// minted certificate (each spec rebuild is heavy, so they share one mint):
    ///
    /// * the checker-core lift/instantiate interchange lemma (`lift_at
    ///   (instantiate_at body val d) (d+k) a = instantiate_at (lift_at body (succ
    ///   (d+k)) a) (lift_at val k a) d`) — a functional-correctness property of
    ///   the ACTUAL type-checking-core de Bruijn operations, discharged by a
    ///   genuine `KExpr.rec` structural induction — mints to a kernel-CHECKED
    ///   `CleanCic` certificate;
    /// * its serialized payload re-checks via an INDEPENDENTLY rebuilt spec +
    ///   kernel (`recheck_lift_instantiate_swap`);
    /// * a tampered term fails the re-check (fail-closed);
    /// * a swapped (zeroed) lineage fails the re-check (fail-closed).
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn lift_instantiate_swap_checker_core_closes() {
        let evidence = certify_lift_instantiate_swap()
            .expect("lift_instantiate_swap must certify to CleanCic");
        let ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(kernel_recheck.is_none());
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");

        // Consumer-independent re-check: rebuild the spec + goal from scratch and
        // re-run the clean kernel on the DESERIALIZED term.
        assert!(
            recheck_lift_instantiate_swap(&term, &context, &lineage),
            "serialized checker-core CleanCic payload must re-check via the clean kernel"
        );

        // Fail-closed: a tampered term must not re-check.
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_lift_instantiate_swap(&tampered, &context, &lineage),
            "tampered checker-core term must fail the offline kernel re-check"
        );

        // Fail-closed: a swapped (zeroed) lineage must not re-check.
        assert!(
            !recheck_lift_instantiate_swap(&term, &context, &trust_ir::ProofDigest::zero()),
            "a zeroed lineage must fail closed"
        );
    }

    /// NO MASQUERADE: the checker-core property genuinely REQUIRES the induction.
    /// A refl-only pseudo-proof (which would suffice iff the goal's LHS reduced to
    /// its RHS) is a WELL-FORMED term of the WRONG type, and the kernel REJECTS it
    /// against the goal. This is the witness that the mint's kernel check is
    /// discriminating.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn lift_instantiate_swap_refl_only_rejected() {
        let (fake_elaborates, rejected) = run_on_large_stack(|| {
            let spec = clean_verify::spec::Specification::new().expect("spec should build");
            let def = spec.get_definition(LEMMA_NAME).expect("def present");
            let goal = def.elaborated_type.as_ref().expect("goal");
            let fake = elaborate_full(spec.env(), REFL_ONLY_FAKE_SRC);
            let elaborates = fake.is_some();
            // The fake is a well-formed term, but of the WRONG type: rejected.
            let rejected = fake.is_some_and(|fk| !kernel_checks_goal(spec.env(), &fk, goal));
            (elaborates, rejected)
        })
        .expect("neg-control thread must not panic");
        assert!(fake_elaborates, "the refl-only fake must elaborate to a well-formed term");
        assert!(
            rejected,
            "Eq.refl alone must NOT type-check the lift/instantiate interchange \
             (LHS is not def-equal to RHS; both are stuck on the free `body`)"
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn relineaged_sorry_beta_proof_and_noncanonical_context_are_rejected() {
        let (sorry_bytes, beta_bytes, canonical_bytes, context) = run_on_large_stack(|| {
            let spec = clean_verify::spec::Specification::new().expect("spec should build");
            let def = spec.get_definition(LEMMA_NAME).expect("definition present");
            let goal = def.elaborated_type.as_ref().expect("goal");
            let proof = def.elaborated_value.as_ref().expect("canonical proof");

            let goal_level = TypeChecker::new(spec.env()).infer_sort(goal).expect("goal sort");
            let sorry = Expr::app(
                Expr::const_(clean_kernel::Name::from_string("sorry"), vec![goal_level]),
                goal.clone(),
            );
            assert!(kernel_checks_goal(spec.env(), &sorry, goal));

            let beta = Expr::app(
                Expr::lam(clean_kernel::BinderInfo::Default, goal.clone(), Expr::bvar(0)),
                proof.clone(),
            );
            assert!(kernel_checks_goal(spec.env(), &beta, goal));
            (
                serialize_term(&sorry).expect("serialize sorry"),
                serialize_term(&beta).expect("serialize beta proof"),
                serialize_term(proof).expect("serialize canonical proof"),
                crate::canonical_empty_context_bytes().expect("canonical context"),
            )
        })
        .expect("forgery construction thread");

        let sorry_lineage = checker_core_lineage_digest(&sorry_bytes, &context);
        assert!(!recheck_lift_instantiate_swap(&sorry_bytes, &context, &sorry_lineage,));
        let beta_lineage = checker_core_lineage_digest(&beta_bytes, &context);
        assert!(!recheck_lift_instantiate_swap(&beta_bytes, &context, &beta_lineage,));

        let mut noncanonical_context = context;
        noncanonical_context.push(0);
        let relined = checker_core_lineage_digest(&canonical_bytes, &noncanonical_context);
        assert!(!recheck_lift_instantiate_swap(&canonical_bytes, &noncanonical_context, &relined,));
    }
}
