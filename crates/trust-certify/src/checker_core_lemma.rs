// trust-certify: CHECKER-CORE lemma lanes (whnf + def_eq), generic engine.
//
// This module grows the kernel-rechecked checker-core beyond the single
// `lift_instantiate_swap` lane in [`crate::checker_core`]. It certifies
// CORRECTNESS lemmas about the two CENTRAL type-checking operations —
// weak-head normalization (`whnf`) and definitional equality (`def_eq`) —
// via the SAME working CleanCic pipeline:
//
//   * `Specification::new()` (clean-verify) builds + FULLY kernel-type-checks
//     each `DerivedProved`, zero-domain-axiom proof TERM against its goal when
//     it registers the lemma via `Environment::add_decl`;
//   * this lane rebuilds the spec, PINS the exact goal source byte-identically
//     (fail-closed on drift), extracts the registered `(elaborated_type,
//     elaborated_value)` pair, and INDEPENDENTLY re-runs the clean kernel
//     `TypeChecker::check_type(term, goal, infer_only = false)`;
//   * a per-lemma NEGATIVE CONTROL (a wrong/weaker term for the SAME goal) is
//     elaborated and fed to the kernel, which MUST reject it before we mint —
//     the no-masquerade witness that the kernel check is discriminating;
//   * the term is serialized + round-tripped through the clean_auto codec and
//     re-checked, and the term/context/label/goal are bound into a lineage
//     digest so a certificate cannot be replayed against another obligation.
//
// The lemmas certified here span model-side INFER/CHECK COHERENCE (the spec's
// historical `tc_infer_soundness` name), relational algorithm-to-typing
// soundness (`bootstrap_infer_sound`), PRESERVATION (subject reduction), and
// TERMINATION (both the small context-free and conditional dependent-model
// results) — plus reflected-infer inversion, model-level whnf idempotence, the
// app/lam/pi def_eq congruence family, and three KernelState-surface relation
// laws. None of these names silently upgrades a reflected relation into a proof
// about the literal Rust implementation:
//
//   whnf_terminates_well_typed :  (the TERMINATION pillar)
//     forall (e : KExpr) (T : KExpr), has_type e T -> terminates_whnf e
//   Weak-head normalization terminates on well-typed terms — `terminates_whnf
//   e := whnf_acc e`, accessibility under the full `whnf_step = beta ∪ delta`
//   (a genuine `Acc`-style predicate, not a vacuous restatement). A RETIRED census
//   axiom, now `DerivedProved`, zero domain axioms, via `beta_bd_acc.rec` (core_spec
//   whnf_terminates_well_typed.rs). HONEST SCOPE (per that file): this is SN for the
//   spec's ACTUAL `has_type` = the context-free `Typing` fragment (degenerate — no
//   var/const rule ⇒ constant lambdas, δ/ι legs vacuous), a genuine proof of the
//   axiom AS STATED, NOT a claim of full dependent-CIC strong normalization.
//
//   whnf_terminates_well_typed_dependent :  (conditional dependent SN)
//     forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (e T : KExpr),
//       TypingCtx tenv (ListType.nil KExpr) e T -> whnf_acc e
//   This is the stronger CLOSED-term result for the dependent `TypingCtx`
//   judgment (including variables under binders and the let case), but it remains
//   conditional on a caller-supplied `M : CandModel tenv`. It does not establish
//   that such a model exists for every environment, nor does it ground the Rust
//   implementation. clean-verify discharges it via `fundamental_general` at
//   `idsubst`, `psubst_id`, and `CR1`, with zero non-foundational domain axioms.
//
//   tc_infer_soundness :  (model-side INFER/CHECK COHERENCE)
//     forall (i3 : RecEnvClosed …) (i4 : …LiftClosed…) (i5 : DefEnvClosed …)
//            (i6 : …LiftClosed…) (st : KernelState) (e T : KExpr),
//       KernelStateMatchesSpec st -> KernelInputAdmissible st e ->
//       KernelInferAccepts st e T -> KernelCheckAccepts st e T
//   "When the model's infer relation accepts `e` with result `T`, its check relation
//   also accepts `e` against that same `T`." This ties the two model relations
//   together but does NOT prove `KernelInferAccepts -> has_type` or correctness of
//   the literal Rust `infer_type` function. clean-verify drained this exact relation
//   from a HelperAxiom to a `DerivedProved` theorem, zero domain axioms; re-checking
//   it here independently attests that exact model-side coherence claim.
//
//   bootstrap_infer_sound :  (modeled algorithm-to-typing soundness)
//     forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (e T : KExpr),
//       KernelInfers tenv G e T -> TypingCtxConv tenv G e T
//   This is soundness of the six-shape `KernelInfers` relation (sort/bvar/pi/lam/
//   const/app; no let arm) against the declarative-with-conversion judgment. The
//   correspondence between that relation and deployed Rust remains an empirical
//   fidelity boundary, not a theorem smuggled into this certificate.
//
//   kernel_infer_inversion :  (reflected-relation structural inversion)
//     forall (st : KernelState) (e T : KExpr),
//       KernelInferAccepts st e T -> InferInversionAt st e T
//   This eliminates clean-verify's five-constructor `KernelInferAccepts` model
//   (sort/const/app/lam/pi; no bvar/let) into its per-shape payload. It is a real
//   kernel-checked recursor proof, but not literal-Rust `infer_type` correctness.
//
//   beta_reduces_preserves_typing :  (the deepest INDUCTION — forward SUBJECT REDUCTION)
//     forall (hf : RedEnvFaithful the_red_env) (e e' T : KExpr),
//       DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) ->
//       beta_reduces e e' -> has_type e T -> has_type e' T
//   "Well-typed terms stay well-typed under β/ι/congruence reduction" — the
//   heart of type safety. Discharged in clean-verify by `beta_reduces.rec`
//   induction over every reduction arm (beta_preservation; the nine congruence
//   arms via typing_app_gen + Typing.conv + beta_reduces_typed_def_eq; the four
//   vacuous let arms via typing_let_absurd), zero domain axioms. (core_spec
//   beta_reduces_preserves_typing.rs.)
//
//   whnf_idempotent :
//     forall (e : KExpr) (e' : KExpr), whnf_to e e' -> whnf_to e' e'
//   "The weak-head normal form of a term is already in weak-head normal form."
//   Discharged in clean-verify by `whnf_to.rec` induction via
//   `whnf_to_target_is_whnf` + `whnf_to.refl` — a genuine correctness property
//   of the kernel's `whnf` reduction, NOT of arithmetic. (core_spec
//   implementation_soundness_whnf_decomposition.rs.)
//
//   instantiate_at_{app,lam,pi}_preserves_def_eq :
//     the substitution-under-a-binder DefEq congruence for EACH of the three
//     binder/application constructors, e.g. (app):
//     forall (f f' a a' val : KExpr) (depth : Nat),
//       DefEq (instantiate_at f val depth) (instantiate_at f' val depth) ->
//       DefEq (instantiate_at a val depth) (instantiate_at a' val depth) ->
//       DefEq (instantiate_at (KExpr.app f a) val depth)
//             (instantiate_at (KExpr.app f' a') val depth)
//   "Substitution is a congruence for definitional equality on applications /
//   lambdas / pis." The lam and pi twins cross a binder, so their body/codomain
//   hypothesis is at `Nat.succ depth`. Discharged in clean-verify via
//   `DefEq.{app,lam,pi}_cong` + `instantiate_at_{app,lam,pi}` +
//   `def_eq_eq_left`/`def_eq_eq_right` — genuine correctness properties of the
//   kernel's `def_eq` (congruence closure under substitution), together covering
//   the whole app/lam/pi constructor family. (core_spec substitution_def_eq.rs.)
//
//   tc_is_def_eq_reflexive / tc_is_def_eq_symmetric / tc_whnf_idempotent :
//     laws of the modeled `KernelDefEqAccepts` / `KernelWhnfAccepts` relations.
//   They are constructive, zero-domain-axiom facts over the KernelState surface.
//   In particular, they do not by themselves prove that the deployed Rust
//   decision procedures return success; that requires the missing grounding
//   bridge called out below.
//
//   tc_def_eq_transitivity / whnf_to_preserves_def_eq :
//     constructive, zero-domain-axiom laws of the separate model-level
//     `is_def_eq` alias / `whnf_to` trace: declarative DefEq transitivity, and
//     transport from one modeled WHNF trace to declarative DefEq. They do not
//     complete the KernelState-surface family above or prove universal
//     transitivity / WHNF correctness for the deployed Rust procedures.
//
//   par_reduces_{c,p}_star_diamond_faithful :  (model-specific confluence)
//     forall (e e1 e2 : KExpr),
//       par_reduces_{c,p}_star (red_rec faithful_red_env) e e1 ->
//       par_reduces_{c,p}_star (red_rec faithful_red_env) e e2 ->
//       par_strips_witness_{c,p}_star (red_rec faithful_red_env) e1 e2
//   These are the star-diamond / Church-Rosser results for clean-verify's two
//   modeled parallel-star relations at its concrete, non-vacuous
//   `faithful_red_env`. That environment is a one-recursor/one-definition KExpr
//   model of a faithful kernel-environment shape; it is not the deployed Rust
//   environment, `the_red_env`, or a MIR-grounded implementation theorem.
//   Confluence here is an important model property, but it alone does not prove
//   definitional-equality decidability. Both proofs have no residual
//   non-foundational/domain axioms relative to the admitted foundational model.
//
//   beta_deterministic / delta_step_deterministic / iota_step_deterministic /
//   unique_normal_forms_c_faithful :  (reduction DETERMINISM + normal-form UNIQUENESS)
//   The reduction relations are well-behaved: β-reduction is deterministic up to def-eq
//   (`beta_reduces e r1 -> beta_reduces e r2 -> DefEq r1 r2`), and the δ/ι reduct
//   partial functions are deterministic (same input → same output, `Eq KExpr e1 e2`).
//   The capstone is UNIQUENESS OF NORMAL FORMS — the direct payoff of the star-diamond
//   confluence above: two par_reduces_c-normal forms reachable from a common source are
//   EQUAL, unconditionally over the real faithful_red_env (`unique_normal_forms_c_faithful`).
//   Together with confluence, this is the full Church-Rosser story that makes conversion
//   checking well-defined. Each `DerivedProved`, EMPTY axiom_deps (core_spec
//   {implementation_soundness_whnf_decomposition,delta_step,iota_step,unique_normal_forms_c}.rs).
//
// The clean CIC kernel (`TypeChecker::check_type`) is the proof-checking TCB —
// the same checker as the `lift_instantiate_swap` lane. Every theorem remains
// explicitly relative to clean-verify's foundational modeling rules (the
// abstract `Typing`/`DefEq` judgment base); those are admitted model premises,
// not hidden proof terms. Inductive-proof SEARCH (banked by clean-verify) is
// outside the TCB, and the kernel re-checks each resulting canonical term here.
//
// GROUNDING CAVEAT (stated honestly): these are MODEL-LEVEL results over
// clean-verify's compact 7-constructor `KExpr` abstraction of the kernel's
// ~20-constructor Rust `Expr`; individual relations cover still smaller slices
// (`KernelInferAccepts`: five constructors, no bvar/let; `KernelInfers`: six
// shapes, no let). Sibling test lanes execute the literal Rust `is_def_eq` and
// `whnf` functions on finite, discriminating inputs: symmetry on a beta pair and
// a negative universe pair, one concrete beta/delta composition chain, and WHNF
// idempotence on a two-step redex. Those are useful per-input regression facts;
// they are not universal theorems, do not establish transitivity for all real
// expressions, and do not bridge these model proofs to MIR. Closing the
// universal literal-function loop still needs the recursive-spec + functional-
// VC path that does not yet exist. This lane does not claim MIR grounding.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{
    ReducedContext, deserialize_term, serialize_context, serialize_term,
};
use sha2::{Digest, Sha256};

use crate::checker_core::{elaborate_full, kernel_checks_goal, run_on_large_stack};

/// A checker-core correctness lemma to certify + re-check through the CleanCic
/// pipeline. All fields are pinned constants so the lane certifies exactly the
/// intended goal type and negative control (fail-closed on any drift).
pub(crate) struct CheckerCoreLemma {
    /// The clean-verify definition name (looked up in the rebuilt spec).
    pub name: &'static str,
    /// The EXACT goal source. Must be byte-identical to the `type_src`
    /// clean-verify registers for `name`; the mint fails closed otherwise.
    pub type_src: &'static str,
    /// A wrong/weaker "proof" of the SAME goal. It MUST elaborate to a
    /// well-formed term AND be REJECTED by the kernel against the goal — the
    /// no-masquerade witness. The mint fails closed unless the fake is rejected.
    pub fake_src: &'static str,
    /// Lineage domain tag — distinct per lemma so certificates never alias.
    pub lineage_domain: &'static str,
    /// Stable obligation label folded into the lineage digest.
    pub label: &'static str,
}

/// WHNF idempotence: `forall e e', whnf_to e e' -> whnf_to e' e'`.
///
/// NEGATIVE control `fun e e' (h : whnf_to e e') => h` is the "forgot to
/// advance the endpoint" error: its type is `... -> whnf_to e e'`, which is NOT
/// the goal `... -> whnf_to e' e'` (`e` is not def-equal to `e'` — both free).
/// The kernel MUST reject it, witnessing that idempotence genuinely needs
/// `whnf_to_target_is_whnf`, not the input reduction verbatim.
pub(crate) const WHNF_IDEMPOTENT: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_idempotent",
    type_src: "forall (e : KExpr) (e' : KExpr), whnf_to e e' -> whnf_to e' e'",
    fake_src: "fun (e : KExpr) (e' : KExpr) (h : whnf_to e e') => h",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf.v1",
    label: "clean-verify.core_spec.whnf_idempotent: whnf_to e e' -> whnf_to e' e'",
};

/// def_eq substitution congruence on applications:
///   `forall f f' a a' val depth,
///      DefEq (inst_at f val depth) (inst_at f' val depth) ->
///      DefEq (inst_at a val depth) (inst_at a' val depth) ->
///      DefEq (inst_at (app f a) val depth) (inst_at (app f' a') val depth)`.
///
/// NEGATIVE control ignores both hypotheses and returns
/// `DefEq.refl (instantiate_at (KExpr.app f a) val depth)`: its type's
/// conclusion is `DefEq (inst_at (app f a)..) (inst_at (app f a)..)`, NOT the
/// goal `DefEq (inst_at (app f a)..) (inst_at (app f' a')..)` (`app f a` is not
/// def-equal to `app f' a'` — the primed vars are free and distinct). The
/// kernel MUST reject it, witnessing that the congruence genuinely needs
/// `DefEq.app_cong` on the hypotheses, not reflexivity.
pub(crate) const INSTANTIATE_AT_APP_PRESERVES_DEF_EQ: CheckerCoreLemma = CheckerCoreLemma {
    name: "instantiate_at_app_preserves_def_eq",
    type_src: "forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (val : KExpr) (depth : Nat), DefEq (instantiate_at f val depth) (instantiate_at f' val depth) -> DefEq (instantiate_at a val depth) (instantiate_at a' val depth) -> DefEq (instantiate_at (KExpr.app f a) val depth) (instantiate_at (KExpr.app f' a') val depth)",
    fake_src: "fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (val : KExpr) (depth : Nat) (hf : DefEq (instantiate_at f val depth) (instantiate_at f' val depth)) (ha : DefEq (instantiate_at a val depth) (instantiate_at a' val depth)) => DefEq.refl (instantiate_at (KExpr.app f a) val depth)",
    lineage_domain: "trust-certify.cleancic.checker-core.defeq.v1",
    label: "clean-verify.core_spec.instantiate_at_app_preserves_def_eq: instantiate_at is a DefEq congruence on app",
};

/// def_eq substitution congruence on LAMBDAS (the binder-crossing twin of
/// [`INSTANTIATE_AT_APP_PRESERVES_DEF_EQ`]):
///   `forall A A' b b' val depth,
///      DefEq (inst_at A val depth) (inst_at A' val depth) ->
///      DefEq (inst_at b val (Nat.succ depth)) (inst_at b' val (Nat.succ depth)) ->
///      DefEq (inst_at (lam A b) val depth) (inst_at (lam A' b') val depth)`.
///
/// The body hypothesis is at `Nat.succ depth` because `instantiate_at` descends
/// UNDER the λ binder — the exact binder-depth bookkeeping the kernel's `def_eq`
/// performs when it compares two lambdas. Discharged in clean-verify via
/// `DefEq.lam_cong` + `instantiate_at_lam` + `def_eq_eq_left`/`def_eq_eq_right`
/// (core_spec substitution_def_eq.rs), zero domain axioms.
///
/// NEGATIVE control ignores both hypotheses and returns
/// `DefEq.refl (instantiate_at (KExpr.lam A b) val depth)`: its conclusion is
/// `DefEq (inst_at (lam A b)..) (inst_at (lam A b)..)`, NOT the goal
/// `... (inst_at (lam A' b')..)` (`lam A b` is not def-equal to `lam A' b'` — the
/// primed vars are free and distinct). The kernel MUST reject it, witnessing that
/// the congruence genuinely needs `DefEq.lam_cong` on the hypotheses.
pub(crate) const INSTANTIATE_AT_LAM_PRESERVES_DEF_EQ: CheckerCoreLemma = CheckerCoreLemma {
    name: "instantiate_at_lam_preserves_def_eq",
    type_src: "forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (val : KExpr) (depth : Nat), DefEq (instantiate_at A val depth) (instantiate_at A' val depth) -> DefEq (instantiate_at b val (Nat.succ depth)) (instantiate_at b' val (Nat.succ depth)) -> DefEq (instantiate_at (KExpr.lam A b) val depth) (instantiate_at (KExpr.lam A' b') val depth)",
    fake_src: "fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (val : KExpr) (depth : Nat) (hA : DefEq (instantiate_at A val depth) (instantiate_at A' val depth)) (hb : DefEq (instantiate_at b val (Nat.succ depth)) (instantiate_at b' val (Nat.succ depth))) => DefEq.refl (instantiate_at (KExpr.lam A b) val depth)",
    lineage_domain: "trust-certify.cleancic.checker-core.defeq-lam.v1",
    label: "clean-verify.core_spec.instantiate_at_lam_preserves_def_eq: instantiate_at is a DefEq congruence on lam",
};

/// def_eq substitution congruence on PIS (the dependent-function twin):
///   `forall A A' B B' val depth,
///      DefEq (inst_at A val depth) (inst_at A' val depth) ->
///      DefEq (inst_at B val (Nat.succ depth)) (inst_at B' val (Nat.succ depth)) ->
///      DefEq (inst_at (pi A B) val depth) (inst_at (pi A' B') val depth)`.
///
/// Same binder-crossing shape as the lambda twin (`instantiate_at` descends under
/// the Π codomain, hence `Nat.succ depth`). Discharged via `DefEq.pi_cong` +
/// `instantiate_at_pi` + `def_eq_eq_left`/`def_eq_eq_right`, zero domain axioms.
///
/// NEGATIVE control returns `DefEq.refl (instantiate_at (KExpr.pi A B) val depth)`
/// — conclusion `DefEq (inst_at (pi A B)..) (inst_at (pi A B)..)`, NOT the goal
/// `... (inst_at (pi A' B')..)`. The kernel MUST reject it.
pub(crate) const INSTANTIATE_AT_PI_PRESERVES_DEF_EQ: CheckerCoreLemma = CheckerCoreLemma {
    name: "instantiate_at_pi_preserves_def_eq",
    type_src: "forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (val : KExpr) (depth : Nat), DefEq (instantiate_at A val depth) (instantiate_at A' val depth) -> DefEq (instantiate_at B val (Nat.succ depth)) (instantiate_at B' val (Nat.succ depth)) -> DefEq (instantiate_at (KExpr.pi A B) val depth) (instantiate_at (KExpr.pi A' B') val depth)",
    fake_src: "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (val : KExpr) (depth : Nat) (hA : DefEq (instantiate_at A val depth) (instantiate_at A' val depth)) (hB : DefEq (instantiate_at B val (Nat.succ depth)) (instantiate_at B' val (Nat.succ depth))) => DefEq.refl (instantiate_at (KExpr.pi A B) val depth)",
    lineage_domain: "trust-certify.cleancic.checker-core.defeq-pi.v1",
    label: "clean-verify.core_spec.instantiate_at_pi_preserves_def_eq: instantiate_at is a DefEq congruence on pi",
};

/// SUBJECT REDUCTION — the keystone type-safety metatheorem: β-reduction
/// PRESERVES typing.
///   `forall (hf : RedEnvFaithful the_red_env) (e e' T : KExpr),
///      DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) ->
///      beta_reduces e e' -> has_type e T -> has_type e' T`
///
/// This is the DEEPEST checker-core correctness fact in this lane: forward
/// subject reduction (a.k.a. type preservation / "well-typed terms stay
/// well-typed under reduction") for the kernel's β/ι/congruence reduction —
/// the heart of type safety. Discharged in clean-verify by `beta_reduces.rec`
/// induction over every reduction arm: `beta_preservation` for the β arm, the
/// nine congruence arms via `typing_app_gen` + `Typing.conv` +
/// `beta_reduces_typed_def_eq` (dependent arms re-establish the type through the
/// def-eq of the reduced argument), and the four `let` arms vacuously via
/// `typing_let_absurd` — `DerivedProved`, ZERO domain axioms
/// (core_spec beta_reduces_preserves_typing.rs).
///
/// NEGATIVE control returns the INPUT typing `ht0 : has_type e0 T0` verbatim,
/// ignoring the reduction — the "forgot to advance the term" error (the exact
/// analogue of the whnf-idempotence "forgot to advance the endpoint" control).
/// Its type is `... -> has_type e0 T0`, NOT the goal `... -> has_type e0' T0`
/// (`e0` is not def-equal to `e0'` — both free). The kernel MUST reject it,
/// witnessing that preservation genuinely needs the induction over
/// `beta_reduces`, not the premise verbatim.
pub(crate) const BETA_REDUCES_PRESERVES_TYPING: CheckerCoreLemma = CheckerCoreLemma {
    name: "beta_reduces_preserves_typing",
    type_src: "forall (hf : RedEnvFaithful the_red_env) (e : KExpr) (e' : KExpr) (T : KExpr), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> beta_reduces e e' -> has_type e T -> has_type e' T",
    fake_src: "fun (hf : RedEnvFaithful the_red_env) (e0 : KExpr) (e0' : KExpr) (T0 : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (hbr : beta_reduces e0 e0') (ht0 : has_type e0 T0) => ht0",
    lineage_domain: "trust-certify.cleancic.checker-core.subject-reduction.v1",
    label: "clean-verify.core_spec.beta_reduces_preserves_typing: forward subject reduction (beta_reduces preserves has_type)",
};

/// MODEL-SIDE INFER/CHECK COHERENCE (historically named `tc_infer_soundness`):
/// when the model's infer relation accepts `e` with result `T`, its check relation
/// also accepts `e` against that same `T`.
///   `forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : …LiftClosed…)
///           (i5 : DefEnvClosed …) (i6 : …LiftClosed…)
///           (st : KernelState) (e T : KExpr),
///      KernelStateMatchesSpec st -> KernelInputAdmissible st e ->
///      KernelInferAccepts st e T -> KernelCheckAccepts st e T`
///
/// This ties the model relations for the two central operations (`infer_type` and
/// the `def_eq`-driven `check_type`) together. It is NOT the separate semantic
/// theorem from infer acceptance to `has_type`, nor literal-Rust function
/// correctness. clean-verify drained it from a HelperAxiom to a `DerivedProved`
/// theorem; its value
/// builds `KernelCheckAccepts.mk` with `R := T` (infer half = the hypothesis;
/// def-eq half via `DefEq.refl T`; admissibility via `infer_result_self_admissible`),
/// zero domain axioms. Re-checking THIS through clean's own kernel is trust
/// independently attesting this exact model-side coherence claim
/// (type_checker_spec.rs).
///
/// NEGATIVE control returns the INFER acceptance `hinfer : KernelInferAccepts st e T`
/// verbatim — the "returned infer-acceptance instead of check-acceptance" error. Its
/// type is `… -> KernelInferAccepts st e T`, NOT the goal `… -> KernelCheckAccepts st
/// e T` (`KernelInferAccepts` and `KernelCheckAccepts` are distinct inductives). The
/// kernel MUST reject it, witnessing that coherence genuinely constructs the
/// `KernelCheckAccepts` derivation, not the infer premise verbatim.
pub(crate) const TC_INFER_SOUNDNESS: CheckerCoreLemma = CheckerCoreLemma {
    name: "tc_infer_soundness",
    type_src: "forall (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) (i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) (st : KernelState) (e : KExpr) (T : KExpr), KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelInferAccepts st e T -> KernelCheckAccepts st e T",
    fake_src: "fun (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) (i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) (st : KernelState) (e : KExpr) (T : KExpr) (hmatch : KernelStateMatchesSpec st) (hadm : KernelInputAdmissible st e) (hinfer : KernelInferAccepts st e T) => hinfer",
    lineage_domain: "trust-certify.cleancic.checker-core.infer-soundness.v1",
    // Protocol compatibility: this historical v1 label is lineage-bound and
    // cannot be reworded without minting a v2 domain. The surrounding docs state
    // the theorem's narrower infer/check-coherence scope precisely.
    label: "clean-verify.type_checker_spec.tc_infer_soundness: KernelInferAccepts st e T -> KernelCheckAccepts st e T (type-checker algorithmic soundness)",
};

/// WHNF STRONG NORMALIZATION — the TERMINATION pillar of kernel soundness: every
/// well-typed term's weak-head normalization terminates.
///   `forall (e : KExpr) (T : KExpr), has_type e T -> terminates_whnf e`
///
/// `terminates_whnf e := whnf_acc e` = accessibility under the FULL
/// `whnf_step = beta_reduces ∪ delta_reduces` — a genuine `Acc`-style
/// well-foundedness / termination predicate (NOT a vacuous alias). Discharged in
/// clean-verify by `beta_bd_acc.rec` induction; a RETIRED census axiom, now a
/// `DerivedProved` ZERO-domain-axiom theorem. It complements the model-side
/// infer/check coherence and preservation results in this checker-core suite
/// (core_spec whnf_terminates_well_typed.rs).
///
/// NEGATIVE control returns the typing hypothesis `ht : has_type e T` — the "handed
/// back the typing premise instead of the termination proof" error. Its type is
/// `… -> has_type e T` (`Typing e T`), NOT the goal `… -> terminates_whnf e`
/// (`whnf_acc e`); `Typing` and `whnf_acc` are distinct inductives, so the kernel
/// REJECTS it, witnessing that termination genuinely needs the accessibility
/// induction, not the typing premise verbatim.
pub(crate) const WHNF_TERMINATES_WELL_TYPED: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_terminates_well_typed",
    type_src: "forall (e : KExpr) (T : KExpr), has_type e T -> terminates_whnf e",
    fake_src: "fun (e : KExpr) (T : KExpr) (ht : has_type e T) => ht",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-termination.v1",
    label: "clean-verify.core_spec.whnf_terminates_well_typed: has_type e T -> terminates_whnf e (whnf termination = whnf_acc accessibility under beta∪delta, for the spec's context-free Typing fragment AS STATED — not a full dependent-CIC SN claim)",
};

/// Structural inversion for clean-verify's reflected `KernelInferAccepts`
/// relation. The relation has five constructors (sort/const/app/lam/pi); bvar
/// and let reduce to the empty inversion payload. This is a kernel-checked
/// eliminator for that model, not a literal-Rust `infer_type` correctness claim.
pub(crate) const KERNEL_INFER_INVERSION: CheckerCoreLemma = CheckerCoreLemma {
    name: "kernel_infer_inversion",
    type_src: "forall (st : KernelState) (e : KExpr) (T : KExpr), KernelInferAccepts st e T -> InferInversionAt st e T",
    fake_src: "fun (st : KernelState) (e : KExpr) (T : KExpr) (h : KernelInferAccepts st e T) => h",
    lineage_domain: "trust-certify.cleancic.checker-core.infer-inversion.v1",
    // Protocol compatibility: this published v1 label is lineage-bound. Honest
    // scope is stated in the surrounding prose; changing the label requires v2.
    label: "clean-verify.core_spec.kernel_infer_inversion: KernelInferAccepts st e T -> InferInversionAt st e T (master inversion for the reflected KernelInferAccepts inductive; all six per-case infer lemmas project from this single eliminator; DerivedProved, empty axiom_deps)",
};

/// Conditional strong normalization for CLOSED terms in the dependent
/// `TypingCtx` model. The result is parametric in a caller-supplied
/// `M : CandModel tenv`; it neither proves model existence for arbitrary `tenv`
/// nor grounds the literal Rust implementation.
pub(crate) const WHNF_TERMINATES_WELL_TYPED_DEPENDENT: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_terminates_well_typed_dependent",
    type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (e : KExpr) (T : KExpr), TypingCtx tenv (ListType.nil KExpr) e T -> whnf_acc e",
    fake_src: "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (e : KExpr) (T : KExpr) (h : TypingCtx tenv (ListType.nil KExpr) e T) => h",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-termination-dependent.v1",
    // Protocol compatibility: keep the published v1 metadata byte-for-byte;
    // the qualification above is the authoritative scope clarification.
    label: "clean-verify.core_spec.whnf_terminates_well_typed_dependent: TypingCtx tenv nil e T -> whnf_acc e (DEPENDENT rich-model strong normalization, parametric in M : CandModel — closes the degenerate-context-free caveat of whnf_terminates_well_typed; DerivedProved, empty axiom_deps; modulo the CandModel hypothesis exactly as clean-verify states)",
};

/// Soundness of clean-verify's context-explicit, six-shape `KernelInfers`
/// relation against `TypingCtxConv`. `KernelInfers` has no let arm, and the
/// relation-to-Rust fidelity boundary remains outside this theorem.
pub(crate) const BOOTSTRAP_INFER_SOUND: CheckerCoreLemma = CheckerCoreLemma {
    name: "bootstrap_infer_sound",
    type_src: "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (e : KExpr) (T : KExpr), KernelInfers tenv G e T -> TypingCtxConv tenv G e T",
    fake_src: "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : KernelInfers tenv G e T) => h",
    lineage_domain: "trust-certify.cleancic.checker-core.bootstrap-infer-sound.v1",
    label: "clean-verify.bootstrap.bootstrap_infer_sound: KernelInfers tenv G e T -> TypingCtxConv tenv G e T (context-explicit algorithmic soundness — the bootstrap infer relation implies the declarative dependent judgment; DerivedProved, empty axiom_deps, by induction on KernelInfers; third of the three crosscheck-pinned flagships)",
};

/// Reflexivity of the modeled `KernelDefEqAccepts` relation on an admissible
/// expression in a spec-matching modeled state. This is not a literal execution
/// theorem for the Rust `is_def_eq` function.
pub(crate) const TC_IS_DEF_EQ_REFLEXIVE: CheckerCoreLemma = CheckerCoreLemma {
    name: "tc_is_def_eq_reflexive",
    type_src: "forall (st : KernelState) (e : KExpr), KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelDefEqAccepts st e e",
    fake_src: "fun (st : KernelState) (e : KExpr) (hstate : KernelStateMatchesSpec st) (hadm : KernelInputAdmissible st e) => hadm",
    lineage_domain: "trust-certify.cleancic.checker-core.tc-is-def-eq-reflexive.v1",
    label: "clean-verify.tc_spec.tc_is_def_eq_reflexive: KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelDefEqAccepts st e e (algorithmic is_def_eq reflexivity over the KernelState surface; DerivedProved, empty axiom_deps)",
};

/// Symmetry of the modeled `KernelDefEqAccepts` relation. The proof eliminates
/// its guarded `DefEqJoinable` payload, swaps it, and rebuilds the relation; it
/// does not establish a deployed-function result without a grounding bridge.
pub(crate) const TC_IS_DEF_EQ_SYMMETRIC: CheckerCoreLemma = CheckerCoreLemma {
    name: "tc_is_def_eq_symmetric",
    type_src: "forall (st : KernelState) (a : KExpr) (b : KExpr), KernelStateMatchesSpec st -> KernelBinaryInputAdmissible st a b -> KernelDefEqAccepts st a b -> KernelDefEqAccepts st b a",
    fake_src: "fun (st : KernelState) (a : KExpr) (b : KExpr) (hstate : KernelStateMatchesSpec st) (hadm : KernelBinaryInputAdmissible st a b) (hdefeq : KernelDefEqAccepts st a b) => hdefeq",
    lineage_domain: "trust-certify.cleancic.checker-core.tc-is-def-eq-symmetric.v1",
    label: "clean-verify.tc_spec.tc_is_def_eq_symmetric: KernelDefEqAccepts st a b -> KernelDefEqAccepts st b a (algorithmic is_def_eq symmetry over the KernelState surface; DerivedProved, empty axiom_deps; the negative control returns the UN-swapped witness, which only the real symmetry proof repairs)",
};

/// Idempotence of the modeled `KernelWhnfAccepts` trace relation. This is the
/// KernelState-surface twin of `WHNF_IDEMPOTENT`, still without literal-Rust
/// `whnf` grounding.
pub(crate) const TC_WHNF_IDEMPOTENT: CheckerCoreLemma = CheckerCoreLemma {
    name: "tc_whnf_idempotent",
    type_src: "forall (st : KernelState) (e : KExpr) (v : KExpr), KernelStateMatchesSpec st -> KernelInputAdmissible st e -> KernelWhnfAccepts st e v -> KernelWhnfAccepts st v v",
    fake_src: "fun (st : KernelState) (e : KExpr) (v : KExpr) (hstate : KernelStateMatchesSpec st) (hadm : KernelInputAdmissible st e) (hwhnf : KernelWhnfAccepts st e v) => hwhnf",
    lineage_domain: "trust-certify.cleancic.checker-core.tc-whnf-idempotent.v1",
    label: "clean-verify.tc_spec.tc_whnf_idempotent: KernelWhnfAccepts st e v -> KernelWhnfAccepts st v v (algorithmic whnf idempotence over the KernelState surface; DerivedProved, empty axiom_deps; distinct from the model-level whnf_idempotent)",
};

/// Transitivity of the formal, model-level `is_def_eq` relation. This is a
/// constructive declarative `DefEq` theorem; it is deliberately distinct from
/// the KernelState-surface acceptance lemmas and from universal correctness of
/// the deployed Rust `TypeChecker::is_def_eq` implementation.
pub(crate) const TC_DEF_EQ_TRANSITIVITY: CheckerCoreLemma = CheckerCoreLemma {
    name: "tc_def_eq_transitivity",
    type_src: "forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), is_def_eq e1 e2 -> is_def_eq e2 e3 -> is_def_eq e1 e3",
    fake_src: "fun (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) (h12 : is_def_eq e1 e2) (h23 : is_def_eq e2 e3) => h12",
    lineage_domain: "trust-certify.cleancic.checker-core.tc-def-eq-transitivity.v1",
    label: "clean-verify.type_checker_spec.tc_def_eq_transitivity: is_def_eq e1 e2 -> is_def_eq e2 e3 -> is_def_eq e1 e3 (TRANSITIVITY of is_def_eq — completes the model-level equivalence relation; DerivedProved, empty axiom_deps)",
};

/// Model-level bridge from a `whnf_to` reduction trace to declarative `DefEq`.
/// This attests the compact KExpr model only; literal Rust WHNF correctness
/// remains outside this certificate lane's authority.
pub(crate) const WHNF_TO_PRESERVES_DEF_EQ: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_to_preserves_def_eq",
    type_src: "forall (e : KExpr) (e' : KExpr), whnf_to e e' -> DefEq e e'",
    fake_src: "fun (e : KExpr) (e' : KExpr) (h : whnf_to e e') => h",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-to-preserves-def-eq.v1",
    label: "clean-verify.core_spec.whnf_to_preserves_def_eq: whnf_to e e' -> DefEq e e' (the whnf→DefEq bridge — a whnf reduction is a definitional equality, load-bearing for the infer-soundness app-arm conv step; DerivedProved, empty axiom_deps)",
};

/// Star-diamond / Church-Rosser for clean-verify's modeled parallel-C-star
/// relation at its concrete, non-vacuous `faithful_red_env`. The environment is
/// a one-recursor/one-definition KExpr model, not the deployed Rust environment
/// or a MIR-grounded reduction theorem.
pub(crate) const PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL: CheckerCoreLemma = CheckerCoreLemma {
    name: "par_reduces_c_star_diamond_faithful",
    type_src: "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), par_reduces_c_star (red_rec faithful_red_env) e e1 -> par_reduces_c_star (red_rec faithful_red_env) e e2 -> par_strips_witness_c_star (red_rec faithful_red_env) e1 e2",
    fake_src: "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : par_reduces_c_star (red_rec faithful_red_env) e e1) (h2 : par_reduces_c_star (red_rec faithful_red_env) e e2) => h1",
    lineage_domain: "trust-certify.cleancic.checker-core.par-reduces-c-star-diamond-faithful.v1",
    // Protocol compatibility: preserve the published v1 label byte-for-byte;
    // the model-specific qualification above is the authoritative scope.
    label: "clean-verify.core_spec.par_reduces_c_star_diamond_faithful: par_reduces_c_star e e1 -> par_reduces_c_star e e2 -> par_strips_witness_c_star e1 e2 (CONFLUENCE / star-diamond for parallel-C reduction over the real faithful_red_env — the Church-Rosser pillar; DerivedProved, empty axiom_deps)",
};

/// The parallel-P-star twin of [`PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL`], with
/// the same model-specific and non-MIR-grounded scope.
pub(crate) const PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL: CheckerCoreLemma = CheckerCoreLemma {
    name: "par_reduces_p_star_diamond_faithful",
    type_src: "forall (e : KExpr) (e1 : KExpr) (e2 : KExpr), par_reduces_p_star (red_rec faithful_red_env) e e1 -> par_reduces_p_star (red_rec faithful_red_env) e e2 -> par_strips_witness_p_star (red_rec faithful_red_env) e1 e2",
    fake_src: "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : par_reduces_p_star (red_rec faithful_red_env) e e1) (h2 : par_reduces_p_star (red_rec faithful_red_env) e e2) => h1",
    lineage_domain: "trust-certify.cleancic.checker-core.par-reduces-p-star-diamond-faithful.v1",
    // Protocol compatibility: preserve the published v1 label byte-for-byte;
    // the model-specific qualification above is the authoritative scope.
    label: "clean-verify.core_spec.par_reduces_p_star_diamond_faithful: par_reduces_p_star e e1 -> par_reduces_p_star e e2 -> par_strips_witness_p_star e1 e2 (CONFLUENCE / star-diamond for parallel-P reduction over the real faithful_red_env — the Church-Rosser pillar, P twin; DerivedProved, empty axiom_deps)",
};

/// BETA reduction is DETERMINISTIC up to definitional equality: any two β-reducts of
/// the same term are def-eq. clean-verify: `DerivedProved`, EMPTY axiom_deps, via
/// DefEq.trans/symm over beta_reduces_preserves_def_eq (implementation_soundness_whnf_decomposition.rs).
pub(crate) const BETA_DETERMINISTIC: CheckerCoreLemma = CheckerCoreLemma {
    name: "beta_deterministic",
    type_src: "forall (e : KExpr) (r1 : KExpr) (r2 : KExpr), beta_reduces e r1 -> beta_reduces e r2 -> DefEq r1 r2",
    fake_src: "fun (e : KExpr) (r1 : KExpr) (r2 : KExpr) (h1 : beta_reduces e r1) (h2 : beta_reduces e r2) => h1",
    lineage_domain: "trust-certify.cleancic.checker-core.beta-deterministic.v1",
    label: "clean-verify.core_spec.beta_deterministic: beta_reduces e r1 -> beta_reduces e r2 -> DefEq r1 r2 (beta reduction is deterministic up to def-eq; DerivedProved, empty axiom_deps)",
};

/// DELTA reduction is a DETERMINISTIC FUNCTION: the `delta_reduct` partial function
/// gives the same output for the same input (two `some` results are equal). clean-verify:
/// `DerivedProved`, EMPTY axiom_deps (delta_step.rs).
pub(crate) const DELTA_STEP_DETERMINISTIC: CheckerCoreLemma = CheckerCoreLemma {
    name: "delta_step_deterministic",
    type_src: "forall (env : DefEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e1) -> Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e2) -> Eq KExpr e1 e2",
    fake_src: "fun (env : DefEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e1)) (h2 : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e2)) => h1",
    lineage_domain: "trust-certify.cleancic.checker-core.delta-step-deterministic.v1",
    label: "clean-verify.core_spec.delta_step_deterministic: delta_reduct env e = some e1 -> delta_reduct env e = some e2 -> e1 = e2 (delta_reduct is a deterministic function; DerivedProved, empty axiom_deps)",
};

/// IOTA reduction is a DETERMINISTIC FUNCTION: the `iota_reduct` partial function gives
/// the same output for the same input. clean-verify: `DerivedProved`, EMPTY axiom_deps
/// (iota_step.rs).
pub(crate) const IOTA_STEP_DETERMINISTIC: CheckerCoreLemma = CheckerCoreLemma {
    name: "iota_step_deterministic",
    type_src: "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e1) -> Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e2) -> Eq KExpr e1 e2",
    fake_src: "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e1)) (h2 : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e2)) => h1",
    lineage_domain: "trust-certify.cleancic.checker-core.iota-step-deterministic.v1",
    label: "clean-verify.core_spec.iota_step_deterministic: iota_reduct env e = some e1 -> iota_reduct env e = some e2 -> e1 = e2 (iota_reduct is a deterministic function; DerivedProved, empty axiom_deps)",
};

/// UNIQUENESS OF NORMAL FORMS — the direct payoff of confluence (par_reduces_c_star
/// diamond): two par_reduces_c-normal forms reachable from a common source are EQUAL,
/// unconditionally over the real faithful_red_env. The capstone that makes conversion
/// checking well-defined. clean-verify: `DerivedProved`, EMPTY axiom_deps, with all four
/// faithful interfaces discharged by honest witnesses (unique_normal_forms_c.rs, Item 3).
pub(crate) const UNIQUE_NORMAL_FORMS_C_FAITHFUL: CheckerCoreLemma = CheckerCoreLemma {
    name: "unique_normal_forms_c_faithful",
    type_src: "forall (e : KExpr) (n1 : KExpr) (n2 : KExpr), par_reduces_c_star (red_rec faithful_red_env) e n1 -> par_reduces_c_star (red_rec faithful_red_env) e n2 -> is_normal_c (red_rec faithful_red_env) n1 -> is_normal_c (red_rec faithful_red_env) n2 -> Eq KExpr n1 n2",
    fake_src: "fun (e : KExpr) (n1 : KExpr) (n2 : KExpr) (h1 : par_reduces_c_star (red_rec faithful_red_env) e n1) (h2 : par_reduces_c_star (red_rec faithful_red_env) e n2) (hn1 : is_normal_c (red_rec faithful_red_env) n1) (hn2 : is_normal_c (red_rec faithful_red_env) n2) => h1",
    lineage_domain: "trust-certify.cleancic.checker-core.unique-normal-forms-c-faithful.v1",
    label: "clean-verify.core_spec.unique_normal_forms_c_faithful: two par_reduces_c-normal forms from a common source are equal (UNIQUENESS OF NORMAL FORMS over the real faithful_red_env — the confluence payoff; DerivedProved, empty axiom_deps)",
};

/// The whnf REDUCER-PROGRESS universal (model level): every const-free, bvar-free
/// KExpr exposes a whnf exit — `whnf_progress_result e` is the `done (is_whnf e) |
/// stuck ..` sum (the `stuck` shape is the honest disclosure that the landed `is_whnf`
/// is narrow). This is `∀e, whnf makes progress`, the model-level core of the recursive
/// whnf reducer's "produces a WHNF" guarantee. clean-verify: `DerivedProved`, EMPTY
/// axiom_deps (core_spec whnf_progress.rs).
pub(crate) const WHNF_PROGRESS_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_progress_bd",
    type_src: "forall (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> whnf_progress_result e",
    fake_src: "fun (e : KExpr) (hbc : Eq Nat (bvar_ceiling e) Nat.zero) (hcf : const_free e) => hcf",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-progress-bd.v1",
    label: "clean-verify.core_spec.whnf_progress_bd: bvar_ceiling e = 0 -> const_free e -> whnf_progress_result e (the whnf REDUCER-PROGRESS universal — every const-free bvar-free KExpr exposes a whnf exit, done|stuck; DerivedProved, empty axiom_deps)",
};

/// The whnf REDUCER-NORMALIZES universal (model level): every WELL-TYPED const-free
/// KExpr whnf-normalizes to a result — `whnf_normalizes_result e` (`done` a landed
/// is_whnf value, or the honestly-disclosed stuck residual). This is the model-level
/// `∀e, is_whnf(whnf e)` (as honestly as the narrow landed `is_whnf` permits), the
/// recursive whnf reducer's universal at the KExpr model level. clean-verify:
/// `DerivedProved`, EMPTY axiom_deps (core_spec whnf_normalizes.rs).
pub(crate) const WHNF_NORMALIZES_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_normalizes_bd",
    type_src: "forall (e : KExpr) (T : KExpr), has_type e T -> const_free e -> whnf_normalizes_result e",
    fake_src: "fun (e : KExpr) (T : KExpr) (ht : has_type e T) (hcf : const_free e) => hcf",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-normalizes-bd.v1",
    label: "clean-verify.core_spec.whnf_normalizes_bd: has_type e T -> const_free e -> whnf_normalizes_result e (the whnf REDUCER-NORMALIZES universal — every well-typed const-free KExpr whnf-normalizes to a result; the model-level ∀e is_whnf(whnf e); DerivedProved, empty axiom_deps)",
};

/// The reducer-universal COMPOSITION GLUE: a const-free bvar-free term with NO
/// `beta_reduces_bd` reduct is a landed `is_whnf` value or the honest stuck
/// residual (`whnf_noredex_class` = progress minus the step arm). This is the
/// kernel-checked model-side implication tying the LITERAL fixpoint-exit MIR
/// witness (the real whnf_outer_loop returns only step-fixpoints) to WHNF-ness.
/// clean-verify: `DerivedProved`, EMPTY axiom_deps, by `whnf_progress_result.rec`
/// with a no-step-strengthened motive; the step arm refuted by `Empty.rec`
/// (core_spec/whnf_progress.rs).
pub(crate) const STEP_FIXPOINT_CLASSIFIES_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "step_fixpoint_classifies_bd",
    type_src: "forall (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> (forall (e2 : KExpr), beta_reduces_bd e e2 -> Empty) -> whnf_noredex_class e",
    fake_src: "fun (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : const_free e) (hns : forall (e2 : KExpr), beta_reduces_bd e e2 -> Empty) => hc",
    lineage_domain: "trust-certify.cleancic.checker-core.step-fixpoint-classifies-bd.v1",
    label: "clean-verify.core_spec.step_fixpoint_classifies_bd: no beta_reduces_bd reduct -> whnf_noredex_class e (the COMPOSITION GLUE — fixpoint of the step + progress => done-or-stuck, kernel-checked; DerivedProved, empty axiom_deps)",
};

/// FULL δ-PROGRESS (model level, the X13b spec-port capstone): every closed KExpr
/// whose constants are ALL DEFINED in the environment exposes a δ-aware whnf exit —
/// a landed is_whnf value, a whnf_env_step (β/ζ or one deterministic head-δ fire),
/// or the honest stuck residual. The δ-extension of WHNF_PROGRESS_BD beyond the
/// const-free fragment. clean-verify: DerivedProved, EMPTY axiom_deps
/// (core_spec/whnf_progress.rs, Aristotle-guide-validated foreign-side first).
pub(crate) const WHNF_PROGRESS_ENV_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_progress_env_bd",
    type_src: "forall (env : DefEnv) (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> whnf_progress_result_env env e",
    fake_src: "fun (env : DefEnv) (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : consts_defined env e) => hc",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-progress-env-bd.v1",
    label: "clean-verify.core_spec.whnf_progress_env_bd: bvar_ceiling e = 0 -> consts_defined env e -> whnf_progress_result_env env e (FULL δ-PROGRESS — every closed fully-defined KExpr exposes a δ-aware whnf exit; DerivedProved, empty axiom_deps)",
};

/// The δ-AWARE COMPOSITION GLUE (X14): a closed, fully-defined term with NO
/// whnf_env_step reduct (no β, no ζ, AND no head-δ) is a landed is_whnf value or
/// the honest stuck residual. The reducer-universal inference over the FULL
/// default-mode step family — fixpoint + full δ-progress ⟹ done-or-stuck.
/// clean-verify: DerivedProved, EMPTY axiom_deps (core_spec/whnf_progress.rs).
pub(crate) const ENV_FIXPOINT_CLASSIFIES_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "env_fixpoint_classifies_bd",
    type_src: "forall (env : DefEnv) (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> (forall (e2 : KExpr), whnf_env_step env e e2 -> Empty) -> whnf_noredex_class e",
    fake_src: "fun (env : DefEnv) (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : consts_defined env e) (hns : forall (e2 : KExpr), whnf_env_step env e e2 -> Empty) => hc",
    lineage_domain: "trust-certify.cleancic.checker-core.env-fixpoint-classifies-bd.v1",
    label: "clean-verify.core_spec.env_fixpoint_classifies_bd: no whnf_env_step reduct -> whnf_noredex_class e (the δ-AWARE COMPOSITION GLUE — fixpoint + FULL δ-progress => done-or-stuck; DerivedProved, empty axiom_deps)",
};

/// FULL 3-WAY PROGRESS (X15): every closed KExpr whose constants are all defined
/// exposes a COMPLETE-default-mode whnf exit — a landed is_whnf value, a
/// whnf_red_step (β/ζ, one head-δ fire, or one head-ι fire over the combined
/// RedEnv), or the honest stuck residual. The δ-progress capstone lifted over the
/// full reduction environment. clean-verify: DerivedProved, EMPTY axiom_deps.
pub(crate) const WHNF_PROGRESS_RED_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_progress_red_bd",
    type_src: "forall (renv : RedEnv) (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined (red_def renv) e -> whnf_progress_result_red renv e",
    fake_src: "fun (renv : RedEnv) (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : consts_defined (red_def renv) e) => hc",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-progress-red-bd.v1",
    label: "clean-verify.core_spec.whnf_progress_red_bd: bvar_ceiling e = 0 -> consts_defined (red_def renv) e -> whnf_progress_result_red renv e (FULL 3-WAY PROGRESS over the complete default-mode step family β/ζ+δ+ι; DerivedProved, empty axiom_deps)",
};

/// THE 3-WAY COMPOSITION GLUE (X15): a closed, fully-defined term with NO
/// whnf_red_step reduct — no β, no ζ, no head-δ, AND no head-ι — is a landed
/// is_whnf value or the honest stuck residual. The reducer-universal inference
/// over the COMPLETE default-mode step family. clean-verify: DerivedProved,
/// EMPTY axiom_deps.
pub(crate) const RED_FIXPOINT_CLASSIFIES_BD: CheckerCoreLemma = CheckerCoreLemma {
    name: "red_fixpoint_classifies_bd",
    type_src: "forall (renv : RedEnv) (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined (red_def renv) e -> (forall (e2 : KExpr), whnf_red_step renv e e2 -> Empty) -> whnf_noredex_class e",
    fake_src: "fun (renv : RedEnv) (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : consts_defined (red_def renv) e) (hns : forall (e2 : KExpr), whnf_red_step renv e e2 -> Empty) => hc",
    lineage_domain: "trust-certify.cleancic.checker-core.red-fixpoint-classifies-bd.v1",
    label: "clean-verify.core_spec.red_fixpoint_classifies_bd: no whnf_red_step reduct -> whnf_noredex_class e (THE 3-WAY COMPOSITION GLUE — fixpoint over the COMPLETE default-mode step family => done-or-stuck; DerivedProved, empty axiom_deps)",
};

/// FIXPOINT-ONLY RETURNS (X16a): a successful whnf_fuel result has NO
/// reduce_once reduct — the executable loop only exits at the fixpoint (or
/// bails honestly). clean-verify: DerivedProved, EMPTY axiom_deps.
pub(crate) const WHNF_FUEL_NO_REDEX: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_fuel_no_redex",
    type_src: "forall (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> Eq (OptionType KExpr) (reduce_once env r) (OptionType.none KExpr)",
    fake_src: "fun (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r)) => h",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-fuel-no-redex.v1",
    label: "clean-verify.core_spec.whnf_fuel_no_redex: whnf_fuel success -> reduce_once fixpoint (FIXPOINT-ONLY RETURNS of the executable loop; DerivedProved, empty axiom_deps)",
};

/// EXECUTABLE-STEP SOUNDNESS (X16b): every some-result of reduce_once is a
/// real whnf_env_step — via the spine-δ correspondence. clean-verify:
/// DerivedProved, EMPTY axiom_deps.
pub(crate) const REDUCE_ONCE_SOUND: CheckerCoreLemma = CheckerCoreLemma {
    name: "reduce_once_sound",
    type_src: "forall (env : DefEnv) (e : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2) -> whnf_env_step env e e2",
    fake_src: "fun (env : DefEnv) (e : KExpr) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2)) => h",
    lineage_domain: "trust-certify.cleancic.checker-core.reduce-once-sound.v1",
    label: "clean-verify.core_spec.reduce_once_sound: reduce_once some -> whnf_env_step (EXECUTABLE-STEP SOUNDNESS via the spine-delta correspondence; DerivedProved, empty axiom_deps)",
};

/// UNCONDITIONAL REACH (X16b corollary): every successful loop result is
/// reached by the δ-aware step star — the soundness hypothesis discharged.
/// clean-verify: DerivedProved, EMPTY axiom_deps.
pub(crate) const WHNF_FUEL_REACHES_SOUND: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_fuel_reaches_sound",
    type_src: "forall (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> env_step_star env e r",
    fake_src: "fun (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r)) => h",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-fuel-reaches-sound.v1",
    label: "clean-verify.core_spec.whnf_fuel_reaches_sound: whnf_fuel success -> env_step_star reach (UNCONDITIONAL REACH of the executable loop; DerivedProved, empty axiom_deps)",
};

/// THE EXECUTABLE-LOOP CAPSTONE (X16c): over a good environment, every
/// successful whnf_fuel result on a closed, fully-defined term CLASSIFIES —
/// a landed is_whnf value or the honest stuck residual. With the fixpoint
/// and reach lemmas, the complete "returns WHNF or honestly bails" statement
/// for the in-spec executable loop — a MODEL-level theorem, kernel-rechecked
/// (it binds no literal-Rust MIR). clean-verify: DerivedProved, EMPTY
/// axiom_deps.
pub(crate) const WHNF_FUEL_CLASSIFIES: CheckerCoreLemma = CheckerCoreLemma {
    name: "whnf_fuel_classifies",
    type_src: "forall (env : DefEnv), def_env_good env -> forall (fuel : Nat) (e : KExpr) (r : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> whnf_noredex_class r",
    fake_src: "fun (env : DefEnv) (hEnv : def_env_good env) (fuel : Nat) (e : KExpr) (r : KExpr) (hc : Eq Nat (bvar_ceiling e) Nat.zero) (hd : consts_defined env e) (h : Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r)) => hd",
    lineage_domain: "trust-certify.cleancic.checker-core.whnf-fuel-classifies.v1",
    label: "clean-verify.core_spec.whnf_fuel_classifies: whnf_fuel success + closed + defined + good env -> whnf_noredex_class (THE EXECUTABLE-LOOP CAPSTONE, model level; DerivedProved, empty axiom_deps)",
};

/// SHA-256 lineage digest binding the term, the empty closed context, the
/// lemma's obligation label, and its pinned goal source. Position-tagged +
/// length-prefixed => injective; the lemma-specific domain keeps the digest
/// disjoint from every other lane.
fn lineage_digest(
    lemma: &CheckerCoreLemma,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(lemma.lineage_domain.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), lemma.label.as_bytes()),
        (b"goal:".as_slice(), lemma.type_src.as_bytes()),
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

/// The only context this closed-lemma lane mints or accepts.  Byte-for-byte
/// canonicality matters: merely hashing caller-supplied context bytes would let
/// an attacker re-lineage an unrelated/non-canonical context that this rechecker
/// never interprets.
fn canonical_empty_context_bytes() -> Option<Vec<u8>> {
    serialize_context(&ReducedContext { decls: Vec::new() }).ok()
}

/// Recompute the proof's authority from the LIVE specification rather than
/// trusting the hand-maintained status fields alone.  Foundational modeling
/// rules remain admitted exactly as before; trust markers and residual
/// non-foundational/domain axioms are never admitted by this certificate lane.
fn lemma_authority_is_clean(
    spec: &clean_verify::spec::Specification,
    lemma: &CheckerCoreLemma,
) -> bool {
    let Some(def) = spec.get_definition(lemma.name) else {
        return false;
    };
    // The closure helpers conservatively expose an empty set for an absent
    // kernel constant. Do not let a future spec-registration drift turn that
    // diagnostic fallback into a fail-open authority result.
    if spec.env().get_const(&clean_kernel::name::Name::from_string(lemma.name)).is_none() {
        return false;
    }
    if def.is_axiom
        || def.proof_status != clean_verify::spec::ProofStatus::DerivedProved
        || !def.axiom_deps.is_empty()
    {
        return false;
    }
    let foundational = clean_verify::spec_axiom_closure::foundational_base(spec);
    // One authoritative kernel closure is enough for both partitions. Besides
    // avoiding two full dependency walks per mint/recheck, this keeps the trust
    // marker and residual decisions on exactly the same closure snapshot.
    let closure = clean_verify::spec_axiom_closure::computed_axiom_closure(spec, lemma.name);
    let (trust_markers, residual) =
        clean_verify::spec_axiom_closure::partition_closure(&closure, &foundational);
    trust_markers.is_empty() && residual.is_empty()
}

/// The heavy body of the mint, run on the large-stack thread.
fn certify_inner(lemma: &CheckerCoreLemma) -> Option<trust_ir::ProofEvidence> {
    let spec = clean_verify::spec::Specification::new().ok()?;
    let def = spec.get_definition(lemma.name)?;

    // Pin the exact checker-core Prop: fail closed if the spec has drifted, so
    // we certify precisely this property and never a silently-changed statement.
    if def.type_src != lemma.type_src {
        return None;
    }
    // Honesty residual (model level): a constructive, zero-domain-axiom proof.
    if !lemma_authority_is_clean(&spec, lemma) {
        return None;
    }

    let goal = def.elaborated_type.as_ref()?;
    let proof = def.elaborated_value.as_ref()?;

    // 1. The clean kernel independently type-checks the DerivedProved proof term
    //    against the checker-core goal.
    if !kernel_checks_goal(spec.env(), proof, goal) {
        return None;
    }

    // 2. NO MASQUERADE: the negative control must (a) elaborate to a well-formed
    //    term and (b) be REJECTED against the goal before we mint. If it cannot
    //    be elaborated we cannot demonstrate a discriminating rejection, so we
    //    fail closed. If it is ACCEPTED, the kernel check is vacuous — fail closed.
    let fake = elaborate_full(spec.env(), lemma.fake_src)?;
    if kernel_checks_goal(spec.env(), &fake, goal) {
        return None;
    }

    // 3. Serialize term + empty closed context via the clean_auto codec, then
    //    re-check the DESERIALIZED payload round-trips to a kernel-valid term.
    let term_bytes = serialize_term(proof).ok()?;
    let context_bytes = canonical_empty_context_bytes()?;
    let roundtrip = deserialize_term(&term_bytes).ok()?;
    if !kernel_checks_goal(spec.env(), &roundtrip, goal) {
        return None;
    }
    let lineage = lineage_digest(lemma, &term_bytes, &context_bytes);

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Mint a kernel-CHECKED `CleanCic` certificate that the clean-verify
/// `DerivedProved` KExpr proof term discharges the given checker-core `lemma`.
/// Returns `None` (fail-closed) on any spec-build, drift, kernel-check,
/// negative-control, serialization, or round-trip failure.
#[must_use]
fn certify_lemma(lemma: &'static CheckerCoreLemma) -> Option<trust_ir::ProofEvidence> {
    run_on_large_stack(move || certify_inner(lemma)).flatten()
}

/// The heavy body of the consumer-side re-check, run on the large-stack thread.
fn recheck_inner(
    lemma: &CheckerCoreLemma,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let Some(spec) = clean_verify::spec::Specification::new().ok() else {
        return false;
    };
    let Some(def) = spec.get_definition(lemma.name) else {
        return false;
    };
    // Rebuild the goal independently and pin it.
    if def.type_src != lemma.type_src {
        return false;
    }
    if !lemma_authority_is_clean(&spec, lemma) {
        return false;
    }
    let (Some(goal), Some(canonical_proof)) =
        (def.elaborated_type.as_ref(), def.elaborated_value.as_ref())
    else {
        return false;
    };

    // Proof authority is canonical, not "any term the ambient spec happens to
    // type-check".  The latter accepts `@sorry goal` because `Environment::new`
    // deliberately contains polymorphic trust-marker axioms.  Pinning the exact
    // independently rebuilt DerivedProved term also excludes forged helper-axiom
    // closures and alternative proofs with broader authority.
    let Ok(canonical_term_bytes) = serialize_term(canonical_proof) else {
        return false;
    };
    if term_bytes != canonical_term_bytes.as_slice() {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(spec.env(), &term, goal) {
        return false;
    }
    &lineage_digest(lemma, term_bytes, context_bytes) == lineage
}

/// Consumer-side re-check of a checker-core `CleanCic` certificate for `lemma`:
/// independently rebuild the spec + goal, recompute its live axiom closure,
/// require the canonical proof/context bytes, deserialize the term, re-run the
/// clean-kernel `check_type`, and re-bind the lineage digest. Returns `true`
/// only when every authority and integrity gate agrees.
#[must_use]
fn recheck_lemma(
    lemma: &'static CheckerCoreLemma,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if canonical_empty_context_bytes().as_deref() != Some(context_bytes) {
        return false;
    }
    let term = term_bytes.to_vec();
    let context = context_bytes.to_vec();
    let lineage = *lineage;
    run_on_large_stack(move || recheck_inner(lemma, &term, &context, &lineage)).unwrap_or(false)
}

/// Certify the WHNF idempotence checker-core lemma (`whnf_to e e' -> whnf_to e'
/// e'`) to a kernel-CHECKED `CleanCic` certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_whnf_idempotent() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_IDEMPOTENT)
}

/// Consumer-side re-check of a WHNF-idempotence checker-core certificate.
#[must_use]
pub fn recheck_whnf_idempotent(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_IDEMPOTENT, term_bytes, context_bytes, lineage)
}

/// Certify the def_eq substitution-congruence checker-core lemma
/// (`instantiate_at_app_preserves_def_eq`) to a kernel-CHECKED `CleanCic`
/// certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_instantiate_at_app_preserves_def_eq() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&INSTANTIATE_AT_APP_PRESERVES_DEF_EQ)
}

/// Consumer-side re-check of a def_eq-congruence checker-core certificate.
#[must_use]
pub fn recheck_instantiate_at_app_preserves_def_eq(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&INSTANTIATE_AT_APP_PRESERVES_DEF_EQ, term_bytes, context_bytes, lineage)
}

/// Certify the def_eq substitution-congruence checker-core lemma on LAMBDAS
/// (`instantiate_at_lam_preserves_def_eq`) to a kernel-CHECKED `CleanCic`
/// certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_instantiate_at_lam_preserves_def_eq() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&INSTANTIATE_AT_LAM_PRESERVES_DEF_EQ)
}

/// Consumer-side re-check of the lambda def_eq-congruence checker-core certificate.
#[must_use]
pub fn recheck_instantiate_at_lam_preserves_def_eq(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&INSTANTIATE_AT_LAM_PRESERVES_DEF_EQ, term_bytes, context_bytes, lineage)
}

/// Certify the def_eq substitution-congruence checker-core lemma on PIS
/// (`instantiate_at_pi_preserves_def_eq`) to a kernel-CHECKED `CleanCic`
/// certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_instantiate_at_pi_preserves_def_eq() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&INSTANTIATE_AT_PI_PRESERVES_DEF_EQ)
}

/// Consumer-side re-check of the pi def_eq-congruence checker-core certificate.
#[must_use]
pub fn recheck_instantiate_at_pi_preserves_def_eq(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&INSTANTIATE_AT_PI_PRESERVES_DEF_EQ, term_bytes, context_bytes, lineage)
}

/// Certify the SUBJECT-REDUCTION keystone metatheorem
/// (`beta_reduces_preserves_typing`: β-reduction preserves typing) to a
/// kernel-CHECKED `CleanCic` certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_beta_reduces_preserves_typing() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&BETA_REDUCES_PRESERVES_TYPING)
}

/// Consumer-side re-check of a subject-reduction checker-core certificate.
#[must_use]
pub fn recheck_beta_reduces_preserves_typing(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&BETA_REDUCES_PRESERVES_TYPING, term_bytes, context_bytes, lineage)
}

/// Certify the model-side infer/check coherence theorem (`tc_infer_soundness`:
/// infer-relation acceptance of `e:T` implies check-relation acceptance of
/// `e:T`) to a kernel-CHECKED `CleanCic` certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_tc_infer_soundness() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&TC_INFER_SOUNDNESS)
}

/// Consumer-side re-check of a type-checker-soundness checker-core certificate.
#[must_use]
pub fn recheck_tc_infer_soundness(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&TC_INFER_SOUNDNESS, term_bytes, context_bytes, lineage)
}

/// Certify the WHNF strong-normalization theorem (`whnf_terminates_well_typed`:
/// every well-typed term's weak-head normalization terminates) to a kernel-CHECKED
/// `CleanCic` certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_whnf_terminates_well_typed() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_TERMINATES_WELL_TYPED)
}

/// Consumer-side re-check of a whnf-termination checker-core certificate.
#[must_use]
pub fn recheck_whnf_terminates_well_typed(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_TERMINATES_WELL_TYPED, term_bytes, context_bytes, lineage)
}

/// Certify structural inversion of the reflected `KernelInferAccepts` relation
/// to a kernel-checked, authority-closed `CleanCic` certificate.
#[must_use]
pub fn certify_kernel_infer_inversion() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&KERNEL_INFER_INVERSION)
}

/// Consumer-side re-check of a reflected-infer-inversion certificate.
#[must_use]
pub fn recheck_kernel_infer_inversion(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&KERNEL_INFER_INVERSION, term_bytes, context_bytes, lineage)
}

/// Certify the conditional dependent-model WHNF normalization theorem for
/// closed terms to an authority-closed `CleanCic` certificate.
#[must_use]
pub fn certify_whnf_terminates_well_typed_dependent() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_TERMINATES_WELL_TYPED_DEPENDENT)
}

/// Consumer-side re-check of a dependent-model WHNF certificate.
#[must_use]
pub fn recheck_whnf_terminates_well_typed_dependent(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_TERMINATES_WELL_TYPED_DEPENDENT, term_bytes, context_bytes, lineage)
}

/// Certify soundness of the modeled six-shape `KernelInfers` relation against
/// `TypingCtxConv` to an authority-closed `CleanCic` certificate.
#[must_use]
pub fn certify_bootstrap_infer_sound() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&BOOTSTRAP_INFER_SOUND)
}

/// Consumer-side re-check of a modeled bootstrap-infer-sound certificate.
#[must_use]
pub fn recheck_bootstrap_infer_sound(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&BOOTSTRAP_INFER_SOUND, term_bytes, context_bytes, lineage)
}

/// Certify reflexivity of the modeled `KernelDefEqAccepts` relation.
#[must_use]
pub fn certify_tc_is_def_eq_reflexive() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&TC_IS_DEF_EQ_REFLEXIVE)
}

/// Consumer-side re-check of a modeled def-eq-reflexivity certificate.
#[must_use]
pub fn recheck_tc_is_def_eq_reflexive(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&TC_IS_DEF_EQ_REFLEXIVE, term_bytes, context_bytes, lineage)
}

/// Certify symmetry of the modeled `KernelDefEqAccepts` relation.
#[must_use]
pub fn certify_tc_is_def_eq_symmetric() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&TC_IS_DEF_EQ_SYMMETRIC)
}

/// Consumer-side re-check of a modeled def-eq-symmetry certificate.
#[must_use]
pub fn recheck_tc_is_def_eq_symmetric(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&TC_IS_DEF_EQ_SYMMETRIC, term_bytes, context_bytes, lineage)
}

/// Certify idempotence of the modeled `KernelWhnfAccepts` relation.
#[must_use]
pub fn certify_tc_whnf_idempotent() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&TC_WHNF_IDEMPOTENT)
}

/// Consumer-side re-check of a modeled WHNF-idempotence certificate.
#[must_use]
pub fn recheck_tc_whnf_idempotent(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&TC_WHNF_IDEMPOTENT, term_bytes, context_bytes, lineage)
}

/// Certify transitivity of the model-level `is_def_eq` relation.
#[must_use]
pub fn certify_tc_def_eq_transitivity() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&TC_DEF_EQ_TRANSITIVITY)
}

/// Consumer-side re-check of the model-level def-eq-transitivity certificate.
#[must_use]
pub fn recheck_tc_def_eq_transitivity(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&TC_DEF_EQ_TRANSITIVITY, term_bytes, context_bytes, lineage)
}

/// Certify the modeled `whnf_to` to declarative `DefEq` bridge.
#[must_use]
pub fn certify_whnf_to_preserves_def_eq() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_TO_PRESERVES_DEF_EQ)
}

/// Consumer-side re-check of the modeled WHNF-to-DefEq bridge certificate.
#[must_use]
pub fn recheck_whnf_to_preserves_def_eq(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_TO_PRESERVES_DEF_EQ, term_bytes, context_bytes, lineage)
}

/// Certify the modeled parallel-C-star diamond at `faithful_red_env`.
#[must_use]
pub fn certify_par_reduces_c_star_diamond_faithful() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL)
}

/// Consumer-side re-check of the modeled parallel-C-star diamond certificate.
#[must_use]
pub fn recheck_par_reduces_c_star_diamond_faithful(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL, term_bytes, context_bytes, lineage)
}

/// Certify the modeled parallel-P-star diamond at `faithful_red_env`.
#[must_use]
pub fn certify_par_reduces_p_star_diamond_faithful() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL)
}

/// Consumer-side re-check of the modeled parallel-P-star diamond certificate.
#[must_use]
pub fn recheck_par_reduces_p_star_diamond_faithful(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL, term_bytes, context_bytes, lineage)
}

/// Certify BETA determinism (`beta_deterministic`) to a kernel-CHECKED cert. Fail-closed.
#[must_use]
pub fn certify_beta_deterministic() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&BETA_DETERMINISTIC)
}

/// Consumer-side re-check of a beta-deterministic checker-core certificate.
#[must_use]
pub fn recheck_beta_deterministic(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&BETA_DETERMINISTIC, term_bytes, context_bytes, lineage)
}

/// Certify DELTA-step determinism (`delta_step_deterministic`) to a kernel-CHECKED cert.
#[must_use]
pub fn certify_delta_step_deterministic() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&DELTA_STEP_DETERMINISTIC)
}

/// Consumer-side re-check of a delta-step-deterministic checker-core certificate.
#[must_use]
pub fn recheck_delta_step_deterministic(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&DELTA_STEP_DETERMINISTIC, term_bytes, context_bytes, lineage)
}

/// Certify IOTA-step determinism (`iota_step_deterministic`) to a kernel-CHECKED cert.
#[must_use]
pub fn certify_iota_step_deterministic() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&IOTA_STEP_DETERMINISTIC)
}

/// Consumer-side re-check of an iota-step-deterministic checker-core certificate.
#[must_use]
pub fn recheck_iota_step_deterministic(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&IOTA_STEP_DETERMINISTIC, term_bytes, context_bytes, lineage)
}

/// Certify UNIQUENESS OF NORMAL FORMS (`unique_normal_forms_c_faithful`) — the
/// confluence payoff — to a kernel-CHECKED `CleanCic` certificate. Fail-closed (`None`).
#[must_use]
pub fn certify_unique_normal_forms_c_faithful() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&UNIQUE_NORMAL_FORMS_C_FAITHFUL)
}

/// Consumer-side re-check of a unique-normal-forms-c-faithful checker-core certificate.
#[must_use]
pub fn recheck_unique_normal_forms_c_faithful(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&UNIQUE_NORMAL_FORMS_C_FAITHFUL, term_bytes, context_bytes, lineage)
}

/// Certify the whnf REDUCER-PROGRESS universal (`whnf_progress_bd`). Fail-closed.
#[must_use]
pub fn certify_whnf_progress_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_PROGRESS_BD)
}

/// Consumer-side re-check of a whnf-progress-bd checker-core certificate.
#[must_use]
pub fn recheck_whnf_progress_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_PROGRESS_BD, term_bytes, context_bytes, lineage)
}

/// Certify the whnf REDUCER-NORMALIZES universal (`whnf_normalizes_bd`). Fail-closed.
#[must_use]
pub fn certify_whnf_normalizes_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_NORMALIZES_BD)
}

/// Consumer-side re-check of a whnf-normalizes-bd checker-core certificate.
#[must_use]
pub fn recheck_whnf_normalizes_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_NORMALIZES_BD, term_bytes, context_bytes, lineage)
}

/// Certify the reducer-universal COMPOSITION GLUE (`step_fixpoint_classifies_bd`:
/// no step ⟹ done-or-stuck). Fail-closed (`None`).
#[must_use]
pub fn certify_step_fixpoint_classifies_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&STEP_FIXPOINT_CLASSIFIES_BD)
}

/// Consumer-side re-check of a step-fixpoint-classifies checker-core certificate.
#[must_use]
pub fn recheck_step_fixpoint_classifies_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&STEP_FIXPOINT_CLASSIFIES_BD, term_bytes, context_bytes, lineage)
}

/// Certify FULL δ-PROGRESS (`whnf_progress_env_bd`). Fail-closed.
#[must_use]
pub fn certify_whnf_progress_env_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_PROGRESS_ENV_BD)
}

/// Consumer-side re-check of a whnf-progress-env-bd checker-core certificate.
#[must_use]
pub fn recheck_whnf_progress_env_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_PROGRESS_ENV_BD, term_bytes, context_bytes, lineage)
}

/// Certify the δ-AWARE COMPOSITION GLUE (`env_fixpoint_classifies_bd`).
/// Fail-closed.
#[must_use]
pub fn certify_env_fixpoint_classifies_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&ENV_FIXPOINT_CLASSIFIES_BD)
}

/// Consumer-side re-check of an env-fixpoint-classifies checker-core certificate.
#[must_use]
pub fn recheck_env_fixpoint_classifies_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&ENV_FIXPOINT_CLASSIFIES_BD, term_bytes, context_bytes, lineage)
}

/// Certify FULL 3-WAY PROGRESS (`whnf_progress_red_bd`). Fail-closed.
#[must_use]
pub fn certify_whnf_progress_red_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_PROGRESS_RED_BD)
}

/// Consumer-side re-check of a whnf-progress-red-bd checker-core certificate.
#[must_use]
pub fn recheck_whnf_progress_red_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_PROGRESS_RED_BD, term_bytes, context_bytes, lineage)
}

/// Certify THE 3-WAY COMPOSITION GLUE (`red_fixpoint_classifies_bd`).
/// Fail-closed.
#[must_use]
pub fn certify_red_fixpoint_classifies_bd() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&RED_FIXPOINT_CLASSIFIES_BD)
}

/// Consumer-side re-check of a red-fixpoint-classifies checker-core certificate.
#[must_use]
pub fn recheck_red_fixpoint_classifies_bd(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&RED_FIXPOINT_CLASSIFIES_BD, term_bytes, context_bytes, lineage)
}

/// Certify FIXPOINT-ONLY RETURNS (`whnf_fuel_no_redex`). Fail-closed.
#[must_use]
pub fn certify_whnf_fuel_no_redex() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_FUEL_NO_REDEX)
}

/// Consumer-side re-check of a whnf-fuel-no-redex checker-core certificate.
#[must_use]
pub fn recheck_whnf_fuel_no_redex(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_FUEL_NO_REDEX, term_bytes, context_bytes, lineage)
}

/// Certify EXECUTABLE-STEP SOUNDNESS (`reduce_once_sound`). Fail-closed.
#[must_use]
pub fn certify_reduce_once_sound() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&REDUCE_ONCE_SOUND)
}

/// Consumer-side re-check of a reduce-once-sound checker-core certificate.
#[must_use]
pub fn recheck_reduce_once_sound(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&REDUCE_ONCE_SOUND, term_bytes, context_bytes, lineage)
}

/// Certify UNCONDITIONAL REACH (`whnf_fuel_reaches_sound`). Fail-closed.
#[must_use]
pub fn certify_whnf_fuel_reaches_sound() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_FUEL_REACHES_SOUND)
}

/// Consumer-side re-check of a whnf-fuel-reaches-sound checker-core certificate.
#[must_use]
pub fn recheck_whnf_fuel_reaches_sound(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_FUEL_REACHES_SOUND, term_bytes, context_bytes, lineage)
}

/// Certify THE EXECUTABLE-LOOP CAPSTONE (`whnf_fuel_classifies`). Fail-closed.
#[must_use]
pub fn certify_whnf_fuel_classifies() -> Option<trust_ir::ProofEvidence> {
    certify_lemma(&WHNF_FUEL_CLASSIFIES)
}

/// Consumer-side re-check of a whnf-fuel-classifies checker-core certificate.
#[must_use]
pub fn recheck_whnf_fuel_classifies(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_lemma(&WHNF_FUEL_CLASSIFIES, term_bytes, context_bytes, lineage)
}

#[cfg(test)]
mod tests {
    use trust_ir::ProofEvidence;

    use super::*;

    /// Shared milestone + fail-closed exercise for one checker-core lemma lane
    /// (each spec rebuild is heavy, so all gates share one mint):
    ///
    /// * the lemma mints to a kernel-CHECKED `CleanCic` certificate;
    /// * its serialized payload re-checks via an INDEPENDENTLY rebuilt spec +
    ///   kernel;
    /// * a tampered term fails the re-check (fail-closed);
    /// * a swapped (zeroed) lineage fails the re-check (fail-closed).
    fn assert_lemma_closes(
        lemma: &'static CheckerCoreLemma,
        certify: fn() -> Option<ProofEvidence>,
        recheck: fn(&[u8], &[u8], &trust_ir::ProofDigest) -> bool,
        what: &str,
    ) {
        let evidence = certify().unwrap_or_else(|| panic!("{what} must certify to CleanCic"));
        let ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } = evidence else {
            panic!("expected CleanCic evidence for {what}");
        };
        assert!(kernel_recheck.is_none());
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload for {what}");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound for {what}");

        // Consumer-independent re-check: rebuild the spec + goal from scratch and
        // re-run the clean kernel on the DESERIALIZED term.
        assert!(
            recheck(&term, &context, &lineage),
            "serialized {what} CleanCic payload must re-check via the clean kernel"
        );

        // Fail-closed: a tampered term must not re-check.
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck(&tampered, &context, &lineage),
            "tampered {what} term must fail the offline kernel re-check"
        );

        // Fail-closed: a swapped (zeroed) lineage must not re-check.
        assert!(
            !recheck(&term, &context, &trust_ir::ProofDigest::zero()),
            "a zeroed lineage must fail closed for {what}"
        );

        // Fail-closed even when an attacker recomputes the public lineage over
        // non-canonical context bytes.  This lane is closed and mints exactly one
        // canonical encoding of the empty context.
        let mut noncanonical_context = context.clone();
        noncanonical_context.push(0);
        let relined = lineage_digest(lemma, &term, &noncanonical_context);
        assert!(
            !recheck(&term, &noncanonical_context, &relined),
            "re-lineaged non-canonical context must fail closed for {what}"
        );
    }

    /// A public SHA lineage is an integrity binding, not proof authority.  Show
    /// that the ambient kernel really would accept polymorphic `@sorry goal`, then
    /// require the lane rechecker to reject that well-typed forged certificate
    /// even when the attacker recomputes a matching lineage.
    fn assert_relineaged_sorry_rejected(
        lemma: &'static CheckerCoreLemma,
        recheck: fn(&[u8], &[u8], &trust_ir::ProofDigest) -> bool,
    ) {
        let (forged_term, context) = run_on_large_stack(move || {
            let spec = clean_verify::spec::Specification::new().expect("spec should build");
            let def = spec.get_definition(lemma.name).expect("def present");
            assert_eq!(def.type_src, lemma.type_src, "pinned goal must match the spec");
            let goal = def.elaborated_type.as_ref().expect("goal");
            let goal_level = clean_kernel::TypeChecker::new(spec.env())
                .infer_sort(goal)
                .expect("checker-core goal has a universe");
            let sorry = clean_kernel::Expr::app(
                clean_kernel::Expr::const_(
                    clean_kernel::Name::from_string("sorry"),
                    vec![goal_level],
                ),
                goal.clone(),
            );
            assert!(
                kernel_checks_goal(spec.env(), &sorry, goal),
                "non-vacuity: the ambient kernel accepts polymorphic @sorry goal"
            );
            (
                serialize_term(&sorry).expect("serialize forged sorry term"),
                canonical_empty_context_bytes().expect("serialize canonical context"),
            )
        })
        .expect("forgery construction thread must not panic");
        let forged_lineage = lineage_digest(lemma, &forged_term, &context);
        assert!(
            !recheck(&forged_term, &context, &forged_lineage),
            "a well-typed @sorry proof with recomputed lineage must fail closed"
        );
    }

    /// NO MASQUERADE: the lemma genuinely REQUIRES its inductive/congruence
    /// argument. The negative control is a WELL-FORMED term of the WRONG type,
    /// and the kernel REJECTS it against the goal — the witness that the mint's
    /// kernel check is discriminating.
    fn assert_negative_control_rejected(lemma: &'static CheckerCoreLemma) {
        let (fake_elaborates, rejected) = run_on_large_stack(|| {
            let spec = clean_verify::spec::Specification::new().expect("spec should build");
            let def = spec.get_definition(lemma.name).expect("def present");
            assert_eq!(def.type_src, lemma.type_src, "pinned goal must match the spec");
            let goal = def.elaborated_type.as_ref().expect("goal");
            let fake = elaborate_full(spec.env(), lemma.fake_src);
            let elaborates = fake.is_some();
            let rejected = fake.is_some_and(|fk| !kernel_checks_goal(spec.env(), &fk, goal));
            (elaborates, rejected)
        })
        .expect("neg-control thread must not panic");
        assert!(fake_elaborates, "the negative control must elaborate to a well-formed term");
        assert!(
            rejected,
            "the negative control (wrong-type term) must NOT type-check against the goal"
        );
    }

    /// The live closure gate is intentionally stricter than the historical
    /// hand-maintained status fields. Check every pinned lane in one shared spec
    /// rebuild so a newly discovered trust marker/domain axiom cannot silently
    /// turn all consumer rechecks into a compatibility-breaking fail-closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn all_pinned_checker_core_authority_closures_are_clean() {
        run_on_large_stack(|| {
            let spec = clean_verify::spec::Specification::new().expect("spec should build");
            for lemma in [
                &WHNF_IDEMPOTENT,
                &INSTANTIATE_AT_APP_PRESERVES_DEF_EQ,
                &INSTANTIATE_AT_LAM_PRESERVES_DEF_EQ,
                &INSTANTIATE_AT_PI_PRESERVES_DEF_EQ,
                &BETA_REDUCES_PRESERVES_TYPING,
                &TC_INFER_SOUNDNESS,
                &WHNF_TERMINATES_WELL_TYPED,
                &KERNEL_INFER_INVERSION,
                &WHNF_TERMINATES_WELL_TYPED_DEPENDENT,
                &BOOTSTRAP_INFER_SOUND,
                &TC_IS_DEF_EQ_REFLEXIVE,
                &TC_IS_DEF_EQ_SYMMETRIC,
                &TC_WHNF_IDEMPOTENT,
                &TC_DEF_EQ_TRANSITIVITY,
                &WHNF_TO_PRESERVES_DEF_EQ,
                &PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL,
                &PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL,
                &STEP_FIXPOINT_CLASSIFIES_BD,
            ] {
                let def = spec.get_definition(lemma.name).expect("pinned definition present");
                assert_eq!(def.type_src, lemma.type_src, "pinned goal drift for {}", lemma.name);
                assert!(
                    lemma_authority_is_clean(&spec, lemma),
                    "live authority closure must remain clean for {}",
                    lemma.name
                );
                let (goal, proof) = (
                    def.elaborated_type.as_ref().expect("elaborated goal"),
                    def.elaborated_value.as_ref().expect("elaborated canonical proof"),
                );
                assert!(
                    kernel_checks_goal(spec.env(), proof, goal),
                    "canonical proof must remain kernel-valid for {}",
                    lemma.name
                );
                let fake = elaborate_full(spec.env(), lemma.fake_src).unwrap_or_else(|| {
                    panic!("negative control must elaborate for {}", lemma.name)
                });
                assert!(
                    !kernel_checks_goal(spec.env(), &fake, goal),
                    "negative control must remain kernel-rejected for {}",
                    lemma.name
                );
            }
        })
        .expect("authority-closure audit thread must not panic");
    }

    /// THE WHNF MILESTONE: `whnf_to e e' -> whnf_to e' e'` (WHNF idempotence) —
    /// a correctness property of the kernel's `whnf` reduction, discharged by a
    /// genuine `whnf_to.rec` induction — mints + re-checks + fails closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_idempotent_checker_core_closes() {
        assert_lemma_closes(
            &WHNF_IDEMPOTENT,
            certify_whnf_idempotent,
            recheck_whnf_idempotent,
            "whnf_idempotent",
        );
    }

    /// NO MASQUERADE for the whnf lane.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_idempotent_negative_control_rejected() {
        assert_negative_control_rejected(&WHNF_IDEMPOTENT);
    }

    /// THE DEF_EQ MILESTONE: `instantiate_at` is a DefEq congruence on
    /// applications — a correctness property of the kernel's `def_eq`,
    /// discharged via `DefEq.app_cong` + `instantiate_at_app` — mints +
    /// re-checks + fails closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn instantiate_at_app_preserves_def_eq_checker_core_closes() {
        assert_lemma_closes(
            &INSTANTIATE_AT_APP_PRESERVES_DEF_EQ,
            certify_instantiate_at_app_preserves_def_eq,
            recheck_instantiate_at_app_preserves_def_eq,
            "instantiate_at_app_preserves_def_eq",
        );
    }

    /// NO MASQUERADE for the def_eq lane.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn instantiate_at_app_preserves_def_eq_negative_control_rejected() {
        assert_negative_control_rejected(&INSTANTIATE_AT_APP_PRESERVES_DEF_EQ);
    }

    /// THE DEF_EQ LAM MILESTONE: `instantiate_at` is a DefEq congruence on
    /// LAMBDAS (the binder-crossing twin) — discharged via `DefEq.lam_cong` +
    /// `instantiate_at_lam` — mints + re-checks + fails closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn instantiate_at_lam_preserves_def_eq_checker_core_closes() {
        assert_lemma_closes(
            &INSTANTIATE_AT_LAM_PRESERVES_DEF_EQ,
            certify_instantiate_at_lam_preserves_def_eq,
            recheck_instantiate_at_lam_preserves_def_eq,
            "instantiate_at_lam_preserves_def_eq",
        );
    }

    /// NO MASQUERADE for the def_eq lam lane.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn instantiate_at_lam_preserves_def_eq_negative_control_rejected() {
        assert_negative_control_rejected(&INSTANTIATE_AT_LAM_PRESERVES_DEF_EQ);
    }

    /// THE DEF_EQ PI MILESTONE: `instantiate_at` is a DefEq congruence on PIS
    /// (the dependent-function twin) — discharged via `DefEq.pi_cong` +
    /// `instantiate_at_pi` — mints + re-checks + fails closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn instantiate_at_pi_preserves_def_eq_checker_core_closes() {
        assert_lemma_closes(
            &INSTANTIATE_AT_PI_PRESERVES_DEF_EQ,
            certify_instantiate_at_pi_preserves_def_eq,
            recheck_instantiate_at_pi_preserves_def_eq,
            "instantiate_at_pi_preserves_def_eq",
        );
    }

    /// NO MASQUERADE for the def_eq pi lane.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn instantiate_at_pi_preserves_def_eq_negative_control_rejected() {
        assert_negative_control_rejected(&INSTANTIATE_AT_PI_PRESERVES_DEF_EQ);
    }

    /// THE SUBJECT-REDUCTION MILESTONE (the keystone type-safety metatheorem):
    /// `beta_reduces e e' -> has_type e T -> has_type e' T` — β-reduction
    /// PRESERVES typing, discharged in clean-verify by a genuine `beta_reduces.rec`
    /// induction over every reduction arm — mints to a kernel-CHECKED `CleanCic`
    /// certificate, re-checks via an independently rebuilt spec + kernel, and fails
    /// closed on tamper/lineage-swap. This is the deepest checker-core correctness
    /// property kernel-rechecked in this lane: type safety under reduction.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn beta_reduces_preserves_typing_checker_core_closes() {
        assert_lemma_closes(
            &BETA_REDUCES_PRESERVES_TYPING,
            certify_beta_reduces_preserves_typing,
            recheck_beta_reduces_preserves_typing,
            "beta_reduces_preserves_typing",
        );
    }

    /// NO MASQUERADE for the subject-reduction lane: the negative control returns
    /// the input typing `ht0 : has_type e0 T0` (forgetting to advance the term),
    /// whose type is NOT the goal `has_type e0' T0`; the kernel REJECTS it,
    /// witnessing that preservation genuinely needs the induction over
    /// `beta_reduces`, not the premise verbatim.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn beta_reduces_preserves_typing_negative_control_rejected() {
        assert_negative_control_rejected(&BETA_REDUCES_PRESERVES_TYPING);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn beta_reduces_preserves_typing_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &BETA_REDUCES_PRESERVES_TYPING,
            recheck_beta_reduces_preserves_typing,
        );
    }

    /// MODEL-SIDE INFER/CHECK COHERENCE: when the infer relation accepts `e:T`,
    /// the check relation accepts `e:T`, tying the two modeled operations
    /// together without claiming algorithm-to-typing or literal-Rust soundness.
    /// clean-verify proves it (drained to `DerivedProved`, zero domain axioms);
    /// this lane INDEPENDENTLY re-checks that proof through clean's own kernel —
    /// trust attesting this exact coherence claim — mints + re-checks + fails
    /// closed on tamper/lineage-swap.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_infer_soundness_checker_core_closes() {
        assert_lemma_closes(
            &TC_INFER_SOUNDNESS,
            certify_tc_infer_soundness,
            recheck_tc_infer_soundness,
            "tc_infer_soundness",
        );
    }

    /// NO MASQUERADE for infer/check coherence: the negative control returns the
    /// INFER acceptance `hinfer : KernelInferAccepts st e T` (not the check
    /// acceptance); its type is NOT the goal `KernelCheckAccepts st e T`, and the
    /// kernel REJECTS it — the witness that coherence genuinely constructs the
    /// `KernelCheckAccepts` derivation.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_infer_soundness_negative_control_rejected() {
        assert_negative_control_rejected(&TC_INFER_SOUNDNESS);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_infer_soundness_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&TC_INFER_SOUNDNESS, recheck_tc_infer_soundness);
    }

    /// THE TERMINATION MILESTONE (whnf strong normalization): every well-typed
    /// term's weak-head normalization terminates —
    /// `has_type e T -> terminates_whnf e` (accessibility under the full whnf_step).
    /// The termination leg of kernel soundness, discharged in clean-verify by
    /// `beta_bd_acc.rec` induction (zero domain axioms); this lane INDEPENDENTLY
    /// re-checks that proof through clean's own kernel — mints + re-checks + fails
    /// closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_terminates_well_typed_checker_core_closes() {
        assert_lemma_closes(
            &WHNF_TERMINATES_WELL_TYPED,
            certify_whnf_terminates_well_typed,
            recheck_whnf_terminates_well_typed,
            "whnf_terminates_well_typed",
        );
    }

    /// NO MASQUERADE for the termination lane: the negative control returns the
    /// typing hypothesis `ht : has_type e T`, whose type is NOT the goal
    /// `terminates_whnf e` (`Typing` and `whnf_acc` are distinct inductives); the
    /// kernel REJECTS it — the witness that termination genuinely needs the
    /// accessibility induction, not the typing premise.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_terminates_well_typed_negative_control_rejected() {
        assert_negative_control_rejected(&WHNF_TERMINATES_WELL_TYPED);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_terminates_well_typed_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &WHNF_TERMINATES_WELL_TYPED,
            recheck_whnf_terminates_well_typed,
        );
    }

    /// Structural inversion of the reflected five-constructor infer relation
    /// mints, independently re-checks, and fails closed on tamper/context drift.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn kernel_infer_inversion_checker_core_closes() {
        assert_lemma_closes(
            &KERNEL_INFER_INVERSION,
            certify_kernel_infer_inversion,
            recheck_kernel_infer_inversion,
            "kernel_infer_inversion",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn kernel_infer_inversion_negative_control_rejected() {
        assert_negative_control_rejected(&KERNEL_INFER_INVERSION);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn kernel_infer_inversion_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&KERNEL_INFER_INVERSION, recheck_kernel_infer_inversion);
    }

    /// Conditional dependent-model SN for closed terms mints and re-checks on
    /// the exact pinned proposition and canonical proof bytes.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_terminates_well_typed_dependent_checker_core_closes() {
        assert_lemma_closes(
            &WHNF_TERMINATES_WELL_TYPED_DEPENDENT,
            certify_whnf_terminates_well_typed_dependent,
            recheck_whnf_terminates_well_typed_dependent,
            "whnf_terminates_well_typed_dependent",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_terminates_well_typed_dependent_negative_control_rejected() {
        assert_negative_control_rejected(&WHNF_TERMINATES_WELL_TYPED_DEPENDENT);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_terminates_well_typed_dependent_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &WHNF_TERMINATES_WELL_TYPED_DEPENDENT,
            recheck_whnf_terminates_well_typed_dependent,
        );
    }

    /// Soundness of the modeled six-shape bootstrap relation mints and re-checks;
    /// this test deliberately does not represent it as literal-Rust grounding.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn bootstrap_infer_sound_checker_core_closes() {
        assert_lemma_closes(
            &BOOTSTRAP_INFER_SOUND,
            certify_bootstrap_infer_sound,
            recheck_bootstrap_infer_sound,
            "bootstrap_infer_sound",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn bootstrap_infer_sound_negative_control_rejected() {
        assert_negative_control_rejected(&BOOTSTRAP_INFER_SOUND);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn bootstrap_infer_sound_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&BOOTSTRAP_INFER_SOUND, recheck_bootstrap_infer_sound);
    }

    /// Reflexivity of the modeled def-eq acceptance relation mints and re-checks.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_is_def_eq_reflexive_checker_core_closes() {
        assert_lemma_closes(
            &TC_IS_DEF_EQ_REFLEXIVE,
            certify_tc_is_def_eq_reflexive,
            recheck_tc_is_def_eq_reflexive,
            "tc_is_def_eq_reflexive",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_is_def_eq_reflexive_negative_control_rejected() {
        assert_negative_control_rejected(&TC_IS_DEF_EQ_REFLEXIVE);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_is_def_eq_reflexive_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&TC_IS_DEF_EQ_REFLEXIVE, recheck_tc_is_def_eq_reflexive);
    }

    /// Symmetry of the modeled def-eq acceptance relation mints and re-checks.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_is_def_eq_symmetric_checker_core_closes() {
        assert_lemma_closes(
            &TC_IS_DEF_EQ_SYMMETRIC,
            certify_tc_is_def_eq_symmetric,
            recheck_tc_is_def_eq_symmetric,
            "tc_is_def_eq_symmetric",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_is_def_eq_symmetric_negative_control_rejected() {
        assert_negative_control_rejected(&TC_IS_DEF_EQ_SYMMETRIC);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_is_def_eq_symmetric_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&TC_IS_DEF_EQ_SYMMETRIC, recheck_tc_is_def_eq_symmetric);
    }

    /// Idempotence of the modeled WHNF acceptance trace mints and re-checks.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_whnf_idempotent_checker_core_closes() {
        assert_lemma_closes(
            &TC_WHNF_IDEMPOTENT,
            certify_tc_whnf_idempotent,
            recheck_tc_whnf_idempotent,
            "tc_whnf_idempotent",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_whnf_idempotent_negative_control_rejected() {
        assert_negative_control_rejected(&TC_WHNF_IDEMPOTENT);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_whnf_idempotent_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&TC_WHNF_IDEMPOTENT, recheck_tc_whnf_idempotent);
    }

    /// Transitivity of the model-level `is_def_eq` relation mints and re-checks
    /// under the same canonical-term/context and live-closure gates as every
    /// other checker-core authority lane.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_def_eq_transitivity_checker_core_closes() {
        assert_lemma_closes(
            &TC_DEF_EQ_TRANSITIVITY,
            certify_tc_def_eq_transitivity,
            recheck_tc_def_eq_transitivity,
            "tc_def_eq_transitivity",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_def_eq_transitivity_negative_control_rejected() {
        assert_negative_control_rejected(&TC_DEF_EQ_TRANSITIVITY);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn tc_def_eq_transitivity_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(&TC_DEF_EQ_TRANSITIVITY, recheck_tc_def_eq_transitivity);
    }

    /// The modeled WHNF-to-DefEq bridge mints and re-checks without extending
    /// its authority to literal Rust WHNF execution.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_to_preserves_def_eq_checker_core_closes() {
        assert_lemma_closes(
            &WHNF_TO_PRESERVES_DEF_EQ,
            certify_whnf_to_preserves_def_eq,
            recheck_whnf_to_preserves_def_eq,
            "whnf_to_preserves_def_eq",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_to_preserves_def_eq_negative_control_rejected() {
        assert_negative_control_rejected(&WHNF_TO_PRESERVES_DEF_EQ);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_to_preserves_def_eq_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &WHNF_TO_PRESERVES_DEF_EQ,
            recheck_whnf_to_preserves_def_eq,
        );
    }

    /// Model-specific parallel-C-star confluence mints and re-checks while
    /// retaining the closed-context and canonical-proof authority gates.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn par_reduces_c_star_diamond_faithful_checker_core_closes() {
        assert_lemma_closes(
            &PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL,
            certify_par_reduces_c_star_diamond_faithful,
            recheck_par_reduces_c_star_diamond_faithful,
            "par_reduces_c_star_diamond_faithful",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn par_reduces_c_star_diamond_faithful_negative_control_rejected() {
        assert_negative_control_rejected(&PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn par_reduces_c_star_diamond_faithful_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &PAR_REDUCES_C_STAR_DIAMOND_FAITHFUL,
            recheck_par_reduces_c_star_diamond_faithful,
        );
    }

    /// Model-specific parallel-P-star confluence mints and re-checks with the
    /// same authority and integrity gates as the C-star twin.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn par_reduces_p_star_diamond_faithful_checker_core_closes() {
        assert_lemma_closes(
            &PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL,
            certify_par_reduces_p_star_diamond_faithful,
            recheck_par_reduces_p_star_diamond_faithful,
            "par_reduces_p_star_diamond_faithful",
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn par_reduces_p_star_diamond_faithful_negative_control_rejected() {
        assert_negative_control_rejected(&PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn par_reduces_p_star_diamond_faithful_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &PAR_REDUCES_P_STAR_DIAMOND_FAITHFUL,
            recheck_par_reduces_p_star_diamond_faithful,
        );
    }

    /// `beta_deterministic`: any two β-reducts of the same term are def-eq. clean-verify
    /// `DerivedProved`, EMPTY axiom_deps; re-checked here through clean's own kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn beta_deterministic_checker_core_closes() {
        assert_lemma_closes(
            &BETA_DETERMINISTIC,
            certify_beta_deterministic,
            recheck_beta_deterministic,
            "beta_deterministic",
        );
    }

    /// NO MASQUERADE (beta determinism): the negative control returns `h1 : beta_reduces
    /// e r1`, whose type is NOT the goal `DefEq r1 r2`; the kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn beta_deterministic_negative_control_rejected() {
        assert_negative_control_rejected(&BETA_DETERMINISTIC);
    }

    /// `delta_step_deterministic`: the `delta_reduct` partial function is deterministic
    /// (same input → same output). clean-verify `DerivedProved`, EMPTY axiom_deps;
    /// re-checked here through clean's own kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn delta_step_deterministic_checker_core_closes() {
        assert_lemma_closes(
            &DELTA_STEP_DETERMINISTIC,
            certify_delta_step_deterministic,
            recheck_delta_step_deterministic,
            "delta_step_deterministic",
        );
    }

    /// NO MASQUERADE (delta determinism): the negative control returns the first equality
    /// hypothesis `h1 : Eq (OptionType KExpr) (delta_reduct env e) (some e1)`, whose type
    /// is NOT the goal `Eq KExpr e1 e2`; the kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn delta_step_deterministic_negative_control_rejected() {
        assert_negative_control_rejected(&DELTA_STEP_DETERMINISTIC);
    }

    /// `iota_step_deterministic`: the `iota_reduct` partial function is deterministic.
    /// clean-verify `DerivedProved`, EMPTY axiom_deps; re-checked through clean's kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn iota_step_deterministic_checker_core_closes() {
        assert_lemma_closes(
            &IOTA_STEP_DETERMINISTIC,
            certify_iota_step_deterministic,
            recheck_iota_step_deterministic,
            "iota_step_deterministic",
        );
    }

    /// NO MASQUERADE (iota determinism): the negative control returns the first equality
    /// hypothesis over `iota_reduct`, whose type is NOT the goal `Eq KExpr e1 e2`; the
    /// kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn iota_step_deterministic_negative_control_rejected() {
        assert_negative_control_rejected(&IOTA_STEP_DETERMINISTIC);
    }

    /// `unique_normal_forms_c_faithful` (UNIQUENESS OF NORMAL FORMS — the confluence
    /// payoff): two par_reduces_c-normal forms reachable from a common source are EQUAL,
    /// unconditionally over the real faithful_red_env. clean-verify `DerivedProved`,
    /// EMPTY axiom_deps; re-checked here through clean's own kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn unique_normal_forms_c_faithful_checker_core_closes() {
        assert_lemma_closes(
            &UNIQUE_NORMAL_FORMS_C_FAITHFUL,
            certify_unique_normal_forms_c_faithful,
            recheck_unique_normal_forms_c_faithful,
            "unique_normal_forms_c_faithful",
        );
    }

    /// NO MASQUERADE (normal-form uniqueness): the negative control returns the first
    /// reduction hypothesis `h1 : par_reduces_c_star ... e n1`, whose type is NOT the
    /// goal `Eq KExpr n1 n2` (a reduction is not an equality proof — uniqueness genuinely
    /// needs the confluence argument); the kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn unique_normal_forms_c_faithful_negative_control_rejected() {
        assert_negative_control_rejected(&UNIQUE_NORMAL_FORMS_C_FAITHFUL);
    }

    /// `whnf_progress_bd` (the whnf REDUCER-PROGRESS universal): every const-free
    /// bvar-free KExpr exposes a whnf exit (`done | stuck`). clean-verify `DerivedProved`,
    /// EMPTY axiom_deps; re-checked here through clean's own kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_progress_bd_checker_core_closes() {
        assert_lemma_closes(
            &WHNF_PROGRESS_BD,
            certify_whnf_progress_bd,
            recheck_whnf_progress_bd,
            "whnf_progress_bd",
        );
    }

    /// NO MASQUERADE (whnf progress): the negative control returns `hcf : const_free e`,
    /// whose type is NOT the goal `whnf_progress_result e`; the kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_progress_bd_negative_control_rejected() {
        assert_negative_control_rejected(&WHNF_PROGRESS_BD);
    }

    /// `whnf_normalizes_bd` (the whnf REDUCER-NORMALIZES universal): every well-typed
    /// const-free KExpr whnf-normalizes to a result — the model-level ∀e is_whnf(whnf e).
    /// clean-verify `DerivedProved`, EMPTY axiom_deps; re-checked through clean's kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_normalizes_bd_checker_core_closes() {
        assert_lemma_closes(
            &WHNF_NORMALIZES_BD,
            certify_whnf_normalizes_bd,
            recheck_whnf_normalizes_bd,
            "whnf_normalizes_bd",
        );
    }

    /// NO MASQUERADE (whnf normalizes): the negative control returns `hcf : const_free e`,
    /// whose type is NOT the goal `whnf_normalizes_result e`; the kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_normalizes_bd_negative_control_rejected() {
        assert_negative_control_rejected(&WHNF_NORMALIZES_BD);
    }

    /// `step_fixpoint_classifies_bd` (the COMPOSITION GLUE): no `beta_reduces_bd`
    /// reduct ⟹ done-or-stuck (`whnf_noredex_class`). The kernel-checked model-side
    /// implication tying the literal fixpoint-exit witness to WHNF-ness — re-checked
    /// here through clean's own kernel.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn step_fixpoint_classifies_bd_checker_core_closes() {
        assert_lemma_closes(
            &STEP_FIXPOINT_CLASSIFIES_BD,
            certify_step_fixpoint_classifies_bd,
            recheck_step_fixpoint_classifies_bd,
            "step_fixpoint_classifies_bd",
        );
    }

    /// NO MASQUERADE (composition glue): the negative control returns
    /// `hc : const_free e`, whose type is NOT the goal `whnf_noredex_class e`
    /// (distinct inductives — the classification genuinely needs the progress
    /// elimination); the kernel REJECTS it.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn step_fixpoint_classifies_bd_negative_control_rejected() {
        assert_negative_control_rejected(&STEP_FIXPOINT_CLASSIFIES_BD);
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn step_fixpoint_classifies_bd_relineaged_sorry_rejected() {
        assert_relineaged_sorry_rejected(
            &STEP_FIXPOINT_CLASSIFIES_BD,
            recheck_step_fixpoint_classifies_bd,
        );
    }
}
