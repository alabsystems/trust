// trust-certify: datatype (dis)equality no-confusion reconstruction lane
// (Brick 3 · Lever A · STEP 4 — the Certified-tier reconstruction machinery).
//
// The QF_LIA lane (`lib.rs`) re-checks a solver UNSAT of a linear-integer
// contradiction as a kernel proof that a reconstructed term inhabits `False`.
// This lane is its sibling for a DATATYPE contradiction: a FALSE equality
// between two DISTINCT constructors (no-confusion). Over the toy datatype
//
//   inductive Level : Type where
//     | zero : Level
//     | succ (pred : Level) : Level
//
// the equation `succ l = zero` is FALSE (the constructors differ), and this
// lane reconstructs it into a Clean-kernel-CHECKED term inhabiting
//
//   ∀ (l : Level), Eq Level (Level.succ l) Level.zero → False
//
// exactly as the QF_LIA lane reconstructs an arithmetic UNSAT into `… → False`.
//
// TWO INDEPENDENT WITNESSES (defense in depth, mirroring the QF_LIA lane):
//   1. ay (OUTSIDE the TCB) is driven on the DECLARED `Level` datatype and must
//      INDEPENDENTLY refute `(= (succ l) zero)` with a real `unsat` (ay's native
//      datatypes theory: distinct constructors are unequal). A `sat`/`unknown`
//      fails the lane closed.
//   2. the clean CIC kernel (`TypeChecker::check_type`, infer_only = false — the
//      ONLY trusted component, the same TCB as every other lane) re-checks a
//      hand-built no-confusion proof TERM against the goal above. The proof
//      SEARCH (which recursor, which minors) is outside the TCB; the kernel
//      independently re-checks the resulting term.
//
// THE NO-CONFUSION PROOF TERM (the datatype analogue of `certify_violation`'s
// Farkas term, using the datatype's own `casesOn` + `Eq.rec`):
//
//   fun (l : Level) (h : Eq Level (succ l) zero) =>
//     @Eq.rec.{0,1} Level (succ l)
//       (motive := fun (x : Level) (_ : Eq Level (succ l) x) =>
//                    @Level.casesOn.{1} (fun _ : Level => Prop) x
//                      False                    -- diagonal at `zero`
//                      (fun _ : Level => True)) -- diagonal at every `succ _`
//       True.intro                              -- minor : motive (succ l) rfl ≡ True
//       zero                                    -- b
//       h
//
// The diagonal `D x := Level.casesOn x False (fun _ => True)` computes
// `D (succ _) ≡ True` and `D zero ≡ False`. `True.intro` inhabits the minor
// slot (`motive (succ l) rfl ≡ D (succ l) ≡ True`); `Eq.rec` transports it along
// `h : succ l = zero` to `motive zero h ≡ D zero ≡ False`. The kernel's iota
// reduction of `Level.casesOn` on the concrete constructors is what makes this
// type-check — no `sorry`, no axiom, a genuine kernel no-confusion proof.
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `proof : goal`;
//   * the goal is BUILT by this lane (`no_confusion_goal`), not reverse-
//     engineered from solver output;
//   * ay must independently return `unsat` for the datatype equation;
//   * the environment is `init_eq` + `init_true_false` + the `Level` inductive
//     (no smuggled axioms); the closed context (empty `LocalContext`) admits no
//     hypotheses;
//   * the NEGATIVE control (a TRUE reflexive equality `succ l = succ l`) is
//     rejected on THREE independent counts: ay returns `sat` (not `unsat`), the
//     lane has no honest `→ False` proof for it, and the analogous term the
//     kernel accepts has type `… → True` and is REJECTED against `… → False`
//     (`True` is not def-eq to `False`) — so no masquerade can ride this lane;
//   * the term + empty context + obligation label are bound into a lineage
//     digest and re-checked on the DESERIALIZED payload (a tampered term / a
//     swapped lineage fails closed).
//
// HONEST SCOPE — STEP-4 INFRASTRUCTURE, NOT GROUNDING (World B). This lane is
// tested over a HAND-CONSTRUCTED datatype (dis)equality. It does NOT extract a
// datatype (dis)equality from real Rust MIR — that is step 2
// (`trust-mir-extract`), which is rustc-fork-blocked in this environment. So
// this lane does NOT ground `kernel_infer_type` and drains NO fidelity axiom:
// the axiom census stays 16. Its VALUE is that it BUILDS and kernel-verifies the
// exact reconstruction machinery the real grounding (once step 2 is unblocked)
// will feed its extracted datatype VCs into — the Certified-tier no-confusion
// reconstruction, proven correct here on the canonical `succ ≠ zero` case.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{
    AyLogic, AyProofBackend, AyProofResult, deserialize_term, serialize_term,
};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Environment, Expr, InductiveDecl, InductiveType, Level, LocalContext,
    TypeChecker,
};
use sha2::{Digest, Sha256};

/// Lineage domain tag for the datatype no-confusion `CleanCic` digest. Distinct
/// from the QF_LIA / finite-sim / inductive-func lanes so certificates never
/// alias across lanes.
const NOCONF_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.datatype-noconf.v1";

/// The SMT-LIB declaration of the toy `Level` datatype fed to the ay backend —
/// the same `(declare-datatype …)` shape the trusted SMT-text path emits
/// (`inductive_to_dt::declaration_smtlib`).
const LEVEL_DT_DECL: &str = "(declare-datatype Level ((zero) (succ (pred Level))))";

/// A datatype (dis)equality obligation this lane can be asked to certify.
///
/// Only `SuccNeZero` is a genuine no-confusion contradiction; `SuccEqSucc` is the
/// NEGATIVE control — a TRUE reflexive equality that the lane MUST fail closed on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatatypeDiseq {
    /// `succ l = zero` — distinct constructors, refutable by no-confusion.
    SuccNeZero,
    /// `succ l = succ l` — a TRUE (reflexive) equality. ay returns `sat` and no
    /// honest `→ False` proof exists, so the lane must reject it (fail-closed).
    SuccEqSucc,
}

impl DatatypeDiseq {
    /// The SMT-LIB assertion body (asserted to ay over the declared `Level`).
    fn ay_assertion(self) -> &'static str {
        match self {
            DatatypeDiseq::SuccNeZero => "(= (succ l) zero)",
            DatatypeDiseq::SuccEqSucc => "(= (succ l) (succ l))",
        }
    }

    /// Stable label bound into the lineage digest so a certificate for one
    /// obligation cannot be replayed against another.
    fn label(self) -> &'static str {
        match self {
            DatatypeDiseq::SuccNeZero => {
                "Level.noConfusion:forall l, Eq Level (succ l) zero -> False"
            }
            DatatypeDiseq::SuccEqSucc => "Level.reflexive-negative-control:succ l = succ l",
        }
    }

    /// The (goal, no-confusion proof) pair for the obligation, or `None`
    /// (fail-closed) when the shape has no honest kernel no-confusion proof —
    /// only `SuccNeZero` (distinct constructors) is reconstructible.
    fn goal_and_proof(self) -> Option<(Expr, Expr)> {
        match self {
            DatatypeDiseq::SuccNeZero => Some((no_confusion_goal(), no_confusion_proof())),
            DatatypeDiseq::SuccEqSucc => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Kernel-term construction helpers (raw CIC `Expr`, de Bruijn indices).
// ---------------------------------------------------------------------------

fn level_ty() -> Expr {
    Expr::const_(Name::from_string("Level"), Vec::new())
}
fn level_zero() -> Expr {
    Expr::const_(Name::from_string("Level.zero"), Vec::new())
}
fn level_succ(x: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Level.succ"), Vec::new()), x)
}
fn false_prop() -> Expr {
    Expr::const_(Name::from_string("False"), Vec::new())
}
fn true_prop() -> Expr {
    Expr::const_(Name::from_string("True"), Vec::new())
}
fn true_intro() -> Expr {
    Expr::const_(Name::from_string("True.intro"), Vec::new())
}

/// Universe level of `Level`: `Level : Type 0 = Sort 1`, so `Eq`/`Eq.rec` over
/// `Level` take `u = 1`.
fn level1() -> Level {
    Level::succ(Level::zero())
}

/// `Eq.{1} Level a b` (`Level`-valued propositional equality, a `Prop`).
fn eq_level(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [level_ty(), a, b])
}

/// The toy `Level = zero | succ (pred : Level)` inductive (mirrors `Nat`).
#[must_use]
pub fn level_inductive() -> InductiveDecl {
    let level = Name::from_string("Level");
    let level_ref = Expr::const_(level.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: level,
            type_: Expr::type_(), // Sort 1
            constructors: vec![
                Constructor { name: Name::from_string("Level.zero"), type_: level_ref.clone() },
                Constructor {
                    name: Name::from_string("Level.succ"),
                    // Level.succ : Level → Level
                    type_: Expr::pi(BinderInfo::Default, level_ref.clone(), level_ref),
                },
            ],
        }],
    }
}

/// The `Eq.rec` motive
/// `λ (x : Level) (heq : Eq Level (succ l) x) =>
///    @Level.casesOn.{1} (λ _:Level => Prop) x False (λ _:Level => True)`.
///
/// `l_idx` is the de Bruijn index of the OUTER `l` binder at the point where the
/// motive is placed (as an argument to `Eq.rec`, under `λ l λ h` ⇒ `l_idx = 1`).
/// The motive body ignores both `x` (via the constant diagonal per constructor)
/// and `heq`; only the `heq` binder TYPE mentions `l`.
fn no_confusion_motive(l_idx: u32) -> Expr {
    // `heq` binder type is evaluated at stack [.., l, .., x] (heq not yet bound):
    // `l` is one deeper than at the motive placement (under `λ x`), `x` = #0.
    let heq_ty = eq_level(level_succ(Expr::bvar(l_idx + 1)), Expr::bvar(0));
    // Diagonal: `D x := Level.casesOn.{1} (λ _ => Prop) x False (λ _ => True)`.
    // Under [.., x, heq] the major `x` = #1.
    let motive_d = Expr::lam(BinderInfo::Default, level_ty(), Expr::prop());
    let succ_minor = Expr::lam(BinderInfo::Default, level_ty(), true_prop());
    let diagonal = Expr::apps(
        Expr::const_(Name::from_string("Level.casesOn"), vec![level1()]),
        [motive_d, Expr::bvar(1), false_prop(), succ_minor],
    );
    Expr::lam(BinderInfo::Default, level_ty(), Expr::lam(BinderInfo::Default, heq_ty, diagonal))
}

/// The obligation statement: `∀ (l : Level), Eq Level (succ l) zero → False`.
#[must_use]
pub fn no_confusion_goal() -> Expr {
    // Under `λ l` (l = #0), `Eq Level (succ l) zero`; body `False` is a const.
    let hyp_ty = eq_level(level_succ(Expr::bvar(0)), level_zero());
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, hyp_ty, false_prop()))
}

/// The GENUINE no-confusion proof term (see the module header). `Eq.rec.{0,1}`:
/// `v = 0` (motive lands in `Prop = Sort 0`), `u = 1` (`Level : Sort 1`); level
/// params are `[v, u]`.
#[must_use]
pub fn no_confusion_proof() -> Expr {
    // Under `λ l λ h`: l = #1, h = #0.
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Eq.rec"), vec![Level::zero(), level1()]),
        [
            level_ty(),                // {α} = Level
            level_succ(Expr::bvar(1)), // {a} = succ l
            no_confusion_motive(1),    // {motive}
            true_intro(),              // (minor : motive (succ l) rfl ≡ True)
            level_zero(),              // {b} = zero
            Expr::bvar(0),             // (h : Eq Level (succ l) zero)
        ],
    );
    // `λ h : Eq Level (succ l) zero` — under `λ l`, l = #0.
    let hyp_ty = eq_level(level_succ(Expr::bvar(0)), level_zero());
    Expr::lam(
        BinderInfo::Default,
        level_ty(),                                      // λ l
        Expr::lam(BinderInfo::Default, hyp_ty, rec_app), // λ h
    )
}

// --- Negative-control terms (a TRUE reflexive equality) --------------------

/// NEGATIVE-control goal `∀ l, Eq Level (succ l) (succ l) → True`. The analogous
/// `Eq.rec` term inhabits THIS (the diagonal at `succ l` computes `True`),
/// proving the kernel reduction genuinely fires — so the `→ False` rejection
/// below is meaningful (a `True`/`False` clash), not a vacuous malformation.
#[must_use]
pub fn succ_eq_succ_true_goal() -> Expr {
    let hyp_ty = eq_level(level_succ(Expr::bvar(0)), level_succ(Expr::bvar(0)));
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, hyp_ty, true_prop()))
}

/// NEGATIVE-control goal `∀ l, Eq Level (succ l) (succ l) → False` — a FALSE
/// statement. The lane must NEVER produce a term the kernel accepts here.
#[must_use]
pub fn succ_eq_succ_false_goal() -> Expr {
    let hyp_ty = eq_level(level_succ(Expr::bvar(0)), level_succ(Expr::bvar(0)));
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, hyp_ty, false_prop()))
}

/// The `Eq.rec` term for the reflexive shape `succ l = succ l` (`b = succ l`).
/// Its natural type is `∀ l, Eq Level (succ l) (succ l) → True` (the diagonal at
/// `succ l` is `True`). Used by the negative control: the kernel ACCEPTS it
/// against [`succ_eq_succ_true_goal`] but REJECTS it against
/// [`succ_eq_succ_false_goal`], so it cannot masquerade as a proof of `False`.
#[must_use]
pub fn succ_eq_succ_pseudo_proof() -> Expr {
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Eq.rec"), vec![Level::zero(), level1()]),
        [
            level_ty(),
            level_succ(Expr::bvar(1)), // {a} = succ l
            no_confusion_motive(1),
            true_intro(),
            level_succ(Expr::bvar(1)), // {b} = succ l  (was zero)
            Expr::bvar(0),             // (h : Eq Level (succ l) (succ l))
        ],
    );
    let hyp_ty = eq_level(level_succ(Expr::bvar(0)), level_succ(Expr::bvar(0)));
    Expr::lam(BinderInfo::Default, level_ty(), Expr::lam(BinderInfo::Default, hyp_ty, rec_app))
}

// ---------------------------------------------------------------------------
// ay driver + kernel check.
// ---------------------------------------------------------------------------

/// Drive the in-process ay solver on the declared `Level` datatype with the
/// obligation's assertion; return `true` iff ay returns a real `unsat`. ay is
/// OUTSIDE the TCB (a `sat`/`unknown` simply fails the lane closed).
#[must_use]
pub fn ay_refutes(obl: DatatypeDiseq) -> bool {
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::All);
    backend.add_raw_declaration(LEVEL_DT_DECL);
    backend.add_raw_declaration("(declare-const l Level)");
    backend.assert_formula(obl.ay_assertion());
    matches!(backend.check_sat(), Ok(AyProofResult::Unsat { .. }))
}

/// Build the kernel environment: `Eq` (+ `Eq.rec`), `True`/`True.intro`/`False`,
/// and the toy `Level` inductive (so `Level.casesOn` is generated). No smuggled
/// axioms. `None` (fail-closed) on any registration failure.
fn build_level_env() -> Option<Environment> {
    let mut env = Environment::default();
    env.init_eq().ok()?;
    env.init_true_false().ok()?;
    env.add_inductive(level_inductive()).ok()?;
    Some(env)
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// closed context.
fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

/// SHA-256 lineage digest binding the term, the empty closed context, and the
/// obligation label. Position-tagged + length-prefixed ⇒ injective.
fn noconf_lineage_digest(
    term_bytes: &[u8],
    context_bytes: &[u8],
    label: &str,
) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(NOCONF_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), label.as_bytes()),
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

/// Mint a kernel-CHECKED `CleanCic` certificate that a FALSE datatype equality
/// reconstructs to a Clean-kernel proof of `… → False` (the Certified tier).
///
/// Fail-closed on every count: ay must return `unsat`; the obligation must be a
/// supported no-confusion shape; the clean kernel must accept the proof term;
/// the serialized payload must re-check after a round-trip. Returns `None`
/// otherwise (the caller records `Trusted`, never a false `Certified`).
#[must_use]
pub fn certify_datatype_disequality(obl: DatatypeDiseq) -> Option<trust_ir::ProofEvidence> {
    // Gate 1 (defense in depth): ay must INDEPENDENTLY refute the equation. The
    // reflexive negative control (`succ l = succ l`) is `sat` here ⇒ fail closed.
    if !ay_refutes(obl) {
        return None;
    }

    // Gate 2 (fail-closed on unsupported shape): only distinct-constructor
    // no-confusion has an honest kernel proof.
    let (goal, proof) = obl.goal_and_proof()?;

    // Gate 3: the clean kernel independently type-checks the no-confusion term.
    let env = build_level_env()?;
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }

    // Serialize term + empty closed context, then independently re-check the
    // DESERIALIZED payload (consumer-side gate).
    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = noconf_lineage_digest(&term_bytes, &context_bytes, obl.label());
    if !recheck_datatype_disequality(obl, &term_bytes, &context_bytes, &lineage) {
        return None;
    }

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check of a datatype no-confusion `CleanCic` certificate:
/// independently rebuild env + goal, deserialize the term, re-run the clean-
/// kernel `check_type`, and re-bind the lineage digest. `true` ONLY if the
/// kernel accepts the deserialized term AND the lineage matches — a tampered
/// term or a swapped lineage fails closed.
#[must_use]
pub fn recheck_datatype_disequality(
    obl: DatatypeDiseq,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let Some((goal, canonical_proof)) = obl.goal_and_proof() else {
        return false;
    };
    if !crate::is_canonical_empty_context(context_bytes)
        || !crate::is_canonical_term(term_bytes, &canonical_proof)
    {
        return false;
    }
    let Some(env) = build_level_env() else {
        return false;
    };
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &goal) {
        return false;
    }
    &noconf_lineage_digest(term_bytes, context_bytes, obl.label()) == lineage
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::ProofEvidence;

    // ── (a)(b)(c): the no-confusion reconstruction closes ────────────────────

    /// THE MILESTONE: a FALSE datatype equality (`succ l = zero`, distinct
    /// constructors) is (b) refuted by ay AND (c) reconstructed into a
    /// clean-kernel-CHECKED `… → False` no-confusion proof, then minted as a
    /// `CleanCic` certificate whose payload re-checks.
    #[test]
    fn datatype_no_confusion_closes() {
        // (b) ay independently refutes `succ l = zero` (real unsat).
        assert!(
            ay_refutes(DatatypeDiseq::SuccNeZero),
            "ay must refute `(= (succ l) zero)` over the declared Level datatype"
        );
        // (c) direct clean-kernel check: the no-confusion term inhabits the goal.
        let env = build_level_env().expect("init eq + true/false + Level");
        assert!(
            kernel_checks_goal(&env, &no_confusion_proof(), &no_confusion_goal()),
            "clean kernel must accept the Eq.rec/casesOn no-confusion proof of \
             `forall l, succ l = zero -> False`"
        );
        // Full mint (ay gate + kernel check + serialize + round-trip + lineage).
        let evidence = certify_datatype_disequality(DatatypeDiseq::SuccNeZero)
            .expect("succ != zero must certify to a CleanCic term");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
        assert!(
            recheck_datatype_disequality(DatatypeDiseq::SuccNeZero, &term, &context, &lineage),
            "serialized no-confusion CleanCic payload must re-check via the clean kernel"
        );
    }

    // ── (d): NEGATIVE control — a TRUE equality must NOT reconstruct to False ─

    /// ay does NOT refute a TRUE reflexive equality: `succ l = succ l` is `sat`.
    /// So the ay gate alone stops any false certificate at the door.
    #[test]
    fn true_equality_not_refuted_by_ay() {
        assert!(
            !ay_refutes(DatatypeDiseq::SuccEqSucc),
            "ay must NOT refute the true equality `(= (succ l) (succ l))` (it is sat)"
        );
    }

    /// The lane fails closed on the TRUE-equality obligation: no `Certified`.
    #[test]
    fn lane_rejects_true_equality() {
        assert!(
            certify_datatype_disequality(DatatypeDiseq::SuccEqSucc).is_none(),
            "the reflexive negative control must never mint a CleanCic certificate"
        );
    }

    /// NO MASQUERADE: the `Eq.rec` term for `succ l = succ l` genuinely inhabits
    /// `… → True` (the kernel's iota reduction of `Level.casesOn` at `succ l`
    /// fires), but the kernel REJECTS it against `… → False`. So even a
    /// hand-crafted term cannot masquerade as a proof of `False`.
    #[test]
    fn true_equality_kernel_rejects_false() {
        let env = build_level_env().expect("init env");
        // The kernel reduction is real: the term inhabits `… → True`.
        assert!(
            kernel_checks_goal(&env, &succ_eq_succ_pseudo_proof(), &succ_eq_succ_true_goal()),
            "the reflexive Eq.rec term must inhabit `forall l, succ l = succ l -> True`"
        );
        // ... and therefore CANNOT inhabit `… → False` (True is not def-eq False).
        assert!(
            !kernel_checks_goal(&env, &succ_eq_succ_pseudo_proof(), &succ_eq_succ_false_goal()),
            "the reflexive Eq.rec term must be REJECTED against `... -> False` (no masquerade)"
        );
    }

    // ── (e): fail-closed on an unsupported shape ─────────────────────────────

    /// An obligation with no honest no-confusion proof yields no goal/proof pair
    /// (fail-closed), so the lane cannot mint anything for it.
    #[test]
    fn unsupported_shape_has_no_proof() {
        assert!(
            DatatypeDiseq::SuccEqSucc.goal_and_proof().is_none(),
            "an unsupported (non-distinct-constructor) shape must have no proof"
        );
    }

    // ── tamper / lineage fail-closed (mirrors the QF_LIA + inductive lanes) ───

    /// A tampered serialized term fails the consumer-side re-check (fail-closed).
    #[test]
    fn tampered_term_rejected() {
        let evidence = certify_datatype_disequality(DatatypeDiseq::SuccNeZero).expect("certify");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_datatype_disequality(DatatypeDiseq::SuccNeZero, &term, &context, &lineage),
            "pristine must re-check"
        );
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_datatype_disequality(DatatypeDiseq::SuccNeZero, &tampered, &context, &lineage),
            "tampered no-confusion term must fail the offline kernel re-check"
        );
    }

    /// A certificate must not re-check under a swapped (zeroed) lineage digest.
    #[test]
    fn swapped_lineage_rejected() {
        let evidence = certify_datatype_disequality(DatatypeDiseq::SuccNeZero).expect("certify");
        let ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            !recheck_datatype_disequality(
                DatatypeDiseq::SuccNeZero,
                &term,
                &context,
                &trust_ir::ProofDigest::zero()
            ),
            "a zeroed lineage must fail closed"
        );
    }

    #[test]
    fn relineaged_ambient_sorry_beta_proof_and_noncanonical_context_are_rejected() {
        let obl = DatatypeDiseq::SuccNeZero;
        let (goal, canonical_proof) = obl.goal_and_proof().expect("supported obligation");
        let context = crate::canonical_empty_context_bytes().expect("canonical context");

        let mut ambient = build_level_env().expect("level env");
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let sorry_lineage = noconf_lineage_digest(&sorry_bytes, &context, obl.label());
        assert!(!recheck_datatype_disequality(obl, &sorry_bytes, &context, &sorry_lineage,));

        let beta = Expr::app(
            Expr::lam(BinderInfo::Default, goal.clone(), Expr::bvar(0)),
            canonical_proof.clone(),
        );
        let minimal = build_level_env().expect("minimal env");
        assert!(kernel_checks_goal(&minimal, &beta, &goal));
        let beta_bytes = serialize_term(&beta).expect("serialize beta proof");
        let beta_lineage = noconf_lineage_digest(&beta_bytes, &context, obl.label());
        assert!(!recheck_datatype_disequality(obl, &beta_bytes, &context, &beta_lineage,));

        let term = serialize_term(&canonical_proof).expect("serialize canonical proof");
        let mut noncanonical_context = context;
        noncanonical_context.push(0);
        let relined = noconf_lineage_digest(&term, &noncanonical_context, obl.label());
        assert!(!recheck_datatype_disequality(obl, &term, &noncanonical_context, &relined,));
    }
}
