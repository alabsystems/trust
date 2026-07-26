// trust-certify: INDUCTIVE functional-correctness re-check lane.
//
// The QF_LIA lane (`lib.rs`) re-checks a solver UNSAT as a kernel proof that a
// reconstructed term inhabits `False`. The `finite_dfa` lane certifies a
// pointwise functional EQUIVALENCE `∀ s, f s = g s` over a FINITE / def-equal
// domain, discharged by `Eq.refl` or a finite `Dom.casesOn`.
//
// This lane pushes past both: it certifies a functional-CORRECTNESS property
// whose discharge is a GENUINE STRUCTURAL INDUCTION (`Nat.rec` with an inductive
// hypothesis) over an INFINITE domain — the frontier that ay / QF_LIA and a
// finite `casesOn` provably cannot reach.
//
// The property proved is a correctness property of a REAL kernel-registered
// operation — `Nat.add` (registered by `Environment::init_nat`, and reduced by
// the kernel's whnf via `Nat.rec` iota):
//
//   zero_add : ∀ (n : Nat), Eq Nat (Nat.add Nat.zero n) n
//
// This is genuinely inductive, NOT definitional: `Nat.add` recurses on its
// SECOND argument (`Nat.add m n := Nat.rec m (fun _ ih => Nat.succ ih) n`), so
//   * `Nat.add n Nat.zero`  iota-reduces to `n`   ⇒ the RIGHT identity is `Eq.refl`;
//   * `Nat.add Nat.zero n`  is STUCK on the variable `n` ⇒ the LEFT identity
//     `Eq.refl` FAILS to type-check, and only a `Nat.rec` proof carrying the
//     inductive hypothesis `ih : Nat.add 0 k = k` closes the `succ` case (via
//     `congrArg Nat.succ ih`). The `zero_add_requires_induction` /
//     `add_zero_right_is_definitional` tests witness exactly this asymmetry.
//
// The clean CIC kernel (`TypeChecker::check_type`, infer_only = false) is the
// only trusted component — the same TCB as the QF_LIA and finite_dfa lanes.
// The inductive-proof SEARCH (which recursor, which minor premises — here banked
// from the Aristotle `inst_above_ceiling_id` family / classic `zero_add`) is
// OUTSIDE the TCB: the kernel independently re-checks the resulting term.
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `term : goal`;
//   * the goal is BUILT by this lane (`zero_add_goal`), not reverse-engineered;
//   * the environment is built ONLY from `init_nat` + `init_eq` (no smuggled
//     axioms), and the closed context (empty `LocalContext`) admits no hypotheses;
//   * the term + closed context + goal identity are bound into the lineage digest,
//     so a certificate cannot be replayed against another obligation;
//   * `recheck_zero_add` independently rebuilds env + goal and re-runs the kernel
//     check on the DESERIALIZED term — a tampered term fails closed.
//
// GROUNDING CAVEAT (stated honestly): like `finite_dfa`, this lane proves the
// property about the CIC `Nat.add` DEFINITION the kernel registers, not about a
// literal Rust function extracted from MIR. Closing the loop to a literal Rust
// kernel fn's functional postcondition additionally requires a functional-VC
// grounding path (see the frontier map in the accompanying synthesis note); that
// path does not yet exist for recursive/inductive specifications.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, Level, LocalContext, TypeChecker};
use sha2::{Digest, Sha256};

/// Lineage domain tag for the inductive functional-correctness `CleanCic`
/// digest. Distinct from the QF_LIA and finite-sim lanes so certificates never
/// alias across lanes.
const INDUCTIVE_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.inductive-func.v1";

/// Stable obligation label folded into the lineage digest.
const ZERO_ADD_LABEL: &str = "Nat.add.zero_add:forall n, Eq Nat (Nat.add Nat.zero n) n";

// ---------------------------------------------------------------------------
// Kernel-term construction helpers (raw CIC `Expr`, de Bruijn indices).
// ---------------------------------------------------------------------------

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), Vec::new())
}
fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), Vec::new())
}
fn nat_succ() -> Expr {
    Expr::const_(Name::from_string("Nat.succ"), Vec::new())
}
fn nat_add() -> Expr {
    Expr::const_(Name::from_string("Nat.add"), Vec::new())
}

/// Universe level of `Nat`: `Nat : Type 0 = Sort 1`, so `Eq`/`Eq.refl`/`congrArg`
/// over `Nat` take level `1 = succ zero`.
fn level1() -> Level {
    Level::succ(Level::zero())
}

/// `Eq.{1} Nat lhs rhs` (`Nat`-valued propositional equality, a `Prop`).
fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [nat_ty(), lhs, rhs])
}

/// `Nat.add Nat.zero x`.
fn add_zero_left(x: Expr) -> Expr {
    Expr::apps(nat_add(), [nat_zero(), x])
}

/// The obligation statement: `∀ (n : Nat), Eq Nat (Nat.add Nat.zero n) n`.
#[must_use]
pub fn zero_add_goal() -> Expr {
    Expr::pi(BinderInfo::Default, nat_ty(), eq_nat(add_zero_left(Expr::bvar(0)), Expr::bvar(0)))
}

/// The GENUINELY INDUCTIVE proof term:
///
/// ```text
/// fun (n : Nat) =>
///   @Nat.rec.{0}
///     (motive := fun (k : Nat) => Eq Nat (Nat.add Nat.zero k) k)
///     (Eq.refl Nat Nat.zero)                       -- base: Nat.add 0 0 ≡ 0
///     (fun (k : Nat) (ih : Eq Nat (Nat.add Nat.zero k) k) =>
///        @congrArg.{1,1} Nat Nat (Nat.add Nat.zero k) k Nat.succ ih)
///                                                   -- step: succ (add 0 k) ≡ add 0 (succ k)
///     n
/// ```
///
/// The `succ` minor premise CONSUMES `ih`; without it the case is unprovable
/// (`Nat.add Nat.zero k` is stuck on the free `k`). The motive is `Prop`-valued
/// ⇒ `Nat.rec.{0}`.
#[must_use]
pub fn zero_add_proof() -> Expr {
    // motive : fun (k : Nat) => Eq Nat (Nat.add Nat.zero k) k     (k = bvar 0)
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ty(),
        eq_nat(add_zero_left(Expr::bvar(0)), Expr::bvar(0)),
    );
    // base : Eq.refl.{1} Nat Nat.zero   (: Eq Nat (add 0 0) 0 by iota)
    let base = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
        [nat_ty(), nat_zero()],
    );
    // step : fun (k : Nat) (ih : Eq Nat (add 0 k) k) =>
    //          congrArg.{1,1} Nat Nat (add 0 k) k Nat.succ ih
    // Under `fun k`: k = bvar 0; the ih binder type is stated there.
    let ih_ty = eq_nat(add_zero_left(Expr::bvar(0)), Expr::bvar(0));
    // Under `fun k => fun ih`: k = bvar 1, ih = bvar 0.
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![level1(), level1()]),
        [
            nat_ty(),                     // {α}
            nat_ty(),                     // {β}
            add_zero_left(Expr::bvar(1)), // {a₁} = Nat.add 0 k
            Expr::bvar(1),                // {a₂} = k
            nat_succ(),                   // f
            Expr::bvar(0),                // h = ih
        ],
    );
    let step =
        Expr::lam(BinderInfo::Default, nat_ty(), Expr::lam(BinderInfo::Default, ih_ty, congr));
    // @Nat.rec.{0} motive base step n     (n = bvar 0 under the outer lambda)
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, base, step, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, nat_ty(), rec_app)
}

/// NEGATIVE control: `fun (n : Nat) => Eq.refl Nat (Nat.add Nat.zero n)`.
/// Its type is `∀ n, Eq Nat (Nat.add 0 n) (Nat.add 0 n)`, which is NOT the goal
/// `∀ n, Eq Nat (Nat.add 0 n) n` because `Nat.add 0 n` is not def-equal to `n`
/// (it is stuck on the free `n`). The kernel MUST reject it — this is the
/// witness that the property genuinely requires induction, not mere unfolding.
#[must_use]
pub fn refl_only_pseudo_proof() -> Expr {
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
        [nat_ty(), add_zero_left(Expr::bvar(0))],
    );
    Expr::lam(BinderInfo::Default, nat_ty(), refl)
}

/// CONTRAST obligation: `∀ (n : Nat), Eq Nat (Nat.add n Nat.zero) n` — the RIGHT
/// identity, which IS definitional (`Nat.add n 0` iota-reduces to `n`).
#[must_use]
pub fn add_zero_right_goal() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat_ty(),
        eq_nat(Expr::apps(nat_add(), [Expr::bvar(0), nat_zero()]), Expr::bvar(0)),
    )
}

/// `fun (n : Nat) => Eq.refl Nat n` — closes `add_zero_right_goal` WITHOUT
/// induction, since `Nat.add n 0 ≡ n`. Demonstrates the asymmetry.
#[must_use]
pub fn add_zero_right_refl_proof() -> Expr {
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
        [nat_ty(), Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, nat_ty(), refl)
}

// ---------------------------------------------------------------------------
// Environment + kernel check.
// ---------------------------------------------------------------------------

/// Build the environment: `Nat` (+ `Nat.rec`, `Nat.add`) and `Eq` (+ `Eq.refl`,
/// `congrArg`). No smuggled axioms. `None` if init fails.
fn build_nat_eq_env() -> Option<Environment> {
    let mut env = Environment::default();
    env.init_nat().ok()?;
    env.init_eq().ok()?;
    Some(env)
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// closed context.
fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

/// SHA-256 lineage digest binding the term, the empty closed context, and the
/// obligation label. Position-tagged + length-prefixed ⇒ injective.
fn inductive_lineage_digest(term_bytes: &[u8], context_bytes: &[u8]) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(INDUCTIVE_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), ZERO_ADD_LABEL.as_bytes()),
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

/// Mint a kernel-CHECKED `CleanCic` certificate that the banked inductive proof
/// term discharges the `zero_add` correctness obligation of the kernel's
/// `Nat.add`. Returns `None` (fail-closed) on any env-build, kernel-check,
/// serialization, or round-trip-recheck failure.
#[must_use]
pub fn certify_zero_add() -> Option<trust_ir::ProofEvidence> {
    let env = build_nat_eq_env()?;
    let goal = zero_add_goal();
    let proof = zero_add_proof();

    // 1. The clean kernel independently type-checks the inductive proof term.
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }

    // 2. Serialize term + empty closed context via the clean_auto codec, then
    //    independently re-check the DESERIALIZED payload (consumer-side gate).
    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = inductive_lineage_digest(&term_bytes, &context_bytes);
    if !recheck_zero_add(&term_bytes, &context_bytes, &lineage) {
        return None;
    }

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check of a `zero_add` `CleanCic` certificate: independently
/// rebuild the env + goal, deserialize the term, re-run the clean-kernel
/// `check_type`, and re-bind the lineage digest. Returns `true` ONLY if the
/// kernel accepts the deserialized term AND the lineage matches — so a tampered
/// term or a swapped lineage fails closed.
#[must_use]
pub fn recheck_zero_add(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !crate::is_canonical_empty_context(context_bytes)
        || !crate::is_canonical_term(term_bytes, &zero_add_proof())
    {
        return false;
    }
    let Some(env) = build_nat_eq_env() else {
        return false;
    };
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &zero_add_goal()) {
        return false;
    }
    &inductive_lineage_digest(term_bytes, context_bytes) == lineage
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::ProofEvidence;

    /// THE MILESTONE: a genuinely inductive functional-correctness property of a
    /// real kernel-registered operation (`Nat.add` left identity) is minted as a
    /// kernel-CHECKED `CleanCic` certificate.
    #[test]
    fn zero_add_inductive_correctness_closes() {
        let env = build_nat_eq_env().expect("init nat+eq");
        // Direct kernel check: the inductive proof term inhabits the goal.
        assert!(
            kernel_checks_goal(&env, &zero_add_proof(), &zero_add_goal()),
            "clean kernel must accept the Nat.rec inductive proof of `forall n, 0 + n = n`"
        );
        // Full mint (kernel check + serialize + round-trip recheck + lineage).
        let evidence = certify_zero_add().expect("zero_add must certify to a CleanCic term");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
        assert!(
            recheck_zero_add(&term, &context, &lineage),
            "serialized inductive CleanCic payload must re-check via the clean kernel"
        );
    }

    /// The property genuinely REQUIRES induction: the `Eq.refl`-only pseudo-proof
    /// (which would suffice if `Nat.add 0 n` reduced to `n`) is REJECTED by the
    /// kernel. This is the witness that ay / QF_LIA / a finite `casesOn` cannot
    /// discharge this obligation.
    #[test]
    fn zero_add_requires_induction() {
        let env = build_nat_eq_env().expect("init nat+eq");
        assert!(
            !kernel_checks_goal(&env, &refl_only_pseudo_proof(), &zero_add_goal()),
            "Eq.refl alone must NOT type-check the LEFT identity (Nat.add 0 n is stuck)"
        );
    }

    /// Contrast: the RIGHT identity IS definitional — `Nat.add n 0` iota-reduces
    /// to `n`, so `Eq.refl` closes it WITHOUT induction. Confirms the asymmetry
    /// (and that the kernel's reduction is doing real work), so the left-identity
    /// test above is a genuine induction obligation and not a kernel artifact.
    #[test]
    fn add_zero_right_is_definitional() {
        let env = build_nat_eq_env().expect("init nat+eq");
        assert!(
            kernel_checks_goal(&env, &add_zero_right_refl_proof(), &add_zero_right_goal()),
            "Eq.refl must close the RIGHT identity `forall n, n + 0 = n` (definitional)"
        );
    }

    /// A tampered serialized term fails the consumer-side re-check (fail-closed).
    #[test]
    fn tampered_inductive_term_rejected() {
        let evidence = certify_zero_add().expect("certify");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_zero_add(&term, &context, &lineage), "pristine must re-check");
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_zero_add(&tampered, &context, &lineage),
            "tampered inductive term must fail the offline kernel re-check"
        );
    }

    /// A certificate minted for this obligation must not re-check under a swapped
    /// (zeroed) lineage digest.
    #[test]
    fn swapped_lineage_rejected() {
        let evidence = certify_zero_add().expect("certify");
        let ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            !recheck_zero_add(&term, &context, &trust_ir::ProofDigest::zero()),
            "a zeroed lineage must fail closed"
        );
    }

    #[test]
    fn relineaged_ambient_sorry_beta_proof_and_noncanonical_context_are_rejected() {
        let goal = zero_add_goal();
        let canonical_proof = zero_add_proof();
        let context = crate::canonical_empty_context_bytes().expect("canonical context");

        let mut ambient = build_nat_eq_env().expect("nat/eq env");
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let sorry_lineage = inductive_lineage_digest(&sorry_bytes, &context);
        assert!(!recheck_zero_add(&sorry_bytes, &context, &sorry_lineage));

        let beta = Expr::app(
            Expr::lam(BinderInfo::Default, goal.clone(), Expr::bvar(0)),
            canonical_proof.clone(),
        );
        let minimal = build_nat_eq_env().expect("minimal env");
        assert!(kernel_checks_goal(&minimal, &beta, &goal));
        let beta_bytes = serialize_term(&beta).expect("serialize beta proof");
        let beta_lineage = inductive_lineage_digest(&beta_bytes, &context);
        assert!(!recheck_zero_add(&beta_bytes, &context, &beta_lineage));

        let term = serialize_term(&canonical_proof).expect("serialize canonical proof");
        let mut noncanonical_context = context;
        noncanonical_context.push(0);
        let relined = inductive_lineage_digest(&term, &noncanonical_context);
        assert!(!recheck_zero_add(&term, &noncanonical_context, &relined));
    }
}
