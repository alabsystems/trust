// trust-certify: datatype FUNCTIONAL (positive-equation) reconstruction lane
// (Brick 3 · Lever A · STEPS 3+4 integration — the Certified-tier discharge of
// the emitted sort-arm functional VC).
//
// The sibling lane `datatype_no_confusion` discharges a datatype DIS-equality (a
// FALSE equation between distinct constructors) by no-confusion. THIS lane is its
// POSITIVE counterpart: it discharges a datatype EQUATION that is TRUE by
// construction — the functional postcondition of a datatype-building function,
// relating the function's OUTPUT to the constructor tree its body builds.
//
// The obligation is the step-3 (`trust-vcgen/datatype_functional.rs`) emitted VC
// for the real kernel sort arm
//   `ExprKind::Sort(l) => Ok(Expr::from_kind(ExprKind::Sort(Level::succ(l))))`
// whose real MIR extraction to `Rvalue::Aggregate(Adt{Sort},[l])` is confirmed by
// step 3's `real_mir_sort_arm_body_is_datatype_aggregate` test. Step 3 emits the
// datatype-`Formula` equation
//   `Forall [l, meta] Eq(_0, Ctor("Expr",[Ctor("Sort",[Ctor("Succ",[l])]), meta]))`
// ([`sort_arm_functional_vc_formula`] reconstructs the exact shape). This is a
// POSITIVE functional equation (return = ctor tree), TRUE by construction, whose
// kernel discharge is by REFLEXIVITY on the datatype model — NOT no-confusion.
//
// THE DISCHARGE (kernel reflexivity over the extracted datatype MODEL):
//   1. register the minimal datatype slice the equation touches in the clean
//      kernel env via `add_inductive` (exactly as `datatype_no_confusion`
//      registers `Level`):
//        inductive Meta     : Type where | mk
//        inductive Level    : Type where | zero | succ (pred : Level)
//        inductive ExprKind : Type where | Sort (l : Level)
//        inductive Expr     : Type where | mk (kind : ExprKind) (meta : Meta)
//   2. register the extracted body as a kernel `Declaration::Definition` (the
//      datatype term the MIR builds):
//        infer_sort_arm_model : Level -> Meta -> Expr
//          := fun (l : Level) (meta : Meta) =>
//                Expr.mk (ExprKind.Sort (Level.succ l)) meta
//      (registering it makes the kernel type-check the model against its type).
//   3. build the proof term of the functional postcondition
//        forall (l : Level) (meta : Meta),
//          Eq Expr (infer_sort_arm_model l meta)
//                  (Expr.mk (ExprKind.Sort (Level.succ l)) meta)
//      as `fun l meta => @Eq.refl.{1} Expr (Expr.mk (ExprKind.Sort (Level.succ l)) meta)`.
//      Its natural type is `Eq Expr RHS RHS`; the kernel accepts it against the
//      goal `Eq Expr (model l meta) RHS` because `model l meta` delta-unfolds +
//      beta-reduces to `RHS`. The clean CIC kernel (`TypeChecker::check_type`,
//      infer_only = false — the ONLY trusted component) is what makes this the
//      Certified-tier discharge; the reduction is genuine (real `add_inductive` +
//      real `Declaration::Definition`, no `sorry`, no axiom).
//
// NO MASQUERADE (negative control, fail-closed):
//   * the WRONG postcondition `= Expr.mk (ExprKind.Sort l) meta` (missing the
//     `succ`) is REJECTED by the kernel: the correct refl term proves
//     `Eq Expr RHS RHS`, but `RHS = Sort(succ l)` is NOT def-eq to the wrong
//     `Sort l` (the datatype `succ l` differs from `l`), so no refl proof of the
//     wrong goal type-checks;
//   * the rejection is NON-VACUOUS: the reflexive-true version of the WRONG rhs
//     (`Eq Expr (Sort l …) (Sort l …)`) IS accepted by the kernel, proving the
//     wrong rhs is a genuine well-typed `Expr` and the wrong goal a genuine
//     `Prop` — so the rejection above is a real def-eq clash, not a malformation;
//   * the mint refuses the `WrongMissingSucc` obligation outright (no honest
//     goal/proof pair), so no false `Certified` can ride this lane.
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `proof : goal`;
//   * the goal is BUILT by this lane (`correct_goal`), not reverse-engineered;
//   * the environment is `init_eq` + the four inductives + the model definition
//     (no smuggled axioms); the closed context (empty `LocalContext`) admits no
//     hypotheses;
//   * the term + empty context + obligation label are bound into a lineage digest
//     and re-checked on the DESERIALIZED payload (a tampered term / swapped
//     lineage fails closed).
//
// HONEST SCOPE — a Certified functional fact about the REPRESENTATIVE sort arm.
//   * What this PROVES: the sort-arm MODEL function (the datatype term the
//     extracted MIR builds) satisfies its functional postcondition, kernel-
//     checked by reflexivity. Combined with the confirmed real-MIR extraction
//     (step 3's `Aggregate` test) and the extraction's faithfulness, this is a
//     Certified functional fact about the real Rust sort arm's OUTPUT SHAPE.
//   * What it does NOT do: it is the REPRESENTATIVE sort arm, not the literal
//     recursive `infer_type` (that needs a step 6: all arms + `model_infer_type`
//     + relating the model to the literal `kernel_infer_type`). It does NOT drain
//     `bootstrap_model_fidelity`. THE AXIOM CENSUS STAYS 16.
//   * The remaining trust edge is `trust-mir-extract`'s extraction faithfulness
//     (the model = real-Rust link): this lane trusts that the MODEL datatype term
//     is the faithful image of the extracted MIR. That is the honest residual.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    LocalContext, TypeChecker,
};
use sha2::{Digest, Sha256};

/// Lineage domain tag for the datatype FUNCTIONAL `CleanCic` digest. Distinct
/// from the no-confusion / QF_LIA / finite-sim / inductive-func lanes so
/// certificates never alias across lanes.
const FUNCTIONAL_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.datatype-functional.v2";
const FUNCTIONAL_VC_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.datatype-functional-vc.v3";

/// The sort-arm functional obligation this lane can be asked to certify.
///
/// Only `Correct` is the TRUE-by-construction functional equation; `WrongMissingSucc`
/// is the NEGATIVE control — the postcondition with the `succ` dropped, which the
/// lane MUST fail closed on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortArmFunctionalFact {
    /// `model l meta = Expr.mk (ExprKind.Sort (Level.succ l)) meta` — the true
    /// functional postcondition, dischargeable by kernel reflexivity.
    Correct,
    /// `model l meta = Expr.mk (ExprKind.Sort l) meta` — the `succ` dropped. A
    /// FALSE equation (`model l meta` reduces to `Sort(succ l)`, not `Sort l`);
    /// the lane must reject it (fail-closed).
    WrongMissingSucc,
}

impl SortArmFunctionalFact {
    /// Stable label bound into the lineage digest so a certificate for one
    /// obligation cannot be replayed against another.
    fn label(self) -> &'static str {
        match self {
            SortArmFunctionalFact::Correct => {
                "infer_sort_arm:forall l meta, model l meta = Expr.mk (ExprKind.Sort (Level.succ l)) meta"
            }
            SortArmFunctionalFact::WrongMissingSucc => {
                "infer_sort_arm:NEGATIVE-CONTROL:forall l meta, model l meta = Expr.mk (ExprKind.Sort l) meta"
            }
        }
    }

    /// The (goal, reflexivity proof) pair, or `None` (fail-closed) when the shape
    /// has no honest kernel proof — only `Correct` reduces by reflexivity.
    fn goal_and_proof(self) -> Option<(Expr, Expr)> {
        match self {
            SortArmFunctionalFact::Correct => Some((correct_goal(), correct_proof())),
            SortArmFunctionalFact::WrongMissingSucc => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Kernel-term construction helpers (raw CIC `Expr`, de Bruijn indices).
// ---------------------------------------------------------------------------

fn meta_ty() -> Expr {
    Expr::const_(Name::from_string("Meta"), Vec::new())
}
fn level_ty() -> Expr {
    Expr::const_(Name::from_string("Level"), Vec::new())
}
fn exprkind_ty() -> Expr {
    Expr::const_(Name::from_string("ExprKind"), Vec::new())
}
fn expr_ty() -> Expr {
    Expr::const_(Name::from_string("Expr"), Vec::new())
}

fn level_succ(x: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Level.succ"), Vec::new()), x)
}
fn exprkind_sort(l: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("ExprKind.Sort"), Vec::new()), l)
}
fn expr_mk(kind: Expr, meta: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Expr.mk"), Vec::new()), [kind, meta])
}

/// Universe level of `Expr`: `Expr : Type 0 = Sort 1`, so `Eq`/`Eq.refl` over
/// `Expr` take `u = 1`.
fn expr_universe() -> Level {
    Level::succ(Level::zero())
}

/// `Eq.{1} Expr a b` (`Expr`-valued propositional equality, a `Prop`).
fn eq_expr(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![expr_universe()]), [expr_ty(), a, b])
}

/// `@Eq.refl.{1} Expr a : Eq Expr a a`.
fn eq_refl_expr(a: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![expr_universe()]), [expr_ty(), a])
}

// --- the datatype cluster (minimal slice the sort-arm equation touches) -----

/// `inductive Meta : Type where | mk` — `Expr`'s opaque metadata field type.
#[must_use]
pub fn meta_inductive() -> InductiveDecl {
    let meta = Name::from_string("Meta");
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: meta.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Meta.mk"),
                type_: Expr::const_(meta, vec![]),
            }],
        }],
    }
}

/// `inductive Level : Type where | zero | succ (pred : Level)` (mirrors `Nat`; the
/// same shape `datatype_no_confusion` registers).
#[must_use]
pub fn level_inductive() -> InductiveDecl {
    let level = Name::from_string("Level");
    let level_ref = Expr::const_(level.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: level,
            type_: Expr::type_(),
            constructors: vec![
                Constructor { name: Name::from_string("Level.zero"), type_: level_ref.clone() },
                Constructor {
                    name: Name::from_string("Level.succ"),
                    type_: Expr::pi(BinderInfo::Default, level_ref.clone(), level_ref),
                },
            ],
        }],
    }
}

/// `inductive ExprKind : Type where | Sort (l : Level)` — the minimal slice: the
/// sort-arm equation touches only the `Sort` constructor.
#[must_use]
pub fn exprkind_inductive() -> InductiveDecl {
    let exprkind = Name::from_string("ExprKind");
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: exprkind.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("ExprKind.Sort"),
                // ExprKind.Sort : Level -> ExprKind
                type_: Expr::pi(BinderInfo::Default, level_ty(), Expr::const_(exprkind, vec![])),
            }],
        }],
    }
}

/// `inductive Expr : Type where | mk (kind : ExprKind) (meta : Meta)` — the
/// single-constructor `Expr` "struct" (`Expr::from_kind` builds `mk`).
#[must_use]
pub fn expr_inductive() -> InductiveDecl {
    let expr = Name::from_string("Expr");
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: expr.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Expr.mk"),
                // Expr.mk : ExprKind -> Meta -> Expr
                type_: Expr::pi(
                    BinderInfo::Default,
                    exprkind_ty(),
                    Expr::pi(BinderInfo::Default, meta_ty(), Expr::const_(expr, vec![])),
                ),
            }],
        }],
    }
}

// --- the extracted MODEL function -------------------------------------------

/// The MODEL function TYPE `Level -> Meta -> Expr`.
#[must_use]
pub fn model_type() -> Expr {
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, meta_ty(), expr_ty()))
}

/// The MODEL function VALUE — the datatype term the extracted MIR builds:
/// `fun (l : Level) (meta : Meta) => Expr.mk (ExprKind.Sort (Level.succ l)) meta`.
/// Under `λ l λ meta`: `l = #1`, `meta = #0`.
#[must_use]
pub fn model_value() -> Expr {
    let body = expr_mk(exprkind_sort(level_succ(Expr::bvar(1))), Expr::bvar(0));
    Expr::lam(BinderInfo::Default, level_ty(), Expr::lam(BinderInfo::Default, meta_ty(), body))
}

/// `infer_sort_arm_model l meta` (the model applied to the two bound params).
fn model_app(l: Expr, meta: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("infer_sort_arm_model"), Vec::new()), [l, meta])
}

/// The datatype constructor tree the body builds, `Expr.mk (ExprKind.Sort
/// (Level.succ l)) meta`, evaluated under `λ l λ meta` (`l = #1`, `meta = #0`).
fn correct_rhs() -> Expr {
    expr_mk(exprkind_sort(level_succ(Expr::bvar(1))), Expr::bvar(0))
}

/// The WRONG rhs (negative control), `Expr.mk (ExprKind.Sort l) meta` — the
/// `succ` dropped — under `λ l λ meta`.
fn wrong_rhs() -> Expr {
    expr_mk(exprkind_sort(Expr::bvar(1)), Expr::bvar(0))
}

// --- the functional goal + reflexivity proof --------------------------------

/// The functional postcondition:
/// `∀ (l : Level) (meta : Meta), Eq Expr (model l meta) (Expr.mk (ExprKind.Sort (Level.succ l)) meta)`.
#[must_use]
pub fn correct_goal() -> Expr {
    let body = eq_expr(model_app(Expr::bvar(1), Expr::bvar(0)), correct_rhs());
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, meta_ty(), body))
}

/// The reflexivity proof `fun l meta => @Eq.refl.{1} Expr (Expr.mk (ExprKind.Sort
/// (Level.succ l)) meta)`. Its natural type is `Eq Expr RHS RHS`; the kernel
/// accepts it against [`correct_goal`] because `model l meta` delta+beta-reduces
/// to `RHS`.
#[must_use]
pub fn correct_proof() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        level_ty(),
        Expr::lam(BinderInfo::Default, meta_ty(), eq_refl_expr(correct_rhs())),
    )
}

/// NEGATIVE-control goal `∀ l meta, Eq Expr (model l meta) (Expr.mk (ExprKind.Sort
/// l) meta)` — the `succ` dropped, a FALSE equation. No refl proof type-checks.
#[must_use]
pub fn wrong_goal() -> Expr {
    let body = eq_expr(model_app(Expr::bvar(1), Expr::bvar(0)), wrong_rhs());
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, meta_ty(), body))
}

/// NEGATIVE-control NON-VACUITY goal `∀ l meta, Eq Expr (Sort l …) (Sort l …)` —
/// the reflexive-TRUE version of the wrong rhs. The kernel ACCEPTS
/// [`wrong_rhs_refl_proof`] here, proving the wrong rhs is a genuine well-typed
/// `Expr` and the wrong goal a genuine `Prop` (so [`wrong_goal`]'s rejection is a
/// real def-eq clash, not a malformation).
#[must_use]
pub fn wrong_rhs_refl_true_goal() -> Expr {
    let body = eq_expr(wrong_rhs(), wrong_rhs());
    Expr::pi(BinderInfo::Default, level_ty(), Expr::pi(BinderInfo::Default, meta_ty(), body))
}

/// `fun l meta => @Eq.refl.{1} Expr (Expr.mk (ExprKind.Sort l) meta)` — the refl
/// term for the WRONG rhs. Inhabits [`wrong_rhs_refl_true_goal`] but NOT
/// [`wrong_goal`] (its `Sort l` is not def-eq to `model l meta ≡ Sort(succ l)`).
#[must_use]
pub fn wrong_rhs_refl_proof() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        level_ty(),
        Expr::lam(BinderInfo::Default, meta_ty(), eq_refl_expr(wrong_rhs())),
    )
}

// ---------------------------------------------------------------------------
// Step-1 correspondence: reconstruct the exact step-3 emitted VC `Formula`.
// ---------------------------------------------------------------------------

/// Reconstruct the step-3 (`trust-vcgen`) emitted sort-arm functional VC as a
/// `trust_types::Formula` — the exact shape
/// `Forall [l, meta] Eq(_0, Ctor("Expr",[Ctor("Sort",[Ctor("Succ",[l])]), meta]))`.
///
/// This documents the correspondence: the CIC goal this lane discharges
/// ([`correct_goal`]) is the kernel image of THIS VC. `datatype_functional_vcs`
/// lives in trust-vcgen (there is intentionally no reverse dependency from the
/// certifier), so the shape is rebuilt here rather than imported and pinned by
/// `sort_arm_vc_formula_matches_step3` below. The `Formula` ctor names
/// (`Succ`/`Sort`/`Expr`) are the trust-mir-extract variant names; they map onto
/// the CIC constructors `Level.succ` / `ExprKind.Sort` / `Expr.mk`. The full
/// datatype descriptors and the machine-width `meta` sort are load-bearing:
/// accepting nominal/empty descriptors or an `Int`/`BitVec` mismatch would let
/// the correspondence drift away from the typed VC actually emitted.
#[must_use]
pub fn sort_arm_functional_vc_formula() -> trust_types::Formula {
    use trust_types::{Formula, Sort};

    let level_ref = Sort::Datatype { name: "Level".to_string(), constructors: Vec::new() };
    let exprkind_ref = Sort::Datatype { name: "ExprKind".to_string(), constructors: Vec::new() };
    let level_sort = Sort::Datatype {
        name: "Level".to_string(),
        constructors: vec![
            ("Zero".to_string(), vec![]),
            ("Succ".to_string(), vec![("0".to_string(), level_ref.clone())]),
            (
                "Max".to_string(),
                vec![("0".to_string(), level_ref.clone()), ("1".to_string(), level_ref.clone())],
            ),
            (
                "IMax".to_string(),
                vec![("0".to_string(), level_ref.clone()), ("1".to_string(), level_ref.clone())],
            ),
            ("Param".to_string(), vec![("0".to_string(), Sort::BitVec(64))]),
        ],
    };
    let exprkind_sort = Sort::Datatype {
        name: "ExprKind".to_string(),
        constructors: vec![
            ("BVar".to_string(), vec![("0".to_string(), Sort::BitVec(32))]),
            ("Sort".to_string(), vec![("0".to_string(), level_ref)]),
            ("Const".to_string(), vec![("0".to_string(), Sort::BitVec(64))]),
        ],
    };
    let expr_sort = Sort::Datatype {
        name: "Expr".to_string(),
        constructors: vec![(
            "Expr".to_string(),
            vec![("kind".to_string(), exprkind_ref), ("meta".to_string(), Sort::BitVec(64))],
        )],
    };
    let meta_sort = Sort::BitVec(64);

    let succ = Formula::Ctor {
        ctor: "Succ".to_string(),
        args: vec![Formula::var_owned("l".to_string(), level_sort.clone())],
        sort: level_sort.clone(),
    };
    let sort_kind =
        Formula::Ctor { ctor: "Sort".to_string(), args: vec![succ], sort: exprkind_sort };
    let expr = Formula::Ctor {
        ctor: "Expr".to_string(),
        args: vec![sort_kind, Formula::var_owned("meta".to_string(), meta_sort.clone())],
        sort: expr_sort.clone(),
    };
    let eq = Formula::Eq(Box::new(Formula::var_owned("_0".to_string(), expr_sort)), Box::new(expr));
    Formula::forall(&[("l", level_sort), ("meta", meta_sort)], eq)
}

// ---------------------------------------------------------------------------
// kernel env + check.
// ---------------------------------------------------------------------------

/// Build the kernel environment: `Eq` (+ `Eq.refl`), the four cluster inductives
/// (`Meta`, `Level`, `ExprKind`, `Expr` — dependencies first), and the
/// `infer_sort_arm_model` definition (registering it kernel-type-checks the model
/// against its type). No smuggled axioms. `None` (fail-closed) on any failure.
fn build_functional_env() -> Option<Environment> {
    let mut env = Environment::default();
    env.init_eq().ok()?;
    env.add_inductive(meta_inductive()).ok()?;
    env.add_inductive(level_inductive()).ok()?;
    env.add_inductive(exprkind_inductive()).ok()?;
    env.add_inductive(expr_inductive()).ok()?;
    env.add_decl(Declaration::Definition {
        name: Name::from_string("infer_sort_arm_model"),
        level_params: vec![],
        type_: model_type(),
        value: model_value(),
        is_reducible: true,
    })
    .ok()?;
    Some(env)
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// closed context.
fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

/// SHA-256 lineage digest binding the term, the empty closed context, and the
/// obligation label. Position-tagged + length-prefixed ⇒ injective.
fn functional_lineage_digest(
    term_bytes: &[u8],
    context_bytes: &[u8],
    label: &str,
) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(FUNCTIONAL_LINEAGE_DOMAIN.as_bytes());
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

/// Mint a kernel-CHECKED `CleanCic` certificate that the sort-arm functional
/// equation reconstructs to a Clean-kernel reflexivity proof (the Certified tier).
///
/// Fail-closed on every count: the obligation must be a supported (reflexive)
/// shape; the clean kernel must accept the proof term; the serialized payload must
/// re-check after a round-trip. Returns `None` otherwise (the caller records
/// `Trusted`, never a false `Certified`).
#[must_use]
pub fn certify_datatype_functional(fact: SortArmFunctionalFact) -> Option<trust_ir::ProofEvidence> {
    // Gate 1 (fail-closed on unsupported shape): only the reflexive `Correct`
    // equation has an honest kernel proof; `WrongMissingSucc` yields no pair.
    let (goal, proof) = fact.goal_and_proof()?;

    // Gate 2 (TCB): the clean kernel independently type-checks the refl term.
    let env = build_functional_env()?;
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }

    // Serialize term + empty closed context, then independently re-check the
    // DESERIALIZED payload (consumer-side gate).
    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = functional_lineage_digest(&term_bytes, &context_bytes, fact.label());
    if !recheck_datatype_functional(fact, &term_bytes, &context_bytes, &lineage) {
        return None;
    }

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Certify the exact non-recursive sort-arm VC emitted by
/// `trust_vcgen::datatype_functional`.
///
/// This dedicated entry point is intentionally not part of generic VC solver
/// dispatch: the supported input is a positive functional equation, while the
/// generic Trust VC convention is a violation formula whose UNSAT result proves
/// safety. Every typed field and the serialized VC are bound into the lineage.
#[must_use]
pub fn certify_datatype_functional_vc(
    vc: &trust_types::VerificationCondition,
) -> Option<trust_ir::ProofEvidence> {
    if !supported_sort_arm_vc(vc) {
        return None;
    }
    let (goal, proof) = SortArmFunctionalFact::Correct.goal_and_proof()?;
    let env = build_functional_env()?;
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }

    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = functional_vc_lineage_digest(&term_bytes, &context_bytes, vc)?;
    if !recheck_datatype_functional_vc(vc, &term_bytes, &context_bytes, &lineage) {
        return None;
    }

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

fn supported_sort_arm_vc(vc: &trust_types::VerificationCondition) -> bool {
    matches!(
        &vc.kind,
        trust_types::VcKind::FunctionalCorrectness { property, context }
            if property == "datatype_functional_arm" && context == "infer_sort_arm"
    ) && vc.function.as_str() == "infer_sort_arm"
        && vc.formula == sort_arm_functional_vc_formula()
        && vc.contract_metadata.is_none()
}

fn functional_vc_lineage_digest(
    term_bytes: &[u8],
    context_bytes: &[u8],
    vc: &trust_types::VerificationCondition,
) -> Option<trust_ir::ProofDigest> {
    let encoded_vc = bincode::serialize(vc).ok()?;
    let mut hasher = Sha256::new();
    hasher.update(FUNCTIONAL_VC_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"vc:".as_slice(), encoded_vc.as_slice()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    Some(trust_ir::ProofDigest::sha256(hasher.finalize().into()))
}

/// Recheck a certificate minted for an exact emitted non-recursive sort-arm
/// VC, including its typed obligation identity and serialized formula binding.
#[must_use]
pub fn recheck_datatype_functional_vc(
    vc: &trust_types::VerificationCondition,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !supported_sort_arm_vc(vc) {
        return false;
    }
    let Some((_, canonical_proof)) = SortArmFunctionalFact::Correct.goal_and_proof() else {
        return false;
    };
    if !crate::is_canonical_empty_context(context_bytes)
        || !crate::is_canonical_term(term_bytes, &canonical_proof)
    {
        return false;
    }
    let Some(env) = build_functional_env() else {
        return false;
    };
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &correct_goal()) {
        return false;
    }
    functional_vc_lineage_digest(term_bytes, context_bytes, vc).as_ref() == Some(lineage)
}

/// Consumer-side re-check of a datatype functional `CleanCic` certificate:
/// independently rebuild env + goal, deserialize the term, re-run the clean-kernel
/// `check_type`, and re-bind the lineage digest. `true` ONLY if the kernel accepts
/// the deserialized term AND the lineage matches — a tampered term or a swapped
/// lineage fails closed.
#[must_use]
pub fn recheck_datatype_functional(
    fact: SortArmFunctionalFact,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let Some((goal, canonical_proof)) = fact.goal_and_proof() else {
        return false;
    };
    if !crate::is_canonical_empty_context(context_bytes)
        || !crate::is_canonical_term(term_bytes, &canonical_proof)
    {
        return false;
    }
    let Some(env) = build_functional_env() else {
        return false;
    };
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &goal) {
        return false;
    }
    &functional_lineage_digest(term_bytes, context_bytes, fact.label()) == lineage
}

#[cfg(test)]
mod tests {
    use trust_ir::ProofEvidence;

    use super::*;

    fn exact_vc() -> trust_types::VerificationCondition {
        trust_types::VerificationCondition {
            kind: trust_types::VcKind::FunctionalCorrectness {
                property: "datatype_functional_arm".to_string(),
                context: "infer_sort_arm".to_string(),
            },
            function: "infer_sort_arm".into(),
            location: trust_types::SourceSpan::default(),
            formula: sort_arm_functional_vc_formula(),
            contract_metadata: None,
            obligation: None,
        }
    }

    // ── THE MILESTONE: the reflexivity discharge closes ───────────────────────

    /// The sort-arm functional equation is discharged by kernel reflexivity: the
    /// model definition type-checks, the refl proof inhabits the functional
    /// postcondition, and the mint round-trips as a `CleanCic` certificate.
    #[test]
    fn certify_datatype_functional_sort_arm() {
        // The env builds ⇒ the model definition kernel-type-checks against its type.
        let env = build_functional_env()
            .expect("init eq + Meta/Level/ExprKind/Expr + infer_sort_arm_model definition");

        // Direct clean-kernel check: the refl term inhabits the functional goal
        // (`model l meta` delta+beta-reduces to the built ctor tree).
        assert!(
            kernel_checks_goal(&env, &correct_proof(), &correct_goal()),
            "clean kernel must accept `fun l meta => Eq.refl (Expr.mk (ExprKind.Sort \
             (Level.succ l)) meta)` against the sort-arm functional postcondition"
        );

        // Full mint (kernel check + serialize + round-trip + lineage).
        let evidence = certify_datatype_functional(SortArmFunctionalFact::Correct)
            .expect("the correct sort-arm equation must certify to a CleanCic term");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
        assert!(
            recheck_datatype_functional(SortArmFunctionalFact::Correct, &term, &context, &lineage),
            "serialized functional CleanCic payload must re-check via the clean kernel"
        );
    }

    // ── NEGATIVE control (no masquerade): the WRONG postcondition is rejected ──

    /// The `succ`-dropped postcondition is REJECTED by the kernel, and the
    /// rejection is NON-VACUOUS: the reflexive-true version of the wrong rhs IS
    /// accepted (so the wrong rhs is a genuine `Expr`, the wrong goal a genuine
    /// `Prop`), yet NO refl proof inhabits the wrong equation.
    #[test]
    fn wrong_postcondition_kernel_rejects() {
        let env = build_functional_env().expect("init env");

        // Non-vacuity: the wrong rhs is a genuine well-typed Expr — the reflexive
        // TRUE version type-checks (the kernel reduction genuinely fires).
        assert!(
            kernel_checks_goal(&env, &wrong_rhs_refl_proof(), &wrong_rhs_refl_true_goal()),
            "the wrong rhs must be a genuine Expr: `Eq Expr (Sort l) (Sort l)` refl must check"
        );

        // The correct refl term does NOT prove the wrong goal (`Sort(succ l)` is
        // not def-eq to the wrong `Sort l`).
        assert!(
            !kernel_checks_goal(&env, &correct_proof(), &wrong_goal()),
            "the correct refl term must be REJECTED against the succ-dropped goal"
        );
        // ... and neither does the wrong rhs's own refl term (`model l meta ≡
        // Sort(succ l)` is not def-eq to the wrong `Sort l`): no masquerade.
        assert!(
            !kernel_checks_goal(&env, &wrong_rhs_refl_proof(), &wrong_goal()),
            "no refl term inhabits the succ-dropped functional equation (no masquerade)"
        );
    }

    /// The lane fails closed on the negative-control obligation: no `Certified`.
    #[test]
    fn lane_rejects_wrong_postcondition() {
        assert!(
            SortArmFunctionalFact::WrongMissingSucc.goal_and_proof().is_none(),
            "the succ-dropped negative control must have no honest goal/proof pair"
        );
        assert!(
            certify_datatype_functional(SortArmFunctionalFact::WrongMissingSucc).is_none(),
            "the negative control must never mint a CleanCic certificate"
        );
    }

    // ── Step-1 correspondence: the discharged VC is step-3's emitted Formula ───

    /// The reconstructed VC `Formula` matches the exact step-3 emitted shape
    /// `Forall [l, meta] Eq(_0, Ctor("Expr",[Ctor("Sort",[Ctor("Succ",[l])]), meta]))`.
    #[test]
    fn sort_arm_vc_formula_matches_step3() {
        use trust_types::Formula;
        let f = sort_arm_functional_vc_formula();
        let Formula::Forall(binders, body) = &f else {
            panic!("expected Forall, got {f:?}");
        };
        let names: Vec<&str> = binders.iter().map(|(s, _)| s.as_str()).collect();
        assert!(names.contains(&"l") && names.contains(&"meta"), "binders l, meta: {names:?}");

        let Formula::Eq(lhs, rhs) = body.as_ref() else {
            panic!("expected Eq body, got {body:?}");
        };
        assert_eq!(lhs.var_name(), Some("_0"), "lhs is the return slot _0");

        let Formula::Ctor { ctor, args, .. } = rhs.as_ref() else {
            panic!("expected Expr Ctor, got {rhs:?}");
        };
        assert_eq!(ctor, "Expr");
        assert_eq!(args.len(), 2, "Expr has kind + meta");
        assert_eq!(args[1].var_name(), Some("meta"), "second Expr field is the meta param");

        let Formula::Ctor { ctor: sc, args: sa, .. } = &args[0] else {
            panic!("expected Sort Ctor, got {:?}", args[0]);
        };
        assert_eq!(sc, "Sort");
        assert_eq!(sa.len(), 1);
        let Formula::Ctor { ctor: succ_c, args: succ_a, .. } = &sa[0] else {
            panic!("expected Succ Ctor, got {:?}", sa[0]);
        };
        assert_eq!(succ_c, "Succ");
        assert_eq!(succ_a.len(), 1);
        assert_eq!(succ_a[0].var_name(), Some("l"), "innermost arg is the level param l");
    }

    #[test]
    fn vc_recheck_rejects_malformed_context_even_with_matching_lineage() {
        let vc = exact_vc();
        let evidence = certify_datatype_functional_vc(&vc).expect("certify exact emitted VC");
        let ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let malformed_context = [context.as_slice(), b"not-a-context"].concat();
        let forged_lineage = functional_vc_lineage_digest(&term, &malformed_context, &vc)
            .expect("lineage hashing remains available to an untrusted presenter");
        assert!(
            !recheck_datatype_functional_vc(&vc, &term, &malformed_context, &forged_lineage),
            "recheck must validate context semantics, not only bind opaque bytes into a hash"
        );
    }

    // ── tamper / lineage fail-closed (mirrors the no-confusion lane) ───────────

    /// A tampered serialized term fails the consumer-side re-check (fail-closed).
    #[test]
    fn tampered_term_rejected() {
        let evidence =
            certify_datatype_functional(SortArmFunctionalFact::Correct).expect("certify");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_datatype_functional(SortArmFunctionalFact::Correct, &term, &context, &lineage),
            "pristine must re-check"
        );
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_datatype_functional(
                SortArmFunctionalFact::Correct,
                &tampered,
                &context,
                &lineage
            ),
            "tampered functional term must fail the offline kernel re-check"
        );
    }

    /// A certificate must not re-check under a swapped (zeroed) lineage digest.
    #[test]
    fn swapped_lineage_rejected() {
        let evidence =
            certify_datatype_functional(SortArmFunctionalFact::Correct).expect("certify");
        let ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            !recheck_datatype_functional(
                SortArmFunctionalFact::Correct,
                &term,
                &context,
                &trust_ir::ProofDigest::zero()
            ),
            "a zeroed lineage must fail closed"
        );
    }

    #[test]
    fn both_recheck_apis_reject_relineaged_sorry_and_valid_noncanonical_proof() {
        let fact = SortArmFunctionalFact::Correct;
        let vc = exact_vc();
        let goal = correct_goal();
        let canonical_proof = correct_proof();
        let context = crate::canonical_empty_context_bytes().expect("canonical context");

        let mut ambient = build_functional_env().expect("functional env");
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let fact_lineage = functional_lineage_digest(&sorry_bytes, &context, fact.label());
        let vc_lineage =
            functional_vc_lineage_digest(&sorry_bytes, &context, &vc).expect("lineage");
        assert!(!recheck_datatype_functional(fact, &sorry_bytes, &context, &fact_lineage,));
        assert!(!recheck_datatype_functional_vc(&vc, &sorry_bytes, &context, &vc_lineage,));

        let beta = Expr::app(
            Expr::lam(BinderInfo::Default, goal.clone(), Expr::bvar(0)),
            canonical_proof.clone(),
        );
        let minimal = build_functional_env().expect("minimal env");
        assert!(kernel_checks_goal(&minimal, &beta, &goal));
        let beta_bytes = serialize_term(&beta).expect("serialize beta proof");
        let fact_lineage = functional_lineage_digest(&beta_bytes, &context, fact.label());
        let vc_lineage = functional_vc_lineage_digest(&beta_bytes, &context, &vc).expect("lineage");
        assert!(!recheck_datatype_functional(fact, &beta_bytes, &context, &fact_lineage,));
        assert!(!recheck_datatype_functional_vc(&vc, &beta_bytes, &context, &vc_lineage,));

        let term = serialize_term(&canonical_proof).expect("canonical proof");
        let mut noncanonical_context = context;
        noncanonical_context.push(0);
        let relined = functional_lineage_digest(&term, &noncanonical_context, fact.label());
        assert!(!recheck_datatype_functional(fact, &term, &noncanonical_context, &relined,));
    }
}
