// Brick 3 · Lever A · STEP 6 (smallest real recursive discharge) — SCRATCH TEST.
//
// The sort-arm lane (`datatype_functional.rs`) discharges a NON-recursive
// functional VC by kernel reflexivity: `model l meta` delta+beta-reduces to the
// built ctor tree, so `Eq.refl` closes it. That works only because the sort arm
// builds a fixed ctor tree with no self-call.
//
// The literal `infer_type` is RECURSIVE. This test builds the analogue of
// `inductive_functional`'s `zero_add` (a genuine `Nat.rec` structural induction),
// but over an EXTRACTED datatype — `Level` (one of the Level/Expr/ExprKind
// cluster trust-mir-extract lowers). It:
//   1. registers `Level = zero | succ (pred)` via `add_inductive` (so `Level.rec`
//      + its iota rule are generated), and
//   2. registers a RECURSIVE model function `mirror : Level -> Level` DEFINED BY
//      `Level.rec` (zero -> zero, succ pred -> succ (mirror pred)), and
//   3. kernel-checks a genuinely INDUCTIVE functional fact
//        `forall l, Eq Level (mirror l) l`
//      whose proof is a `Level.rec` term carrying the inductive hypothesis
//      `ih : mirror pred = pred`, consumed in the succ arm via `congrArg`.
//
// WHY THIS IS GENUINE INDUCTION (not refl-at-a-ctor):
//   * `mirror l` is STUCK on a free `l` (Level.rec only iota-fires on a concrete
//     ctor), exactly like `Nat.add 0 n` is stuck on a free `n`. So the refl-only
//     pseudo-proof `fun l => Eq.refl Level (mirror l)` is REJECTED by the kernel
//     (test `mirror_id_requires_induction`), and ONLY the `Level.rec` term that
//     carries and consumes the IH closes the goal. This is the same load-bearing
//     asymmetry the `zero_add` milestone witnesses.
//   * SHAPE MATCH TO THE REAL TARGET: `mirror l = l` is "recursive function
//     `mirror` agrees with `id` on every `l`", proved by structural induction
//     where each recursive arm consumes the IH. That is the MINIMAL instance of
//     the exact proof shape `bootstrap_model_fidelity` needs —
//     `forall e, model_infer_type e = kernel_infer_type e` — two recursive
//     functions agreeing on all inputs, by induction on the datatype.
//
// SCOPE / NO OVERCLAIM: this grounds NOTHING in clean-verify. It does NOT drain a
// fidelity axiom, does NOT ground `kernel_infer_type`, and the axiom census STAYS
// 16. Its value is the demonstration that the structural-induction discharge
// machinery works over an EXTRACTED datatype's recursive model function — the
// machinery the recursive `infer_type` arms would need. See the returned
// assessment for the wall between this and the literal mutually-recursive
// `infer_type <-> whnf <-> is_def_eq` cluster.

use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    LocalContext, TypeChecker,
};

// --- kernel-term helpers (raw CIC Expr, de Bruijn) --------------------------

fn level_ty() -> Expr {
    Expr::const_(Name::from_string("Level"), Vec::new())
}
fn level_zero() -> Expr {
    Expr::const_(Name::from_string("Level.zero"), Vec::new())
}
fn level_succ(x: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Level.succ"), Vec::new()), x)
}
fn mirror(x: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("mirror"), Vec::new()), x)
}

/// `Level : Type 0 = Sort 1`, so Eq/Eq.refl/congrArg over `Level` take `u = 1`.
fn level1() -> Level {
    Level::succ(Level::zero())
}

/// `Eq.{1} Level a b`.
fn eq_level(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [level_ty(), a, b])
}

/// `inductive Level : Type where | zero | succ (pred : Level)` (2-ctor slice of
/// the extracted Level cluster — the same shape the no-confusion/functional
/// lanes register).
fn level_inductive() -> InductiveDecl {
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

/// The RECURSIVE model function value, DEFINED BY `Level.rec`:
/// `fun (l : Level) => @Level.rec.{1} (fun _ => Level) Level.zero
///                        (fun (pred : Level) (ih : Level) => Level.succ ih) l`.
/// zero -> zero, succ pred -> succ (mirror pred).
fn mirror_value() -> Expr {
    let motive = Expr::lam(BinderInfo::Default, level_ty(), level_ty()); // fun _:Level => Level
    let zero_case = level_zero();
    // fun (pred : Level) (ih : Level) => Level.succ ih   (ih = #0)
    let succ_case = Expr::lam(
        BinderInfo::Default,
        level_ty(),
        Expr::lam(BinderInfo::Default, level_ty(), level_succ(Expr::bvar(0))),
    );
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Level.rec"), vec![level1()]), // motive lands in Level : Sort 1
        [motive, zero_case, succ_case, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, level_ty(), rec_app)
}

fn mirror_type() -> Expr {
    Expr::pi(BinderInfo::Default, level_ty(), level_ty())
}

/// Goal: `forall (l : Level), Eq Level (mirror l) l`.
fn mirror_id_goal() -> Expr {
    Expr::pi(BinderInfo::Default, level_ty(), eq_level(mirror(Expr::bvar(0)), Expr::bvar(0)))
}

/// The GENUINELY INDUCTIVE proof, by `Level.rec.{0}` (motive is Prop-valued):
/// ```text
/// fun (l : Level) =>
///   @Level.rec.{0}
///     (motive := fun (x : Level) => Eq Level (mirror x) x)
///     (Eq.refl Level Level.zero)                          -- base: mirror 0 ≡ 0
///     (fun (pred : Level) (ih : Eq Level (mirror pred) pred) =>
///        @congrArg.{1,1} Level Level (mirror pred) pred Level.succ ih)
///                                          -- step: succ (mirror pred) ≡ mirror (succ pred)
///     l
/// ```
fn mirror_id_proof() -> Expr {
    // motive := fun (x : Level) => Eq Level (mirror x) x     (x = #0)
    let motive =
        Expr::lam(BinderInfo::Default, level_ty(), eq_level(mirror(Expr::bvar(0)), Expr::bvar(0)));
    // base : Eq.refl.{1} Level Level.zero   (: Eq Level (mirror 0) 0 by iota)
    let base = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
        [level_ty(), level_zero()],
    );
    // ih binder type under `fun pred`: pred = #0.
    let ih_ty = eq_level(mirror(Expr::bvar(0)), Expr::bvar(0));
    // congrArg.{1,1} Level Level (mirror pred) pred Level.succ ih  — under `fun pred fun ih`:
    //   pred = #1, ih = #0.  Produces `Eq Level (succ (mirror pred)) (succ pred)`.
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![level1(), level1()]),
        [
            level_ty(),                            // {α}
            level_ty(),                            // {β}
            mirror(Expr::bvar(1)),                 // {a₁} = mirror pred
            Expr::bvar(1),                         // {a₂} = pred
            Expr::const_(Name::from_string("Level.succ"), Vec::new()), // f = Level.succ
            Expr::bvar(0),                         // h = ih
        ],
    );
    let succ_case = Expr::lam(
        BinderInfo::Default,
        level_ty(),
        Expr::lam(BinderInfo::Default, ih_ty, congr),
    );
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Level.rec"), vec![Level::zero()]), // Prop motive => .{0}
        [motive, base, succ_case, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, level_ty(), rec_app)
}

/// NEGATIVE control: `fun (l : Level) => Eq.refl Level (mirror l)`. Its type is
/// `forall l, Eq Level (mirror l) (mirror l)`, NOT the goal `... (mirror l) l`
/// (mirror l is stuck on the free l). The kernel MUST reject it.
fn mirror_id_refl_only() -> Expr {
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
        [level_ty(), mirror(Expr::bvar(0))],
    );
    Expr::lam(BinderInfo::Default, level_ty(), refl)
}

/// Definitional CONTRAST goal `forall l, Eq Level (mirror (succ l)) (succ (mirror l))`
/// — TRUE by iota alone (mirror (succ l) reduces to succ (mirror l)), no IH needed.
fn mirror_succ_step_goal() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        level_ty(),
        eq_level(mirror(level_succ(Expr::bvar(0))), level_succ(mirror(Expr::bvar(0)))),
    )
}

/// `fun l => Eq.refl Level (succ (mirror l))` — closes the definitional contrast
/// WITHOUT induction (mirror (succ l) ≡ succ (mirror l) by iota+delta).
fn mirror_succ_step_refl_proof() -> Expr {
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
        [level_ty(), level_succ(mirror(Expr::bvar(0)))],
    );
    Expr::lam(BinderInfo::Default, level_ty(), refl)
}

fn build_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.add_inductive(level_inductive()).expect("add Level inductive (=> Level.rec)");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mirror"),
        level_params: vec![],
        type_: mirror_type(),
        value: mirror_value(),
        is_reducible: true,
    })
    .expect("register recursive `mirror` definition (kernel type-checks its Level.rec body)");
    env
}

fn kernel_checks(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

// --- the tests --------------------------------------------------------------

/// THE MILESTONE: a genuinely inductive functional fact about a RECURSIVE
/// extracted-datatype model function (`mirror : Level -> Level`) is kernel-checked
/// via `Level.rec` carrying and consuming the inductive hypothesis.
#[test]
fn mirror_id_recursive_functional_fact_kernel_checks() {
    let env = build_env();
    assert!(
        kernel_checks(&env, &mirror_id_proof(), &mirror_id_goal()),
        "clean kernel must accept the Level.rec inductive proof of `forall l, mirror l = l`"
    );
}

/// The fact GENUINELY requires induction: the refl-only pseudo-proof (which would
/// suffice if `mirror l` reduced to `l`) is REJECTED — `mirror l` is stuck on the
/// free `l`, so only a `Level.rec` proof carrying the IH closes it. No masquerade.
#[test]
fn mirror_id_requires_induction() {
    let env = build_env();
    assert!(
        !kernel_checks(&env, &mirror_id_refl_only(), &mirror_id_goal()),
        "Eq.refl alone must NOT type-check `forall l, mirror l = l` (mirror l is stuck on free l)"
    );
}

/// CONTRAST (asymmetry witness): the per-constructor step
/// `mirror (succ l) = succ (mirror l)` IS definitional (iota+delta), closed by
/// `Eq.refl` with no induction — confirming the kernel's reduction genuinely
/// fires, so the `mirror l = l` obligation above is a real induction, not a
/// reduction artifact.
#[test]
fn mirror_succ_step_is_definitional() {
    let env = build_env();
    assert!(
        kernel_checks(&env, &mirror_succ_step_refl_proof(), &mirror_succ_step_goal()),
        "Eq.refl must close the definitional step `forall l, mirror (succ l) = succ (mirror l)`"
    );
}
