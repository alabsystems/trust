// trust-certify: CHECKER-CORE is_def_eq FUNCTION-grounding lane.
//
// Grounds the REAL Rust `clean_kernel::TypeChecker::is_def_eq(a, b) -> bool` —
// one of the three central recursive checker-core operations (the
// `infer_type <-> whnf <-> is_def_eq` cluster) — by CALLING it on concrete
// `Expr` pairs and observing its genuine boolean output. Sibling of
// `checker_core_infer_type_fn` (which grounds the real `infer_type` sort arm);
// this is the first lane that reads the real `is_def_eq` function's output.
//
//   * POSITIVE fixtures: pairs that ARE definitionally equal (reflexivity of a
//     sort and of a pi, and a genuine BETA redex that exercises is_def_eq's
//     actual reduction machinery, not mere structural equality) — the real
//     is_def_eq MUST return `true`.
//   * DISCRIMINATION fixtures: pairs that are NOT def-eq (distinct universes,
//     distinct heads sort-vs-pi, distinct Pi domains) — the real is_def_eq MUST
//     return `false`.
//
// A kernel is_def_eq that rubber-stamped `true` would fail EVERY discrimination
// fixture; one that always returned `false` would fail EVERY positive. The lane
// requires both a positive and a negative and checks the real function's output
// against every fixture's expected verdict, so it reads the literal function's
// genuine, discriminating behaviour — never a rubber stamp.
//
// GROUNDING SCOPE (stated with full honesty): PER-INPUT observation of the real
// Rust function on concrete closed inputs — genuine fidelity EVIDENCE about the
// literal `is_def_eq` (differential-grade, the same epistemic character as the
// `checker_core_infer_type_fn` sort-arm lane and clean-verify's fidelity gate).
// It is NOT a for-all proof of is_def_eq's correctness; that universal fact needs
// the recursive-function functional-VC extracted from the literal Rust MIR (the
// recursive-kernel-fn path that does not exist yet). This lane retires no axiom;
// it grounds the real function on a finite, discriminating fixture set. The
// Sort/BVar/Lam/Pi/App fixtures never consult the environment, so
// `Environment::new()` is a faithful context for them; the delta test additionally
// registers a definition and reads is_def_eq's env-consulting (delta) behaviour.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_kernel::{BinderInfo, Environment, Expr, Level, TypeChecker};

/// One concrete `(a, b)` pair exercised against the REAL Rust `is_def_eq`, with
/// the boolean verdict the real function MUST return.
#[derive(Clone)]
pub struct DefEqFnFixture {
    /// Human description of the conceptual def-eq check.
    pub label: &'static str,
    /// Left operand.
    pub a: Expr,
    /// Right operand.
    pub b: Expr,
    /// The def-eq verdict the real function MUST return for this pair.
    pub expect_def_eq: bool,
}

/// `Sort n` as an `Expr` (n = universe level, so `sort(0)` is `Prop`).
fn sort(n: u32) -> Expr {
    let mut level = Level::zero();
    for _ in 0..n {
        level = Level::succ(level);
    }
    Expr::sort(level)
}

/// Call the REAL `clean_kernel::TypeChecker::is_def_eq` on `(a, b)` in a minimal
/// environment and return its actual boolean output.
fn real_is_def_eq(a: &Expr, b: &Expr) -> bool {
    let env = Environment::new();
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.is_def_eq(a, b)
}

/// A well-typed beta redex `(λ (x : Sort 1). x) (Sort 0)` whose β-reduct is
/// `Sort 0` — the argument `Sort 0` has type `Sort 1`, matching the binder, so
/// the redex is type-correct and reduces cleanly.
fn beta_redex_reducing_to_sort0() -> Expr {
    Expr::app(Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(0)), sort(0))
}

/// A SYNTACTICALLY-DIFFERENT well-typed redex also reducing to `Sort 0`:
/// `(λ (x : Sort 2). Sort 0) (Sort 1)` — a constant function ignoring its
/// argument. Distinct term, same β-reduct, so it is def-eq to
/// `beta_redex_reducing_to_sort0` only if is_def_eq reduces BOTH operands.
fn const_redex_reducing_to_sort0() -> Expr {
    Expr::app(Expr::lam(BinderInfo::Default, sort(2), sort(0)), sort(1))
}

/// A well-typed redex reducing to `Sort 1`: `(λ (x : Sort 2). x) (Sort 1)`
/// (argument `Sort 1` has type `Sort 2`). Its reduct `Sort 1` differs from
/// `Sort 0`, so it must NOT be def-eq to a redex reducing to `Sort 0` — the
/// witness that reducing both sides does not mask a genuine difference.
fn beta_redex_reducing_to_sort1() -> Expr {
    Expr::app(Expr::lam(BinderInfo::Default, sort(2), Expr::bvar(0)), sort(1))
}

/// A closed, uninhabited PROPOSITION `P := Π (z : Sort 0). z` (∀ z : Prop, z),
/// used only as a TYPE to build proof terms (no inhabitant needed):
/// `P : Sort (imax 1 0) = Sort 0`, so `P` — and any arrow into it — is a Prop.
fn false_prop() -> Expr {
    Expr::pi(BinderInfo::Default, sort(0), Expr::bvar(0))
}

/// The grounding fixtures for the real `is_def_eq`: positives (must be def-eq)
/// and discrimination negatives (must NOT be def-eq).
#[must_use]
pub fn is_def_eq_fn_fixtures() -> Vec<DefEqFnFixture> {
    vec![
        DefEqFnFixture {
            label: "is_def_eq(Sort 0, Sort 0) = true (reflexivity)",
            a: sort(0),
            b: sort(0),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq((λ x. x) (Sort 0), Sort 0) = true (beta, LHS reduces)",
            a: beta_redex_reducing_to_sort0(),
            b: sort(0),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq(Sort 0, (λ x. x) (Sort 0)) = true (RHS reduces)",
            a: sort(0),
            b: beta_redex_reducing_to_sort0(),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq((λ x. x)(Sort 0), (λ x. Sort 0)(Sort 1)) = true (BOTH reduce → Sort 0)",
            a: beta_redex_reducing_to_sort0(),
            b: const_redex_reducing_to_sort0(),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq((λ x. x)(Sort 0), (λ x. x)(Sort 1)) = false (both reduce, Sort 0 ≠ Sort 1)",
            a: beta_redex_reducing_to_sort0(),
            b: beta_redex_reducing_to_sort1(),
            expect_def_eq: false,
        },
        DefEqFnFixture {
            label: "is_def_eq(Pi Sort0 Sort0, Pi Sort0 Sort0) = true (reflexivity)",
            a: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            b: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq(Pi Sort0 ((λz.z)(Sort0)), Pi Sort0 Sort0) = true (CODOMAIN reduces)",
            a: Expr::pi(BinderInfo::Default, sort(0), beta_redex_reducing_to_sort0()),
            b: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq(Pi ((λz.z)(Sort0)) Sort0, Pi Sort0 Sort0) = true (DOMAIN reduces)",
            a: Expr::pi(BinderInfo::Default, beta_redex_reducing_to_sort0(), sort(0)),
            b: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            expect_def_eq: true,
        },
        DefEqFnFixture {
            label: "is_def_eq(Pi ((λz.z)(Sort0)) Sort0, Pi Sort1 Sort0) = false (domain reduces to Sort0 ≠ Sort1)",
            a: Expr::pi(BinderInfo::Default, beta_redex_reducing_to_sort0(), sort(0)),
            b: Expr::pi(BinderInfo::Default, sort(1), sort(0)),
            expect_def_eq: false,
        },
        DefEqFnFixture {
            label: "is_def_eq(Sort 0, Sort 1) = false (distinct universe)",
            a: sort(0),
            b: sort(1),
            expect_def_eq: false,
        },
        DefEqFnFixture {
            label: "is_def_eq(Sort 0, Pi Sort0 Sort0) = false (distinct head)",
            a: sort(0),
            b: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            expect_def_eq: false,
        },
        DefEqFnFixture {
            label: "is_def_eq(Pi Sort0 _, Pi Sort1 _) = false (distinct domain)",
            a: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            b: Expr::pi(BinderInfo::Default, sort(1), sort(0)),
            expect_def_eq: false,
        },
    ]
}

/// Certify — at the level of the REAL Rust `is_def_eq` FUNCTION — that it agrees
/// with the expected verdict on EVERY fixture: positives are def-eq, negatives
/// are not. Returns `true` iff the real function's genuine output matches every
/// fixture's `expect_def_eq` AND the fixture set contains both a positive and a
/// negative (so the lane is non-vacuous and genuinely discriminating). A single
/// wrong verdict fails closed.
#[must_use]
pub fn certify_real_is_def_eq_fn() -> bool {
    let fixtures = is_def_eq_fn_fixtures();
    let has_pos = fixtures.iter().any(|f| f.expect_def_eq);
    let has_neg = fixtures.iter().any(|f| !f.expect_def_eq);
    if !has_pos || !has_neg {
        return false;
    }
    fixtures.iter().all(|f| real_is_def_eq(&f.a, &f.b) == f.expect_def_eq)
}

#[cfg(test)]
mod tests {
    use clean_kernel::{Constructor, Declaration, InductiveDecl, InductiveType, LevelVec, Name};

    use super::*;

    /// FUNCTION-level grounding: the real Rust `is_def_eq` agrees with the
    /// expected verdict on every fixture (positives def-eq, negatives not) —
    /// reading the genuine, discriminating output of the literal function.
    #[test]
    fn real_is_def_eq_fn_grounds_and_discriminates() {
        assert!(
            certify_real_is_def_eq_fn(),
            "the real Rust is_def_eq must agree with every fixture verdict"
        );
    }

    /// NO MASQUERADE (positive): the REAL function reduces a genuine beta redex —
    /// `(λ x. x) (Sort 0)` is def-eq `Sort 0`. This exercises is_def_eq's actual
    /// whnf/reduction path, not structural equality.
    #[test]
    fn real_is_def_eq_accepts_beta_redex() {
        assert!(
            real_is_def_eq(&beta_redex_reducing_to_sort0(), &sort(0)),
            "(λ x. x) (Sort 0) must be def-eq Sort 0 under the real is_def_eq"
        );
    }

    /// NO MASQUERADE (discrimination): the REAL function REJECTS distinct
    /// universes — is_def_eq is not a rubber stamp that returns `true`.
    #[test]
    fn real_is_def_eq_rejects_distinct_universes() {
        assert!(
            !real_is_def_eq(&sort(0), &sort(1)),
            "Sort 0 and Sort 1 must NOT be def-eq under the real is_def_eq"
        );
    }

    /// NO MASQUERADE (both operands reduced): TWO syntactically-different redexes
    /// that both β-reduce to `Sort 0` are def-eq — the real is_def_eq reduces BOTH
    /// sides, not just the left. A def_eq that reduced only one operand and then
    /// compared structurally would REJECT this pair.
    #[test]
    fn real_is_def_eq_reduces_both_operands() {
        assert!(
            real_is_def_eq(&beta_redex_reducing_to_sort0(), &const_redex_reducing_to_sort0()),
            "(λ x. x)(Sort 0) and (λ x. Sort 0)(Sort 1) both reduce to Sort 0 — must be def-eq"
        );
    }

    /// NO MASQUERADE (reduction does not mask difference): two redexes reducing to
    /// DIFFERENT normal forms (`Sort 0` vs `Sort 1`) are NOT def-eq — reducing both
    /// sides still discriminates, it does not collapse everything reducible.
    #[test]
    fn real_is_def_eq_reduced_forms_still_discriminate() {
        assert!(
            !real_is_def_eq(&beta_redex_reducing_to_sort0(), &beta_redex_reducing_to_sort1()),
            "(λ x. x)(Sort 0) → Sort 0 and (λ x. x)(Sort 1) → Sort 1 must NOT be def-eq"
        );
    }

    /// DELTA (environment-consulting): with a REDUCIBLE definition
    /// `MyDef : Sort 1 := Sort 0` in the environment, the real is_def_eq unfolds it
    /// — `is_def_eq(Const MyDef, Sort 0) = true` — yet still DISCRIMINATES:
    /// `is_def_eq(Const MyDef, Sort 1) = false` (MyDef unfolds to Sort 0, not
    /// Sort 1). Grounds the delta path of def-eq, which the empty-env fixtures never
    /// exercise.
    #[test]
    fn real_is_def_eq_delta_unfolds_and_discriminates() {
        let (eq_value, eq_wrong) = {
            let mut env = Environment::new();
            env.add_decl(Declaration::Definition {
                name: Name::from_string("Trust.Certify.MyDef"),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())),
                value: sort(0),
                is_reducible: true,
            })
            .expect("register reducible MyDef");
            let tc = TypeChecker::with_mode(&env, env.mode());
            let c = Expr::const_(Name::from_string("Trust.Certify.MyDef"), LevelVec::new());
            (tc.is_def_eq(&c, &sort(0)), tc.is_def_eq(&c, &sort(1)))
        };
        assert!(eq_value, "is_def_eq(Const MyDef, Sort 0) must be true (delta-unfold to Sort 0)");
        assert!(!eq_wrong, "is_def_eq(Const MyDef, Sort 1) must be false (MyDef ≠ Sort 1)");
    }

    /// PROOF IRRELEVANCE (Prop-specific, load-bearing discrimination): any two
    /// proofs of a PROPOSITION are definitionally equal regardless of their
    /// syntactic structure — the real is_def_eq infers the common type, finds it is
    /// a Prop (`Sort 0`), and returns `true`. The LOAD-BEARING witness that this is
    /// genuine irrelevance (not a rubber stamp that ignores structure) is that the
    /// SAME structural difference at a non-Prop (`Type`) type is NOT def-eq. Four
    /// adversarially-verified facets:
    ///   (1) fst/snd projections of the Prop `P → P → P` — def-eq;
    ///   (2) DISCRIMINATION: the same shape at `Sort 1` (a Type) — NOT def-eq;
    ///   (3) reduction-DISTINCT proofs `λh.h` vs `λh.(h P)` of the Prop `P → P`
    ///       (both neutral, no reduction path — ONLY irrelevance can equate them);
    ///   (4) polymorphic Church booleans, proofs of `∀ (p : Prop). p → p → p`.
    /// These trigger is_def_eq's internal `infer_type` (the Prop check), so they run
    /// on the large stack, like the `infer_type` lane.
    #[test]
    fn real_is_def_eq_proof_irrelevance_grounds_and_discriminates() {
        use crate::checker_core::run_on_large_stack;
        let p = false_prop();

        // (1) two distinct proofs (fst vs snd projection) of the Prop P → P → P.
        let irrel_a = Expr::lam(
            BinderInfo::Default,
            p.clone(),
            Expr::lam(BinderInfo::Default, p.clone(), Expr::bvar(1)),
        );
        let irrel_b = Expr::lam(
            BinderInfo::Default,
            p.clone(),
            Expr::lam(BinderInfo::Default, p.clone(), Expr::bvar(0)),
        );
        // (2) DISCRIMINATION: the SAME shape at Sort 1 (a Type, NOT a Prop).
        let type_a = Expr::lam(
            BinderInfo::Default,
            sort(1),
            Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(1)),
        );
        let type_b = Expr::lam(
            BinderInfo::Default,
            sort(1),
            Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(0)),
        );
        // (3) reduction-DISTINCT proofs of the Prop P → P: λh.h vs λh.(h P).
        let redx_a = Expr::lam(BinderInfo::Default, p.clone(), Expr::bvar(0));
        let redx_b = Expr::lam(BinderInfo::Default, p.clone(), Expr::app(Expr::bvar(0), p.clone()));
        // (4) polymorphic Church booleans: proofs of ∀ (p : Prop). p → p → p.
        let poly_a = Expr::lam(
            BinderInfo::Default,
            sort(0),
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
            ),
        );
        let poly_b = Expr::lam(
            BinderInfo::Default,
            sort(0),
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(0)),
            ),
        );

        let (irrel, control, redx, poly) = run_on_large_stack(move || {
            (
                real_is_def_eq(&irrel_a, &irrel_b),
                real_is_def_eq(&type_a, &type_b),
                real_is_def_eq(&redx_a, &redx_b),
                real_is_def_eq(&poly_a, &poly_b),
            )
        })
        .expect("real is_def_eq proof-irrelevance calls must complete on the large stack");

        assert!(
            irrel,
            "two distinct proofs of the Prop P → P → P must be def-eq (proof irrelevance)"
        );
        assert!(
            !control,
            "the SAME shape at Type level (Sort1 → Sort1 → Sort1) must NOT be def-eq — \
             proof irrelevance is Prop-specific, not a rubber stamp"
        );
        assert!(
            redx,
            "reduction-distinct proofs λh.h and λh.(h P) of the Prop P → P must be def-eq \
             (both neutral — only proof irrelevance can equate them)"
        );
        assert!(poly, "polymorphic Church booleans (proofs of ∀ p:Prop. p → p → p) must be def-eq");
    }

    /// ETA (function extensionality, definitional): a NEUTRAL function `f` is
    /// def-eq to its eta-expansion `λ x. (f x)`. To make this genuine eta and not
    /// beta, `f` is a BOUND variable (compared under an outer `λ (f : T). …`, so
    /// is_def_eq pushes `f` into context as a stuck fvar — `f x` is neutral, no
    /// redex). The type `T` is a non-Prop TYPE, so the equality is ETA and not
    /// proof irrelevance. Three adversarially-verified facets:
    ///   (1) BASIC: `λf. f` vs `λf. λx. f x` at `T = Sort0 → Sort0` — def-eq;
    ///   (2) DISCRIMINATION: `λf. f` vs `λf. λx. f (f x)` — NOT def-eq (eta expands
    ///       ONE application; `f∘f ≠ f`), the witness eta is not a rubber stamp;
    ///   (3) DEPENDENT: same eta at a DEPENDENT function type `T = Π (x:Sort1). x`.
    /// Eta triggers is_def_eq's internal type inference, so this runs on the large
    /// stack.
    #[test]
    fn real_is_def_eq_eta_grounds_and_discriminates() {
        use crate::checker_core::run_on_large_stack;

        // Non-Prop function types (so the equality is ETA, not proof irrelevance).
        let fn_ty = Expr::pi(BinderInfo::Default, sort(0), sort(0)); // Sort0 → Sort0 : Sort 1
        let dep_ty = Expr::pi(BinderInfo::Default, sort(1), Expr::bvar(0)); // Π(x:Sort1). x : Sort 2

        // (1) BASIC: λ(f:T). f   vs   λ(f:T). λ(x:Sort0). f x   (f = bvar 1, x = bvar 0).
        let eta_a = Expr::lam(BinderInfo::Default, fn_ty.clone(), Expr::bvar(0));
        let eta_b = Expr::lam(
            BinderInfo::Default,
            fn_ty.clone(),
            Expr::lam(BinderInfo::Default, sort(0), Expr::app(Expr::bvar(1), Expr::bvar(0))),
        );
        // (2) DISCRIMINATION: λ(f:T). f   vs   λ(f:T). λ(x:Sort0). f (f x).
        let dbl_a = Expr::lam(BinderInfo::Default, fn_ty.clone(), Expr::bvar(0));
        let dbl_b = Expr::lam(
            BinderInfo::Default,
            fn_ty,
            Expr::lam(
                BinderInfo::Default,
                sort(0),
                Expr::app(Expr::bvar(1), Expr::app(Expr::bvar(1), Expr::bvar(0))),
            ),
        );
        // (3) DEPENDENT: λ(f:Π(x:Sort1).x). f   vs   λf. λ(x:Sort1). f x.
        let dep_a = Expr::lam(BinderInfo::Default, dep_ty.clone(), Expr::bvar(0));
        let dep_b = Expr::lam(
            BinderInfo::Default,
            dep_ty,
            Expr::lam(BinderInfo::Default, sort(1), Expr::app(Expr::bvar(1), Expr::bvar(0))),
        );

        let (basic, double, dependent) = run_on_large_stack(move || {
            (
                real_is_def_eq(&eta_a, &eta_b),
                real_is_def_eq(&dbl_a, &dbl_b),
                real_is_def_eq(&dep_a, &dep_b),
            )
        })
        .expect("real is_def_eq eta calls must complete on the large stack");

        assert!(
            basic,
            "λf. f must be def-eq λf. λx. f x by eta (f neutral, non-Prop function type)"
        );
        assert!(
            !double,
            "λf. f must NOT be def-eq λf. λx. f (f x) — eta expands ONE application, f∘f ≠ f"
        );
        assert!(dependent, "eta must also hold at a DEPENDENT function type Π(x:Sort1). x");
    }

    /// RECURSIVE-recursor IOTA (the minor consumes an induction hypothesis): unlike
    /// the enum `MyBool.rec` (whose minors take no IH), `MyNat.rec` over
    /// `MyNat = zero | succ(MyNat)` has a `succ` minor `(n) (ih) => …` that USES the
    /// recursive result `ih`. The fold `fun n ih => succ (succ ih)` doubles, so
    /// `MyNat.rec … (succ zero)` COMPUTES to `succ (succ zero)` (2) by iota +
    /// recursion. is_def_eq fully normalizes both sides, so it grounds that the real
    /// kernel genuinely runs the recursive recursor — the computed value is `2`, and
    /// it discriminates against `1` and `3`.
    #[test]
    fn real_is_def_eq_iota_computes_recursive_recursor() {
        use crate::checker_core::run_on_large_stack;

        let mynat = Expr::const_(Name::from_string("MyNat"), LevelVec::new());
        let zero = Expr::const_(Name::from_string("MyNat.zero"), LevelVec::new());
        let succ = Expr::const_(Name::from_string("MyNat.succ"), LevelVec::new());
        let s = |e: Expr| Expr::app(succ.clone(), e); // succ applied
        let (num1, num2, num3) = (s(zero.clone()), s(s(zero.clone())), s(s(s(zero.clone()))));

        // MyNat.rec.{1} (fun _ => MyNat) zero (fun n ih => succ (succ ih)) (succ zero)
        let motive = Expr::lam(BinderInfo::Default, mynat.clone(), mynat.clone());
        let minor_succ = Expr::lam(
            BinderInfo::Default,
            mynat.clone(),
            Expr::lam(BinderInfo::Default, mynat.clone(), s(s(Expr::bvar(0)))), // n=bvar1, ih=bvar0
        );
        let rec_app = Expr::apps(
            Expr::const_(Name::from_string("MyNat.rec"), vec![Level::succ(Level::zero())]),
            [motive, zero.clone(), minor_succ, num1.clone()],
        );

        let (is_two, is_one, is_three) = run_on_large_stack(move || {
            let mut env = Environment::new();
            let dt = Expr::const_(Name::from_string("MyNat"), LevelVec::new());
            env.add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("MyNat"),
                    type_: Expr::type_(),
                    constructors: vec![
                        Constructor { name: Name::from_string("MyNat.zero"), type_: dt.clone() },
                        Constructor {
                            name: Name::from_string("MyNat.succ"),
                            type_: Expr::pi(BinderInfo::Default, dt.clone(), dt.clone()),
                        },
                    ],
                }],
            })
            .expect("register MyNat inductive");
            let tc = TypeChecker::with_mode(&env, env.mode());
            (
                tc.is_def_eq(&rec_app, &num2),
                tc.is_def_eq(&rec_app, &num1),
                tc.is_def_eq(&rec_app, &num3),
            )
        })
        .expect("real is_def_eq recursive-recursor calls must complete on the large stack");

        assert!(
            is_two,
            "MyNat.rec doubling (succ zero) must COMPUTE to succ (succ zero) = 2 (recursive iota)"
        );
        assert!(!is_one, "the recursive recursor's result 2 must NOT be def-eq 1");
        assert!(!is_three, "the recursive recursor's result 2 must NOT be def-eq 3");
    }

    /// INDEXED-FAMILY recursor iota — the J rule (`Eq.rec`, the equality
    /// eliminator): `Eq.rec α a motive minor a (Eq.refl a)` iota-reduces to
    /// `minor`. `Eq` is indexed by its second argument, and `Eq.rec` (provided by
    /// `env.init_eq()`, repaired to Lean 4's promoted-singleton form) is the
    /// canonical INDEXED recursor — distinct from the parameter-only `MyBool`/
    /// `MyNat` recursors. With `α = Sort 3`, `a = Sort 2`, motive
    /// `λ (x) (h : Eq a x). Sort 2`, minor `Sort 1`, the recursor applied to the
    /// canonical `Eq.refl a` computes to the minor `Sort 1`. Validated via
    /// is_def_eq (full normalization drives the iota) with a discrimination against
    /// `Sort 2`. (Signature/arg-order verified against the kernel's core_eq
    /// recursor generation and its own iota test.)
    #[test]
    fn real_is_def_eq_iota_computes_indexed_eq_rec_j_rule() {
        use crate::checker_core::run_on_large_stack;

        // lvl(n) = the universe level n (succ^n zero).
        let lvl = |n: u32| {
            let mut l = Level::zero();
            for _ in 0..n {
                l = Level::succ(l);
            }
            l
        };
        // motive := λ (x : Sort 3) (h : @Eq.{4} (Sort 3) (Sort 2) x). Sort 2   (Sort v, v = 3)
        let h_ty = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![lvl(4)]),
            [sort(3), sort(2), Expr::bvar(0)],
        );
        let motive =
            Expr::lam(BinderInfo::Default, sort(3), Expr::lam(BinderInfo::Default, h_ty, sort(2)));
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![lvl(4)]),
            [sort(3), sort(2)],
        );
        // @Eq.rec.{v=3, u=4} (Sort 3=α) (Sort 2=a) motive (Sort 1=minor) (Sort 2=b) (Eq.refl α a)
        let rec_app = Expr::apps(
            Expr::const_(Name::from_string("Eq.rec"), vec![lvl(3), lvl(4)]),
            [sort(3), sort(2), motive, sort(1), sort(2), refl],
        );
        let expected = sort(1); // iota reduct = the minor
        let wrong = sort(2); // discrimination

        let (is_minor, is_wrong) = run_on_large_stack(move || {
            let mut env = Environment::new();
            env.init_eq().expect("init_eq registers Eq/Eq.refl/Eq.rec");
            let tc = TypeChecker::with_mode(&env, env.mode());
            (tc.is_def_eq(&rec_app, &expected), tc.is_def_eq(&rec_app, &wrong))
        })
        .expect("real is_def_eq Eq.rec (J rule) calls must complete on the large stack");

        assert!(
            is_minor,
            "Eq.rec α a motive minor a (Eq.refl a) must IOTA-reduce (J rule) to the minor Sort 1"
        );
        assert!(!is_wrong, "the J-rule reduct Sort 1 must NOT be def-eq Sort 2 (discrimination)");
    }

    /// NO MASQUERADE (Pi congruence with subterm reduction): the REAL is_def_eq
    /// recurses into a `Pi`'s DOMAIN and CODOMAIN and reduces each — a `Pi` whose
    /// domain (or codomain) is a redex reducing to `Sort 0` is def-eq to the plain
    /// `Pi Sort0 Sort0`, yet a Pi whose domain reduces to `Sort 0` is NOT def-eq to
    /// one with domain `Sort 1`. Structural congruence AND subterm reduction, both
    /// load-bearing.
    #[test]
    fn real_is_def_eq_pi_congruence_reduces_subterms() {
        let redex = beta_redex_reducing_to_sort0(); // → Sort 0
        let plain = Expr::pi(BinderInfo::Default, sort(0), sort(0));
        assert!(
            real_is_def_eq(&Expr::pi(BinderInfo::Default, sort(0), redex.clone()), &plain),
            "Pi with a codomain reducing to Sort 0 must be def-eq Pi Sort0 Sort0"
        );
        assert!(
            real_is_def_eq(&Expr::pi(BinderInfo::Default, redex.clone(), sort(0)), &plain),
            "Pi with a domain reducing to Sort 0 must be def-eq Pi Sort0 Sort0"
        );
        assert!(
            !real_is_def_eq(
                &Expr::pi(BinderInfo::Default, redex, sort(0)),
                &Expr::pi(BinderInfo::Default, sort(1), sort(0))
            ),
            "Pi domain reducing to Sort 0 must NOT be def-eq Pi with domain Sort 1"
        );
    }

    /// SYMMETRY of the REAL `is_def_eq`: the clean_kernel def-eq verdict must not
    /// depend on argument order. For a def-eq pair that is NOT syntactically
    /// identical — the beta redex `(λ (x:Sort 1). x) (Sort 0)` and its reduct
    /// `Sort 0` — the real checker must answer `true` in BOTH orders. For a
    /// non-def-eq pair — `Sort 0` (Prop) vs `Sort 1` (Type) — it must answer
    /// `false` in BOTH orders. The equality `is_def_eq(a,b) == is_def_eq(b,a)` is
    /// asserted directly, so an asymmetric checker (e.g. one comparing universe
    /// levels with `<=` instead of `==`, which would accept `Sort 0 ≟ Sort 1` one
    /// way only) is caught. This grounds symmetry per-input on the real fn, which
    /// the existing reduction-direction fixtures do NOT (they check each direction
    /// against its own hardcoded expectation, never one order against the other,
    /// and never observe a negative pair in both orders).
    #[test]
    fn real_is_def_eq_symmetry_grounds_and_discriminates() {
        // POSITIVE: def-eq but syntactically distinct — a redex vs its reduct.
        let redex = beta_redex_reducing_to_sort0();
        let reduct = sort(0);
        assert_ne!(
            redex, reduct,
            "guard: positive pair must be syntactically DISTINCT so symmetry is non-trivial"
        );
        let fwd = real_is_def_eq(&redex, &reduct);
        let bwd = real_is_def_eq(&reduct, &redex);
        assert!(fwd, "is_def_eq(redex, reduct) must hold — the redex beta-reduces to Sort 0");
        assert!(bwd, "is_def_eq(reduct, redex) must hold — the redex reduces on the RHS too");
        assert_eq!(fwd, bwd, "SYMMETRY: def-eq verdict must be identical in both argument orders");

        // DISCRIMINATION: NOT def-eq — distinct universes; must be false BOTH ways.
        // An asymmetric checker that accepts one direction only is caught here.
        let s0 = sort(0);
        let s1 = sort(1);
        assert_ne!(s0, s1, "guard: discrimination pair must be distinct universes");
        let neg_fwd = real_is_def_eq(&s0, &s1);
        let neg_bwd = real_is_def_eq(&s1, &s0);
        assert!(!neg_fwd, "Sort 0 ≟ Sort 1 must be REJECTED (distinct universes)");
        assert!(
            !neg_bwd,
            "Sort 1 ≟ Sort 0 must be REJECTED — an is_def_eq that accepts one way only is caught"
        );
        assert_eq!(
            neg_fwd, neg_bwd,
            "SYMMETRY: non-def-eq verdict must be identical in both argument orders"
        );
    }

    /// TRANSITIVITY of the REAL is_def_eq, composed across DIFFERENT reduction
    /// mechanisms: if the literal function relates `a ≈ b` and `b ≈ c`, it must
    /// relate `a ≈ c`. The chain is built so the two legs fire on DISTINCT
    /// machinery — leg 1 is BETA (`a = (λ x. x)(Sort 0)` whnf-reduces to
    /// `b = Sort 0`) and leg 2 is DELTA (`b = Sort 0` is what `c = Const TransDef`
    /// unfolds to, for the reducible definition `TransDef : Sort 1 := Sort 0`).
    /// So `a ≈ c` forces is_def_eq to COMPOSE a beta reduction on the left with a
    /// delta unfolding on the right (neither `a` nor `c` is a bare `Sort`): the
    /// transitive edge is not free — both mechanisms are load-bearing.
    ///
    /// Each is_def_eq call runs on its OWN fresh `TypeChecker` (hence its own
    /// `equiv_manager`), so the positive `a ≈ c` verdict CANNOT be short-circuited
    /// by the cross-call union-find amortization that the `a ≈ b` and `b ≈ c` calls
    /// would otherwise populate — `is_def_eq_impl` consults `equiv_manager.is_equiv`
    /// at entry (def_eq/mod.rs) and records every positive result, so a shared
    /// checker would answer `a ≈ c` from the union-find's transitive closure without
    /// running either whnf path. Fresh checkers force `a ≈ c` to genuinely reduce.
    ///
    /// DISCRIMINATION (transitivity is NOT vacuous): a second triple keeps
    /// `a ≈ b` (beta) but breaks the pivot, `b ≉ c2` (`b = Sort 0`, `c2 = Sort 1`,
    /// distinct universes). The real function must then return `a ≉ c2`
    /// (`(λ x. x)(Sort 0)` reduces to Sort 0, which is not def-eq Sort 1).
    #[test]
    fn real_is_def_eq_transitivity_grounds_and_discriminates() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("Trust.Certify.TransDef"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())), // Sort 1
            value: sort(0),
            is_reducible: true,
        })
        .expect("register reducible TransDef := Sort 0");

        // Fresh TypeChecker (its own equiv_manager) per call, so no cross-call
        // union-find amortization can short-circuit the composed `a ≈ c` verdict —
        // it must genuinely compose beta (left) with delta (right).
        let deq = |a: &Expr, b: &Expr| -> bool {
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.is_def_eq(a, b)
        };

        // POSITIVE chain a --(beta)--> b --(delta)--> c, every term equal to Sort 0.
        let a = beta_redex_reducing_to_sort0(); // (λ x. x)(Sort 0)  →β Sort 0
        let b = sort(0); // Sort 0
        let c = Expr::const_(Name::from_string("Trust.Certify.TransDef"), LevelVec::new()); // →δ Sort 0

        let ab = deq(&a, &b); // leg 1: beta
        let bc = deq(&b, &c); // leg 2: delta
        let ac = deq(&a, &c); // composed: beta + delta (fresh equiv_manager)

        assert!(ab, "leg 1 must hold: (λ x. x)(Sort 0) ≈ Sort 0 by beta");
        assert!(bc, "leg 2 must hold: Sort 0 ≈ Const TransDef by delta unfolding");
        assert!(
            ac,
            "TRANSITIVITY: a ≈ b (beta) and b ≈ c (delta) must force a ≈ c — \
             (λ x. x)(Sort 0) ≈ Const TransDef, composing BOTH mechanisms"
        );

        // DISCRIMINATION: keep a ≈ b (beta) but break the pivot b ≉ c2, so a ≉ c2.
        let c2 = sort(1); // Sort 1
        let bc2 = deq(&b, &c2); // must be FALSE: Sort 0 ≠ Sort 1
        let ac2 = deq(&a, &c2); // must be FALSE: (λ x. x)(Sort 0) →β Sort 0 ≠ Sort 1

        assert!(ab, "discrimination reuses leg a ≈ b (beta), which still holds");
        assert!(!bc2, "discrimination pivot: Sort 0 must NOT be def-eq Sort 1");
        assert!(
            !ac2,
            "TRANSITIVITY NOT VACUOUS: with the pivot broken (b ≉ c2) the real \
             is_def_eq must return a ≉ c2 — (λ x. x)(Sort 0) reduces to Sort 0, not Sort 1"
        );
    }
}
