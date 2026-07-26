// trust-certify: CHECKER-CORE whnf FUNCTION-grounding lane.
//
// Grounds the REAL Rust `clean_kernel::TypeChecker::whnf(e) -> Expr` — the
// weak-head-normalization operation of the recursive checker core (the
// `infer_type <-> whnf <-> is_def_eq` cluster) — by CALLING it on concrete terms
// and observing its genuine REDUCT.
//
// This complements the two sibling whnf-related lanes rather than duplicating
// them: `checker_core_is_whnf` grounds the is_whnf PREDICATE on statically-known
// WHNF heads (is the result already in WHNF), and `checker_core_lemma`'s
// `whnf_idempotent` / `tc_whnf_idempotent` are MODEL-LEVEL / KernelState-surface
// FOR-ALL correctness lemmas. THIS lane grounds the real whnf FUNCTION's actual
// REDUCTION behaviour — that it genuinely fires a redex and leaves a normal form
// fixed — AND, via `real_whnf_idempotence_grounds_and_discriminates`, grounds
// whnf IDEMPOTENCE per-input on the literal Rust fn (whnf(whnf(e)) == whnf(e) for
// a two-step redex), the literal-Rust companion to those model-level idempotence
// lemmas.
//
//   * REDUCTION: whnf of a well-typed beta redex `(λ (x : Sort 1). x) (Sort 0)`
//     MUST reduce to `Sort 0` — AND the reduct must NOT still be the redex (it
//     genuinely reduced, not a no-op) NOR the wrong reduct `Sort 1`.
//   * FIXPOINT: whnf of a term ALREADY in weak-head normal form (a `Sort`, a
//     `Pi`) returns it UNCHANGED.
//
// A whnf that returned its input unchanged (a no-op) would fail the reduction
// fixture; one that returned garbage would fail both. Requiring at least one
// genuine reduction and one fixpoint keeps the lane non-vacuous, so it reads the
// real function's genuine, discriminating reduction output — never a rubber stamp.
//
// GROUNDING SCOPE (stated with full honesty): PER-INPUT observation of the real
// Rust whnf on concrete closed inputs — differential-grade fidelity evidence
// about the literal function (same epistemic character as the
// `checker_core_infer_type_fn` / `checker_core_is_def_eq_fn` lanes and
// clean-verify's fidelity gate), NOT a for-all proof of whnf's correctness. That
// universal fact needs the recursive-function functional-VC from the literal Rust
// MIR (the recursive-kernel-fn path that does not exist yet). This lane retires
// no axiom; it grounds the real function on a finite, discriminating fixture set.
// The Sort/BVar/Lam/Pi/App fixtures never consult the environment, so
// `Environment::new()` is a faithful context for them; the delta test additionally
// registers a definition and reads whnf's env-consulting (delta) behaviour.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

/// One concrete input exercised against the REAL Rust `whnf`, with the reduct
/// the real function MUST return and whether the input is expected to reduce
/// (`reduces = true`) or be a fixpoint (`reduces = false`).
#[derive(Clone)]
pub struct WhnfFnFixture {
    /// Human description of the conceptual reduction.
    pub label: &'static str,
    /// The input term.
    pub input: Expr,
    /// The weak-head normal form the real function MUST produce.
    pub expected: Expr,
    /// `true` if the input is a redex that must strictly change under whnf;
    /// `false` if the input is already WHNF and must be returned unchanged.
    pub reduces: bool,
}

/// `Sort n` (n = universe level; `sort(0)` is `Prop`).
fn sort(n: u32) -> Expr {
    let mut level = Level::zero();
    for _ in 0..n {
        level = Level::succ(level);
    }
    Expr::sort(level)
}

/// A well-typed beta redex `(λ (x : Sort 1). x) (Sort 0)` whose weak-head reduct
/// is `Sort 0`.
fn beta_redex_reducing_to_sort0() -> Expr {
    Expr::app(Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(0)), sort(0))
}

/// A well-typed term needing TWO head-reduction steps to reach WHNF:
/// `(λ (x : Sort 1). x) ((λ (y : Sort 1). y) (Sort 0))`. The outer redex reduces
/// to the inner redex `(λ y. y) (Sort 0)`, which is ITSELF a redex; only a whnf
/// that ITERATES (reduces the head until it is no longer a redex) reaches
/// `Sort 0`. A single-step reducer would stop at the inner redex.
fn two_step_beta_redex_to_sort0() -> Expr {
    let inner = beta_redex_reducing_to_sort0(); // (λ y. y) (Sort 0)
    Expr::app(Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(0)), inner)
}

/// A two-argument application SPINE whose weak-head reduct is its FIRST argument:
/// `((λ (x : Sort 1). λ (y : Sort 1). x) (Sort 0)) (Π Sort0 Sort0)`. The head
/// `λ x. λ y. x` is the K combinator (returns the first arg); reducing the spine
/// takes TWO beta steps and yields `Sort 0` — NOT the second argument, and not
/// the intermediate `λ y. Sort 0`. Grounds whnf reducing a multi-argument spine.
fn k_spine_reducing_to_sort0() -> Expr {
    // λ (x : Sort 1). λ (y : Sort 1). x     (body `x` is bvar 1 under two binders)
    let k = Expr::lam(
        BinderInfo::Default,
        sort(1),
        Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(1)),
    );
    // ((K) (Sort 0)) (Π Sort0 Sort0)  — first arg Sort 0, second arg a distinct Pi.
    Expr::app(Expr::app(k, sort(0)), Expr::pi(BinderInfo::Default, sort(0), sort(0)))
}

/// A ZETA (let) redex whose weak-head reduct is `Sort 0`:
/// `let (x : Sort 1) := Sort 0 in x`. Zeta reduction substitutes the bound value
/// for the body variable — `x[x := Sort 0] = Sort 0`. Grounds whnf's let/zeta
/// reduction (distinct from beta and delta).
fn let_zeta_reducing_to_sort0() -> Expr {
    Expr::let_named(Name::anon(), sort(1), sort(0), Expr::bvar(0), false)
}

/// Call the REAL `clean_kernel::TypeChecker::whnf` on `e` in a minimal
/// environment and return its actual reduct.
fn real_whnf(e: &Expr) -> Expr {
    let env = Environment::new();
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(e)
}

/// The grounding fixtures for the real `whnf`: a genuine reduction and fixpoints.
#[must_use]
pub fn whnf_fn_fixtures() -> Vec<WhnfFnFixture> {
    vec![
        WhnfFnFixture {
            label: "whnf((λ x. x) (Sort 0)) = Sort 0 (beta reduction)",
            input: beta_redex_reducing_to_sort0(),
            expected: sort(0),
            reduces: true,
        },
        WhnfFnFixture {
            label: "whnf((λ x. x) ((λ y. y) (Sort 0))) = Sort 0 (ITERATED, two steps)",
            input: two_step_beta_redex_to_sort0(),
            expected: sort(0),
            reduces: true,
        },
        WhnfFnFixture {
            label: "whnf(((λ x. λ y. x) (Sort 0)) (Π Sort0 Sort0)) = Sort 0 (K-SPINE, two args)",
            input: k_spine_reducing_to_sort0(),
            expected: sort(0),
            reduces: true,
        },
        WhnfFnFixture {
            label: "whnf(let (x : Sort 1) := Sort 0 in x) = Sort 0 (ZETA / let reduction)",
            input: let_zeta_reducing_to_sort0(),
            expected: sort(0),
            reduces: true,
        },
        WhnfFnFixture {
            label: "whnf(Sort 0) = Sort 0 (already WHNF)",
            input: sort(0),
            expected: sort(0),
            reduces: false,
        },
        WhnfFnFixture {
            label: "whnf(Pi Sort0 Sort0) = Pi Sort0 Sort0 (already WHNF)",
            input: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            expected: Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            reduces: false,
        },
    ]
}

/// Certify — at the level of the REAL Rust `whnf` FUNCTION — that on every
/// fixture the real reduct equals `expected`, AND every `reduces = true` input
/// genuinely CHANGED (whnf is not a no-op) while every `reduces = false` input
/// was returned UNCHANGED. Returns `true` iff all of that holds and the fixture
/// set contains both a reduction and a fixpoint (non-vacuous). Fail-closed on any
/// mismatch.
#[must_use]
pub fn certify_real_whnf_fn() -> bool {
    let fixtures = whnf_fn_fixtures();
    let has_reduction = fixtures.iter().any(|f| f.reduces);
    let has_fixpoint = fixtures.iter().any(|f| !f.reduces);
    if !has_reduction || !has_fixpoint {
        return false;
    }
    fixtures.iter().all(|f| {
        let out = real_whnf(&f.input);
        // The reduct must equal the expected weak-head normal form.
        if out != f.expected {
            return false;
        }
        // A redex must strictly change; a WHNF term must be returned unchanged.
        if f.reduces { out != f.input } else { out == f.input }
    })
}

#[cfg(test)]
mod tests {
    use clean_kernel::{Constructor, Declaration, InductiveDecl, InductiveType, LevelVec, Name};

    use super::*;

    /// FUNCTION-level grounding: the real Rust `whnf` produces the expected
    /// reduct on every fixture, genuinely reducing redexes and fixing normal
    /// forms — reading the discriminating output of the literal function.
    #[test]
    fn real_whnf_fn_grounds_and_discriminates() {
        assert!(
            certify_real_whnf_fn(),
            "the real Rust whnf must reduce/fix every fixture as expected"
        );
    }

    /// NO MASQUERADE (reduction): the REAL whnf strictly reduces a beta redex —
    /// `(λ x. x) (Sort 0)` becomes `Sort 0` and is NO LONGER the redex.
    #[test]
    fn real_whnf_reduces_beta_redex() {
        let redex = beta_redex_reducing_to_sort0();
        let out = real_whnf(&redex);
        assert_eq!(out, sort(0), "beta redex must whnf to Sort 0");
        assert_ne!(out, redex, "whnf must genuinely reduce the redex, not no-op");
    }

    /// NO MASQUERADE (iteration): the REAL whnf reduces a TWO-step redex all the
    /// way to `Sort 0` — it does not stop at the intermediate inner redex
    /// `(λ y. y) (Sort 0)`. This witnesses that whnf ITERATES head reduction to a
    /// fixpoint (the recursive/loop behaviour), not a single beta step.
    #[test]
    fn real_whnf_iterates_to_fixpoint() {
        let two_step = two_step_beta_redex_to_sort0();
        let out = real_whnf(&two_step);
        assert_eq!(out, sort(0), "two-step redex must whnf all the way to Sort 0");
        assert_ne!(out, two_step, "whnf must reduce, not no-op");
        assert_ne!(
            out,
            beta_redex_reducing_to_sort0(),
            "whnf must NOT stop at the intermediate inner redex — it iterates"
        );
    }

    /// NO MASQUERADE (application spine): the REAL whnf reduces a two-argument
    /// K-combinator spine `((λ x. λ y. x) (Sort 0)) (Π Sort0 Sort0)` to its FIRST
    /// argument `Sort 0` — not the second argument (the `Pi`), and not the
    /// intermediate `λ y. Sort 0`. Grounds reduction across an argument spine.
    #[test]
    fn real_whnf_reduces_application_spine() {
        let spine = k_spine_reducing_to_sort0();
        let out = real_whnf(&spine);
        assert_eq!(out, sort(0), "K-spine must whnf to its first argument Sort 0");
        assert_ne!(
            out,
            Expr::pi(BinderInfo::Default, sort(0), sort(0)),
            "whnf must NOT return the SECOND argument — K returns the first"
        );
        assert_ne!(out, spine, "whnf must genuinely reduce the spine, not no-op");
    }

    /// IOTA reduction (recursor on a constructor): registers `MyBool = MyTrue |
    /// MyFalse`, builds the boolean-`not` fold `MyBool.rec (fun _ => MyBool) MyFalse
    /// MyTrue MyTrue`, and grounds that the REAL whnf IOTA-reduces the recursor
    /// applied to the constructor `MyTrue` to the matching minor `MyFalse`. Iota is
    /// the fourth core reduction rule (beside beta/delta/zeta), and the reduct is a
    /// distinct constructor, so the observation is discriminating.
    #[test]
    fn real_whnf_iota_reduces_recursor_on_constructor() {
        let my_true = Expr::const_(Name::from_string("MyBool.MyTrue"), LevelVec::new());
        let my_false = Expr::const_(Name::from_string("MyBool.MyFalse"), LevelVec::new());
        let out = {
            let mut env = Environment::new();
            let dt_ref = Expr::const_(Name::from_string("MyBool"), LevelVec::new());
            env.add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("MyBool"),
                    type_: Expr::type_(), // Type = Sort 1
                    constructors: vec![
                        Constructor {
                            name: Name::from_string("MyBool.MyTrue"),
                            type_: dt_ref.clone(),
                        },
                        Constructor {
                            name: Name::from_string("MyBool.MyFalse"),
                            type_: dt_ref.clone(),
                        },
                    ],
                }],
            })
            .expect("register MyBool inductive");
            // motive `fun (_ : MyBool) => MyBool` (u = 1); minors are the SWAPPED
            // constructors (the `not` fold); major `MyTrue` selects the first minor.
            let motive = Expr::lam(BinderInfo::Default, dt_ref.clone(), dt_ref.clone());
            let rec_app = Expr::apps(
                Expr::const_(Name::from_string("MyBool.rec"), vec![Level::succ(Level::zero())]),
                [motive, my_false.clone(), my_true.clone(), my_true.clone()],
            );
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.whnf(&rec_app)
        };
        assert_eq!(
            out, my_false,
            "MyBool.rec (not) applied to MyTrue must IOTA-reduce to the MyFalse minor"
        );
        assert_ne!(out, my_true, "the iota reduct must be the MATCHING minor, not the major");
    }

    /// IOTA with a DEPENDENT motive: the motive genuinely uses the scrutinee, so
    /// the two minors have DIFFERENT types (`motive MyTrue ≡ MyBool` a datatype,
    /// `motive MyFalse ≡ Sort 0` a proposition universe) — an elimination only a
    /// DEPENDENT motive can type. The motive is itself a large-elimination fold
    /// `fun (b : MyBool) => MyBool.rec.{2} (fun _ => Sort 1) MyBool Sort0 b`.
    /// The REAL whnf iota-reduces the recursor on `MyTrue` to the `MyBool`-typed
    /// minor `MyFalse`, AND the REAL infer_type assigns the recursor application
    /// the DEPENDENT return type `motive MyTrue ≡ MyBool` — the witness the
    /// dependent elimination is genuinely well-formed, not just reducible.
    #[test]
    fn real_whnf_iota_reduces_dependent_motive_recursor() {
        let my_true = Expr::const_(Name::from_string("MyBool.MyTrue"), LevelVec::new());
        let my_false = Expr::const_(Name::from_string("MyBool.MyFalse"), LevelVec::new());
        let mybool = Expr::const_(Name::from_string("MyBool"), LevelVec::new());
        let rec_name = Name::from_string("MyBool.rec");
        let level1 = Level::succ(Level::zero());
        let level2 = Level::succ(Level::succ(Level::zero()));

        // DEPENDENT motive: fun (b : MyBool) =>
        //     MyBool.rec.{2} (fun _ => Sort 1) MyBool Sort0 b
        //   motive MyTrue  ≡ MyBool  (datatype),   motive MyFalse ≡ Sort 0 (a Prop universe).
        let inner_motive = Expr::lam(BinderInfo::Default, mybool.clone(), sort(1));
        let motive_body = Expr::apps(
            Expr::const_(rec_name.clone(), vec![level2]),
            [inner_motive, mybool.clone(), sort(0), Expr::bvar(0)], // b = the motive binder
        );
        let motive = Expr::lam(BinderInfo::Default, mybool.clone(), motive_body);

        // Outer: MyBool.rec.{1} motive (MyFalse : motive MyTrue ≡ MyBool)
        //                              (Π(z:Sort0).z : motive MyFalse ≡ Sort 0) MyTrue
        let prop = Expr::pi(BinderInfo::Default, sort(0), Expr::bvar(0)); // Π (z:Sort0). z : Sort 0
        let rec_app = Expr::apps(
            Expr::const_(rec_name, vec![level1]),
            [motive, my_false.clone(), prop, my_true.clone()],
        );

        let (whnf_out, infer_ty, infer_ty_whnf) = {
            let mut env = Environment::new();
            let dt_ref = mybool.clone();
            env.add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("MyBool"),
                    type_: Expr::type_(),
                    constructors: vec![
                        Constructor {
                            name: Name::from_string("MyBool.MyTrue"),
                            type_: dt_ref.clone(),
                        },
                        Constructor {
                            name: Name::from_string("MyBool.MyFalse"),
                            type_: dt_ref.clone(),
                        },
                    ],
                }],
            })
            .expect("register MyBool inductive");
            let tc = TypeChecker::with_mode(&env, env.mode());
            let inferred = tc.infer_type(&rec_app).ok();
            let inferred_whnf = inferred.as_ref().map(|t| tc.whnf(t));
            (tc.whnf(&rec_app), inferred, inferred_whnf)
        };
        assert_eq!(
            whnf_out, my_false,
            "dependent-motive recursor on MyTrue must IOTA-reduce to the MyBool-typed minor MyFalse"
        );
        // The dependent elimination is well-formed: infer_type SUCCEEDS and assigns
        // the DEPENDENT return type `motive MyTrue` (returned as the unreduced
        // application `(fun b => ...) MyTrue`).
        assert!(
            infer_ty.is_some(),
            "the dependent elimination must be well-formed — infer_type succeeds \
             (its type is the dependent `motive MyTrue`)"
        );
        // …and that dependent return type NORMALIZES (beta then iota) to MyBool.
        assert_eq!(
            infer_ty_whnf,
            Some(mybool),
            "the dependent return type `motive MyTrue` must normalize (beta+iota) to MyBool"
        );
    }

    /// NO MASQUERADE (zeta): the REAL whnf performs LET reduction — `let x := Sort 0
    /// in x` substitutes the bound value and yields `Sort 0`, genuinely reducing
    /// (not returning the let). Grounds zeta, the reduction rule for `let`.
    #[test]
    fn real_whnf_reduces_let_zeta() {
        let z = let_zeta_reducing_to_sort0();
        let out = real_whnf(&z);
        assert_eq!(out, sort(0), "let (x := Sort 0) in x must zeta-reduce to Sort 0");
        assert_ne!(out, z, "whnf must genuinely zeta-reduce the let, not no-op");
    }

    /// DELTA reduction + REDUCIBILITY (environment-consulting): a REDUCIBLE
    /// definition `MyDef : Sort 1 := Sort 0` unfolds under whnf to `Sort 0`, while
    /// an OPAQUE constant `MyOpaque : Sort 1 := Sort 0` (value hidden) stays STUCK
    /// — whnf returns it unchanged. Grounds delta reduction AND the reducibility
    /// distinction the earlier beta-only fixtures never exercised.
    #[test]
    fn real_whnf_delta_unfolds_reducible_not_opaque() {
        let (def_out, opaque_out) = {
            let mut env = Environment::new();
            env.add_decl(Declaration::Definition {
                name: Name::from_string("Trust.Certify.MyDef"),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())),
                value: sort(0),
                is_reducible: true,
            })
            .expect("register reducible MyDef");
            env.add_decl(Declaration::Opaque {
                name: Name::from_string("Trust.Certify.MyOpaque"),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())),
                value: sort(0),
            })
            .expect("register opaque MyOpaque");
            let tc = TypeChecker::with_mode(&env, env.mode());
            let def_c = Expr::const_(Name::from_string("Trust.Certify.MyDef"), LevelVec::new());
            let opaque_c =
                Expr::const_(Name::from_string("Trust.Certify.MyOpaque"), LevelVec::new());
            (tc.whnf(&def_c), tc.whnf(&opaque_c))
        };
        assert_eq!(def_out, sort(0), "whnf(Const MyDef) must DELTA-unfold to its value Sort 0");
        let opaque_c = Expr::const_(Name::from_string("Trust.Certify.MyOpaque"), LevelVec::new());
        assert_eq!(
            opaque_out, opaque_c,
            "whnf(Const MyOpaque) must stay STUCK — opaque values are not unfolded"
        );
    }

    /// NO MASQUERADE (fixpoint): the REAL whnf leaves an already-WHNF term
    /// (a `Sort`) unchanged — it does not spuriously rewrite normal forms.
    #[test]
    fn real_whnf_fixes_normal_form() {
        assert_eq!(real_whnf(&sort(0)), sort(0), "whnf of Sort 0 must be Sort 0 unchanged");
    }

    /// IDEMPOTENCE (real fn, per-input): the REAL `TypeChecker::whnf` reaches a
    /// weak-head fixpoint in ONE shot — feeding its own output back through `whnf`
    /// is a structural no-op, `whnf(whnf(e)) == whnf(e)`. To make that fixpoint
    /// claim load-bearing (not the trivial already-WHNF slice that
    /// `real_whnf_fixes_normal_form` already covers), the input is a TWO-step redex
    /// `(λ x. x) ((λ y. y) (Sort 0))`: a whnf that fired only the OUTER beta step
    /// would return the residual inner redex `(λ y. y) (Sort 0)` from the first
    /// call, and the second `whnf` would then reduce it further — making
    /// `twice != once` and FAILING the idempotence assert. A whnf that iterates to
    /// a true fixpoint returns `Sort 0` from both calls.
    /// Discrimination: `once != redex` — the first `whnf` genuinely reduced (a
    /// whnf-is-the-identity stub would leave `once == redex` and fail here), so the
    /// second call's stability is a real fixpoint, not the vacuous identity.
    /// This nests the REAL `real_whnf` call (done by no existing test).
    #[test]
    fn real_whnf_idempotence_grounds_and_discriminates() {
        // Inner redex: (λ (y : Sort 1). y) (Sort 0) — itself a beta redex.
        let inner = Expr::app(Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(0)), sort(0));
        // Outer: (λ (x : Sort 1). x) ((λ y. y) (Sort 0)) — needs TWO head steps to
        // reach the fixpoint `Sort 0`. A single-step reducer stops at `inner`.
        let redex =
            Expr::app(Expr::lam(BinderInfo::Default, sort(1), Expr::bvar(0)), inner.clone());

        // First reduction: drive the REAL whnf and keep the returned Expr.
        let once = real_whnf(&redex);
        // Second reduction: feed the (claimed) weak-head normal form back through whnf.
        let twice = real_whnf(&once);

        // POSITIVE — idempotence / true fixpoint: whnf(whnf(e)) == whnf(e).
        // A whnf that stopped one head-step early (leaving the residual inner redex)
        // would make `twice != once` and fail here.
        assert_eq!(twice, once, "whnf must be idempotent: re-reducing its own output is a no-op",);
        // The first whnf must actually reach the fully-reduced `Sort 0`, not stop at
        // the intermediate inner redex — this is what makes the SECOND whnf call
        // load-bearing rather than a trivial already-WHNF fixpoint.
        assert_eq!(once, sort(0), "whnf must iterate the two-step redex all the way to Sort 0",);
        assert_ne!(once, inner, "whnf must NOT stop at the intermediate inner redex — it iterates",);

        // DISCRIMINATION — non-triviality: the first whnf genuinely reduced.
        // A whnf that returned its input unchanged (the identity) would satisfy the
        // idempotence assert vacuously but fail this one.
        assert_ne!(
            once, redex,
            "first whnf must genuinely reduce the redex (else idempotence is vacuous)",
        );
    }

    /// PRESERVATION / SUBJECT REDUCTION on the REAL fns — the literal-Rust per-input
    /// companion to the model-level `beta_reduces_preserves_typing` / `tc_subject_
    /// reduction`: whnf-reducing a well-typed term PRESERVES its type. For a well-typed
    /// `e` with `T = infer_type(e)`, the real whnf reduct `e' = whnf(e)` still checks
    /// against `T` — `check_type(whnf(e), infer_type(e)) = Ok`. Grounded on a beta redex
    /// so preservation is non-trivial (`e' != e`, the reduction genuinely fired).
    /// DISCRIMINATION: the reduct is REJECTED against a wrong type (`Sort 2`), so
    /// `check_type` is discriminating and preservation is a genuine fact.
    #[test]
    fn real_whnf_preserves_typing() {
        // e = (λ (x : Sort 1). x) (Sort 0): well-typed with type Sort 1; whnf(e) = Sort 0,
        // which also has type Sort 1 — so whnf preserved the type.
        let e = beta_redex_reducing_to_sort0();
        let env = Environment::new();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let t = tc.infer_type(&e).expect("the redex is well-typed"); // Sort 1
        let e2 = tc.whnf(&e); // Sort 0
        assert_ne!(
            e2, e,
            "guard: whnf genuinely reduced the redex, so preservation is non-trivial"
        );
        assert!(
            tc.check_type(&e2, &t).is_ok(),
            "PRESERVATION: the whnf reduct must still have the ORIGINAL inferred type"
        );

        // DISCRIMINATION: the reduct must NOT check against a wrong type.
        assert!(
            tc.check_type(&e2, &sort(2)).is_err(),
            "check_type(whnf reduct, Sort 2) must be REJECTED — check_type discriminates, so \
             preservation above is non-vacuous"
        );
    }
}
