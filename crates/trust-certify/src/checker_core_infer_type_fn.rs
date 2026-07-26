// trust-certify: CHECKER-CORE infer_type FUNCTION-grounding lane (sort arm).
//
// WHAT THIS ADDS OVER `checker_core_infer_sort`.
//
// The sibling `checker_core_infer_sort` lane grounds the JUDGMENT
// `KernelInferAccepts st (Sort l) (Sort (l+1))` — it builds a
// `KernelInferAccepts.sort` proof TERM (a value of clean-verify's model-side
// inductive relation) and kernel-checks it. That certifies the MODEL's
// inference relation, not the real Rust inference FUNCTION.
//
// This lane grounds the real Rust FUNCTION. clean-verify keeps that literal
// function-fidelity problem distinct from its model-side judgments; historical
// named bridge axioms/results in this area have been retired rather than treated
// as live authority. `tc_infer_soundness` is a `DerivedProved` model-side
// infer/check coherence relation, not function fidelity. This lane therefore
// CALLS the real
// `clean_kernel::TypeChecker::infer_type` on a concrete `Sort l` and observes
// that the returned `Expr` is exactly `Sort (l+1)`:
//
//   let tc = TypeChecker::with_mode(&env, env.mode());
//   tc.infer_type(&Expr::sort(l))  ==  Ok(Expr::sort(Level::succ(l)))
//
// This is the SAME kind of real-kernel call the `checker_core` lane makes with
// `check_type`, but on the inference-producing entry point `infer_type`, whose
// OUTPUT we read and compare.
//
// GROUNDING SCOPE (stated with full honesty — load-bearing):
//
//   * This is PER-INPUT FUNCTION GROUNDING. It observes the real Rust
//     `infer_type` function's actual output on the CONCRETE inputs `Sort 0`,
//     `Sort 1`, ... and confirms it equals the model's `Sort (l+1)`. It is
//     genuine fidelity EVIDENCE about the real function (stronger than the
//     judgment lane: it reads the function's real return value), of the same
//     epistemic character as a cross-validation / differential test.
//
//   * It is NOT a FOR-ALL refinement/equality between the model relation and the
//     literal Rust `infer_type` implementation. That universal result requires a
//     functional verification condition extracted from the function's MIR — the
//     recursive-kernel-fn path the trust-loop (trust-ir / trust-cg) does not
//     support today. This per-input evidence retires no axiom; it does not claim
//     to close that missing functional proof.
//
//   * The sort arm is the NON-RECURSIVE base case: `infer_type` returns
//     `Sort (succ l)` directly, consulting neither the environment nor a
//     recursive sub-inference. So this per-input grounding is exact and total
//     for the sort arm's finite fixtures. The RECURSIVE lam/app arms are ALSO
//     per-input-grounded below (`certify_real_infer_fn`): on a concrete closed
//     input the real function runs its recursive sub-inferences to completion
//     and returns a concrete `Expr` we read exactly — same epistemic character
//     as the sort arm. What still needs the functional-VC (not a call) is the
//     FOR-ALL literal-Rust/model refinement, and the env-dependent `const` arm
//     (a call would need a populated environment fixture).
//
//   * SOUNDNESS (infer→check): `real_infer_type_sound_against_check_type` grounds,
//     per-input on the REAL fns, that the type the real `infer_type` produces is one
//     the real `check_type` ACCEPTS (`infer_type(e)=Ok(T) ⟹ check_type(e,T)=Ok`) — the
//     two entry points agree — with `check_type` shown discriminating (it rejects a
//     wrong type). This is the literal-Rust per-input companion to the MODEL-LEVEL
//     flagship `tc_infer_soundness` (KernelInferAccepts ⟹ KernelCheckAccepts) attested
//     in `checker_core_lemma`.
//
// NO MASQUERADE:
//   (1) POSITIVE: the certify fn only returns `true` when the REAL
//       `infer_type(Sort l)` returns a value STRUCTURALLY equal to the model's
//       `Sort (succ l)` — a real function call, real `Expr` structural `==`.
//   (2) WRONG-RESULT CONTROL: the same real output is checked against the WRONG
//       expected result `Sort l` (and `Sort (l+2)`); the match MUST fail. If it
//       matched, the observation would be a rubber stamp rather than reading the
//       function's genuine output.
//   (3) FAIL CLOSED: on a non-sort input whose inference errors (an undefined
//       `Const`), the real `infer_type` returns `Err`, so the sort-fact grounder
//       returns `false` — it never mints a sort fact from a non-sort.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, LevelVec, Name, TypeChecker};

/// A concrete sort-inference operation exercised against the REAL Rust
/// `infer_type`: the kernel inferring the type of `Sort level`, whose real
/// result must be `Sort (succ level)`.
#[derive(Clone)]
pub struct InferSortFnFixture {
    /// Human description of the conceptual operation.
    pub label: &'static str,
    /// The universe level whose sort we infer.
    pub level: Level,
}

/// `infer_type(Sort 0)` — real result must be `Sort 1`.
#[must_use]
pub fn infer_sort0_fn() -> InferSortFnFixture {
    InferSortFnFixture { label: "real infer_type(Sort 0) = Sort 1", level: Level::zero() }
}

/// `infer_type(Sort 1)` — real result must be `Sort 2`.
#[must_use]
pub fn infer_sort1_fn() -> InferSortFnFixture {
    InferSortFnFixture {
        label: "real infer_type(Sort 1) = Sort 2",
        level: Level::succ(Level::zero()),
    }
}

/// Call the REAL `clean_kernel::TypeChecker::infer_type` on `Sort level` in a
/// minimal environment and return its actual output `Expr`. `None` (fail-closed)
/// if the real function errors. The sort arm never consults the environment, so
/// `Environment::new()` is a sufficient and faithful context.
fn real_infer_type_of_sort(level: &Level) -> Option<Expr> {
    let env = Environment::new();
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.infer_type(&Expr::sort(level.clone())).ok()
}

/// FUNCTION-level grounding of the sort arm: returns `true` iff the REAL Rust
/// `infer_type(Sort l)` returns a value structurally equal to `expected`.
/// Fail-closed (`false`) if the real function errors.
fn real_infer_sort_equals(level: &Level, expected: &Expr) -> bool {
    match real_infer_type_of_sort(level) {
        Some(out) => &out == expected,
        None => false,
    }
}

/// Certify — at the level of the REAL Rust `infer_type` FUNCTION — that
/// `infer_type(Sort l) = Sort (l+1)`, with a discriminating wrong-result
/// control. Returns `true` iff:
///   (a) POSITIVE: the real `infer_type(Sort l)` output structurally equals
///       `Sort (succ l)`; AND
///   (b) WRONG-RESULT CONTROL: the real output does NOT equal the wrong result
///       `Sort l`, and does NOT equal the too-high result `Sort (l+2)` — the
///       observation genuinely reads the function's output and is discriminating.
/// Fail-closed on any real-function error.
#[must_use]
pub fn certify_real_infer_sort_fn(fixture: &InferSortFnFixture) -> bool {
    let l = &fixture.level;
    let expected = Expr::sort(Level::succ(l.clone()));

    // (a) POSITIVE: the real function's genuine output equals the model result.
    if !real_infer_sort_equals(l, &expected) {
        return false;
    }

    // (b) WRONG-RESULT CONTROL: the real output must NOT equal the wrong result
    // `Sort l` (off by one low) nor `Sort (l+2)` (off by one high). If either
    // matched, we would not be reading the real output discriminatingly.
    let wrong_low = Expr::sort(l.clone());
    let wrong_high = Expr::sort(Level::succ(Level::succ(l.clone())));
    if real_infer_sort_equals(l, &wrong_low) || real_infer_sort_equals(l, &wrong_high) {
        return false;
    }

    true
}

/// FAIL-CLOSED guard: the real `infer_type` on an undefined `Const` (a non-sort
/// input that cannot be inferred) returns `Err`, so the sort-fact grounder
/// returns `false`. Returns `true` iff the real function genuinely errors on the
/// undefined constant — the witness that this lane never mints a sort fact from
/// a non-sort / uninferable input.
#[must_use]
pub fn non_sort_input_fails_closed() -> bool {
    let env = Environment::new();
    let tc = TypeChecker::with_mode(&env, env.mode());
    // An undefined constant: the real infer_type must error (not fabricate a Sort).
    let undefined = Expr::from_kind(ExprKind::Const(
        Name::from_string("Trust.Certify.NoSuchConst"),
        LevelVec::new(),
    ));
    let errored = tc.infer_type(&undefined).is_err();
    // And the grounder built on it must therefore not equal any sort result:
    // real_infer_sort_equals is sort-only, so cross-check the error directly.
    errored
}

// ---------------------------------------------------------------------------
// RECURSIVE ARMS, per-input: `infer_type` on CONCRETE CLOSED lam / app inputs.
//
// The sort arm above is the non-recursive base case. The recursive arms
// (lam/app/pi) infer sub-terms — but on a CONCRETE CLOSED input the real
// function RUNS TO COMPLETION and returns a concrete `Expr`, so per-input
// grounding of these arms is exactly a call whose output we read (the SAME
// epistemic character as the sort arm — differential evidence about the literal
// function, NOT a for-all literal-Rust/model refinement, which still needs the
// functional-VC). These fixtures pick inputs whose real output is
// UNAMBIGUOUS (no universe `imax` normalization to guess): the lam arm returns a
// `Pi`, the app arm a fixed `Sort`, so structural `==` is exact.
// ---------------------------------------------------------------------------

/// A concrete inference exercised against the REAL Rust `infer_type` on a closed
/// term (any arm), with the exact `Expr` the real function MUST return and a
/// discriminating WRONG result it must NOT return.
#[derive(Clone)]
pub struct InferFnFixture {
    /// Human description of the conceptual operation.
    pub label: &'static str,
    /// The closed input term.
    pub input: Expr,
    /// The `Expr` the real `infer_type` MUST return (structural `==`).
    pub expected: Expr,
    /// A plausible-but-wrong result the real output must NOT equal.
    pub wrong: Expr,
}

/// LAM arm: `infer_type(λ (x : Sort 0). x) = Π (_ : Sort 0). Sort 0` — the
/// identity on `Sort 0`; the body `x` is inferred under the binder (the
/// recursive step) and its type `Sort 0` becomes the codomain.
#[must_use]
pub fn infer_lam_identity_fn() -> InferFnFixture {
    let sort0 = Expr::sort(Level::zero());
    InferFnFixture {
        label: "real infer_type(λ (x:Sort 0). x) = Π (Sort 0). Sort 0",
        input: Expr::lam(BinderInfo::Default, sort0.clone(), Expr::bvar(0)),
        expected: Expr::pi(BinderInfo::Default, sort0.clone(), sort0.clone()),
        // Wrong: the non-dependent arrow with a bumped codomain.
        wrong: Expr::pi(BinderInfo::Default, sort0, Expr::sort(Level::succ(Level::zero()))),
    }
}

/// APP arm: `infer_type((λ (x : Sort 1). x) (Sort 0)) = Sort 1` — applying the
/// identity-on-`Type` to `Sort 0` (which has type `Sort 1`); the function and
/// argument are inferred (the recursive step) and the Π-codomain instantiated.
#[must_use]
pub fn infer_app_identity_fn() -> InferFnFixture {
    let sort1 = Expr::sort(Level::succ(Level::zero()));
    let id_on_type = Expr::lam(BinderInfo::Default, sort1.clone(), Expr::bvar(0));
    InferFnFixture {
        label: "real infer_type((λ (x:Sort 1). x) (Sort 0)) = Sort 1",
        input: Expr::app(id_on_type, Expr::sort(Level::zero())),
        expected: sort1,
        // Wrong: the argument's own type off by one.
        wrong: Expr::sort(Level::zero()),
    }
}

/// `Sort n` as an `Expr`.
fn sortn(n: u32) -> Expr {
    let mut level = Level::zero();
    for _ in 0..n {
        level = Level::succ(level);
    }
    Expr::sort(level)
}

/// PI arm (basic): `infer_type(Π (_ : Sort 0). Sort 0) = Sort 1` — the Pi's type
/// is `Sort (imax (type-of-domain) (type-of-codomain)) = Sort (imax 1 1) = Sort 1`.
/// Grounds the universe rule for dependent products.
#[must_use]
pub fn infer_pi_basic_fn() -> InferFnFixture {
    InferFnFixture {
        label: "real infer_type(Π (Sort 0). Sort 0) = Sort 1",
        input: Expr::pi(BinderInfo::Default, sortn(0), sortn(0)),
        expected: sortn(1),
        wrong: sortn(0),
    }
}

/// PI arm (max picks the domain): `infer_type(Π (_ : Sort 2). Sort 0) = Sort 3`
/// — `imax (type-of Sort 2 = Sort 3) (type-of Sort 0 = Sort 1) = max 3 1 = 3`.
/// Grounds that the universe `max` selects the larger level.
#[must_use]
pub fn infer_pi_max_fn() -> InferFnFixture {
    InferFnFixture {
        label: "real infer_type(Π (Sort 2). Sort 0) = Sort 3 (max picks domain)",
        input: Expr::pi(BinderInfo::Default, sortn(2), sortn(0)),
        expected: sortn(3),
        wrong: sortn(2),
    }
}

/// PI arm (IMPREDICATIVE collapse): `infer_type(Π (_ : Sort 3). (Π (_ : Sort 0). z))
/// = Sort 0` — the inner `Π (z : Sort 0). z` is a PROPOSITION (its type is
/// `Sort (imax 1 0) = Sort 0`), so the outer Pi INTO a Prop is itself a Prop
/// regardless of the domain's `Sort 3`: `imax 4 0 = 0`. Grounds the impredicativity
/// of `Prop` — the subtle `imax _ 0 = 0` rule, NOT the naive `max`.
#[must_use]
pub fn infer_pi_impredicative_fn() -> InferFnFixture {
    // inner: Π (z : Sort 0). z   —   a closed proposition (: Sort 0)
    let prop = Expr::pi(BinderInfo::Default, sortn(0), Expr::bvar(0));
    InferFnFixture {
        label: "real infer_type(Π (Sort 3). (Π (Sort 0). z)) = Sort 0 (impredicative Prop)",
        input: Expr::pi(BinderInfo::Default, sortn(3), prop),
        expected: sortn(0),
        // Wrong: the NAIVE max that ignores the imax-into-Prop collapse.
        wrong: sortn(4),
    }
}

/// Call the REAL `clean_kernel::TypeChecker::infer_type` on a closed term and
/// return its actual output `Expr`. `None` (fail-closed) if the real function
/// errors. These lam/app/pi inputs are closed over `Sort`/`bvar` only, so they
/// never consult the environment — `Environment::new()` is a faithful context.
fn real_infer_type(input: &Expr) -> Option<Expr> {
    let env = Environment::new();
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.infer_type(input).ok()
}

/// Certify — at the level of the REAL Rust `infer_type` FUNCTION — that on the
/// fixture's closed input the real output structurally equals `expected` AND does
/// NOT equal the discriminating `wrong` result. Fail-closed on any real-function
/// error. Reads the genuine output of the recursive arm, never a rubber stamp.
#[must_use]
pub fn certify_real_infer_fn(fixture: &InferFnFixture) -> bool {
    match real_infer_type(&fixture.input) {
        Some(out) => out == fixture.expected && out != fixture.wrong,
        None => false,
    }
}

/// FAIL-CLOSED guard for the recursive arms: an ILL-TYPED application (`Sort 0`
/// applied as if it were a function) cannot be inferred, so the real `infer_type`
/// returns `Err` and the grounder yields `false` — it never fabricates a type for
/// a non-typeable term. Returns `true` iff the real function genuinely errors.
#[must_use]
pub fn ill_typed_app_fails_closed() -> bool {
    // `(Sort 0) (Sort 0)` — the "function" `Sort 0` is not a Π; infer must error.
    let bad = Expr::app(Expr::sort(Level::zero()), Expr::sort(Level::zero()));
    real_infer_type(&bad).is_none()
}

#[cfg(test)]
mod tests {
    use clean_kernel::Declaration;

    use super::*;
    use crate::checker_core::run_on_large_stack;

    /// THE MILESTONE (first FUNCTION-level grounding of the real Rust
    /// `infer_type`): the real `clean_kernel::TypeChecker::infer_type` is CALLED
    /// on `Sort 0` and `Sort 1`, and its genuine output is observed to equal the
    /// model's `Sort (l+1)`, with a discriminating wrong-result control and a
    /// fail-closed guard on a non-sort input.
    ///
    /// Run on the large stack for consistency with the sibling lanes (the debug
    /// `infer_type` cross-validates with the micro-checker and recursively
    /// asserts the type-of-type invariant).
    #[test]
    fn real_infer_sort_fn_grounds_and_fails_closed() {
        let (sort0, sort1, non_sort_closed) = run_on_large_stack(|| {
            (
                certify_real_infer_sort_fn(&infer_sort0_fn()),
                certify_real_infer_sort_fn(&infer_sort1_fn()),
                non_sort_input_fails_closed(),
            )
        })
        .expect("real infer_type calls must complete on the large stack");

        assert!(
            sort0,
            "real infer_type(Sort 0) must return exactly Sort 1 and reject wrong results"
        );
        assert!(
            sort1,
            "real infer_type(Sort 1) must return exactly Sort 2 and reject wrong results"
        );
        assert!(non_sort_closed, "real infer_type on an undefined Const must error (fail closed)");
    }

    /// RECURSIVE ARMS, per-input: the real `infer_type` is CALLED on the closed
    /// lam and app inputs, and its genuine output is observed to equal the exact
    /// expected `Expr` (a `Pi` for the lam arm, a fixed `Sort` for the app arm),
    /// with a discriminating wrong-result control and a fail-closed guard on an
    /// ill-typed application — grounding two RECURSIVE arms of the literal
    /// function beyond the sort base case.
    #[test]
    fn real_infer_recursive_arms_ground_and_fail_closed() {
        let (lam, app, ill_typed_closed) = run_on_large_stack(|| {
            (
                certify_real_infer_fn(&infer_lam_identity_fn()),
                certify_real_infer_fn(&infer_app_identity_fn()),
                ill_typed_app_fails_closed(),
            )
        })
        .expect("real infer_type calls must complete on the large stack");

        assert!(lam, "real infer_type(λ (x:Sort 0). x) must return exactly Π (Sort 0). Sort 0");
        assert!(app, "real infer_type((λ (x:Sort 1). x) (Sort 0)) must return exactly Sort 1");
        assert!(
            ill_typed_closed,
            "real infer_type on an ill-typed application must error (fail closed)"
        );
    }

    /// PI arm, per-input: the real `infer_type` computes the universe of a
    /// dependent product — the basic `imax`, the `max`-picks-the-larger case, and
    /// crucially the IMPREDICATIVE `imax _ 0 = 0` collapse (a `Π` into `Prop` is a
    /// `Prop`). The impredicative fixture's WRONG result is the naive `max` that a
    /// checker missing impredicativity would produce, so this genuinely grounds the
    /// subtle universe rule, not a rubber stamp.
    #[test]
    fn real_infer_pi_arm_grounds_universe_rule() {
        let (basic, max, impredicative) = run_on_large_stack(|| {
            (
                certify_real_infer_fn(&infer_pi_basic_fn()),
                certify_real_infer_fn(&infer_pi_max_fn()),
                certify_real_infer_fn(&infer_pi_impredicative_fn()),
            )
        })
        .expect("real infer_type Pi calls must complete on the large stack");

        assert!(basic, "infer_type(Π (Sort 0). Sort 0) must be exactly Sort 1");
        assert!(max, "infer_type(Π (Sort 2). Sort 0) must be exactly Sort 3 (max picks domain)");
        assert!(
            impredicative,
            "infer_type(Π (Sort 3). Prop) must be exactly Sort 0 (imax _ 0 = 0, impredicative)"
        );
    }

    /// CONST arm (ENVIRONMENT lookup): unlike every other fixture in this lane
    /// (which uses the empty `Environment::new()`), this registers a definition
    /// `MyDef : Sort 1 := Sort 0` and grounds that the real `infer_type` CONSULTS
    /// THE ENVIRONMENT — `infer_type(Const MyDef)` returns its DECLARED type
    /// `Sort 1` (not its value `Sort 0`), the env-consulting arm the module docs
    /// previously excluded.
    #[test]
    fn real_infer_const_arm_grounds_env_lookup() {
        let out = run_on_large_stack(|| {
            let mut env = Environment::new();
            env.add_decl(Declaration::Definition {
                name: Name::from_string("Trust.Certify.MyDef"),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())), // : Sort 1
                value: Expr::sort(Level::zero()),              // := Sort 0
                is_reducible: true,
            })
            .expect("register MyDef");
            let tc = TypeChecker::with_mode(&env, env.mode());
            let c = Expr::const_(Name::from_string("Trust.Certify.MyDef"), LevelVec::new());
            tc.infer_type(&c).ok()
        })
        .expect("real infer_type of a Const must complete on the large stack");
        assert_eq!(
            out,
            Some(Expr::sort(Level::succ(Level::zero()))),
            "infer_type(Const MyDef) must be its DECLARED type Sort 1 (env lookup), not Sort 0"
        );
    }

    /// LET arm: `infer_type(let (x : Sort 1) := Sort 0 in x) = Sort 1` — the body
    /// `x` has the binder's type `Sort 1`, and the let's type is the body's type.
    /// Grounds the `let`/local-definition typing arm of the real function.
    #[test]
    fn real_infer_let_arm_grounds_typing() {
        let out = run_on_large_stack(|| {
            // let (x : Sort 1) := Sort 0 in x
            let e = Expr::let_named(Name::anon(), sortn(1), sortn(0), Expr::bvar(0), false);
            real_infer_type(&e)
        })
        .expect("real infer_type of a let must complete on the large stack");
        assert_eq!(
            out,
            Some(sortn(1)),
            "infer_type(let (x:Sort 1) := Sort 0 in x) must be the body's type Sort 1"
        );
    }

    /// NO MASQUERADE, isolated: the real output for `Sort 0` is `Sort 1`, so
    /// matching it against the WRONG result `Sort 0` must fail. This is the
    /// witness that `certify_real_infer_sort_fn` reads the genuine function
    /// output and is not a rubber stamp.
    #[test]
    fn real_infer_sort_wrong_result_rejected() {
        let (right, wrong_low, wrong_high) = run_on_large_stack(|| {
            let l = Level::zero();
            (
                real_infer_sort_equals(&l, &Expr::sort(Level::succ(l.clone()))),
                real_infer_sort_equals(&l, &Expr::sort(l.clone())),
                real_infer_sort_equals(&l, &Expr::sort(Level::succ(Level::succ(l.clone())))),
            )
        })
        .expect("neg-control calls must complete");
        assert!(right, "real infer_type(Sort 0) equals Sort 1");
        assert!(!wrong_low, "real infer_type(Sort 0) must NOT equal Sort 0");
        assert!(!wrong_high, "real infer_type(Sort 0) must NOT equal Sort 2");
    }

    /// SOUNDNESS of infer→check on the REAL fns — the literal-Rust per-input companion
    /// to the model-level flagship `tc_infer_soundness` (`infer accepts e:T ⟹ check
    /// accepts e:T`). For a well-typed term, the type the REAL `infer_type` PRODUCES is
    /// one the REAL `check_type` ACCEPTS: `infer_type(e) = Ok(T) ⟹ check_type(e, T) =
    /// Ok`. Grounded per-input across a sort, an identity lambda, and a beta redex — the
    /// two real entry points AGREE. DISCRIMINATION: `check_type` against a WRONG type
    /// (`Sort 2` for a term of type `Sort 1`) is REJECTED, so `check_type` is not a
    /// rubber stamp and the agreement is a genuine soundness fact, not vacuous.
    #[test]
    fn real_infer_type_sound_against_check_type() {
        let (all_sound, inferred_is_sort1, wrong_rejected) = run_on_large_stack(|| {
            let env = Environment::new();
            let tc = TypeChecker::with_mode(&env, env.mode());

            // POSITIVE: infer_type(e) = T ⟹ check_type(e, T) accepts, for each well-typed e.
            let id_on_prop = Expr::lam(BinderInfo::Default, sortn(0), Expr::bvar(0));
            let redex =
                Expr::app(Expr::lam(BinderInfo::Default, sortn(1), Expr::bvar(0)), sortn(0));
            let cases = [sortn(0), id_on_prop, redex];
            let all_sound = cases.iter().all(|e| match tc.infer_type(e) {
                Ok(t) => tc.check_type(e, &t).is_ok(),
                Err(_) => false,
            });

            // DISCRIMINATION: check_type against a WRONG type must be rejected.
            let e = sortn(0);
            let inferred_is_sort1 = tc.infer_type(&e).ok().as_ref() == Some(&sortn(1));
            let wrong_rejected = tc.check_type(&e, &sortn(2)).is_err();

            (all_sound, inferred_is_sort1, wrong_rejected)
        })
        .expect("infer/check calls must complete");

        assert!(inferred_is_sort1, "guard: real infer_type(Sort 0) = Sort 1");
        assert!(
            all_sound,
            "SOUNDNESS: for every well-typed e, the real check_type must ACCEPT the type \
             the real infer_type produced — the two entry points agree"
        );
        assert!(
            wrong_rejected,
            "check_type(Sort 0, Sort 2) must be REJECTED — check_type discriminates, so the \
             soundness agreement above is non-vacuous"
        );
    }
}
