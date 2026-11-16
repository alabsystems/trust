// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§R3b ACCEPTANCE EVIDENCE — the values the emitted `gcd` is checked
//! against, decided at the REAL kernel, each with a refuting control.**
//!
//! Promoted from a probe on 2026-08-27. Every row it used to print it now
//! ASSERTS, because the rows are what `tests/ui/trust/clean_origin_wf_rec_gcd.rs`
//! rests on: that fixture runs the EMITTED binary and compares it to these
//! literals, so a literal that is not itself a kernel decision would make the
//! fixture a tautology about two copies of the same guess.
//!
//! # THE ONE THING THIS FILE MAY NOT BE READ AS SAYING
//!
//! It does not say `gcd` is PROVED correct. `n1` measures that `Nat.gcd` is
//! ABSENT from the prelude, so there is no prelude gcd to state agreement with
//! and no correctness theorem is available to state at all. What is decided
//! here is that specific closed applications of `gcdF` reduce to specific
//! numerals — nine of them, plus tight-fuel rows, plus the five the fixture
//! uses — and that the wrong numerals do NOT. That is an acceptance table with
//! controls, exactly as the shipped `addAcc`/`dbl`/`fact` fixtures use, and it
//! is the honest ceiling of this increment.
//!
//! The fuel-sufficiency fact — any `f >= a + 2b` returns `gcd a b`, because
//! `a + 2b` strictly decreases by `b` on every non-fixed step and the only
//! fixed points are `(g, 0)` — is TRUE and is measured at both ends by `n3`.
//! It is not proved. A later increment can close that with a Clean theorem.
//!
//! # WHERE THE REFUTING CONTROLS ARE DECIDED
//!
//! Every ADMIT row goes through the whole island lane (parse, elaborate,
//! kernel-check). The REFUSALS are put to the kernel DIRECTLY: `theorem v :
//! gcd2 a b = wrong := Eq.refl (gcd2 a b)` goes through
//! `Environment::check_decl_readonly` — the same `clean_kernel` declaration
//! check the island's registration runs — over the environment the island
//! itself produced for `gcdF`/`gcd2`, and it must fail with the kernel's TYPE
//! MISMATCH. The same builder at the TRUE value must be ADMITTED, so a refusal
//! can never be a malformed term. Two island-level refusals at small fuel stay,
//! so the lane itself is still seen refusing a false `rfl`.
//!
//! Why not the island for every refusal: measured 2026-09-28 (debug test
//! build, Clean pin `5390f432`), Clean's ELABORATOR refuses a false `rfl` over
//! this well-founded definition in time EXPONENTIAL in the fuel — about 0.01 s
//! at fuel 8, 0.15 s at 11, 23 s at 15, 82 s at 16, over 90 s at 18, and the
//! rows here (fuel 33, 84, 654) did not finish in 15 minutes — while the
//! kernel decides every row, `270 192` (fuel 654) included, in under 50 ms.
//! A sample of the stuck process sits in the unifier (`unify_app_args` ->
//! `try_whnf`), inside `reduce_nat`'s operand whnf, in the whnf cache's
//! structural `Expr` equality — elaborator time, not the kernel's verdict.
//!
//! Historical diagnosis (2026-09-29): the timings and pin constraints below
//! describe the measured tree at that date.
//!
//! The defect is in `clean_kernel`'s structural `Expr` equality, and the
//! elaborator is only where it is reached. That equality short-circuited only
//! on `Arc::ptr_eq`, so two structurally equal terms built APART were compared
//! as their tree expansions. `gcdF` unfolds call-by-name, and each step names
//! each operand twice, so the unevaluated operand after `f` steps is an
//! `f`-deep DAG whose tree grows by a constant factor per step. A whnf-cache
//! probe that meets a separately built twin of that operand walks the whole
//! tree. Bisected 2026-09-29 over Clean `336d2003..0b9c67d28` with a fuel-13
//! false-`rfl` probe (0.07 s good, 6.5-8.7 s bad): the first slow commit is
//! Clean `1a8f1c807` ("assign a bare metavariable the constant AS WRITTEN,
//! not its unfolding"). That change is correct and Lean-faithful. By no longer
//! whnf-ing an argument before assigning it to a metavariable, it hands the
//! unifier the unevaluated DAG, and so it EXPOSED the equality defect rather
//! than introducing it. The fix belongs in Clean: its kernel commit
//! "structural Expr equality walks the two DAGs, not their tree expansions"
//! memoizes node pairs already proven equal, as Lean's `expr_eq_fn` does. Its
//! unit test `test_independent_twin_dags_compare_in_dag_size_not_tree_size`
//! bounds the walk at 448 node visits for a 12-step twin; it measures 177,
//! against 18,434,053 without the memo. With that fix, the same probe refuses
//! at fuel 16 in 0.13 s (274 s without it) and at fuel 654 in 5.1 s.
//!
//! The island-level refusals at full fuel grow back only when the Clean
//! gitlink carries that kernel. Moving the gitlink changes `crates/clean-kernel`
//! away from K, the Clean commit trust-ir records. The required
//! `fast.first-party-pin-lattice` gate refuses that (L3,
//! `docs/first-party-pin-ledger.md#pin-lattice`), so the fix arrives with the
//! pin-lattice train in which trust-ir moves K to a Clean commit that
//! contains it.

#![allow(clippy::doc_markdown)]

use clean_kernel::{
    Declaration, Environment, Expr, KernelEnvError, Level, Name, TypeError as KernelTypeError,
};

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|c| c.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(220).collect()
}

const GCD_FUEL: &str = "def gcdF (f a b : Nat) : Nat := \
                        if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
                        termination_by f";

const WRAPPER: &str = "def gcd2 (a b : Nat) : Nat := gcdF (a + b + b) a b";

/// `gcdF` and `gcd2` exactly as the island elaborated them and the kernel
/// registered them: the environment every kernel-direct row is checked in.
fn gcd_environment() -> Environment {
    island(&format!("{GCD_FUEL}\n{WRAPPER}"))
        .unwrap_or_else(|why| panic!("the island must admit `gcdF`/`gcd2`: {}", first_line(&why)))
}

/// Put `theorem v : gcd2 a b = v := @Eq.refl Nat (gcd2 a b)` to the kernel's
/// full declaration check (`check_decl_readonly`: the declaration's type is a
/// `Prop`, and its value type-checks against it) — the `rfl` row with no
/// elaborator in between. The environment is not modified.
fn kernel_rfl(env: &Environment, a: u32, b: u32, v: u32) -> Result<(), KernelEnvError> {
    let cnst = |name: &str, levels: Vec<Level>| Expr::const_(Name::from_string(name), levels);
    let one = || vec![Level::succ(Level::zero())];
    let lhs = Expr::apps(cnst("gcd2", vec![]), [Expr::nat_lit(a.into()), Expr::nat_lit(b.into())]);
    env.check_decl_readonly(&Declaration::Theorem {
        name: Name::from_string("gcd_final_probes_kernel_row"),
        level_params: vec![],
        type_: Expr::apps(
            cnst("Eq", one()),
            [cnst("Nat", vec![]), lhs.clone(), Expr::nat_lit(v.into())],
        ),
        value: Expr::apps(cnst("Eq.refl", one()), [cnst("Nat", vec![]), lhs]),
    })
}

/// The refuting control, at the kernel: the same builder ADMITS `gcd2 a b =
/// gcd a b` (so it constructs a well-formed `rfl` row), and the kernel REFUSES
/// `gcd2 a b = wrong` with a type mismatch — `gcd2 a b` is not definitionally
/// `wrong`, which is the verdict, not a malformed term.
fn assert_kernel_refuses(env: &Environment, a: u32, b: u32, wrong: u32, why: &str) {
    let right = gcd(a, b);
    assert_ne!(right, wrong, "a control row must state a FALSE value");
    if let Err(error) = kernel_rfl(env, a, b, right) {
        panic!(
            "BUILDER CONTROL: the kernel must ADMIT `gcd2 {a} {b} = {right}` built the same way: {error}"
        );
    }
    match kernel_rfl(env, a, b, wrong) {
        Err(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }) => {}
        Ok(()) => {
            panic!("CONTROL: `gcd2 {a} {b} = {wrong}` is FALSE and the kernel ADMITTED it — {why}")
        }
        Err(other) => panic!(
            "CONTROL: `gcd2 {a} {b} = {wrong}` must be refused by the kernel's TYPE MISMATCH \
             (not being def-eq), not by: {other}"
        ),
    }
}

/// **WHY THE ACCEPTANCE ROWS ARE LITERALS.** If the prelude carried a `gcd`,
/// every row below could be stated against IT (`gcd2 12 18 = Nat.gcd 12 18`)
/// and would then be a claim about agreement with a definition somebody else
/// wrote, which is much stronger than agreement with a numeral. It does not.
/// Recorded as an assertion rather than a comment so that the day the prelude
/// GAINS one, this fails and the acceptance table gets upgraded instead of
/// quietly staying weaker than it needs to be.
#[test]
fn n1_the_prelude_has_no_gcd_to_state_correctness_against() {
    let env = island("def unit : Nat := 0").expect("trivial island");
    for name in ["Nat.gcd", "Nat.gcdAux", "gcd"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` is now in the prelude. The acceptance rows in this file and in \
             `tests/ui/trust/clean_origin_wf_rec_gcd.rs` are hand-computed literals BECAUSE \
             there was nothing to compare against; state them against `{name}` instead, and \
             say so in the fixture's header, which currently claims this absence."
        );
    }
}

/// The closed values, through the two-argument Clean wrapper `gcd2`, at the
/// kernel. The refuting controls below are what make the admits DECISIONS: a
/// kernel that admitted `gcd2 12 18 = 3` would admit anything. They are
/// decided at the kernel directly (see the module docs for why and for the
/// builder control), plus one island-level refusal at small fuel.
#[test]
fn n2_closed_values_through_the_wrapper() {
    for (a, b, want) in [
        (0_u32, 0_u32, 0_u32),
        (5, 0, 5),
        (0, 5, 5),
        (1, 1, 1),
        (6, 6, 6),
        (7, 13, 1),
        (12, 18, 6),
        (18, 12, 6),
        (48, 18, 6),
    ] {
        let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 {a} {b} = {want} := rfl");
        assert!(
            island(&src).is_ok(),
            "the KERNEL must reduce `gcd2 {a} {b}` to `{want}`: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
        assert_eq!(want, gcd(a, b), "…and `{want}` must be the real gcd of {a} and {b}");
    }
    let env = gcd_environment();
    for (a, b, wrong) in [(7_u32, 13_u32, 7_u32), (48, 18, 18), (12, 18, 3)] {
        assert_kernel_refuses(&env, a, b, wrong, "if it admits, the rows above are not decisions");
    }
    // The island lane itself refusing a false `rfl`, at fuel 8 (`4 + 2 + 2`):
    // `1` divides both, so a body returning a common divisor rather than the
    // greatest would pass the admits and fail here.
    let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 4 2 = 1 := rfl");
    assert!(
        island(&src).is_err(),
        "CONTROL: `gcd2 4 2 = 1` is FALSE and the island must refuse it — if it admits, the \
         rows above are not decisions"
    );
}

/// Does the fuel bound `a + b + b` hold at every input, or only at the ones
/// above? The step map's fixed point is `(g, 0)`, and `a + 2b` strictly
/// decreases by `b` per step while `b > 0` — so `a + 2b` steps always suffice.
/// This row asks the kernel the same question at the TIGHT end: exactly enough
/// fuel, and one less.
#[test]
fn n3_the_fuel_bound_is_tight_enough() {
    for (a, b) in [(1_u32, 7_u32), (7, 1), (12, 18), (13, 5)] {
        let exact = a + b + b;
        for fuel in [exact, exact + 1] {
            let want = gcd(a, b);
            let src = format!("{GCD_FUEL}\ntheorem v : gcdF {fuel} {a} {b} = {want} := rfl");
            assert!(
                island(&src).is_ok(),
                "fuel {fuel} must already suffice for ({a}, {b}) -> {want}; the bound claimed \
                 in this file's header is `a + 2b`, and this row is its TIGHT end"
            );
        }
        // …and one BELOW the bound must not be assumed to work. Recorded as a
        // measurement rather than a claim: for these inputs the map reaches its
        // fixed point early, so short fuel may still be enough. What must never
        // happen is a fixture row resting on fuel nobody measured.
        let short = a + b + b - 1;
        let want = gcd(a, b);
        let src = format!("{GCD_FUEL}\ntheorem v : gcdF {short} {a} {b} = {want} := rfl");
        eprintln!(
            "ROW n3 short fuel={short:>3} ({a},{b}) -> {want} | {}",
            if island(&src).is_ok() {
                "still admits (fixed point reached early)"
            } else {
                "REFUSED"
            }
        );
    }
}

const fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
/// **THE FIXTURE'S OWN FIVE ROWS**, decided here so that
/// `tests/ui/trust/clean_origin_wf_rec_gcd.rs` is comparing the emitted binary
/// against kernel decisions rather than against my arithmetic. `270 192` is the
/// large one — 654 units of fuel, so 654 emitted frames — and it is included
/// precisely because a shallow row cannot distinguish a working recursion from
/// one that returns its argument.
#[test]
fn n4_the_run_pass_fixture_rows_are_kernel_decisions() {
    for (a, b, want) in [(12_u32, 18_u32, 6_u32), (270, 192, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)] {
        assert_eq!(want, gcd(a, b), "the fixture's expected value must be the real gcd");
        let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 {a} {b} = {want} := rfl");
        assert!(
            island(&src).is_ok(),
            "the KERNEL must reduce `gcd2 {a} {b}` to `{want}` — this is the row the run-pass \
             fixture asserts about the EMITTED binary: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }
    // Decided at the kernel directly; see the module docs.
    let env = gcd_environment();
    for (a, b, wrong) in [(270_u32, 192_u32, 2_u32), (270, 192, 12), (12, 18, 18), (7, 13, 7)] {
        assert_kernel_refuses(
            &env,
            a,
            b,
            wrong,
            "`wrong` is a DIVISOR of both (or one of the inputs) in every row here, so a body \
             that returned a common divisor rather than the GREATEST one would pass the admits \
             and fail here",
        );
    }
    // …and the island lane itself refusing one, at fuel 8 (`2 + 3 + 3`): `2` is
    // one of the inputs, so a body that returned its argument fails here.
    let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 2 3 = 2 := rfl");
    assert!(
        island(&src).is_err(),
        "CONTROL: `gcd2 2 3 = 2` is FALSE and the island must refuse it"
    );
}
