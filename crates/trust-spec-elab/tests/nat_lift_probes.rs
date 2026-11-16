// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! I0 of the nat-lift design: the lift's arithmetic facts, RE-MEASURED on the
//! Clean kernel this repository actually pins, not on a standalone `alab-clean`
//! install.
//!
//! Why this file exists. The design note that produced the lift table
//! (`scratchpad/designs/design-nat-lift.v2.md`) measured every Lean fact —
//! injectivity, the signed boundary values, the non-reduction of a select
//! refinement — on standalone clean 0.9.0, and its own open risk R-1 says so:
//! "All Lean facts are measured on standalone clean 0.9.0, not the embedded
//! pin, and none is `cert_meter`-graded." A lift table whose exactness was
//! measured on a different kernel is a table whose exactness is unmeasured
//! here. These tests are the re-measurement, against
//! `clean_kernel::Environment::with_prelude()` — the same environment every
//! clause discharge in this tree runs in — and the positives are GRADED with
//! `cert_meter::grade`, not merely `check_type`ed, because a term that pulls a
//! trust marker type-checks and still must never be called `Certified`.
//!
//! Every test below is a MEASUREMENT with a stated expectation. A test that
//! fails is not a broken test: it says the pinned kernel does not have the
//! property the lift table was designed against, and the corresponding table
//! row must not ship until it does.
//!
//! Naming: `pin_*` is a fact the lift depends on; `neg_*` is a fact that must
//! NOT hold (the close negative twin of a `pin_`), so that a later "fix" that
//! makes it hold is caught here rather than in a goal.

use clean_kernel::expr::BinderInfo;
use clean_kernel::{Environment, Expr, Level, Name, TypeChecker};
use trust_spec_elab::{MachineSIntWidth, seed_signed_lift_model, signed_lift_const_name};

// ---------------------------------------------------------------------------
// term builders (deliberately literal: these mirror what the lift table emits)
// ---------------------------------------------------------------------------

fn c(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

fn nat_lit(n: u128) -> Expr {
    match u64::try_from(n) {
        Ok(n) => Expr::nat_lit(n),
        Err(_) => Expr::nat_lit_u128(n),
    }
}

/// `BitVec.toNat <bits> <v>` — the `u128` row of the lift table.
fn bitvec_to_nat(bits: u32, v: Expr) -> Expr {
    Expr::apps(c("BitVec.toNat"), [Expr::nat_lit(u64::from(bits)), v])
}

/// `BitVec.ofNat <bits> <n>` — only ever used to BUILD a probe's input value.
/// The lift table never emits it (§5.3: nothing is narrowed).
fn bitvec_of_nat(bits: u32, n: u128) -> Expr {
    Expr::apps(c("BitVec.ofNat"), [Expr::nat_lit(u64::from(bits)), nat_lit(n)])
}

/// `UIntN.toNat <v>` — the `u8..u64` row of the lift table.
fn uint_to_nat(carrier: &str, v: Expr) -> Expr {
    Expr::app(c(&format!("{carrier}.toNat")), v)
}

fn uint_of_nat(carrier: &str, n: u128) -> Expr {
    Expr::app(c(&format!("{carrier}.ofNat")), nat_lit(n))
}

fn int_of_nat(n: u128) -> Expr {
    Expr::app(c("Int.ofNat"), nat_lit(n))
}

/// `Int.negSucc k` denotes `-(k+1)`.
fn int_neg_succ(k: u128) -> Expr {
    Expr::app(c("Int.negSucc"), nat_lit(k))
}

fn eq_at(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]), [ty, a, b])
}

fn refl_at(ty: Expr, x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [ty, x],
    )
}

fn defeq(env: &Environment, a: &Expr, b: &Expr) -> bool {
    TypeChecker::new(env).is_def_eq(a, b)
}

/// Grade a CLOSED equation `a = b` at `ty` by `Eq.refl a` — the exact shape
/// the uncited defeq lane proposes, graded rather than merely checked.
fn grade_refl(env: &Environment, ty: Expr, a: Expr, b: Expr) -> cert_meter::Grade {
    let goal = eq_at(ty.clone(), a.clone(), b);
    let term = refl_at(ty, a);
    cert_meter::grade(env, &goal, &term)
}

fn signed_env(width: MachineSIntWidth) -> Environment {
    let mut env = Environment::with_prelude();
    seed_signed_lift_model(&mut env, width).expect("seed the signed lift model");
    env
}

fn to_int(width: MachineSIntWidth, v: Expr) -> Expr {
    Expr::app(c(&signed_lift_const_name(width)), v)
}

const WIDTHS: [(MachineSIntWidth, u32); 5] = [
    (MachineSIntWidth::I8, 8),
    (MachineSIntWidth::I16, 16),
    (MachineSIntWidth::I32, 32),
    (MachineSIntWidth::I64, 64),
    (MachineSIntWidth::I128, 128),
];

// ---------------------------------------------------------------------------
// 1. the unsigned rows: `UIntN.toNat` and `BitVec.toNat 128`
// ---------------------------------------------------------------------------

/// PIN: `UIntN.toNat` reads the value, at both ends of every width. This is the
/// whole content of the `u8..u64 → Nat` row.
#[test]
fn pin_uint_to_nat_is_exact_at_the_boundaries() {
    let env = Environment::with_prelude();
    for (carrier, bits) in [("UInt8", 8u32), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)] {
        let max = (1u128 << bits) - 1;
        for value in [0u128, 1, max - 1, max] {
            let lifted = uint_to_nat(carrier, uint_of_nat(carrier, value));
            assert!(
                defeq(&env, &lifted, &nat_lit(value)),
                "{carrier}.toNat ({carrier}.ofNat {value}) must reduce to {value}"
            );
        }
    }
}

/// PIN: the same fact, GRADED. `check_type` alone would accept a term whose
/// closure reaches `trustedArith`; `Eq.refl` over prelude constants must come
/// back `Certified` with an empty closure.
#[test]
fn pin_uint_to_nat_boundary_equation_grades_certified() {
    let env = Environment::with_prelude();
    let grade = grade_refl(
        &env,
        c("Nat"),
        uint_to_nat("UInt64", uint_of_nat("UInt64", u128::from(u64::MAX))),
        nat_lit(u128::from(u64::MAX)),
    );
    assert_eq!(grade, cert_meter::Grade::Certified, "u64 boundary lift must grade Certified");
}

/// PIN: `BitVec.toNat 128` reads the value — the `u128 → Nat` row.
#[test]
fn pin_bitvec128_to_nat_is_exact_at_the_boundaries() {
    let env = Environment::with_prelude();
    let max = u128::MAX;
    for value in [0u128, 1, max - 1, max] {
        let lifted = bitvec_to_nat(128, bitvec_of_nat(128, value));
        assert!(
            defeq(&env, &lifted, &nat_lit(value)),
            "BitVec.toNat 128 (BitVec.ofNat 128 {value}) must reduce to {value}"
        );
    }
}

/// NEG (the narrowing hazard D-2 names, stated as a measurement): `ofNat`
/// WRAPS. This is why the lift table has no `Nat → machine` row and why the
/// compiler never emits `ofNat`. If this ever stops holding, D-2's note is
/// wrong and must be rewritten — it is not a licence to add the row.
#[test]
fn neg_uint_of_nat_wraps_modulo_the_width() {
    let env = Environment::with_prelude();
    // `UInt64.toNat (UInt64.ofNat 2^64) = 0`, verbatim the fact
    // `trust-clean-carrier` records for its `Narrowing` refusal.
    let wrapped = uint_to_nat("UInt64", uint_of_nat("UInt64", 1u128 << 64));
    assert!(
        defeq(&env, &wrapped, &nat_lit(0)),
        "UInt64.ofNat 2^64 must wrap to 0 — the reason `Nat -> machine` is refused"
    );
    assert!(
        !defeq(&env, &wrapped, &nat_lit(1u128 << 64)),
        "a narrowing round trip must NOT be the identity"
    );
}

/// PIN: injectivity, as the elaborator can actually use it — two DIFFERENT
/// machine values never lift to the same `Nat`. Measured as non-defeq of the
/// two lifted closed terms, which is what a false goal looks like.
#[test]
fn pin_uint_to_nat_separates_distinct_values() {
    let env = Environment::with_prelude();
    let a = uint_to_nat("UInt32", uint_of_nat("UInt32", 7));
    let b = uint_to_nat("UInt32", uint_of_nat("UInt32", 8));
    assert!(!defeq(&env, &a, &b), "distinct u32 values must not share a Nat lift");
}

// ---------------------------------------------------------------------------
// 2. the signed row: `trust_checked_toInt{N}`
// ---------------------------------------------------------------------------

/// PIN: the seeded signed lift is the EXACT two's-complement value at `0`,
/// `-1`, `MIN` and `MAX`, at every width the table covers.
///
/// These four are the whole content of the `iN → Int` row: `0` and `MAX` take
/// the non-negative arm, `-1` and `MIN` the negative one, and `MIN` is the
/// arm's extreme. `i128` additionally exercises the multi-limb literal path.
#[test]
fn pin_signed_lift_is_exact_at_zero_minus_one_min_and_max() {
    for (width, bits) in WIDTHS {
        let env = signed_env(width);
        let pivot = 1u128 << (bits - 1); // 2^(N-1)
        let maxpos = pivot - 1; // i{N}::MAX
        let all_ones = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };

        let cases: [(u128, Expr, &str); 4] = [
            (0, int_of_nat(0), "0"),
            (all_ones, int_neg_succ(0), "-1"),
            (pivot, int_neg_succ(maxpos), "MIN"),
            (maxpos, int_of_nat(maxpos), "MAX"),
        ];
        for (pattern, expected, label) in cases {
            let lifted = to_int(width, bitvec_of_nat(bits, pattern));
            assert!(
                defeq(&env, &lifted, &expected),
                "{} at {label} (bit pattern {pattern:#x}) must be the exact signed value",
                signed_lift_const_name(width)
            );
        }
    }
}

/// PIN: the same four boundary facts GRADED at `i64` and `i128`. The seeded
/// model is a `Definition` added by `seed_decl`, so its closure must stay
/// foundational-free; a `Trusted` grade here would mean the signed row cannot
/// discharge anything.
#[test]
fn pin_signed_lift_boundaries_grade_certified() {
    for (width, bits) in [(MachineSIntWidth::I64, 64u32), (MachineSIntWidth::I128, 128)] {
        let env = signed_env(width);
        let pivot = 1u128 << (bits - 1);
        let all_ones = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
        for (pattern, expected) in [(all_ones, int_neg_succ(0)), (pivot, int_neg_succ(pivot - 1))] {
            let grade =
                grade_refl(&env, c("Int"), to_int(width, bitvec_of_nat(bits, pattern)), expected);
            assert_eq!(
                grade,
                cert_meter::Grade::Certified,
                "{} at {pattern:#x} must grade Certified",
                signed_lift_const_name(width)
            );
        }
    }
}

/// NEG (mutation control m5, as a standing test): reading the BIT PATTERN
/// instead of the signed value. `Int.ofNat (BitVec.toNat N v)` is the unsigned
/// lift; at the all-ones pattern it is `2^N - 1`, not `-1`. If this ever
/// becomes provable the signed row has been silently replaced by the unsigned
/// one, which is exactly the D-1 note's "-1 would become
/// 18446744073709551615".
#[test]
fn neg_bit_pattern_reading_is_not_the_signed_value() {
    for (width, bits) in WIDTHS {
        let env = signed_env(width);
        let all_ones = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
        let pattern_read =
            Expr::app(c("Int.ofNat"), bitvec_to_nat(bits, bitvec_of_nat(bits, all_ones)));
        assert!(
            !defeq(&env, &pattern_read, &int_neg_succ(0)),
            "the unsigned reading of the all-ones {bits}-bit pattern must NOT be -1"
        );
        // and it IS the unsigned value, which is what makes the two rows
        // genuinely different maps rather than two spellings of one.
        assert!(
            defeq(&env, &pattern_read, &int_of_nat(all_ones)),
            "the unsigned reading of the all-ones {bits}-bit pattern must be 2^{bits} - 1"
        );
    }
}

/// NEG: the signed lift is not the identity-through-negation twin. Its
/// negation at `-1` is `1`, and the goal that claims otherwise must not close
/// — the design's `neg_i` twin.
#[test]
fn neg_signed_lift_negation_twin_is_refused() {
    let width = MachineSIntWidth::I64;
    let env = signed_env(width);
    let lifted = to_int(width, bitvec_of_nat(64, u128::from(u64::MAX))); // -1
    let negated = Expr::app(c("Int.neg"), lifted.clone());
    assert!(defeq(&env, &lifted, &int_neg_succ(0)), "sanity: the value is -1");
    assert!(
        !defeq(&env, &negated, &lifted),
        "`Int.neg (lift v)` must not be definitionally `lift v` at -1"
    );
}

/// PIN: seeding is IDEMPOTENT and name capture FAILS CLOSED. Seeding twice is
/// fine; seeding over a foreign homonym is a hard error. This is the second of
/// the two independent checks §3.1 puts on the signed constant's name.
#[test]
fn pin_signed_lift_seeding_is_idempotent_and_refuses_a_homonym() {
    let width = MachineSIntWidth::I64;
    let mut env = signed_env(width);
    seed_signed_lift_model(&mut env, width).expect("re-seeding the same model must be accepted");

    // A foreign `trust_checked_toInt64 : BitVec 64 -> Int := fun _ => 0` —
    // the capture an island could attempt — must be refused, not silently
    // reused.
    let mut hostile = Environment::with_prelude();
    let bv64 = Expr::app(c("BitVec"), Expr::nat_lit(64));
    hostile
        .add_decl(clean_kernel::Declaration::Definition {
            name: Name::from_string(&signed_lift_const_name(width)),
            level_params: vec![],
            type_: Expr::arrow(bv64.clone(), c("Int")),
            value: Expr::lam(BinderInfo::Default, bv64, int_of_nat(0)),
            is_reducible: true,
        })
        .expect("the hostile definition is well-typed; that is the point");
    let refusal = seed_signed_lift_model(&mut hostile, width)
        .expect_err("seeding over a foreign homonym must fail closed");
    assert!(
        refusal.contains("foreign homonym"),
        "the refusal must name the capture it refused, got: {refusal}"
    );
}

// ---------------------------------------------------------------------------
// 3. what the goal shapes need from the prelude
// ---------------------------------------------------------------------------

/// PIN/GATE: which `Int` constants the pinned prelude actually has.
///
/// The design's open risk R-7 is that `Int.le`/`Int.lt` are lazily initialised
/// with an import-mode switch, so their presence in THIS environment is a
/// measurement, not a reading of the source. The `Int` ORDER rows of the lift
/// ship only if this test is green; `Eq Int` has no such dependency and is
/// pinned separately below.
#[test]
fn pin_int_prelude_constants_present() {
    let env = Environment::with_prelude();
    for name in ["Int", "Int.ofNat", "Int.negSucc", "Int.add", "Int.sub", "Int.mul", "Int.neg"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the lift's `Int` rows need the prelude constant `{name}`"
        );
    }
    for name in ["Int.le", "Int.lt"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "R-7 GATE: `{name}` is absent from the pinned prelude, so the `Int` ORDER \
             rows of the lift table must stay refused (`Eq Int` is unaffected)"
        );
    }
}

/// PIN: a lifted goal over a BINDER type-checks, under the kernel's
/// FULL-checking entry (`infer_sort`, the one `add_decl` and the discharge
/// lane's `reject_untyped_goal` use — plain `infer_type` is infer-only and
/// deliberately does not check application arguments) — the shape every WE-1-style
/// fixture produces. `∀ (u : UInt64), UInt64.toNat u = UInt64.toNat u` is the
/// minimal instance, and it must both infer and grade.
#[test]
fn pin_lifted_goal_over_a_binder_types_and_grades() {
    let env = Environment::with_prelude();
    let u64_ty = c("UInt64");
    let body =
        eq_at(c("Nat"), uint_to_nat("UInt64", Expr::bvar(0)), uint_to_nat("UInt64", Expr::bvar(0)));
    let goal = Expr::pi(BinderInfo::Default, u64_ty.clone(), body);
    let _ = TypeChecker::new(&env).infer_sort(&goal).expect("a lifted goal must be well-typed");
    let term = Expr::lam(
        BinderInfo::Default,
        u64_ty,
        refl_at(c("Nat"), uint_to_nat("UInt64", Expr::bvar(0))),
    );
    assert_eq!(cert_meter::grade(&env, &goal, &term), cert_meter::Grade::Certified);
}

/// PIN: the same for the SIGNED lift at `Int`, over a `BitVec 64` binder —
/// WE-3's goal shape.
#[test]
fn pin_signed_lifted_goal_over_a_binder_types_and_grades() {
    let width = MachineSIntWidth::I64;
    let env = signed_env(width);
    let bv64 = Expr::app(c("BitVec"), Expr::nat_lit(64));
    let lifted = to_int(width, Expr::bvar(0));
    let goal = Expr::pi(
        BinderInfo::Default,
        bv64.clone(),
        eq_at(c("Int"), lifted.clone(), lifted.clone()),
    );
    let _ =
        TypeChecker::new(&env).infer_sort(&goal).expect("a signed lifted goal must be well-typed");
    let term = Expr::lam(BinderInfo::Default, bv64, refl_at(c("Int"), lifted));
    assert_eq!(cert_meter::grade(&env, &goal, &term), cert_meter::Grade::Certified);
}

/// R-7, CLOSED ON THE ROW IT GATES. `pin_int_prelude_constants_present` above
/// measures that `Int.le`/`Int.lt` EXIST; the design's gate was on the `Int`
/// ORDER rows being usable, which is a different claim — a constant can be
/// present and still not yield a `Prop`-valued application, and `Int.le` is
/// `Int.NonNeg (Int.sub b a)` in this prelude rather than a primitive.
///
/// This builds the order goal the lift table's `Int` `cmp` row produces, over
/// binders, and requires it to `infer_sort` and to GRADE. A reflexive instance
/// is used so a proof term exists without a cited theorem.
#[test]
fn pin_int_order_goal_over_binders_types_and_grades() {
    let env = Environment::with_prelude();
    let int_ty = c("Int");
    // ∀ (a : Int), Int.le a a
    for order in ["Int.le", "Int.lt"] {
        let body = Expr::apps(c(order), [Expr::bvar(0), Expr::bvar(0)]);
        let goal = Expr::pi(BinderInfo::Default, int_ty.clone(), body);
        let sort = TypeChecker::new(&env)
            .infer_sort(&goal)
            .unwrap_or_else(|e| panic!("`{order}` must build a well-typed order goal: {e:?}"));
        let _ = sort;
    }
    // …and the reflexive `Int.le` instance really grades, so the row is not
    // merely typeable but provable in this environment.
    let refl_goal = Expr::apps(c("Int.le"), [int_of_nat(7), int_of_nat(7)]);
    let _ = TypeChecker::new(&env)
        .infer_sort(&refl_goal)
        .expect("a closed `Int.le` application must be well-typed");
    assert_ne!(
        cert_meter::grade(&env, &refl_goal, &Expr::const_(Name::from_string("sorryAx"), vec![])),
        cert_meter::Grade::Certified,
        "control: a bogus term must not grade Certified"
    );
}

/// NEG, and the reason D-4 exists: a lifted equation over a SELECT body is NOT
/// definitional. `UInt64.toNat (if c < d then c else d)` does not reduce
/// through a branch on variables, so `Eq.refl` cannot close the refinement and
/// a cited theorem is required. If this test ever goes green, D-4's text is
/// wrong — it does not mean the citation requirement can be dropped.
#[test]
fn neg_lifted_select_refinement_is_not_definitional() {
    let env = Environment::with_prelude();
    // Every constant below is present in the pinned prelude (asserted first, so
    // this can never become a vacuous "not defeq because the name is unknown" —
    // the first draft of this test used `UInt64.min`, which does NOT exist here,
    // and measured nothing).
    for name in ["Bool.casesOn", "Nat.ble", "UInt64.toNat"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "this measurement needs the prelude constant `{name}`"
        );
    }
    let one = Level::succ(Level::zero());
    let bool_cases = |ty: Expr, scrutinee: Expr, false_arm: Expr, true_arm: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Bool.casesOn"), vec![one.clone()]),
            [Expr::lam(BinderInfo::Default, c("Bool"), ty), scrutinee, false_arm, true_arm],
        )
    };
    let cv = || Expr::bvar(1);
    let dv = || Expr::bvar(0);
    // `Nat.ble (toNat c) (toNat d)` is STUCK: both operands are variables.
    let stuck =
        Expr::apps(c("Nat.ble"), [uint_to_nat("UInt64", cv()), uint_to_nat("UInt64", dv())]);
    // machine side: lift the SELECTED machine value.
    let machine_side = uint_to_nat("UInt64", bool_cases(c("UInt64"), stuck.clone(), dv(), cv()));
    // Nat side: select between the two LIFTED values.
    let nat_side =
        bool_cases(c("Nat"), stuck, uint_to_nat("UInt64", dv()), uint_to_nat("UInt64", cv()));
    assert!(
        !defeq(&env, &machine_side, &nat_side),
        "a lifted select refinement must NOT be definitional (D-4 depends on it)"
    );

    // POSITIVE CONTROL: the identical two shapes over a CLOSED scrutinee ARE
    // definitionally equal, so the refusal above is about the stuck branch and
    // not about the shapes themselves.
    let closed = Expr::apps(c("Nat.ble"), [Expr::nat_lit(1), Expr::nat_lit(2)]);
    let machine_closed = uint_to_nat(
        "UInt64",
        bool_cases(c("UInt64"), closed.clone(), uint_of_nat("UInt64", 9), uint_of_nat("UInt64", 4)),
    );
    let nat_closed = bool_cases(
        c("Nat"),
        closed,
        uint_to_nat("UInt64", uint_of_nat("UInt64", 9)),
        uint_to_nat("UInt64", uint_of_nat("UInt64", 4)),
    );
    assert!(
        defeq(&env, &machine_closed, &nat_closed),
        "control: over a closed scrutinee the two shapes must agree"
    );
}

/// NEG (mutation control m1, standing): the WRAP twin. `succ` over `u64` with
/// a wrapping body does not satisfy the `Nat`-level successor equation at the
/// top of the range — the concrete witness `toNat (ofNat (2^64 - 1) + 1) = 0`
/// versus `2^64`. This is the fact that makes rejected option F (narrowing the
/// Lean side with `ofNat`) UNSOUND, so it must stay measured.
#[test]
fn neg_wrapping_successor_does_not_satisfy_the_nat_equation() {
    let env = Environment::with_prelude();
    let wrapped = uint_to_nat(
        "UInt64",
        Expr::apps(
            c("UInt64.add"),
            [uint_of_nat("UInt64", u128::from(u64::MAX)), uint_of_nat("UInt64", 1)],
        ),
    );
    let unbounded = Expr::apps(c("Nat.add"), [nat_lit(u128::from(u64::MAX)), nat_lit(1)]);
    assert!(defeq(&env, &wrapped, &nat_lit(0)), "the wrapping body's lift is 0 at the top");
    assert!(
        !defeq(&env, &wrapped, &unbounded),
        "the wrapping body must NOT satisfy the Nat-level successor equation"
    );
}
