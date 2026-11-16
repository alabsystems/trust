// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! KR0-style seeded-base controls for the reference entry used by island
//! acceptance. Core-owned declarations cannot be redeclared by island text;
//! seed them through the kernel, as kr0_e9_base_recheck does. The native-fold
//! bypass is process-global, so these controls have their own test binary.
use clean_kernel::env::native_fold_mint_bypass;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceRefusal, TheoryId,
};
use trust_certify::reference_mint::{ReferenceMiss, check_registered_in};

fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn one() -> Vec<Level> {
    vec![Level::succ(Level::zero())]
}
fn eq(carrier: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(name("Eq"), one()), [c(carrier), lhs, rhs])
}
fn refl(carrier: &str, lhs: Expr) -> Expr {
    Expr::apps(Expr::const_(name("Eq.refl"), one()), [c(carrier), lhs])
}
fn theorem(env: &mut Environment, n: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Theorem { name: name(n), level_params: vec![], type_, value })
        .expect("Extended control: the stored theorem really registers");
}
fn assert_refused_base(env: &Environment, n: &str) {
    match check_registered_in(env, &name(n)) {
        Err(ReferenceMiss::Refused(ReferenceRefusal::BaseRecheck { decl, .. })) => {
            assert_eq!(decl, name(n), "the declaration's own base judgment must be rechecked");
        }
        other => panic!("expected BaseRecheck of {n}, got {other:?}"),
    }
}

#[test]
fn platform_rfl_is_refused_even_when_the_extended_reducer_can_fire() {
    native_fold_mint_bypass::run(|| {
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Opaque {
            name: name("System.Platform.getIsOSX"),
            level_params: vec![],
            type_: Expr::arrow(c("Unit"), c("Bool")),
            value: Expr::lam(BinderInfo::Default, c("Unit"), c("Bool.false")),
        })
        .expect("typed opaque extern");
        env.add_decl(Declaration::Definition {
            name: name("System.Platform.isOSX"),
            level_params: vec![],
            type_: c("Bool"),
            value: Expr::app(c("System.Platform.getIsOSX"), c("Unit.unit")),
            is_reducible: false,
        })
        .expect("platform definition");
        let host = c(if cfg!(target_os = "macos") { "Bool.true" } else { "Bool.false" });
        // On this Mac: System.Platform.isOSX = true := rfl.
        theorem(
            &mut env,
            "tg8_platform_mutant",
            eq("Bool", c("System.Platform.isOSX"), host.clone()),
            refl("Bool", host),
        );
        let osx = c("System.Platform.isOSX");
        theorem(
            &mut env,
            "tg8_platform_refl",
            eq("Bool", osx.clone(), osx.clone()),
            refl("Bool", osx),
        );
        assert_refused_base(&env, "tg8_platform_mutant");
        let accepted = check_registered_in(&env, &name("tg8_platform_refl"))
            .expect("honest reflexivity still passes in the same base");
        assert_eq!(accepted.theory_id(), TheoryId::LeanReferenceV1);
    });
}

#[test]
fn string_drop_rfl_is_refused_even_when_the_extended_reducer_can_fire() {
    native_fold_mint_bypass::run(|| {
        let mut env = Environment::with_prelude();
        // A typed opaque String-returning head exposes the same extra-Lean
        // reducer without an external library. This is not the separate Lean
        // 4 String.Slice import/ABI qualification in Clean's integration suite.
        env.add_decl(Declaration::Opaque {
            name: name("String.drop"),
            level_params: vec![],
            type_: Expr::arrow(c("String"), Expr::arrow(c("Nat"), c("String"))),
            value: Expr::lam(
                BinderInfo::Default,
                c("String"),
                Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(1)),
            ),
        })
        .expect("typed opaque drop head");
        let drop = |s: &str| Expr::apps(c("String.drop"), [Expr::str_lit(s), Expr::nat_lit(1)]);
        let lhs = drop("abc");
        theorem(
            &mut env,
            "tg8_drop_mutant",
            eq("String", lhs.clone(), drop("xbc")),
            refl("String", lhs.clone()),
        );
        theorem(
            &mut env,
            "tg8_drop_refl",
            eq("String", lhs.clone(), lhs.clone()),
            refl("String", lhs),
        );
        assert_refused_base(&env, "tg8_drop_mutant");
        let accepted = check_registered_in(&env, &name("tg8_drop_refl"))
            .expect("honest reflexivity still passes in the same base");
        assert_eq!(accepted.theory_id(), TheoryId::LeanReferenceV1);
    });
}

#[test]
fn anonymous_universe_polymorphic_judgments_are_checked_generically() {
    use trust_certify::reference_mint::check_island_judgment_in;
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: name("_trust_island_reference").num(0),
        level_params: vec![],
        type_: c("Nat"),
        value: Expr::nat_lit(0),
        is_reducible: false,
    })
    .expect("a private-wrapper name is already occupied");
    let u = Level::param(name("u"));
    let eq = Expr::apps(
        Expr::const_(name("Eq"), vec![u.clone()]),
        [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)],
    );
    let refl =
        Expr::apps(Expr::const_(name("Eq.refl"), vec![u.clone()]), [Expr::bvar(1), Expr::bvar(0)]);
    let goal = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), eq),
    );
    let value = Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), refl),
    );
    let certificate = check_island_judgment_in(&env, &goal, &value)
        .expect("generic reflexivity in its original universe");
    assert_eq!(certificate.theory_id(), TheoryId::LeanReferenceV1);
    let wrong = Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(u),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    assert!(
        check_island_judgment_in(&env, &goal, &wrong).is_err(),
        "a binder value cannot replace the generic equality proof"
    );
    assert!(
        env.get_const(&name("_trust_island_reference").num(1)).is_none(),
        "the wrapper must not change the caller's environment"
    );
}
