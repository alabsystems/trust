// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! KR0 switch review, problem 1: the E9 lane builds its reference entry from
//! the island environment, whose constants were added under `Extended`. A base
//! theorem whose `FullKernelCheck` stamp was earned with a reducer Lean's
//! kernel does not have must not yield a `ReferenceCertificate` when a
//! judgment cites it.
//!
//! Measured at Clean `415e0e9cb` (Trust's pin when the switch was built):
//! `check_closed_in` returned `Ok(LeanReferenceV1)` for `isOSX = <host>`
//! proved by citing such a base theorem. At Clean `a64fb0f4b` (R143's base
//! re-check) the entry re-checks the cited base constant in Lean's theory and
//! refuses with `BaseRecheck`.
//!
//! In its own test binary because it opens Clean's native-fold authority
//! bypass, which is process-global.

use clean_kernel::env::native_fold_mint_bypass;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceRefusal, TheoryId,
};
use trust_certify::reference_mint::{ReferenceMiss, check_closed_in};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn one() -> Vec<Level> {
    vec![Level::succ(Level::zero())]
}

fn eq_bool(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(name("Eq"), one()), [c("Bool"), lhs, rhs])
}

fn refl_bool(e: Expr) -> Expr {
    Expr::apps(Expr::const_(name("Eq.refl"), one()), [c("Bool"), e])
}

/// The prelude plus Lean's platform declarations: an opaque extern and
/// `isOSX` over it (as Clean's own `reference_entry_base_recheck.rs`).
fn platform_env() -> Environment {
    let mut env = Environment::with_prelude();
    let unit = c("Unit");
    env.add_decl(Declaration::Opaque {
        name: name("System.Platform.getIsOSX"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, unit.clone(), c("Bool")),
        value: Expr::lam(BinderInfo::Default, unit, c("Bool.false")),
    })
    .expect("opaque getIsOSX");
    env.add_decl(Declaration::Definition {
        name: name("System.Platform.isOSX"),
        level_params: vec![],
        type_: c("Bool"),
        value: Expr::app(c("System.Platform.getIsOSX"), c("Unit.unit")),
        is_reducible: false,
    })
    .expect("def isOSX");
    env
}

#[test]
fn an_e9_judgment_citing_an_extended_only_base_theorem_gets_no_certificate() {
    let host = c(if cfg!(target_os = "macos") { "Bool.true" } else { "Bool.false" });
    let stated = eq_bool(c("System.Platform.isOSX"), host.clone());
    native_fold_mint_bypass::run(|| {
        let mut island = platform_env();
        // Extended admits the host's answer with the platform reducer allowed:
        // the stamp is a real `FullKernelCheck`, earned in the wrong theory.
        island
            .add_decl(Declaration::Theorem {
                name: name("kr0_e9_host_answer"),
                level_params: vec![],
                type_: stated.clone(),
                value: refl_bool(host.clone()),
            })
            .expect("Extended admits the host's answer");
        // Control: a base theorem Lean's theory proves, in the same island.
        let t = c("Bool.true");
        island
            .add_decl(Declaration::Theorem {
                name: name("kr0_e9_refl"),
                level_params: vec![],
                type_: eq_bool(t.clone(), t.clone()),
                value: refl_bool(t.clone()),
            })
            .expect("reflexivity");

        let refused = check_closed_in(&island, &stated, &c("kr0_e9_host_answer"));
        match &refused {
            Err(ReferenceMiss::Refused(ReferenceRefusal::BaseRecheck { decl, .. })) => {
                assert_eq!(decl, &name("kr0_e9_host_answer"));
            }
            other => panic!("expected BaseRecheck of the Extended-earned theorem, got {other:?}"),
        }

        let certificate = check_closed_in(&island, &eq_bool(t.clone(), t), &c("kr0_e9_refl"))
            .expect("control: a citation of a base theorem that re-checks is certified");
        assert_eq!(certificate.theory_id(), TheoryId::LeanReferenceV1);
    });
}
