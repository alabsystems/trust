//! TINV D2 PREMISE RAIL (plan defect #14), on the compiler's OWN extracted MIR.
//!
//! The census's D2 admits a write through a field alias of a TINV `S`
//! (`let r = &mut self.i; *r = v;`). That is sound only if the safety walk's state at the
//! R point of the root (sticky-dirty after the field borrow, `obligations.rs` "STICKY
//! gen") REFLECTS the write through the alias: the write has no finding of its own
//! (`place_write::resolve_place` cuts hits at a reference), so the row's σ must come from
//! the generator's own reading of `(*self).i` after `*r = v`, not from the entry value.
//!
//! FIXTURE. `tests/fixtures/tinv_alias_write_fx.rs`, captured verbatim with the stage-1
//! compiler (`rustc 1.99.0-dev (efa8829d7 2026-10-05)`) as
//!
//! ```text
//! rustc -Ztrust-verify=on -Ztrust-dump=mir:<dir> --edition 2021 --crate-type lib \
//!       --crate-name tinvfx tinv_alias_write_fx.rs
//! ```
//!
//! and bundled into `tests/fixtures/tinv_alias_write_fx.json` (a JSON array sorted by
//! def path). The dump is the per-function TrustVerify input; at `-Copt-level=0` it keeps
//! the alias local (`_3 = &mut ((*_1).0); (*_3) = copy _2`), which is the shape D2 admits.
//!
//! WHAT THIS PINS, for `P { i: u64, n: u64 }` with the conjunct `i <= n`:
//! * (a) `set`: `*(&mut self.i) = v` with `v` arbitrary. The R row is REFUTED by ay (SAT):
//!   the write through the alias is seen. An UNSAT here would be a false proof.
//! * (b) `set_guarded`: the same write under `if v <= self.n`. The R row is PROVED by ay
//!   and kernel-certified: σ at R holds exactly `v`, so the guard is what proves it.
//! * (c) `set_via`: the alias passed to the in-crate `put(r: &mut u64, v)`. Measured:
//!   never a false UNSAT, with `put` in or out of the inventory: the R row is unsituated
//!   (the call havocs `*self`) and refuted, so Houdini drops it as `Situatedness`.
//! * End to end (real kernel mint), Houdini drops `i <= n` in `set` (Refuted, R), in
//!   `set_via` (Situatedness) without `set`, and with both left out certifies it over
//!   `dup` (E) and `set_guarded` (R through the alias).

use trust_types::{TypeInvariantPoint, VcKind};

use super::*;
use crate::type_invariant::obligations::{BodyTinvPlan, TinvRowKey, type_invariant_check_vcs};

const FIXTURE: &str = include_str!("../../tests/fixtures/tinv_alias_write_fx.json");

fn fixtures() -> Vec<VerifiableFunction> {
    serde_json::from_str(FIXTURE).expect("fixture bundle must deserialize")
}

fn load(def_path: &str) -> VerifiableFunction {
    fixtures()
        .into_iter()
        .find(|f| f.def_path == def_path)
        .unwrap_or_else(|| panic!("fixture `{def_path}` missing"))
}

/// `tinvfx::P { i: u64, n: u64 }` with the single conjunct `i <= n`.
fn p_fx() -> TinvType {
    TinvType {
        def_path: "tinvfx::P".into(),
        fields: ["i", "n"].into_iter().map(|n| (n.to_string(), u64_ty())).collect(),
        conjuncts: vec![c0()],
    }
}

/// `put`'s identity, as `set_via`'s call to it carries it.
fn put_identity() -> CalleeIdentity {
    let via = load("tinvfx::P::set_via");
    via.body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func, callee_identity: Some(id), .. } if func == "tinvfx::put" => {
                Some(*id)
            }
            _ => None,
        })
        .expect("set_via calls tinvfx::put with an identity")
}

/// Every row of `def_path`'s body for `i <= n`, with `inventory` as the derived inventory.
fn rows_of(
    def_path: &str,
    inventory: &HashSet<CalleeIdentity>,
) -> Result<Vec<(TinvRowKey, VerificationCondition)>, TinvObligationRefusal> {
    let func = load(def_path);
    let types = [p_fx()];
    let plan = BodyTinvPlan {
        types: &types,
        facts: None,
        inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
        step_budget: u64::MAX,
    };
    let out = type_invariant_check_vcs(&func, &plan)?;
    assert!(out.refused.is_empty(), "{def_path}: {:?}", out.refused);
    assert!(out.uninstantiable.is_empty(), "{def_path}: {:?}", out.uninstantiable);
    Ok(out.rows)
}

fn r_rows(rows: &[(TinvRowKey, VerificationCondition)]) -> Vec<&VerificationCondition> {
    rows.iter()
        .filter(|(k, _)| k.point == TypeInvariantPoint::Return)
        .map(|(k, vc)| {
            assert!(matches!(vc.kind, VcKind::TypeInvariant { .. }));
            assert_eq!(k.conjunct, 0);
            vc
        })
        .collect()
}

fn kernel_certifies(vc: &VerificationCondition) -> bool {
    let vc = vc.clone();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            trust_certify::certify_vc(&vc)
                .is_some_and(|evidence| trust_certify::replay_vc_evidence(&vc, &evidence))
        })
        .expect("spawn")
        .join()
        .expect("certify thread must not panic")
}

#[test]
fn a_write_through_a_field_alias_is_seen_at_r_unguarded_is_refuted() {
    // (a) `fn set(&mut self, v: u64) { let r = &mut self.i; *r = v; }`.
    let rows = rows_of("tinvfx::P::set", &HashSet::new()).expect("set is walked");
    let r = r_rows(&rows);
    assert_eq!(r.len(), 1, "one R row on `*self`: {rows:#?}");
    let vc = r[0];
    assert_eq!(vc.type_invariant_situatedness_refusal(), None, "{:#?}", vc.formula);
    let result = ay_solve(vc);
    assert!(
        matches!(result, VerificationResult::Failed { .. }),
        "FALSE PROOF: the R row of `set` must be refuted (v is arbitrary), got {result:?}\n\
         formula: {:#?}",
        vc.formula
    );
    assert!(!kernel_certifies(vc), "the kernel certified a refuted row");

    // CONTROL: the same real body with the write `(*_3) = copy _2` deleted (the borrow
    // kept, so the root is still sticky-dirty) proves its R row. The refutation above is
    // the alias write, not the window.
    let mut twin = load("tinvfx::P::set");
    let before = twin.body.blocks[0].stmts.len();
    twin.body.blocks[0].stmts.retain(|st| {
        !matches!(st, Statement::Assign { place, .. }
            if place.local == 3 && place.projections == [Projection::Deref])
    });
    assert_eq!(twin.body.blocks[0].stmts.len(), before - 1, "the alias write was found");
    let types = [p_fx()];
    let inventory = HashSet::new();
    let plan = BodyTinvPlan {
        types: &types,
        facts: None,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
        step_budget: u64::MAX,
    };
    let rows = type_invariant_check_vcs(&twin, &plan).expect("the twin is walked").rows;
    let r = r_rows(&rows);
    assert_eq!(r.len(), 1, "{rows:#?}");
    assert_eq!(r[0].type_invariant_situatedness_refusal(), None);
    assert_eq!(ay(r[0]), Some(true), "{:#?}", r[0].formula);
}

#[test]
fn a_write_through_a_field_alias_is_seen_at_r_guarded_is_proved_and_certified() {
    // (b) `if v <= self.n { let r = &mut self.i; *r = v; }`.
    let rows = rows_of("tinvfx::P::set_guarded", &HashSet::new()).expect("set_guarded is walked");
    let r = r_rows(&rows);
    assert!(!r.is_empty(), "set_guarded owes R: {rows:#?}");
    for vc in r {
        assert_eq!(vc.type_invariant_situatedness_refusal(), None, "{:#?}", vc.formula);
        assert_eq!(ay(vc), Some(true), "the guarded R row must be proved: {:#?}", vc.formula);
        assert!(kernel_certifies(vc), "the guarded R row must be kernel-certified");
    }
}

#[test]
fn an_alias_passed_to_an_in_crate_helper_is_never_a_false_proof() {
    // (c) `fn set_via(&mut self, v: u64) { put(&mut self.i, v) }`, `put(r, v) { *r = v }`.
    // MEASURED (2026-10-06): with `put` in or out of the inventory, the walk is not
    // refused and its one R row is UNSITUATED (the call havocs all of `*self`, so the
    // core reads fresh `self*.0#..`/`self*.1#..` no hypothesis binds) and refuted by ay.
    // Houdini drops it as `Situatedness`: fail-closed. The rail is the first assertion;
    // the rest pin today's behaviour, so a change to it is seen.
    let put = put_identity();
    for inventory in [HashSet::new(), HashSet::from([put])] {
        let rows = rows_of("tinvfx::P::set_via", &inventory).unwrap_or_else(|why| {
            panic!("set_via refused ({} in inventory): {why:?}", inventory.len())
        });
        let r = r_rows(&rows);
        assert_eq!(r.len(), 1, "{rows:#?}");
        let vc = r[0];
        let situated = vc.type_invariant_situatedness_refusal().is_none();
        let verdict = ay(vc);
        assert!(
            !(situated && verdict == Some(true)),
            "FALSE PROOF: set_via's R row is situated and proved: {:#?}",
            vc.formula
        );
        assert!(!situated, "today's R row is unsituated: {:#?}", vc.formula);
        assert_eq!(verdict, Some(false), "{:#?}", vc.formula);
    }
}

#[test]
fn houdini_on_the_alias_fixture_drops_the_unguarded_write_and_certifies_the_guarded_one() {
    let all = fixtures();
    let put = put_identity();
    let bodies: Vec<TinvBody<'_>> = all
        .iter()
        .map(|f| TinvBody {
            identity: (f.def_path == "tinvfx::put").then_some(put),
            func: f,
            facts: None,
        })
        .collect();
    let without = |gone: &[&str]| -> Vec<TinvBody<'_>> {
        bodies.iter().copied().filter(|b| !gone.contains(&b.func.def_path.as_str())).collect()
    };
    // The real mint, as `certify_tests::run_certified` runs it.
    let mint = |vc: &VerificationCondition| {
        let evidence = trust_certify::certify_vc(vc)?;
        trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
    };
    let run = |bodies: &[TinvBody<'_>]| {
        houdini(&[p_fx()], bodies, &NoExactModels, &|_| true, &Ay, &mint, BUDGET)
    };

    // Every body: `set`'s R row refutes `i <= n` in round 1.
    let out = run(&bodies);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.certificates.is_empty());
    assert_eq!(out.dropped.len(), 1, "{:?}", out.dropped);
    let d = &out.dropped[0];
    assert_eq!((d.conjunct, d.cause, d.point), (0, DropCause::Refuted, TypeInvariantPoint::Return));
    assert_eq!(d.function, "tinvfx::P::set");

    // Without `set`: `set_via`'s unsituated R row drops it (c).
    let out = run(&without(&["tinvfx::P::set"]));
    assert!(out.certificates.is_empty());
    assert_eq!(out.dropped.len(), 1, "{:?}", out.dropped);
    assert_eq!(out.dropped[0].cause, DropCause::Situatedness);
    assert_eq!(out.dropped[0].function, "tinvfx::P::set_via");

    // Without both: `dup` (E) and `set_guarded` (R through the alias) certify with the
    // real kernel mint.
    let out = run(&without(&["tinvfx::P::set", "tinvfx::P::set_via"]));
    assert!(out.dropped.is_empty(), "{:?}", out.dropped);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    let cert = &out.certificates["tinvfx::P"];
    assert_eq!(cert.conjuncts().iter().map(|c| c.id).collect::<Vec<_>>(), vec![0]);
    assert!(
        cert.rows().iter().any(|r| r.function() == "tinvfx::P::set_guarded"
            && r.key().point == TypeInvariantPoint::Return)
    );
    assert!(cert.rows().iter().any(
        |r| r.function() == "tinvfx::P::dup" && r.key().point == TypeInvariantPoint::Establish
    ));
}
