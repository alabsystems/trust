//! Real-MIR cover for the RECURSIVE-ENUM half of the UNINHABITED MATCH ARM false
//! REFUTATION, on MIR extracted with `-Ztrust-dump=mir:<dir>` by a stage1 `trustc`
//! of main 7be75e9a80 from the source programs quoted per test.
//!
//! THE DEFECT, measured on that stage1 (`-Ztrust-verify-level=2`, advisory policy):
//!
//! ```ignore (illustrative)
//! pub enum NoExt {}
//! pub enum T<X> { A, B(<payload>), Ext(X) }
//! pub fn name(t: &T<NoExt>) -> &'static str {
//!     match t { T::A => "A", T::B(_) => "B", T::Ext(e) => e.unreachable() }
//! }
//! ```
//!
//!     <payload> = u8, Box<u8>, Box<X>, Option<X>   [unreach] PROVED
//!     <payload> = Box<T<X>>, Vec<T<X>>             [unreach] FAILED, `_2 = 2`
//!
//! rustc drops the dead `Ext` arm from the `SwitchInt` (`[0, 1], otherwise ->
//! Unreachable`), so the code is CORRECT and only the discriminant-domain fact can
//! close the `otherwise` edge. The uninhabitedness judgement was never the
//! difference: a RECURSIVE enum is lowered as a bare by-name `Ty::Datatype { name:
//! "T<NoExt>", variants: [] }` marker at its use site (the definition lives in
//! `body.datatype_defs`), and the tag-set producer typed `(*_1)` with `place_ty_cow`,
//! which widens a marker before every projection step but not after the last one.
//! The marker has no variants, so NO domain fact was published at all — `_2 = 2`
//! was simply the first value the solver picked outside `{0, 1}`.
//!
//! THE FIX resolves the source place's type through the body's table
//! (`place_ty_resolved_cow`) before reading the tag set. The adversarial direction is
//! the load-bearing half: resolution makes MORE enums eligible for a globally
//! published premise, so a recursive enum's LIVE tags must keep every reachable
//! failure reachable. MUTATION LEDGER (applied, built and run):
//!
//!     REVERT (`place_ty_resolved_cow`        recursive_box_*, recursive_vec_*,
//!       returns the unresolved marker)       recursive_live_sibling_*
//!     KEEP-TAG-0 (`.filter(discriminant      recursive_live_sibling_*,
//!       == 0)`, deleting LIVE tags)          recursive_inhabited_payload_*
use trust_types::{CounterexampleValue, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Whether `result` is a refutation whose witness assigns `name` (SSA-version suffix
/// stripped) the integer `value`.
fn refuted_at(result: &VerificationResult, name: &str, value: i128) -> bool {
    let VerificationResult::Failed { counterexample: Some(ce), .. } = result else {
        return false;
    };
    ce.assignments.iter().any(|(n, v)| {
        n.split('#').next() == Some(name) && matches!(v, CounterexampleValue::Int(x) if *x == value)
    })
}

/// The fixture's scrutinee really is the shape the defect needs: a bare marker whose
/// definition is in the body's table. Without this, a future extractor that inlines
/// the definition would turn every test below into a re-run of the non-recursive
/// cover in `uninhabited_arm_realmir.rs`.
fn assert_scrutinee_is_bare_marker(func: &VerifiableFunction, name: &str) {
    let ty = &func.body.locals.iter().find(|l| l.index == 1).expect("local _1").ty;
    let trust_types::Ty::Ref { inner, .. } = ty else { panic!("`_1` must be a reference: {ty:?}") };
    assert_eq!(
        trust_types::bare_datatype_marker_name(inner),
        Some(name),
        "the scrutinee must be the bare by-name marker the defect needs"
    );
    assert!(
        trust_types::datatype_marker_definition(&func.body.datatype_defs, inner).is_some(),
        "the body's datatype table must define `{name}`"
    );
}

/// Every `Unreachable` row of `func` must be PROVED and kernel-certify.
fn assert_unreachable_rows_proved(func: &VerifiableFunction) {
    let r = router();
    let mut seen = 0;
    for vc in trust_vcgen::generate_vcs(func) {
        if !matches!(vc.kind, VcKind::Unreachable) {
            continue;
        }
        seen += 1;
        let result = r.verify_one(&vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "the dead `Ext` arm's Unreachable block must be UNSAT — a model here is the \
             FALSE REFUTATION of correct Rust; got {result:?}\nformula: {:?}",
            vc.formula
        );
        assert!(
            trust_certify::certify_vc(&vc).is_some(),
            "the proof must kernel-certify\nformula: {:?}",
            vc.formula
        );
    }
    assert_eq!(seen, 1, "the fixture has exactly one Unreachable block");
}

/// `enum T<X> { A, B(Box<T<X>>), Ext(X) }` at `T<NoExt>`. MEASURED: `[unreach]
/// FAILED` at `_2 = 2` before the fix; PROVED and kernel-certified with it.
#[test]
fn recursive_box_enum_dead_variant_arm_is_proved() {
    let func = load(include_str!("fixtures/uninhabited_recursive_box_mir.json"));
    assert_scrutinee_is_bare_marker(&func, "boxrec::T<boxrec::NoExt>");
    assert_unreachable_rows_proved(&func);
}

/// The same enum recursive through `Vec<T<X>>` (the `subset.rs` `ty_name` shape).
#[test]
fn recursive_vec_enum_dead_variant_arm_is_proved() {
    let func = load(include_str!("fixtures/uninhabited_recursive_vec_mir.json"));
    assert_scrutinee_is_bare_marker(&func, "vecrec::T<vecrec::NoExt>");
    assert_unreachable_rows_proved(&func);
}

/// ADVERSARIAL. `enum T<X> { A, B(Box<T<X>>), Ext(X), C(u8) }` at `T<NoExt>`:
///
/// ```ignore (illustrative)
/// match t { T::A => 0, T::B(_) => 1, T::Ext(e) => e.unreachable(), T::C(_) => unreachable!() }
/// ```
///
/// `Ext` (tag 2) is dead, `C` (tag 3) is LIVE, so the `unreachable!()` panic is
/// genuinely reachable and must stay REFUTED at `_2 = 3`, while the `otherwise` arm
/// (only tag 2 reaches it) proves.
#[test]
fn recursive_live_sibling_keeps_its_reachable_panic_refuted() {
    let func = load(include_str!("fixtures/uninhabited_recursive_live_sibling_mir.json"));
    assert_scrutinee_is_bare_marker(&func, "reclive::T<reclive::NoExt>");
    let r = router();
    let all: Vec<_> = trust_vcgen::generate_vcs(&func)
        .into_iter()
        .map(|vc| {
            let v = r.verify_one(&vc);
            (vc, v)
        })
        .collect();

    let unreachable: Vec<_> =
        all.iter().filter(|(vc, _)| matches!(vc.kind, VcKind::Unreachable)).collect();
    assert_eq!(unreachable.len(), 1, "the fixture has exactly one Unreachable block");
    assert!(
        matches!(unreachable[0].1, VerificationResult::Proved { .. }),
        "the dead-tag Unreachable must be proved; got {:?}",
        unreachable[0].1
    );

    let panics: Vec<_> = all
        .iter()
        .filter(|(vc, _)| {
            matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call"))
        })
        .collect();
    assert!(!panics.is_empty(), "vacuity guard: the live `unreachable!()` must emit a row");
    assert!(
        panics.iter().all(|(_, result)| refuted_at(result, "_2", 3)),
        "the LIVE variant's `unreachable!()` is reachable at tag 3 and must stay refuted \
         there — proving it is a FALSE PROOF; got {:?}",
        panics.iter().map(|(_, r)| r).collect::<Vec<_>>()
    );
}

/// ADVERSARIAL. The same recursive enum at `T<u8>`, where `Ext` is INHABITED:
///
/// ```ignore (illustrative)
/// match t { T::A => 0, T::B(_) => 1, T::Ext(_) => unreachable!(), T::C(v) => *v }
/// ```
///
/// The resolved definition must not lose tag 2: the panic stays refuted at `_2 = 2`.
#[test]
fn recursive_inhabited_payload_keeps_its_reachable_panic_refuted() {
    let func = load(include_str!("fixtures/uninhabited_recursive_inhabited_payload_mir.json"));
    assert_scrutinee_is_bare_marker(&func, "reclive::T<u8>");
    let r = router();
    let panics: Vec<_> = trust_vcgen::generate_vcs(&func)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call"))
        })
        .map(|vc| r.verify_one(&vc))
        .collect();
    assert!(!panics.is_empty(), "vacuity guard: the `unreachable!()` must emit a row");
    assert!(
        panics.iter().all(|result| refuted_at(result, "_2", 2)),
        "`Ext(u8)` is inhabited, so its `unreachable!()` is reachable at tag 2 and must \
         stay refuted there; got {panics:?}"
    );
}
