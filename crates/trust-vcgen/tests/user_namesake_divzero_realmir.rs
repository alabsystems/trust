// Trust (2026-10-06, DIVZERO-NAME-1): `panic_calls::divzero_call`, the call-site
// recognizer that MINTS core's zero-divisor row (`divisor != 0` on arg 1), decided
// its callee by the last path segment alone. A call to a USER function or method
// merely named `div_ceil`, `rem_euclid`, `div_euclid` or `step_by` was therefore
// charged `[divzero]` / `[remzero]` over the user function's own arguments and
// REFUTED at `a = 0, b = 0`: measured on the stage 1 of `4ccd862830`
// (`scratchpad/scout20/carry/divzero-confirm/z1.rs`), each caller was refused while the
// callee's own row read `no_obligations | proved | trust-structural`, and a
// verify-off build of the same calls returned 0.
//
// The fixtures are REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>
// -Ztrust-policy=advisory`, the stage 1 of `46e9afaf95`, optimized MIR) of
// `fixtures/user_namesake_divzero/{user_divzero,renamed_divzero,core_divzero}.rs`,
// one caller per file, spans rewritten to `<dump-root>/`. The extractor is not
// touched by this fix, so these are the bodies the fixed compiler hands vcgen as
// well. `renamed_divzero.rs` is `user_divzero.rs` with every callee renamed off
// core's names (same bodies, same lines); that crate builds rc=0 on the same stage 1
// while `user_divzero.rs` is refused with 10 errors. Every user-namesake test here
// fails on the tail-only recognizer; the controls pin that core's own methods and
// std's `Iterator::step_by` keep their rows and their verdicts.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/user_namesake_divzero/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Every call's rendered callee, in block order (the fixture premise).
fn callees(func: &VerifiableFunction) -> Vec<String> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.clone()),
            _ => None,
        })
        .collect()
}

fn zero_divisor_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
        .collect()
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

#[test]
fn a_call_to_a_user_fn_named_like_a_core_divisor_method_mints_no_row() {
    for (name, want_callee) in [
        ("p1", "user_divzero::Q::div_ceil"),
        ("p2", "user_divzero::rem_euclid"),
        ("p3", "user_divzero::div_euclid"),
        ("p4", "user_divzero::S::step_by"),
        ("p5", "<u8 as user_divzero::Euclid>::rem_euclid"),
    ] {
        let func = load(name);
        assert_eq!(callees(&func), [want_callee], "{name}: fixture premise");
        let rows = zero_divisor_rows(&func);
        assert!(
            rows.is_empty(),
            "{name}: `{want_callee}` is a user function (no division at all); it owes no \
             zero-divisor row, got {:?}",
            rows.iter().map(|vc| (&vc.kind, vc.formula.to_smtlib())).collect::<Vec<_>>()
        );
    }
}

/// The namesake caller and its renamed twin now get the SAME obligations from vcgen:
/// no row is minted from the callee's name. (The twin crate is accepted by the
/// compiler; what remains between the two after this fix is the callee's name.)
#[test]
fn a_namesake_caller_gets_exactly_its_renamed_twins_obligations() {
    let shape = |func: &VerifiableFunction| -> Vec<(String, String)> {
        let mut rows: Vec<(String, String)> = generate_vcs(func)
            .iter()
            .map(|vc| (format!("{:?}", vc.kind), vc.formula.to_smtlib()))
            .collect();
        rows.sort();
        rows
    };
    for (namesake, twin) in [("p1", "r1"), ("p2", "r2"), ("p3", "r3"), ("p4", "r4"), ("p5", "r5")] {
        let (n, t) = (load(namesake), load(twin));
        assert_eq!(
            shape(&n),
            shape(&t),
            "{namesake} (`{:?}`) must get exactly the obligations of its renamed twin {twin} \
             (`{:?}`)",
            callees(&n),
            callees(&t)
        );
    }
}

/// core's `div_ceil` / `rem_euclid` / `div_euclid` keep exactly one row, refuted when
/// the divisor is unconstrained and proved under a dominating `b != 0`.
#[test]
fn cores_divisor_methods_keep_their_row_and_their_verdict() {
    for (name, want_callee, kind, refuted) in [
        ("c1", "core::num::<impl u32>::div_ceil", VcKind::DivisionByZero, true),
        ("c3", "core::num::<impl i64>::rem_euclid", VcKind::RemainderByZero, true),
        ("c4", "core::num::<impl i32>::div_euclid", VcKind::DivisionByZero, true),
        ("g1", "core::num::<impl u32>::div_ceil", VcKind::DivisionByZero, false),
    ] {
        let func = load(name);
        assert_eq!(callees(&func), [want_callee], "{name}: fixture premise");
        let rows = zero_divisor_rows(&func);
        assert_eq!(rows.len(), 1, "{name}: core's `{want_callee}` keeps exactly one row");
        assert_eq!(rows[0].kind, kind, "{name}");
        let v = verdict(&rows[0]);
        if refuted {
            assert!(
                matches!(v, VerificationResult::Failed { .. }),
                "{name}: an unconstrained divisor reaches zero: REFUTED; got {v:?}"
            );
        } else {
            assert!(
                matches!(v, VerificationResult::Proved { .. }),
                "{name}: `if b != 0` must PROVE the row; got {v:?}"
            );
        }
    }
}

/// std's `Iterator::step_by` keeps its row on every receiver, a user iterator that
/// inherits std's default (which panics on a zero step) included.
#[test]
fn std_iterator_step_by_keeps_its_row_and_its_verdict() {
    for (name, want_step_by) in [
        (
            "c2",
            "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::step_by",
        ),
        ("s1", "<core_divzero::It as core::iter::traits::iterator::Iterator>::step_by"),
        (
            "s2",
            "<core::slice::iter::Iter<'_, u32> as core::iter::traits::iterator::Iterator>::step_by",
        ),
    ] {
        let func = load(name);
        assert!(
            callees(&func).iter().any(|c| c == want_step_by),
            "{name}: fixture premise, callees {:?}",
            callees(&func)
        );
        let rows = zero_divisor_rows(&func);
        assert_eq!(rows.len(), 1, "{name}: `{want_step_by}` keeps exactly one row");
        assert_eq!(rows[0].kind, VcKind::DivisionByZero, "{name}");
        let v = verdict(&rows[0]);
        assert!(
            matches!(v, VerificationResult::Failed { .. }),
            "{name}: an unconstrained step reaches zero: REFUTED; got {v:?}"
        );
    }
}

/// The fn-item deny-list keeps its answer for every spelling above: a `true` there
/// only withholds the vanilla admission of a sysroot item handed over as a value.
#[test]
fn the_fn_item_deny_list_answer_does_not_move() {
    for callee in [
        "user_divzero::Q::div_ceil",
        "user_divzero::rem_euclid",
        "user_divzero::div_euclid",
        "user_divzero::S::step_by",
        "<u8 as user_divzero::Euclid>::rem_euclid",
        "core::num::<impl u32>::div_ceil",
        "core::num::<impl i64>::rem_euclid",
        "core::num::<impl i32>::div_euclid",
        "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::step_by",
    ] {
        assert!(trust_vcgen::callee_has_call_site_panic_family(callee), "`{callee}`");
    }
}
