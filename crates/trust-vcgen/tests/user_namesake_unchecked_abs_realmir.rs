// Trust (2026-10-06, UNCHECKED-NAME-1 + ABS-NAME-1): two call-site recognizers that
// MINT a row decided their callee by name, not by owner.
//
// * `overflow_arith_call`'s `unchecked_{add,sub,mul}` arms read the last path segment
//   alone, so a call to a USER `fn unchecked_add(a: u32, b: u32) -> u32 { a ^ b }` was
//   charged `UncheckedArithmeticOverflow` over its arguments. Measured on the stage 1 of
//   `9e11546767`: `x_add`/`x_mul` were refused with an `unknown` row, and `y_add` (`a <
//   10 && b < 10`) read `proved | clean-kernel-certified | unchecked arithmetic overflow
//   (Add)` — a Certified row about an addition the program never performs.
// * `is_signed_abs_call` was `method_tail == "abs"` plus a `core::num::` / `std::num::`
//   SUBSTRING, so `mycore::num::abs(x)` and `G::<core::num::Wrapping<i32>>::abs(x)`
//   minted `NegationOverflow { x == i32::MIN }`, refuted at `x = -2147483648` and
//   reported as a "guaranteed Level 0 safety violation" of functions that cannot panic.
//
// The fixtures are REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>
// -Ztrust-policy=advisory`, stage 1 of `9e11546767`, optimized MIR) of
// `fixtures/user_namesake_unchecked_abs/{user_unchecked,user_abs}.rs`, one caller per
// file, spans rewritten to `<dump-root>/`. The extractor is not touched by this fix, so
// these are the bodies the fixed compiler hands vcgen as well. Every user-namesake test
// here fails on the tail/substring recognizers (one row each); the controls pin that
// core's own `unchecked_*` and `abs` keep their rows and their verdicts.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/user_namesake_unchecked_abs/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The single call's rendered callee (the fixture premise).
fn callee(func: &VerifiableFunction) -> String {
    let calls: Vec<&str> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{}: fixture premise is one call, got {calls:?}", func.name);
    calls[0].to_string()
}

fn unchecked_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::UncheckedArithmeticOverflow { .. }))
        .collect()
}

fn negation_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        .collect()
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

#[test]
fn a_call_to_a_user_fn_named_unchecked_op_mints_no_unchecked_overflow_row() {
    for (name, want_callee) in [
        ("x_add", "user_unchecked::unchecked_add"),
        ("x_mul", "user_unchecked::unchecked_mul"),
        ("y_add", "user_unchecked::unchecked_add"),
        ("y_tmul", "<u32 as user_unchecked::T>::unchecked_mul"),
    ] {
        let func = load(name);
        assert_eq!(callee(&func), want_callee, "{name}: fixture premise");
        let rows = unchecked_rows(&func);
        assert!(
            rows.is_empty(),
            "{name}: `{want_callee}` is a user function (no arithmetic at all); it owes no \
             unchecked-overflow row, got {:?}",
            rows.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }
}

/// The row only: the in-process router has no backend for `UncheckedArithmeticOverflow`
/// (it answers `Unknown`, "no backend can handle this VC"). In the compiler the
/// unguarded row reads `unknown | trust-full-verifier` and the guarded one `proved |
/// clean-kernel-certified` (stage 1 of `9e11546767`, the `controls` revision of
/// `tests/ui/trust/user_namesake_unchecked_and_abs.rs`), so what this test pins is that
/// the row is still minted, with its operation and its authenticated seed.
#[test]
fn core_unchecked_ops_keep_their_row() {
    for (name, want_callee, op) in [
        ("m_unguarded", "core::num::<impl u32>::unchecked_add", BinOp::Add),
        ("m_guarded", "core::num::<impl u32>::unchecked_add", BinOp::Add),
        ("path_unguarded", "core::num::<impl u64>::unchecked_mul", BinOp::Mul),
    ] {
        let func = load(name);
        assert_eq!(callee(&func), want_callee, "{name}: fixture premise");
        let rows = unchecked_rows(&func);
        assert_eq!(rows.len(), 1, "{name}: core's `{want_callee}` keeps exactly one row");
        assert!(
            matches!(rows[0].kind, VcKind::UncheckedArithmeticOverflow { op: o, .. } if o == op),
            "{name}: {:?}",
            rows[0].kind
        );
        assert!(
            !matches!(rows[0].formula, Formula::Bool(_)),
            "{name}: the row carries a real operand-dependent formula"
        );
        assert!(rows[0].obligation.is_some(), "{name}: the row keeps its authenticated seed");
    }
}

#[test]
fn a_call_to_a_user_abs_under_a_core_num_lookalike_path_mints_no_negation_row() {
    for (name, want_callee) in [
        ("a4", "user_abs::G::<core::num::wrapping::Wrapping<i32>>::abs"),
        ("c1", "user_abs::mycore::num::abs"),
        ("s1", "user_abs::mystd::num::abs"),
    ] {
        let func = load(name);
        assert_eq!(callee(&func), want_callee, "{name}: fixture premise");
        let rows = negation_rows(&func);
        assert!(
            rows.is_empty(),
            "{name}: `{want_callee}` is a user function (`x ^ 1`, it cannot panic); it owes \
             no negation row, got {:?}",
            rows.iter().map(|vc| (&vc.kind, vc.formula.to_smtlib())).collect::<Vec<_>>()
        );
    }
}

#[test]
fn core_signed_abs_keeps_its_row_and_its_verdict() {
    for (name, refuted) in [("e1", true), ("e2", false)] {
        let func = load(name);
        assert_eq!(callee(&func), "core::num::<impl i32>::abs", "{name}: fixture premise");
        let rows = negation_rows(&func);
        assert_eq!(rows.len(), 1, "{name}: core's `i32::abs` keeps exactly one negation row");
        let v = verdict(&rows[0]);
        if refuted {
            assert!(
                matches!(v, VerificationResult::Failed { .. }),
                "{name}: unguarded `x.abs()` panics at `i32::MIN`: REFUTED; got {v:?}"
            );
        } else {
            assert!(
                matches!(v, VerificationResult::Proved { .. }),
                "{name}: `x != i32::MIN` must PROVE the row; got {v:?}"
            );
        }
    }
}

/// The accept/reject table of the exported predicate trust-clean's negation-subject
/// gates now call, and the fn-item deny-list's unchanged answer.
#[test]
fn signed_abs_predicate_accepts_exactly_cores_signed_integer_abs() {
    for callee in [
        "core::num::<impl i8>::abs",
        "core::num::<impl i16>::abs",
        "core::num::<impl i32>::abs",
        "core::num::<impl i64>::abs",
        "core::num::<impl i128>::abs",
        "core::num::<impl isize>::abs",
        "std::num::<impl i32>::abs",
        "std::num::<impl isize>::abs",
    ] {
        assert!(trust_vcgen::is_signed_abs_call(callee), "`{callee}` is core's signed `abs`");
        assert!(trust_vcgen::callee_has_call_site_panic_family(callee), "`{callee}`");
    }
    // Spellings the old SUBSTRING test accepted. Each is refused now; the deny-list
    // (`callee_has_call_site_panic_family`, which only withholds an admission) keeps
    // answering `true` for every one of them, as before.
    for callee in [
        "user_abs::mycore::num::abs",
        "user_abs::mystd::num::abs",
        "user_abs::G::<core::num::wrapping::Wrapping<i32>>::abs",
        "foo_core::num::abs",
        "__trust_crate@1973d11b2baa21fa::core::num::<impl i32>::abs",
        // Core items that are not the primitive inherent `abs`: `Wrapping`/`Saturating`
        // are total, and `NonZero<iN>::abs` is charged by its own refusal
        // (`numeric_panic`, "nonzero-negation-overflow-unmodeled").
        "core::num::wrapping::Wrapping::<i32>::abs",
        "core::num::saturating::Saturating::<i32>::abs",
        "core::num::nonzero::NonZero::<i32>::abs",
        // core has no unsigned `abs`.
        "core::num::<impl u32>::abs",
    ] {
        assert!(!trust_vcgen::is_signed_abs_call(callee), "`{callee}` is not core's signed `abs`");
        assert!(
            trust_vcgen::callee_has_call_site_panic_family(callee),
            "`{callee}`: the deny-list answer must not move"
        );
    }
    // Never matched, before or after.
    for callee in [
        "core::num::<impl i32>::wrapping_abs",
        "core::num::<impl i32>::unsigned_abs",
        "core::num::<impl i32>::checked_abs",
        "core::num::<impl i32>::abs_diff",
        "core::f64::<impl f64>::abs",
        "abs",
        "<i32 as num_traits::Signed>::abs",
    ] {
        assert!(!trust_vcgen::is_signed_abs_call(callee), "`{callee}`");
    }
}
