// Trust (wave-19 review, 2026-10-09): a STAMPED GENUINE core keeps the rows of its
// `abs`, `unchecked_add` and `pow`, on REAL extracted MIR. Wave 23 (2026-10-11) adds the
// numeric family's rows (`ilog2`, `strict_add`, `clamp`, `next_power_of_two`,
// `strict_neg`) and the disclosed cost of that fix; see the section at the end.
//
// The extractor stamps the real core's paths (`__trust_crate@<id>::core::…`) whenever
// another crate named `core` is in the graph (`trust_types::sysroot_identity_stamp_required`,
// rule 1), and under `-Zbuild-std` (rule 2). ABS-NAME-1 and UNCHECKED-NAME-1 anchored the
// `abs` and `unchecked_*` arms on `numeric_panic::int_inherent`, which refuses every
// stamp, as POW-SYMEXP-1 had for `pow`. MEASURED on the stage 1 of `46e9afaf95` with a
// verify-off `--crate-name core` dependency in the graph: `x.abs()` lost its `negation`
// row (refuted at `x = i32::MIN` on the stage 1 of `f39efe05ca`), the default build went
// from exit 1 to exit 0 on a `runtime_checked` row, and the binary panicked "attempt to
// negate with overflow"; `unsafe { a.unchecked_add(b) }` lost its `unchecked_overflow`
// row; `a.pow(e)` was charged only its absent-callee row on both.
//
// The minting arms now read core's exact spelling behind one leading stamp
// (`numeric_panic::int_inherent_minting`). Each test below fails before that change
// (no row is generated). Fixtures: `-Ztrust-dump=mir-only` captures by that stage 1 of
// `fixtures/stamped_genuine_core/stamped_core.rs.txt`, one function per file.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/stamped_genuine_core/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// The fixture premise: the one call is core's, behind the extractor's stamp.
fn assert_stamped_core_callee(func: &VerifiableFunction, leaf: &str) {
    let calls: Vec<&str> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{}: one call, got {calls:?}", func.name);
    let callee = calls[0];
    assert!(
        callee.starts_with(TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX)
            && callee.contains("::core::num::<impl ")
            && callee.ends_with(leaf),
        "{}: fixture premise is a stamped core `{leaf}`, got `{callee}`",
        func.name
    );
    assert!(!path_root_is_authenticated_sysroot_crate(callee), "premise: the stamp is there");
}

fn verdicts(vcs: &[VerificationCondition]) -> Vec<VerificationResult> {
    let router = test_router::deterministic_test_router();
    vcs.iter()
        .map(|vc| router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1)
        .collect()
}

fn rows(name: &str, leaf: &str, keep: impl Fn(&VcKind) -> bool) -> Vec<VerificationResult> {
    let func = load(name);
    assert_stamped_core_callee(&func, leaf);
    let vcs: Vec<VerificationCondition> =
        generate_vcs(&func).into_iter().filter(|vc| keep(&vc.kind)).collect();
    assert_eq!(vcs.len(), 1, "{name}: exactly one `{leaf}` row must be minted; got {vcs:#?}");
    verdicts(&vcs)
}

#[test]
fn a_stamped_core_abs_keeps_its_negation_row() {
    let neg = |k: &VcKind| matches!(k, VcKind::NegationOverflow { .. });
    let unguarded = rows("abs_unguarded", "abs", neg);
    assert!(
        matches!(unguarded[0], VerificationResult::Failed { .. }),
        "`x.abs()` panics at i32::MIN and must be refuted: {unguarded:?}"
    );
    let guarded = rows("abs_guarded", "abs", neg);
    assert!(
        matches!(guarded[0], VerificationResult::Proved { .. }),
        "`if x != i32::MIN {{ x.abs() }}` must prove: {guarded:?}"
    );
}

#[test]
fn a_stamped_core_unchecked_add_keeps_its_ub_row() {
    let r = rows("unchecked_add_unguarded", "unchecked_add", |k| {
        matches!(k, VcKind::UncheckedArithmeticOverflow { op: BinOp::Add, .. })
    });
    assert!(
        !matches!(r[0], VerificationResult::Proved { .. }),
        "an unguarded `a.unchecked_add(b)` must not prove: {r:?}"
    );
}

#[test]
fn a_stamped_core_pow_keeps_its_overflow_row() {
    let r = rows("pow_unguarded", "pow", |k| matches!(k, VcKind::ArithmeticOverflow { .. }));
    assert!(
        matches!(r[0], VerificationResult::Failed { .. }),
        "an unguarded `a.pow(e)` overflows and must be refuted: {r:?}"
    );
}

// ----- the numeric family (wave 23, STAMPED-CORE-MINT-1 residual, 2026-10-11) -----
//
// `numeric_panic::numeric_value_panic_row` and `numeric_overflow_call` authenticated
// the callee through `int_inherent`, or through the trait half of a qualified spelling
// that the stamp hid (`__trust_crate@414739228a72f04f::<i32 as core::cmp::Ord>::clamp`,
// the stamp in front of the WHOLE path). In a graph that stamps core they minted
// nothing for `ilog2`, `strict_add`, `clamp`, `next_power_of_two` and `strict_neg`:
// MEASURED on the stage 1 of `5911b1325f`, the default build of each unguarded call
// exits 0 on a `runtime_checked` row, and a verify-on binary exits 101 on the caller's
// value. Both now read past one leading stamp (`numeric_panic::after_one_identity_stamp`).
// Each test below fails before that change (no family row is generated). Fixtures:
// `-Ztrust-dump=mir-only` captures by that stage 1 of
// `fixtures/stamped_genuine_core/stamped_core_family.rs.txt`, one function per file.

/// The fixture premise for a family call: exactly one call, core's spelling `rest`
/// behind ONE well-formed extractor stamp.
fn assert_stamped_family_callee(func: &VerifiableFunction, rest: &str) {
    let calls: Vec<&str> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{}: one call, got {calls:?}", func.name);
    let callee = calls[0];
    let after = callee
        .strip_prefix(TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX)
        .and_then(|r| r.split_once("::"))
        .map(|(id, after)| (id.len() == 16 && id.bytes().all(|b| b.is_ascii_hexdigit()), after));
    assert_eq!(
        after,
        Some((true, rest)),
        "{}: fixture premise is a stamped core `{rest}`, got `{callee}`",
        func.name
    );
    assert!(!path_root_is_authenticated_sysroot_crate(callee), "premise: the stamp is there");
}

fn family_rows(name: &str, rest: &str, keep: impl Fn(&VcKind) -> bool) -> Vec<VerificationResult> {
    let func = load(name);
    assert_stamped_family_callee(&func, rest);
    let vcs: Vec<VerificationCondition> =
        generate_vcs(&func).into_iter().filter(|vc| keep(&vc.kind)).collect();
    assert_eq!(vcs.len(), 1, "{name}: exactly one `{rest}` row must be minted; got {vcs:#?}");
    verdicts(&vcs)
}

fn assertion_starting(prefix: &'static str) -> impl Fn(&VcKind) -> bool {
    move |k| matches!(k, VcKind::Assertion { message } if message.starts_with(prefix))
}

/// The unguarded call's row must be REFUTED (the in-process solver finds the
/// panicking argument), and the guarded twin's must prove.
fn unguarded_refuted_guarded_proved(stem: &str, rest: &str, keep: impl Fn(&VcKind) -> bool + Copy) {
    let unguarded = family_rows(&format!("{stem}_family_unguarded"), rest, keep);
    assert!(
        matches!(unguarded[0], VerificationResult::Failed { .. }),
        "an unguarded stamped `{rest}` panics for some argument and must be refuted: {unguarded:?}"
    );
    let guarded = family_rows(&format!("{stem}_family_guarded"), rest, keep);
    assert!(
        matches!(guarded[0], VerificationResult::Proved { .. }),
        "the guarded stamped `{rest}` must prove: {guarded:?}"
    );
}

#[test]
fn a_stamped_core_ilog2_keeps_its_domain_row() {
    unguarded_refuted_guarded_proved(
        "ilog2",
        "core::num::<impl u32>::ilog2",
        &assertion_starting("ilog2: argument of integer logarithm must be positive"),
    );
}

#[test]
fn a_stamped_core_strict_add_keeps_its_overflow_row() {
    let add = |k: &VcKind| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. });
    let unguarded =
        family_rows("strict_add_family_unguarded", "core::num::<impl u32>::strict_add", add);
    assert!(
        matches!(unguarded[0], VerificationResult::Failed { .. }),
        "an unguarded `a.strict_add(b)` overflows and must be refuted: {unguarded:?}"
    );
    let guarded =
        family_rows("strict_add_family_guarded", "core::num::<impl u32>::strict_add", add);
    assert!(
        matches!(guarded[0], VerificationResult::Proved { .. }),
        "`if a < 1000 && b < 1000 {{ a.strict_add(b) }}` must prove: {guarded:?}"
    );
}

#[test]
fn a_stamped_core_clamp_keeps_its_bounds_row_through_the_qualified_spelling() {
    unguarded_refuted_guarded_proved(
        "clamp",
        "<i32 as core::cmp::Ord>::clamp",
        &assertion_starting("Ord::clamp: min > max"),
    );
}

#[test]
fn a_stamped_core_next_power_of_two_keeps_its_overflow_row() {
    unguarded_refuted_guarded_proved(
        "next_power_of_two",
        "core::num::<impl u32>::next_power_of_two",
        &assertion_starting("next_power_of_two: attempt to add with overflow"),
    );
}

#[test]
fn a_stamped_core_strict_neg_keeps_its_negation_row() {
    unguarded_refuted_guarded_proved(
        "strict_neg",
        "core::num::<impl i32>::strict_neg",
        &assertion_starting("strict_neg: attempt to negate with overflow"),
    );
}

/// The disclosed COST of reading past the stamp (DECISION_QUEUE STAMPED-CORE-MINT-2):
/// `Duration::from_secs(1) + Duration::from_secs(2)` in a graph that stamps core. The
/// `Add` call now reaches `duration_op_row`, but the GRANT that decides its operands
/// from literals (`literal_duration_nanos`) stays authenticated, because a forged
/// `core::time::Duration::from_secs` could return a value at the edge. The stamped
/// constructors are therefore not read as literals, and the sum is charged the
/// fail-closed row: a false red where the plain graph proves a decided row
/// (`std_numeric_family/dur_lit_add.json`, `Want::Proved`). MEASURED BEFORE on the
/// stage 1 of `5911b1325f` (this fixture's source, default policy): accepted with
/// warnings on one `runtime_checked` absent-callee row.
#[test]
fn a_stamped_core_literal_duration_sum_is_refused_not_decided() {
    let func = load("dur_lit_add_family_cost");
    let calls: Vec<&str> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 3, "premise: two constructors and one `Add`, got {calls:?}");
    let stamp = "__trust_crate@414739228a72f04f::";
    assert!(
        calls[..2].iter().all(|c| *c == format!("{stamp}core::time::Duration::from_secs")),
        "premise: stamped constructors, got {calls:?}"
    );
    assert!(
        calls[2]
            .starts_with(&format!("{stamp}<core::time::Duration as core::ops::arith::Add>::add")),
        "premise: the stamped `Add`, got {calls:?}"
    );
    let unmodeled: Vec<String> = generate_vcs(&func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, .. } if kind.starts_with("duration-") => Some(kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        unmodeled,
        ["duration-arith-overflow-unmodeled"],
        "the stamped literal sum is charged the fail-closed row, not decided"
    );
}
