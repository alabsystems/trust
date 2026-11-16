// Trust (2026-10-07, DIV-CEIL-1): the std unsigned `div_ceil` value model, pinned
// on REAL extracted MIR. The fixtures under `fixtures/div_ceil/` are
//
//     trustc --edition 2021 --crate-type lib --emit=metadata -Cpanic=abort \
//            -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory div_ceil_alloc.rs
//
// on stage1 of main `7be75e9a80` (one function per file, named by the function;
// the source sits beside them). Before the model the call's destination was
// havoc'd, so `if n > MAX { return None } vec![0; n.div_ceil(8)]` FAILED its
// unbounded-allocation row with `count = 268435456, n = 0`, while the same size
// spelled `(n + 7) / 8` proved (the `ty` crate's `tla-model-ir`
// `attr::slot_bitset` was the real site). The model is the library's own
// definition, `a / b + (a % b != 0)`; the `b == 0` panic stays charged.
//
// `repro_*` are the reporter's `divceil.rs` (beside them), dumped the same way.
//
// Every direction is load-bearing:
//   * the guarded allocations PROVE (the gap this closes), the reporter's
//     `via_div_ceil` among them, as its `(n + 7) / 8` control already did;
//   * an unguarded one, and one whose guard is too weak (`n <= 2^40` with
//     divisor 1), still FAIL — the model bounds by the true value, not a guess;
//   * at the boundary, `n <= 8 * (2^28 - 1)` PROVES and `n <= 8 * (2^28 - 1) + 1`
//     FAILS: one more element rounds UP to exactly the 2^28 ceiling, which a
//     floor (`n / 8`) model would have missed — so the model is the ceiling;
//   * returned directly, `ensures result <= 32` proves for a `u8` over 8 and
//     `<= 31` is refuted (`255.div_ceil(8) == 32`);
//   * a variable divisor still carries a REFUTED `DivisionByZero` row.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/div_ceil/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The verdict of every row of `name` whose kind `select` accepts. Panics if
/// there is none: each fixture is chosen to carry the row it is asked about.
fn verdicts(
    name: &str,
    select: impl Fn(&VcKind) -> bool,
) -> Vec<(VerificationCondition, VerificationResult)> {
    let func = load(name);
    let all = generate_vcs(&func);
    let kinds: Vec<String> = all.iter().map(|vc| format!("{:?}", vc.kind)).collect();
    let rows: Vec<VerificationCondition> = all.into_iter().filter(|vc| select(&vc.kind)).collect();
    assert!(!rows.is_empty(), "{name}: expected at least one selected row; rows: {kinds:#?}");
    let router = router();
    rows.into_iter()
        .map(|vc| {
            let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
            (vc, r)
        })
        .collect()
}

fn show(rows: &[(VerificationCondition, VerificationResult)]) -> String {
    rows.iter()
        .map(|(vc, r)| format!("{:?}\n{}\n  => {r:?}", vc.kind, vc.formula.to_smtlib()))
        .collect::<Vec<_>>()
        .join("\n")
}

fn is_alloc(k: &VcKind) -> bool {
    matches!(k, VcKind::UnboundedAllocation { .. })
}

fn all_proved(rows: &[(VerificationCondition, VerificationResult)]) -> bool {
    rows.iter().all(|(_, r)| matches!(r, VerificationResult::Proved { .. }))
}

fn any_failed(rows: &[(VerificationCondition, VerificationResult)]) -> bool {
    rows.iter().any(|(_, r)| matches!(r, VerificationResult::Failed { .. }))
}

#[test]
fn a_guarded_div_ceil_allocation_proves() {
    for name in [
        "div_ceil_bounded",
        "div_ceil_u32",
        "div_ceil_tight_ok",
        "repro_via_div_ceil",
        "repro_via_add_div",
    ] {
        let rows = verdicts(name, is_alloc);
        assert!(all_proved(&rows), "{name}: the guarded allocation must PROVE\n{}", show(&rows));
    }
}

#[test]
fn an_unbounded_div_ceil_allocation_still_fails() {
    // No guard: `n.div_ceil(8)` reaches `usize::MAX / 8 + 1`.
    // Guard too weak: `n <= 2^40` and `n.div_ceil(1) == n`, past the 2^28 ceiling.
    // One past the boundary: `(8 * (2^28 - 1) + 1).div_ceil(8) == 2^28`.
    for name in ["div_ceil_unbounded", "div_ceil_by_one_over", "div_ceil_tight_over"] {
        let rows = verdicts(name, is_alloc);
        assert!(any_failed(&rows), "{name}: the allocation must stay REFUTED\n{}", show(&rows));
    }
}

#[test]
fn a_variable_divisor_keeps_its_division_by_zero_row() {
    let rows = verdicts("div_ceil_var_divisor", |k| matches!(k, VcKind::DivisionByZero));
    assert!(any_failed(&rows), "`n.div_ceil(d)` must stay REFUTED at d == 0\n{}", show(&rows));
}

#[test]
fn a_returned_div_ceil_meets_its_postcondition_exactly() {
    let post = |k: &VcKind| matches!(k, VcKind::Postcondition);
    let rows = verdicts("div_ceil_ret_ok", post);
    assert!(all_proved(&rows), "`ensures result <= 32` must PROVE\n{}", show(&rows));
    let rows = verdicts("div_ceil_ret_over", post);
    assert!(any_failed(&rows), "`ensures result <= 31` must be REFUTED\n{}", show(&rows));
}

/// `div_ceil_bounded` with its `div_ceil` call rewritten by `edit`.
fn bounded_with_call(edit: impl Fn(&mut String, &mut Option<CalleeKey>)) -> VerifiableFunction {
    let mut func = load("div_ceil_bounded");
    let mut edited = 0;
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, callee_key, .. } = &mut block.terminator
            && callee.ends_with("::div_ceil")
        {
            edit(callee, callee_key);
            edited += 1;
        }
    }
    assert_eq!(edited, 1, "the fixture carries exactly one `div_ceil` call");
    func
}

fn alloc_fails(func: &VerifiableFunction) -> bool {
    let router = router();
    generate_vcs(func).into_iter().filter(|vc| is_alloc(&vc.kind)).any(|vc| {
        matches!(
            router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1,
            VerificationResult::Failed { .. }
        )
    })
}

#[test]
fn only_the_sysroot_unsigned_div_ceil_is_modeled() {
    // A user crate's same-spelled item: not a real-sysroot key, so no fact.
    let user = bounded_with_call(|_, key| {
        if let Some(k) = key.as_mut() {
            k.krate_is_real_sysroot = false;
        }
    });
    assert!(alloc_fails(&user), "a non-sysroot `div_ceil` must leave the count havoc'd");
    // Signed `div_ceil` (unstable, a different rounding) is deliberately unmodeled.
    let signed = bounded_with_call(|c, _| *c = "core::num::<impl isize>::div_ceil".into());
    assert!(alloc_fails(&signed), "signed `div_ceil` must stay unmodeled");
    // A path whose width disagrees with the destination (`u32` path, `usize` dest).
    let narrow = bounded_with_call(|c, _| *c = "core::num::<impl u32>::div_ceil".into());
    assert!(alloc_fails(&narrow), "a path/destination width disagreement must emit nothing");
    // A longer leaf is not `div_ceil`.
    let other = bounded_with_call(|c, _| *c = "core::num::<impl usize>::div_ceil_x".into());
    assert!(alloc_fails(&other), "only the exact `div_ceil` leaf is modeled");
}
