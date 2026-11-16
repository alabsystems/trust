// Trust (2026-10-10, sweep p50): a `for i in 0..k` whose end `k` is a JOINED local
// (`let k = if n > 26 { 26 } else { n }`, MIR `_7 = copy _2` with `_2` written on
// both arms) gets its yield fact `i < _7` on the single-valued copy
// (`iterator_yield::resolve_range_bound_formula`). Before, the walk followed the copy
// into the multiply-written `_2` and withheld the fact, so `b'a' + i` was refuted
// with `i = 159` over an end of 0. Fixtures are the real extracted MIR
// (`-Ztrust-dump=mir`) of the programs quoted on each test; the end-to-end pin is
// `tests/ui/trust/policy_b/range_joined_end.rs`.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/range_joined_end/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// The verdict of every panic row the loop body carries (bounds and arithmetic).
fn panic_row_verdicts(name: &str) -> Vec<(String, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    generate_vcs(&func)
        .into_iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::SliceBoundsCheck
                    | VcKind::IndexOutOfBounds
                    | VcKind::ArithmeticOverflow { .. }
            )
        })
        .map(|vc| {
            let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
            (vc.formula.to_smtlib(), r)
        })
        .collect()
}

fn assert_all_proved(name: &str) {
    let rows = panic_row_verdicts(name);
    assert!(!rows.is_empty(), "{name}: the loop body must still carry its panic rows");
    for (smt, r) in &rows {
        assert!(
            matches!(r, VerificationResult::Proved { .. }),
            "{name}: must PROVE\n{smt}\n=> {r:?}"
        );
    }
}

fn assert_some_refuted(name: &str) {
    let rows = panic_row_verdicts(name);
    assert!(
        rows.iter().any(|(_, r)| matches!(r, VerificationResult::Failed { .. })),
        "{name}: a panicking program must keep a REFUTED row\n{rows:#?}"
    );
}

/// `let k = if n > 26 { 26 } else { n }; for i in 0..k { s = s.wrapping_add(97 + i) }`
/// (`n: u8`) and `let k = if n > v.len() { v.len() } else { n }; for i in 0..k { v[i] }`.
#[test]
fn a_joined_range_end_bounds_the_payload() {
    assert_all_proved("pos1");
    assert_all_proved("pos2");
}

/// SOUNDNESS DIRECTION: the fact is `i < k` for the value `k` held when the range was
/// built, nothing more, so a joined end that can exceed the bound is REFUTED (before,
/// these rows were the Unknown `UnmodeledCalleeReturn` of an unbounded payload).
/// `if c { 200 } else { n.min(26) }` overflows `97 + i`; `if n > 100 { v.len() } else
/// { n }` indexes past a short `v`; `let mut k = n.min(4); if c { k = n }` indexes past
/// `a: &[u32; 4]`.
#[test]
fn a_joined_end_that_can_exceed_the_bound_is_refuted() {
    assert_some_refuted("neg1");
    assert_some_refuted("neg2");
    assert_some_refuted("neg5");
}

/// Review round 110: the slice-range lane reads a bound AT the indexing call, where
/// the call block's own defs are not conjoined, so a copy temp of a joined bound
/// (`_7 = copy k`) is a free name there. It asks the exact-at-call resolution before
/// the joined-copy fallback: `let k = if n < b.len() { n } else { b.len() }; &b[..k]`
/// and `&b[s..e]` over two clamped joins keep their proofs (the fallback first refuted
/// both with `_7 = 1, b__slice_len = 0`; `ui/trust/range_bound_joined_before_its_call.rs`).
#[test]
fn a_joined_slice_bound_is_read_at_its_call() {
    assert_all_proved("joined_slice_prefix");
    assert_all_proved("joined_slice_middle");
}
