// Trust (STD-RECEIVER-ANCHOR-1, 2026-10-04): a `&mut v` handed to a USER `IndexMut`
// impl on std's `Vec` is not length-benign, so the `.len()` tie does not survive
// the call; std's own `Index`/`IndexMut` on std's containers still keeps it. Pinned
// on REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, `scratchpad/stage1-w11fix`, the
// stage 1 of `38e6c69b1c`; this branch's base `43dc4c407d` adds only tests and docs
// to it), one function per file under `fixtures/std_receiver_anchor/`; the sources are in the header of
// `src/generate/std_receiver_anchor_tests.rs`. The end-to-end pin is
// `tests/ui/trust/resize_benign_index_mut_requires_std_impl_run.rs`. These are
// dumps, so they pin the rows the lanes mint, not the compiler path.
//
// BEFORE, on that compiler: `user_len` (both the generic local impl and the
// dependency's impl) read `overflow:sub proved` (Certified) and its check was
// elided; `user_idx` read `slice proved`. Each std control read `overflow:sub
// proved` and must keep it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/std_receiver_anchor/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The production split of `func`'s rows of one kind: how many the interval lane
/// discharged, and the in-process verdict on each one it handed on.
fn rows(
    func: &VerifiableFunction,
    is_kind: impl Fn(&VerificationCondition) -> bool,
) -> (usize, Vec<VerificationResult>) {
    let (solver, discharged) = trust_vcgen::generate_vcs_with_discharge(func);
    let r = router();
    let routed: Vec<VerificationResult> =
        solver.iter().filter(|vc| is_kind(vc)).map(|vc| r.verify_one(vc)).collect();
    (discharged.iter().filter(|(vc, _)| is_kind(vc)).count(), routed)
}

fn is_sub(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })
}

fn is_slice(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::SliceBoundsCheck)
}

fn proved(results: &[VerificationResult]) -> bool {
    results.iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
}

/// The reclassification `havoc_decline` gives a row whose verdict rests on an
/// unconstrained call result (`UnsupportedMir`, preclassified Unknown, never
/// dispatched to a solver).
fn is_unmodeled_callee_return(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "UnmodeledCalleeReturn")
}

#[test]
fn a_user_index_mut_impl_on_std_vec_keeps_the_len_minus_one_unproved() {
    // `if v.len() == 0 { return 0; } v[K] = 1; v.len() - 1`, the impl truncating `v`.
    // Without the tie, the second `v.len()` is a call result nothing constrains, so
    // the `- 1` row is either a `Sub` row that does not prove or `havoc_decline`'s
    // Unknown. BEFORE it was one `Sub` row that proved.
    for name in ["user_generic_impl_len", "user_dep_impl_len"] {
        let func = load(name);
        let (discharged, routed) = rows(&func, is_sub);
        assert_eq!(discharged, 0, "{name}: no interval proof of `v.len() - 1`");
        assert!(
            routed.iter().all(|r| !matches!(r, VerificationResult::Proved { .. })),
            "{name}: the second `v.len()` is not the guarded one, so `- 1` may underflow: \
             {routed:?}"
        );
        let (solver, discharged_all) = trust_vcgen::generate_vcs_with_discharge(&func);
        let declined = solver.iter().filter(|vc| is_unmodeled_callee_return(vc)).count()
            + discharged_all.iter().filter(|(vc, _)| is_unmodeled_callee_return(vc)).count();
        assert_eq!(
            routed.len() + declined,
            1,
            "{name}: vacuity guard, the `- 1` row is minted (as `Sub` or as Unknown)"
        );
    }
}

#[test]
fn a_user_index_mut_impl_on_std_vec_keeps_the_index_unproved() {
    // `if i < v.len() { v[K] = 1; v[i] } else { 0 }`: the write empties `v`. Either
    // the bounds row is minted and not proved, or no row claims it at all.
    for name in ["user_generic_impl_idx", "user_dep_impl_idx"] {
        let (discharged, routed) = rows(&load(name), is_slice);
        assert_eq!(discharged, 0, "{name}");
        assert!(
            routed.iter().all(|r| !matches!(r, VerificationResult::Proved { .. })),
            "{name}: `i < v.len()` was read before `v` was emptied: {routed:?}"
        );
    }
}

#[test]
fn std_index_on_std_vec_keeps_the_len_minus_one_proved() {
    // `v[0] = 1`, `v[0..2]`, `v[1..]`, `v[..2]`, `v[..]`, `v[0..=1]`, `v[..=1]`
    // (each `.sort()`ed) between the guard and `v.len() - 1`: std's own impls.
    for name in [
        "std_vec_usize_len",
        "std_vec_range_len",
        "std_vec_range_from_len",
        "std_vec_range_to_len",
        "std_vec_range_full_len",
        "std_vec_range_incl_len",
        "std_vec_range_to_incl_len",
    ] {
        let (discharged, routed) = rows(&load(name), is_sub);
        assert_eq!(discharged + routed.len(), 1, "{name}: vacuity guard");
        assert!(proved(&routed), "{name}: std's index never resizes: {routed:?}");
    }
}
