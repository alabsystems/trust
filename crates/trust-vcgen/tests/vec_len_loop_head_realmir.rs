// Trust (VEC-LEN-LOOP-1, 2026-10-07): a std `Vec` length that nothing between its read
// and an index can change keeps that length inside a loop; a loop that may change it
// stays refuted.
//
// THE DEFECT (measured on the stage 1 of `7be75e9a80`, the preview3 snapshot of main,
// `-Ztrust-verify=on -Ztrust-verify-profile=unix_hardened -Ztrust-verify-level=2
// -Ztrust-policy=advisory -Ztrust-verify-output=json`): `ro` and `rw_vec` below read
// `slice failed` with a counterexample whose `Vec` length is 0 (`v#e_s2_t = 0`, resp.
// `v = 0`), while `first` (no loop) and `ro_slice` (`&[u8]`) proved. The `vec![0; n]`
// length fact is a semantic guard, which the guard map weakens to `true` at every loop
// header; the `_k == v.len()` tie is a path definition, which every call that havocs
// the name `v` kills (for a `&mut Vec` parameter: every call). See
// `src/generate/vec_len_invariant.rs` for the fix and its soundness argument.
//
// FIXTURES: `fixtures/vec_len_loop_head/`, one function per file, dumped
// (`-Ztrust-dump=mir:<dir>`) by that compiler from the two sources below (`veclen3`,
// `veclen4`), compiled with `--crate-type=lib --edition=2021` and the flags above. That
// compiler reported every `slice` row of the functions listed in `PROVED_AFTER` other
// than `first` and `ro_slice` FAILED, every refuted row failed too, and `own_*` read
// `container-index-unstable-len` (Unknown).
//
// The owned-`Vec` rows here are decided by that EARLIER gate
// (`guards::local_mut_borrows_may_resize`), whatever this module answers, so they pin
// only that this change does not turn them into proofs. What `vec_len_invariant`
// itself answers for an owned base, for a resizer inside or outside the stretch, and
// for the dominance and sole-predecessor gates is pinned by the unit rows in
// `src/generate/vec_len_invariant.rs`, on these same fixtures.
//
// ```ignore (source of the fixtures)
// pub fn ro(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let v = vec![0u8; n];
//     let mut acc = 0;
//     for i in 0..n { acc |= v[i]; }
//     acc
// }
// pub fn ro_slice(v: &[u8]) -> u8 {
//     let mut acc = 0;
//     for i in 0..v.len() { acc |= v[i]; }
//     acc
// }
// pub fn rw_vec(v: &mut Vec<u8>) {
//     for i in 0..v.len() { v[i] = 1; }
// }
// pub fn rw_vec_local(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let mut v = vec![0u8; n];
//     for i in 0..n { v[i] = 1; }
//     v[0..n].len() as u8
// }
// pub fn truncates(v: &mut Vec<u8>) {
//     let n = v.len();
//     for i in 0..n { v.truncate(i); v[i] = 1; }
// }
// pub fn pops(v: &mut Vec<u8>) {
//     for i in 0..v.len() { v.pop(); v[i] = 1; }
// }
// #[inline(never)]
// pub fn opaque(v: &mut Vec<u8>) { v.clear(); }
// pub fn escapes(v: &mut Vec<u8>) {
//     for i in 0..v.len() { opaque(v); v[i] = 1; }
// }
// pub fn reassigns(v: &mut Vec<u8>) {
//     for i in 0..v.len() { *v = Vec::new(); v[i] = 1; }
// }
// pub fn own_truncates(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let mut v = vec![0u8; n];
//     let mut acc = 0;
//     for i in 0..n { v.truncate(i); acc |= v[i]; }
//     acc
// }
// pub fn own_pushes(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let mut v = vec![0u8; n];
//     let mut acc = 0;
//     for i in 0..n { acc |= v[i]; v.push(1); }
//     acc
// }
// #[inline(never)]
// pub fn opaque_own(v: &mut Vec<u8>) { v.clear(); }
// pub fn own_escapes(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let mut v = vec![0u8; n];
//     let mut acc = 0;
//     for i in 0..n { opaque_own(&mut v); acc |= v[i]; }
//     acc
// }
// pub fn own_reassigns(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let mut v = vec![0u8; n];
//     let mut acc = 0;
//     for i in 0..n { acc |= v[i]; v = Vec::new(); }
//     acc
// }
// pub fn ro_off_by_one(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let v = vec![0u8; n];
//     let mut acc = 0;
//     for i in 0..=n { acc |= v[i]; }
//     acc
// }
// pub fn rw_vec_off_by_one(v: &mut Vec<u8>) {
//     for i in 0..=v.len() { v[i] = 1; }
// }
// pub fn first(n: usize) -> u8 {
//     let v = vec![0u8; n];
//     if n > 0 { v[0] } else { 0 }
// }
// ```
//
// ```ignore (source of the `veclen4` fixtures)
// pub fn push_then_rw(v: &mut Vec<u8>) {
//     v.push(0);
//     for i in 0..v.len() { v[i] = 1; }
// }
// pub fn rw_then_truncate(v: &mut Vec<u8>) {
//     for i in 0..v.len() { v[i] = 1; }
//     v.truncate(0);
// }
// pub fn pop_after_index(v: &mut Vec<u8>) {
//     for i in 0..v.len() { v[i] = 1; v.pop(); }
// }
// #[inline(never)]
// pub fn opaque(v: &mut Vec<u8>) { v.clear(); }
// pub fn opaque_then_rw(v: &mut Vec<u8>) {
//     opaque(v);
//     for i in 0..v.len() { v[i] = 1; }
// }
// pub fn own_push_then_ro(n: usize) -> u8 {
//     if n > 1000 { return 0; }
//     let mut v = Vec::new();
//     for _ in 0..n { v.push(0u8); }
//     let mut acc = 0;
//     for i in 0..v.len() { acc |= v[i]; }
//     acc
// }
// ```
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
use trust_types::{
    Terminator, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/vec_len_loop_head/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

fn is_slice(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::SliceBoundsCheck)
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

/// `(interval-discharged slice rows, routed slice verdicts)` for `func`.
fn slice_rows(func: &VerifiableFunction) -> (usize, Vec<VerificationResult>) {
    let (solver, discharged) = trust_vcgen::generate_vcs_with_discharge(func);
    let r = router();
    let routed: Vec<VerificationResult> =
        solver.iter().filter(|vc| is_slice(vc)).map(|vc| r.verify_one(vc)).collect();
    (discharged.iter().filter(|(vc, _)| is_slice(vc)).count(), routed)
}

/// Every `index`/`index_mut` callee of `func` (vacuity guard: the row under test is
/// the std `Vec`/slice index the fixture source names).
fn index_callees(func: &VerifiableFunction) -> Vec<&str> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: callee, .. }
                if callee.ends_with("::index") || callee.ends_with("::index_mut") =>
            {
                Some(callee.as_str())
            }
            _ => None,
        })
        .collect()
}

/// `(fixture, slice rows)`: each row proved, by the interval lane or ay.
const PROVED_AFTER: &[(&str, usize)] =
    &[("ro", 1), ("rw_vec", 1), ("rw_vec_local", 1), ("first", 1), ("ro_slice", 1)];

/// The one fail-honest `container-index-unstable-len` row of `func` (preclassified, so
/// it sits in the discharged list with its verdict), asserted present and unproved,
/// and no slice row proved by either lane.
///
/// Trust (VEC-LEN-PARAM-COPY-1, 2026-10-07): the length-stability oracle now sees a
/// `&mut Vec` parameter handed by `copy _1` to any callee outside std's length-benign
/// set, so a `&mut Vec` parameter that reaches a resizer or an unknown callee
/// ANYWHERE in the body has no recoverable length at its index: the EARLIER gate
/// (`collection_abstract_len_with_base`) answers Unknown before
/// `vec_len_invariant` sees the row. Before that fix the row was minted and only
/// the path-definition kill kept a resize loop refuted.
fn assert_fail_honest_unknown(name: &str, func: &VerifiableFunction) {
    let (discharged, routed) = slice_rows(func);
    assert_eq!(discharged, 0, "{name}: no interval proof of the index");
    assert!(routed.is_empty(), "{name}: no length-bearing slice row is minted: {routed:?}");
    let (_, discharged) = trust_vcgen::generate_vcs_with_discharge(func);
    let unstable: Vec<&VerificationResult> = discharged
        .iter()
        .filter(|(vc, _)| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "container-index-unstable-len")
        })
        .map(|(_, r)| r)
        .collect();
    assert_eq!(unstable.len(), 1, "{name}: vacuity guard, the fail-honest index row");
    assert!(!is_proved(unstable[0]), "{name}: {unstable:?}");
}

#[test]
fn an_unchanged_vec_length_survives_the_loop_head() {
    for &(name, n) in PROVED_AFTER {
        let func = load(name);
        let (discharged, routed) = slice_rows(&func);
        assert_eq!(discharged + routed.len(), n, "{name}: vacuity guard, {n} slice row(s)");
        assert!(routed.iter().all(is_proved), "{name}: the length is unchanged: {routed:?}");
    }
    assert!(
        index_callees(&load("rw_vec"))
            .iter()
            .any(|c| c.starts_with("<alloc::vec::Vec<u8> as core::ops::index::IndexMut<usize>>")),
        "vacuity guard: `rw_vec` writes through std's `IndexMut` on the `&mut Vec`"
    );
}

#[test]
fn a_loop_that_may_change_the_length_is_never_proved() {
    // `truncates`/`pops`/`escapes`/`reassigns` change (or may change) the length of the
    // `&mut Vec` in the loop before indexing, `pop_after_index` after it (the next
    // iteration indexes the shorter vector). Since VEC-LEN-PARAM-COPY-1 the length
    // oracle sees `copy _1` reach the resizer, so the index is the fail-honest
    // Unknown, no longer a minted row that only the path-definition kill refutes.
    for name in ["truncates", "pops", "escapes", "reassigns", "pop_after_index"] {
        assert_fail_honest_unknown(name, &load(name));
    }
}

#[test]
fn an_index_one_past_the_end_stays_refuted() {
    // The two off-by-one twins never change the length but index one past the end.
    for name in ["ro_off_by_one", "rw_vec_off_by_one"] {
        let func = load(name);
        let (discharged, routed) = slice_rows(&func);
        assert_eq!(discharged, 0, "{name}: no interval proof of the index");
        assert_eq!(routed.len(), 1, "{name}: vacuity guard, the slice row is minted");
        assert!(
            !routed.iter().any(is_proved),
            "{name}: the index may be out of bounds: {routed:?}"
        );
    }
}

#[test]
fn an_owned_vec_resized_in_the_loop_mints_no_provable_row() {
    // The `&mut v` the resize takes keeps the length unrecoverable at the index
    // (`container-index-unstable-len`, Unknown); this change must not turn it into a
    // provable bounds row. Decided by the EARLIER gate (see the header): not a pin of
    // this module's owned-base scan, which the unit rows pin.
    for name in ["own_truncates", "own_pushes", "own_escapes", "own_reassigns", "own_push_then_ro"]
    {
        let func = load(name);
        let (discharged, routed) = slice_rows(&func);
        assert_eq!(discharged, 0, "{name}");
        assert!(!routed.iter().any(is_proved), "{name}: {routed:?}");
        // The fail-honest row is preclassified, so it is in the discharged list with
        // its verdict, which must not be a proof.
        let (_, discharged) = trust_vcgen::generate_vcs_with_discharge(&func);
        let unstable: Vec<&VerificationResult> = discharged
            .iter()
            .filter(|(vc, _)| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "container-index-unstable-len")
            })
            .map(|(_, r)| r)
            .collect();
        assert_eq!(unstable.len(), 1, "{name}: vacuity guard, the fail-honest index row");
        assert!(!is_proved(unstable[0]), "{name}: {unstable:?}");
    }
}

#[test]
fn a_mut_vec_parameter_resized_outside_the_stretch_is_unknown() {
    // CAPABILITY COST of VEC-LEN-PARAM-COPY-1 (measured, recorded in DECISION_QUEUE):
    // `push_then_rw` resizes before the length is read and `rw_then_truncate` after the
    // loop, so no resizer runs between the read and the index and the index is in
    // bounds. VEC-LEN-LOOP-1 proved both, but only because the earlier length gate
    // missed the `copy _1` into `push`/`truncate` and called the parameter's length
    // stable. That same blindness let a resize INSIDE the stretch through, kept
    // refuted by the path-definition kill alone. The gate now sees the resizer and
    // answers Unknown; recovering these two needs the version oracle to re-version a
    // `&mut Vec` parameter's length at the resizing call (KNOWN_HAZARDS
    // VEC-LEN-PARAM-COPY-1, CLOSED, its residual).
    for name in ["push_then_rw", "rw_then_truncate"] {
        assert_fail_honest_unknown(name, &load(name));
    }
}

#[test]
fn a_resizer_must_be_std_s_own() {
    // `push_then_rw`'s one resizer is std `Vec::push`, run before the length is read
    // (VEC-LEN-LOOP-1 proved it until VEC-LEN-PARAM-COPY-1; see above). Re-point that call at a user function taking the
    // `&mut Vec` (crate identity included), keeping std's `IndexMut<usize>` index and
    // the `Vec::len` read: the parameter now reaches a callee that may resize (or
    // retain it), so no loop-invariant length is minted and the row stays unproved.
    let mut func = load("push_then_rw");
    let mut touched = 0;
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: callee, callee_key: Some(key), .. } = &mut b.terminator
            && callee == "alloc::vec::Vec::<u8>::push"
        {
            *callee = "veclen4::my_push".to_string();
            key.krate_is_real_sysroot = false;
            key.krate_name = "veclen4".to_string();
            touched += 1;
        }
    }
    assert_eq!(touched, 1, "vacuity guard: one std `push`");
    assert!(
        index_callees(&func)
            .iter()
            .any(|c| c.starts_with("<alloc::vec::Vec<u8> as core::ops::index::IndexMut<usize>>")),
        "vacuity guard: the index stays std's own, so the use block is still collected"
    );
    // A user callee may resize: never proved. Since VEC-LEN-PARAM-COPY-1 the earlier
    // gate refuses it (as it refuses std's `push` here, see above); the unit rows in
    // `src/generate/vec_len_invariant.rs` pin this module's own answer for the
    // re-pointed `push`.
    assert_fail_honest_unknown("push_then_rw re-pointed", &func);
}

#[test]
fn an_unknown_callee_anywhere_still_refuses_the_base() {
    // OPEN residual (DECISION_QUEUE VEC-LEN-LOOP-1): `opaque(v)` runs BEFORE `v.len()`
    // is read, so the index is in bounds, but a mention of the base that is neither
    // length-benign nor a non-retaining std resizer refuses the base for the whole
    // body (a callee may retain the pointer and a later call resize through it). The
    // row stays unproved (a false failure, never a false proof). A fix that narrows
    // this must replace this row, not delete it.
    // Since VEC-LEN-PARAM-COPY-1 the earlier length gate refuses it first.
    assert_fail_honest_unknown("opaque_then_rw", &load("opaque_then_rw"));
}
