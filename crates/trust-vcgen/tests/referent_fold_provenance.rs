//! Trust: 2026-09-18 — THE PROVENANCE NARROWING OF THE UNATTRIBUTABLE-STORE ARM,
//! MEASURED ON THE SAME REAL-COMPILER MIR THE ROUND-A13 ROWS USE.
//!
//! `referent_fold::written_place_rebinds`' unattributable-store arm used to ask
//! `guard_reachable_by_pointer` — "does a borrow of this guard exist ANYWHERE in the
//! body" — about a store whose pointer it could not resolve. The two questions have no
//! connection to each other, so a `vec![..]` in scope plus any borrow of a guard
//! refused the fold, the store havocked instead of defining, and a correct program was
//! REFUTED. `docs/KNOWN_HAZARDS.md`, "The referent fold refuses a correct program when
//! a shared borrow meets an unattributable store (2026-09-18)".
//!
//! The arm now conjoins provenance: `unattributable_store_rebinds` asks whether the
//! STORE'S OWN pointer local may hold a value derived from one of those borrows,
//! through a fail-closed forward taint. This file pins the two directions of that
//! narrowing against each other on the `escaped_seam_rev19b_*` fixtures — captures from
//! the pristine prebuilt stage1 driver, the same ones
//! `escaped_local_seam_realmir.rs`'s `a13p2_*` rows read:
//!
//!  * RECOVERED — `v6_shared_param_drop_ctl` at `-O0`, whose `vec![1u8, 2, 3]` desugar
//!    stores `(*_28).1.0.0 = [1, 2, 3]` through a raw pointer derived from
//!    `Box::<[u8; 3]>::new_uninit()`, while the body's only borrow of the guard `_3` is
//!    the shared `_10 = &_3`. Nothing connects the two, and the store cannot rebind
//!    `j`. The oracle quoted beside the fixtures never panics (`v6_..._ctl: ok 13`).
//!  * STILL CLOSED — `v3_shared_param_cast_store_bug`, where the unresolvable pointer
//!    IS the laundered borrow (`_13 = &_3; _12 = &raw const (*_13);
//!    launder(_12) -> _11; (*_11) = _4`), and `v4_mut_param_guard_bug`, its `&mut`
//!    twin. Both PANIC at runtime and the sealed driver PROVED `v3`; a narrowing that
//!    admits either is a false proof and strictly worse than the bug it fixes.
//!
//! Every verdict here is this crate's own `generate_vcs` + the deterministic in-process
//! `ay` router, exactly as in `escaped_local_seam_realmir.rs`.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

fn fixture(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/escaped_seam_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

type RowAt = (VcKind, VerificationResult, bool, (usize, usize));

fn verdicts_at(name: &str) -> Vec<RowAt> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = trust_router::Router::deterministic_in_process_ay(
                30_000,
                trust_types::determinism::EffortScale::BUILTIN,
            );
            router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    let at = (vc.location.line_start as usize, vc.location.col_start as usize);
                    (vc.kind, r, certified, at)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn is_refuted(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Failed { counterexample: Some(_), .. })
}

fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

fn is_index_oob(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds)
}

/// Every bounds row at `(line, col)` PROVES, and no refuted row of the body is
/// kernel-certified.
fn assert_bounds_rows_prove(name: &str, at: (usize, usize)) {
    let rows = verdicts_at(name);
    let here: Vec<&RowAt> =
        rows.iter().filter(|(k, _, _, loc)| is_bounds(k) && *loc == at).collect();
    assert!(!here.is_empty(), "{name}: the bounds row at {at:?} must be generated; rows {rows:?}");
    for (kind, verdict, _, _) in &here {
        assert!(is_proved(verdict), "{name}: {kind:?} at {at:?} must PROVE; got {verdict:?}");
    }
    for (_, r, c, _) in &rows {
        assert!(!(is_refuted(r) && *c), "{name}: a refuted row may not also be kernel-certified");
    }
}

/// The `IndexOutOfBounds` row at `(line, col)` is NOT proved, and no false proof there
/// is kernel-certified.
fn assert_read_not_proved(name: &str, at: (usize, usize)) {
    let rows = verdicts_at(name);
    let read: Vec<&RowAt> =
        rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == at).collect();
    assert!(!read.is_empty(), "{name}: the read row at {at:?} must be generated; rows {rows:?}");
    for (kind, verdict, certified, _) in &read {
        assert!(
            !is_proved(verdict),
            "{name}: the read at {at:?} ({kind:?}) is PROVED on a panicking program; got {verdict:?}"
        );
        assert!(
            !(is_proved(verdict) && *certified),
            "{name}: a false proof at {at:?} may never be kernel-certified"
        );
    }
    for (_, r, c, _) in &rows {
        assert!(!(is_refuted(r) && *c), "{name}: a refuted row may not also be kernel-certified");
    }
}

/// THE FALSE REFUTATION THE PROVENANCE-BLIND ARM MINTED.
///
/// ```ignore
/// pub fn v6_shared_param_drop_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
///     if s.len() < 4 { return 0; }
///     if j >= s.len() { return 0; }
///     let q = &j;                 // the only borrow of the guard `j`: SHARED
///     let r = &mut s[j];          // referent `(*s)[j]`, guards `s` and `j`
///     { let v = vec![1u8, 2, 3]; let _n = v.len() + *q; }
///     *r = 3;                     // s[j] == 3, so `s[j] as usize == 3 < 4`
///     t[s[j] as usize]            // L82 — REFUTED at -O0 before this change
/// }
/// ```
///
/// At `-O1` the allocation is gone and both rows already proved; at `-O0` the `vec!`
/// desugar's `(*_28).1.0.0 = [1, 2, 3]` is an unresolvable store, and the old arm
/// answered it with the body-global "is `j` borrowed anywhere" — which the shared
/// `_10 = &_3` makes true. `_28` is a cast of `Box::<[u8; 3]>::new_uninit()`'s
/// destination and carries no borrow of `_3`, so the taint leaves it clean and the
/// fold stands.
#[test]
fn a_vec_in_scope_no_longer_refutes_a_shared_borrow_of_the_guard() {
    for name in ["rev19b_v6_shared_param_drop_ctl_o0", "rev19b_v6_shared_param_drop_ctl_o1"] {
        assert_bounds_rows_prove(name, (82, 4));
        assert_bounds_rows_prove(name, (82, 6));
    }
}

/// THE ROW THE NARROWING MAY NOT REACH — the store whose pointer IS the borrow.
///
/// `v3`: `let pj = launder(&j); … unsafe { *pj = k }; *r = 3; t[s[j] as usize]`, which
/// PANICS (`v3_..._bug: PANIC`) and which the sealed pre-campaign driver PROVED at
/// `-O0`. The taint seeds on `_13 = &_3`, carries through the `&raw const (*_13)`
/// re-derivation and through `launder`'s destination, so `(*_11) = _4` is still
/// attributed to the guard and the fold is still refused. `v4` is the `&mut` twin,
/// whose store resolves to `_3` outright and never reaches this arm — it says the
/// change did not delete the question.
///
/// A fix that recovered `v6` above by also admitting these two would be a FALSE PROVE,
/// which is worse than the false refutation it closes.
#[test]
fn a_laundered_borrow_written_through_is_still_attributed_to_the_guard() {
    for name in
        ["rev19b_v3_shared_param_cast_store_bug_o0", "rev19b_v3_shared_param_cast_store_bug_o1"]
    {
        assert_read_not_proved(name, (46, 4));
    }
    for name in ["rev19b_v4_mut_param_guard_bug_o0", "rev19b_v4_mut_param_guard_bug_o1"] {
        assert_read_not_proved(name, (58, 4));
    }
}

/// THE CONTROLS THAT SEPARATE "THE QUESTION WAS NARROWED" FROM "THE QUESTION STOPPED
/// BEING ASKED". `v1` (a shared borrow, no call in the region), `v2` (the borrow passed
/// to a call), `v5` (no borrow of the guard at all) and `v7` (the borrow taken after the
/// region) proved through every round and must keep proving: the narrowing touches only
/// the arm reached by a store whose pointer does not resolve, and none of these four
/// bodies has one.
#[test]
fn the_rows_that_already_proved_still_prove() {
    for name in ["rev19b_v1_shared_param_no_call_ctl_o0", "rev19b_v1_shared_param_no_call_ctl_o1"] {
        assert_bounds_rows_prove(name, (22, 4));
        assert_bounds_rows_prove(name, (22, 6));
    }
    for name in ["rev19b_v2_shared_param_call_ctl_o0", "rev19b_v2_shared_param_call_ctl_o1"] {
        assert_bounds_rows_prove(name, (33, 4));
        assert_bounds_rows_prove(name, (33, 6));
    }
    for name in ["rev19b_v5_plain_param_call_ctl_o0", "rev19b_v5_plain_param_call_ctl_o1"] {
        assert_bounds_rows_prove(name, (68, 4));
        assert_bounds_rows_prove(name, (68, 6));
    }
    for name in
        ["rev19b_v7_shared_param_borrow_after_ctl_o0", "rev19b_v7_shared_param_borrow_after_ctl_o1"]
    {
        assert_bounds_rows_prove(name, (92, 12));
        assert_bounds_rows_prove(name, (92, 14));
    }
}
