// Regression (Vec panic-freedom soundness, 2026-07-07): `Vec::remove(i)`,
// `swap_remove(i)`, and `insert(i, x)` PANIC when the index is out of range
// (`i >= len` for remove/swap_remove, `i > len` for insert). That panic path was
// unmodeled, so a genuinely-unsafe `v.remove(i)` compiled clean — a hole in
// pillar-1 panic-freedom.
//
// The DANGER in modeling it: recovering the abstract `coll_len(v)` for the
// receiver lets a `.len()` tie (`let n = v.len()`) reach the obligation. But the
// tie-killer does NOT recognize remove/insert/swap_remove as resizes, so a tie
// minted BEFORE an intervening resize SURVIVES it and can discharge a genuinely
// out-of-bounds later access:
//
//     let n = v.len();   // n == coll_len(v)
//     v.remove(0);       // (unmodeled resize — tie NOT killed)
//     v.remove(n - 1);   // obligation (n-1) >= coll_len(v), with n == coll_len
//                        // → UNSAT → PROVED → FALSE-ACCEPT (v may now be empty!)
//
// So the lane is deliberately fail-honest: every Vec panic-method index emits an
// `UnsupportedMir { kind: "vec-panic-method-index-unmodeled" }` VC — preclassified
// Unknown, NEVER proved — and never a dischargeable `SliceBoundsCheck`. This
// over-refuses (conservative, acceptable); it can never false-accept. The
// completeness follow-up (a version-aware coll_len that treats remove/insert/
// swap_remove as resizes) is tracked separately.
//
// (2026-10-10, sweep c05) ONE exception mints the real precondition: the call is
// the SOLE resize of a `&mut Vec` parameter and no use of the vector is reachable
// after it (`value_facts::vec_sole_mutator_block`). Every `.len()` then ran before
// the resize, so `coll_len(v)` is the length the call sees. Two resizes (the shape
// above), a resize in a loop, and a use after the resize are all declined by it.
// The `vp_sole_*` fixtures are trustc MIR dumps of exactly those functions.
// (Merge of 2026-10-14) The VEC-INSERT region lane described below is asked FIRST
// (`safety.rs`, `vec_mutator_index_violation(..).or_else(..)`), so a resize no
// mutation of its vector reaches is charged over the region's fresh `L0` before
// this lane is consulted; the `vp_sole_*` tests pin which lane answers each shape.
//
// Non-Vec receivers whose `remove`/`insert` do NOT panic on an out-of-range index
// (HashMap/BTreeMap/HashSet return Option; VecDeque/String have different
// signatures) must NOT match this lane and must compile clean w.r.t. it.
//
// Trust (VEC-INSERT, 2026-09-25; these rows re-pinned in W4 fix round 1 — the
// implementing commit changed the design they pin and never ran this target). The
// follow-up the paragraph above names has landed as `generate/vec_region.rs`: a
// mutator inside its base's PRE-MUTATION REGION (no path from any write, move,
// drop or `&mut`/raw borrow of the base reaches it) is charged its REAL
// precondition, `i >= L0` / `i > L0`, over a fresh symbol `L0` that only the
// region's own `len`/`is_empty`/`deref` facts constrain. The stale-tie hazard
// above cannot reach it — `L0` is not `coll_len(v)`, and nothing minted outside
// the region names it — and a mutator reached AFTER another mutation of its base
// is outside the region and keeps the fail-honest row. So the anchors below
// now say: an unguarded mutator's charged row is REFUTED (never proved), and in
// `bat_rmrm` the SECOND remove still carries the fail-honest Unknown.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

/// The solver verdict of every `SliceBoundsCheck` row, with its column.
fn slice_bounds_verdicts(v: Vec<VerificationCondition>) -> Vec<(usize, VerificationResult)> {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let rows: Vec<VerificationCondition> =
                v.into_iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).collect();
            let router = test_router::deterministic_test_router();
            let results = router.verify_all(&rows);
            rows.iter()
                .zip(results)
                .map(|(vc, (_, verdict))| (vc.location.col_start as usize, verdict))
                .collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn vcs(name: &str) -> Vec<VerificationCondition> {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap();
    let f: VerifiableFunction = serde_json::from_str(&json).unwrap();
    generate_vcs(&f)
}

fn vec_panic_unknowns(vcs: &[VerificationCondition]) -> usize {
    vcs.iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "vec-panic-method-index-unmodeled")
        })
        .count()
}

fn slice_bounds_checks(vcs: &[VerificationCondition]) -> usize {
    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).count()
}

/// The columns of the fail-honest `vec-panic-method-index-unmodeled` rows, sorted.
fn vec_panic_unknown_columns(vcs: &[VerificationCondition]) -> Vec<usize> {
    let mut cols: Vec<usize> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "vec-panic-method-index-unmodeled")
        })
        .map(|vc| vc.location.col_start as usize)
        .collect();
    cols.sort_unstable();
    cols
}

/// Is this row's raw obligation stated over a VEC-INSERT region length (the fresh
/// `__trust_vec_region_len_<root>` of `generate/vec_region.rs`)? The sole-resize lane
/// states its row over the body-wide `coll_len(v)` instead, which a `.len()` tie
/// minted anywhere in the body can name.
fn obligation_is_over_region_length(vc: &VerificationCondition) -> bool {
    vc.obligation
        .as_ref()
        .is_some_and(|o| format!("{:?}", o.body).contains("\"__trust_vec_region_len_"))
}

#[test]
fn unconstrained_vec_remove_is_charged_and_never_proved() {
    // `fn rm(v: Vec<u8>, i: usize) { v.remove(i); }` — genuinely unsafe (i unbounded).
    let v = vcs("vp_rm");
    assert_eq!(
        vec_panic_unknowns(&v),
        0,
        "inside the base's pre-mutation region the call is charged its real precondition"
    );
    assert_eq!(slice_bounds_checks(&v), 1, "Vec::remove must carry exactly one charged row");
    for (_, verdict) in slice_bounds_verdicts(v) {
        assert!(
            matches!(verdict, VerificationResult::Failed { .. }),
            "an unguarded `v.remove(i)` must be REFUTED (`i >= L0` is satisfiable); got {verdict:?}"
        );
    }
}

#[test]
fn unconstrained_vec_swap_remove_is_charged_and_never_proved() {
    let v = vcs("vp_srm");
    assert_eq!(vec_panic_unknowns(&v), 0, "swap_remove in its region is charged, not rowed");
    assert_eq!(slice_bounds_checks(&v), 1, "swap_remove must carry exactly one charged row");
    for (_, verdict) in slice_bounds_verdicts(v) {
        assert!(
            matches!(verdict, VerificationResult::Failed { .. }),
            "an unguarded `v.swap_remove(i)` must be REFUTED; got {verdict:?}"
        );
    }
}

#[test]
fn unconstrained_vec_insert_is_charged_and_never_proved() {
    let v = vcs("vp_ins");
    assert_eq!(vec_panic_unknowns(&v), 0, "insert in its region is charged, not rowed");
    assert_eq!(slice_bounds_checks(&v), 1, "insert must carry exactly one charged row");
    for (_, verdict) in slice_bounds_verdicts(v) {
        assert!(
            matches!(verdict, VerificationResult::Failed { .. }),
            "an unguarded `v.insert(i, x)` must be REFUTED (`i > L0` is satisfiable); got {verdict:?}"
        );
    }
}

#[test]
fn hashmap_remove_is_not_a_panic_method() {
    // `HashMap::remove` returns `Option<V>` — it never panics on a missing key, so
    // it must NOT match the Vec panic lane (compiles clean w.r.t. it).
    let v = vcs("vp_hm");
    assert_eq!(
        vec_panic_unknowns(&v),
        0,
        "HashMap::remove returns Option and must not be treated as a panicking Vec method"
    );
}

#[test]
fn vec_pop_is_not_a_panic_method() {
    // `Vec::pop` is total (returns `Option<T>`, no index) — no panic obligation.
    let v = vcs("vp_pp");
    assert_eq!(
        vec_panic_unknowns(&v),
        0,
        "Vec::pop takes no index and never panics — it must not match the panic lane"
    );
}

#[test]
fn len_tie_across_intervening_remove_never_false_accepts() {
    // THE regression anchor. `let n = v.len(); if n > 0 { v.remove(0); v.remove(n - 1); }`
    // on a `&mut Vec` parameter is genuinely unsafe (if v has 1 element: remove(0)
    // empties it, then remove(0) panics). An earlier design recovered coll_len(v) and
    // let the `n == coll_len` tie survive the first (unmodeled) remove, discharging
    // the second remove's bound → FALSE-ACCEPT.
    //
    // VEC-INSERT: the FIRST remove (bb2, column 54) is inside the pre-mutation region
    // and is charged `0 >= L0` — which the guard `n > 0` with `n == L0` refutes, so it
    // PROVES, correctly. The SECOND remove (bb4, column 67) follows a mutation of the
    // base, is outside the region, and must keep the fail-honest Unknown: no
    // dischargeable row may exist for it.
    let v = vcs("bat_rmrm");
    assert_eq!(
        vec_panic_unknowns(&v),
        1,
        "the second remove (after a mutation of its base) must stay a fail-honest Unknown"
    );
    let verdicts = slice_bounds_verdicts(v);
    assert_eq!(
        verdicts.iter().map(|(col, _)| *col).collect::<Vec<_>>(),
        vec![54],
        "SOUNDNESS: the only dischargeable row is the FIRST remove's; the surviving \
         .len() tie must never reach the second (genuinely OOB) remove"
    );
    assert!(
        matches!(verdicts[0].1, VerificationResult::Proved { .. }),
        "precision: `if n > 0 {{ v.remove(0) }}` with `n == L0` is in bounds; got {:?}",
        verdicts[0].1
    );
}

fn vec_method_bounds_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).collect()
}

/// `if i < v.len() { Some(v.swap_remove(i)) }` on `v: &mut Vec<u32>`: the sole,
/// final resize carries the real `i >= len` row, and no Unknown. (Since the merge of
/// 2026-10-14 the region lane answers first here, over its `L0`; the sole-resize
/// lane's own `coll_len(v)` row is pinned by `a_reborrow_receiver_must_have_no_other_use`.)
#[test]
fn sole_final_resize_of_a_vec_parameter_carries_the_real_precondition() {
    let v = vcs("vp_sole_guarded");
    assert_eq!(vec_panic_unknowns(&v), 0, "{v:#?}");
    assert_eq!(vec_method_bounds_rows(&v).len(), 1, "{v:#?}");
    // Unguarded and off-by-one programs get the same real row (the solver refutes
    // it); the shape gate does not look at the guard.
    for name in ["vp_sole_unguarded", "vp_sole_rem_le"] {
        let v = vcs(name);
        assert_eq!(vec_panic_unknowns(&v), 0, "{name}");
        assert_eq!(vec_method_bounds_rows(&v).len(), 1, "{name}");
    }
}

/// Two resizes, a resize inside a loop, and a use of the vector after the resize:
/// the sole-resize lane (`coll_len(v)`) declines all three, so no row over
/// `coll_len(v)` reaches any of them. Since the merge of 2026-10-14 the VEC-INSERT
/// region lane (`generate/vec_region.rs`, 62ad431b1d2) is asked first and charges a
/// resize that NO mutation of its vector reaches — the FIRST of two, or one followed
/// only by a later use — its real precondition over the region's fresh `L0`, which
/// no fact minted after a resize can name (the shape `bat_rmrm` pins above). Every
/// other resize — the second of two, one inside a loop — keeps the fail-honest
/// Unknown and gets no bounds row at all.
#[test]
fn a_second_resize_a_loop_or_a_later_use_keeps_the_unknown() {
    // (fixture, columns of the resizes that keep the Unknown, columns the region charges)
    for (name, unknown_cols, region_cols) in [
        ("vp_sole_two", vec![92], vec![79]),
        ("vp_sole_looped", vec![64], vec![]),
        ("vp_sole_after", vec![], vec![69]),
    ] {
        let v = vcs(name);
        assert_eq!(vec_panic_unknown_columns(&v), unknown_cols, "{name}: {v:#?}");
        let rows = vec_method_bounds_rows(&v);
        let mut cols: Vec<usize> = rows.iter().map(|vc| vc.location.col_start as usize).collect();
        cols.sort_unstable();
        assert_eq!(
            cols, region_cols,
            "{name}: SOUNDNESS: a resize after another mutation of its vector, or on a \
             loop, must have no bounds row: {v:#?}"
        );
        for vc in rows {
            assert!(
                obligation_is_over_region_length(vc),
                "{name}: every row here is the region lane's, never one over `coll_len(v)`: \
                 {vc:#?}"
            );
        }
    }
}

/// The c05 MIR with its receiver moved to a reborrow `_7 = &mut (*_1)`, with or
/// without a second use `_8 = copy _7` of it (review round 95: `truncate(copy _t)`
/// would resize through the alias while the sole-resize lane looks only at `v`).
///
/// * The reborrow taken in an EARLIER block (`bb1`, ahead of the guard's switch):
///   that block mutates `v`, so the region lane cannot reach the call and the
///   sole-resize lane alone decides. It admits a reborrow used only as the receiver
///   (one row over `coll_len(v)`) and declines a second use back to the Unknown.
/// * The reborrow taken in the call's OWN block (`bb2`, rustc's two-phase autoref):
///   since the merge of 2026-10-14 the region lane is asked first and charges the
///   call over its fresh `L0` with or without the copy. No statement of the call's
///   block can resize the vector before the call, and the copy outlives the call only
///   into blocks the region already excludes (the call itself is a mutation of `v`).
#[test]
fn a_reborrow_receiver_must_have_no_other_use() {
    let text = std::fs::read_to_string("tests/fixtures/vp_sole_guarded.json").unwrap();
    let build = |borrow_block: usize, second_use: bool| -> VerifiableFunction {
        let mut d: serde_json::Value = serde_json::from_str(&text).unwrap();
        let locals = d["body"]["locals"].as_array_mut().unwrap();
        let vec_ty = locals[1]["ty"].clone();
        locals.push(serde_json::json!({"index": 7, "ty": vec_ty.clone(), "name": null}));
        locals.push(serde_json::json!({"index": 8, "ty": vec_ty, "name": null}));
        let span = d["body"]["blocks"][2]["terminator"]["Call"]["span"].clone();
        let mut stmts = vec![serde_json::json!({"Assign": {
            "place": {"local": 7, "projections": []},
            "rvalue": {"Ref": {"mutable": true, "place": {"local": 1, "projections": ["Deref"]}}},
            "span": span.clone()}})];
        if second_use {
            stmts.push(serde_json::json!({"Assign": {
                "place": {"local": 8, "projections": []},
                "rvalue": {"Use": {"Copy": {"local": 7, "projections": []}}},
                "span": span}}));
        }
        let block = &mut d["body"]["blocks"][borrow_block]["stmts"];
        let old = block.as_array().cloned().unwrap_or_default();
        stmts.extend(old);
        *block = serde_json::Value::Array(stmts);
        d["body"]["blocks"][2]["terminator"]["Call"]["args"][0] =
            serde_json::json!({"Copy": {"local": 7, "projections": []}});
        serde_json::from_value(d).unwrap()
    };
    // The sole-resize lane alone (`bb1`).
    let v = generate_vcs(&build(1, false));
    assert_eq!(vec_panic_unknowns(&v), 0, "{v:#?}");
    let rows = vec_method_bounds_rows(&v);
    assert_eq!(rows.len(), 1, "{v:#?}");
    assert!(!obligation_is_over_region_length(rows[0]), "the sole-resize lane's row: {v:#?}");
    let v = generate_vcs(&build(1, true));
    assert_eq!(vec_panic_unknowns(&v), 1, "a second use of the reborrow declines: {v:#?}");
    assert_eq!(vec_method_bounds_rows(&v).len(), 0, "{v:#?}");
    // The region lane (`bb2`), with and without the copy.
    for second_use in [false, true] {
        let v = generate_vcs(&build(2, second_use));
        assert_eq!(vec_panic_unknowns(&v), 0, "second_use={second_use}: {v:#?}");
        let rows = vec_method_bounds_rows(&v);
        assert_eq!(rows.len(), 1, "second_use={second_use}: {v:#?}");
        assert!(obligation_is_over_region_length(rows[0]), "second_use={second_use}: {v:#?}");
    }
}

/// `let _ = &mut v[I::default()]; v.remove(i)` with `Vec<u32>: IndexMut<I>`: a user
/// `IndexMut<K>` impl on `Vec` is orphan-legal and can resize it, so an index call
/// whose index is not `usize` or a std range is not a benign use (review round 96).
#[test]
fn a_generic_index_before_the_resize_keeps_the_unknown() {
    let v = vcs("vp_sole_generic_index");
    assert_eq!(vec_panic_unknowns(&v), 1, "{v:#?}");
    assert_eq!(vec_method_bounds_rows(&v).len(), 0, "{v:#?}");
}
