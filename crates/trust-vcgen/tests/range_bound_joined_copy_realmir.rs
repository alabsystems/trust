//! Trust: 2026-10-14 (follow-up of dd584167118) — a range bound stated AT A CALL is
//! never resolved through the joined-copy fallback.
//!
//! `iterator_yield::resolve_range_bound_formula` resolves a single-assignment copy of a
//! multiply-written local (`_15 = copy k`, `k` written on two paths) to the copy's own
//! bare name: a name of one value, which a fact keyed on a payload may use. An
//! obligation stated at a call meets the copy's value only through the copy's
//! definition, and that reaches the row only where the copy's block is conjoined (the
//! call block's definitions in the BTree / VecDeque lanes, the dominating path
//! definitions; never the slice lane's own call block, and not a copy made in a loop
//! body ahead of a write of `k`). Where it does not reach, the copy is a FREE variable
//! and the row is refuted on an arbitrary model, the class-10 FAILED that
//! `range_bound_use` removed from the slice lane. dd584167118 moved the slice
//! violation off the fallback and left the BTree range lane, the VecDeque range lane,
//! the slice lane's `a..=b` fallback, the endpoint facts conjoined onto the slice
//! violation and the `is_char_boundary` axiom on it. All of them now ask
//! `panic_calls::range_bound_at_call_formula` (exact, then unchanged-until-call, then
//! the SSA version at the read into the range, else the lane's declined row), which
//! also reads the `RangeInclusive::new(a, b)` call that builds `a..=b` below
//! `-Copt-level=2` (`range_bound_use::range_inclusive_new_at`).
//!
//! MEASURED BEFORE THIS CHANGE (same fixtures, same router):
//!  * `sl_inclusive_ctl` — correct — was REFUTED at `_10 = 8` (`_10 = copy k`, free);
//!  * `bt_joined_after_bug`, `bt_stale_guard_bug`, `bt_inclusive_joined_after_bug`,
//!    `sl_inclusive_joined_after_bug`, `vd_joined_after_bug` were REFUTED on a free copy
//!    (`_15 = -1` for a `usize`; `_14 = 8`; `_14 = 1`): arbitrary models;
//!  * no probe PROVED a panicking program: the copy's definition, which would carry
//!    the shared-token false-PROVE shape of `slice_range_bound_at_call.rs`
//!    (`joined_after_bug`), did not reach any of these rows;
//!  * `cb_join_tested_ctl` proved with its axiom on the copy `e` and its violation on
//!    `n#<token>`, met only through `e`'s path definition; both now read `n#<token>`.
//!
//! The rows pin three directions, as in `slice_range_bound_at_call.rs`:
//!  * PROVE — every correct probe (`*_ctl`), stated on the bound's VERSIONED source;
//!  * DECLINE (Unknown, never refuted, never proved) — a bound whose value at the read
//!    into the range is not its value at the call;
//!  * NOT PROVED — every panicking probe; the unguarded one REFUTED on a realised value.
//!
//! The yield lanes keep the fallback (a payload fact on a free name is only weaker):
//! `y_joined_end_ctl` (sweep p50) still proves and the guard-before-write probes do not.
//!
//! THE FIXTURES (`tests/fixtures/range_bound_joined_copy/<opt>_<fn>.json`) are
//! `-Ztrust-dump=mir-only` captures, one function per file, of the sources beside them
//! (`range_join.rs`, `yield_join.rs`, `deque_join.rs`):
//!
//! ```text
//! trustc --edition 2024 --crate-type lib --emit=metadata -Copt-level=<0|1> \
//!        -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory <source>.rs
//! ```
//!
//! on the stage 1 compiler of this checkout on 2026-10-14, written compact, span files
//! rewritten to `<dump-root>/`. Verdicts are this crate's, through `generate_vcs` and
//! the deterministic in-process `ay` router; certification is `trust_certify::certify_vc`.

use trust_types::{
    CounterexampleValue, Formula, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

struct Row {
    vc: VerificationCondition,
    verdict: VerificationResult,
    certified: bool,
}

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/range_bound_joined_copy/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

fn verdicts(name: &str) -> Vec<Row> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, verdict)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    Row { vc, verdict, certified }
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// The lane a probe exercises: its stated row, or the row it declines to.
#[derive(Clone, Copy)]
enum Lane {
    BTree,
    Slice,
    Deque,
    Index,
}

impl Lane {
    fn stated(self, kind: &VcKind) -> bool {
        match self {
            Lane::BTree => matches!(kind, VcKind::Assertion { message }
                if message.starts_with("BTreeMap/BTreeSet::range")),
            Lane::Slice | Lane::Deque => matches!(kind, VcKind::SliceBoundsCheck),
            Lane::Index => matches!(kind, VcKind::IndexOutOfBounds),
        }
    }

    fn declined(self, kind: &VcKind) -> Option<&str> {
        let VcKind::UnsupportedMir { kind, .. } = kind else { return None };
        let ours = match self {
            Lane::BTree => kind == "btree-range-bounds-unmodeled",
            Lane::Slice => kind.starts_with("slice-range-") || kind.starts_with("str-range-"),
            Lane::Deque => kind == "vecdeque-range-bounds-unmodeled",
            Lane::Index => false,
        };
        ours.then_some(kind.as_str())
    }
}

/// The lane's rows charged to source `line` of `name`; exactly one is expected.
fn row_at(name: &str, lane: Lane, line: u32) -> Row {
    let mut rows: Vec<Row> = verdicts(name)
        .into_iter()
        .filter(|r| {
            r.vc.location.line_start == line
                && (lane.stated(&r.vc.kind) || lane.declined(&r.vc.kind).is_some())
        })
        .collect();
    let c = census(&rows);
    assert_eq!(rows.len(), 1, "{name}: expected one row at line {line}: {c:#?}");
    rows.pop().expect("one row")
}

fn census(rows: &[Row]) -> Vec<String> {
    rows.iter()
        .map(|r| {
            format!(
                "{}:{} {:?} certified={} body={:?} verdict={:?}",
                r.vc.location.line_start,
                r.vc.location.col_start,
                r.vc.kind,
                r.certified,
                r.vc.obligation.as_ref().map(|o| &o.body),
                r.verdict
            )
        })
        .collect()
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn is_failed(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Failed { .. })
}

fn body(row: &Row) -> &Formula {
    &row.vc.obligation.as_ref().expect("the row records its obligation").body
}

/// A VERSIONED name of the bound's source (`k#s0_0_s1_0`), never a copy temp (`_15`).
fn is_versioned(f: &Formula, source: &str) -> bool {
    matches!(f, Formula::Var(name, _) if name.starts_with(&format!("{source}#")))
}

/// The lane's row at `line` is STATED and PROVED.
fn assert_proves(name: &str, lane: Lane, line: u32) -> Row {
    let row = row_at(name, lane, line);
    let c = census(std::slice::from_ref(&row));
    assert!(lane.stated(&row.vc.kind), "{name}: the row must be stated: {c:#?}");
    assert!(is_proved(&row.verdict), "{name}: a correct program must prove: {c:#?}");
    row
}

/// The lane's row at `line` is its DECLINED row: Unknown, neither proved, refuted nor
/// certified.
fn assert_declined(name: &str, lane: Lane, line: u32, kind: &str) {
    let row = row_at(name, lane, line);
    let c = census(std::slice::from_ref(&row));
    assert_eq!(lane.declined(&row.vc.kind), Some(kind), "{name}: must decline: {c:#?}");
    assert!(
        !is_proved(&row.verdict) && !is_failed(&row.verdict) && !row.certified,
        "{name}: a declined row is Unknown: {c:#?}"
    );
}

/// The lane's row at `line` is neither proved nor certified (the program panics).
fn assert_not_proved(name: &str, lane: Lane, line: u32) -> Row {
    let row = row_at(name, lane, line);
    let c = census(std::slice::from_ref(&row));
    assert!(
        !is_proved(&row.verdict) && !row.certified,
        "{name}: a program that PANICS has a proved or certified row: {c:#?}"
    );
    row
}

fn witness_int(r: &VerificationResult, name: impl Fn(&str) -> bool) -> Option<i128> {
    let VerificationResult::Failed { counterexample: Some(cex), .. } = r else { return None };
    cex.assignments.iter().find(|(n, _)| name(n)).and_then(|(_, v)| match v {
        CounterexampleValue::Int(v) => Some(*v),
        CounterexampleValue::Uint(v) => i128::try_from(*v).ok(),
        _ => None,
    })
}

fn both_opt_levels(f: impl Fn(&str)) {
    for opt in ["o0", "o1"] {
        f(opt);
    }
}

// ── BTreeMap::range ──────────────────────────────────────────────────────────────

/// `range_join.rs` — correct, `k` multiply written and guarded before the range:
///
/// ```text
/// bt_join_guard_ctl   (line 16): if a > k { return 0 } m.range(a..k)      (range in the call's block)
/// bt_cross_block_ctl  (line 62): if a > k { return 0 } let r = a..k; black_box(0); m.range(r)
/// bt_inclusive_ctl    (line 85): if a > k { return 0 } m.range(a..=k)     (a `RangeInclusive::new` call)
/// ```
///
/// Each is stated as `a > k#<token>` (unchanged-until-call; the version at the read into
/// the range; the read into `RangeInclusive::new`) and proves. They proved before too, on
/// the copy temp, through its definition in the call block or a dominating block.
#[test]
fn a_guarded_joined_btree_bound_proves_on_its_versioned_source() {
    both_opt_levels(|opt| {
        for (f, line) in
            [("bt_join_guard_ctl", 16), ("bt_cross_block_ctl", 62), ("bt_inclusive_ctl", 85)]
        {
            let name = format!("{opt}_{f}");
            let row = assert_proves(&name, Lane::BTree, line);
            let c = census(std::slice::from_ref(&row));
            assert!(
                matches!(body(&row), Formula::Gt(s, e)
                    if matches!(&**s, Formula::Var(a, _) if a == "a") && is_versioned(e, "k")),
                "{name}: the violation must read `a > k#<token>`: {c:#?}"
            );
        }
    });
}

/// `range_join.rs` — each panics on a non-empty map; the range is read BEFORE `k` is
/// rewritten and a guard reads the new value:
///
/// ```text
/// bt_joined_after_bug           (line 32):  for &c in xs { let r = a..k; if c { k = n }
///                                                          if a > k { return } m.range(r) }
/// bt_stale_guard_bug            (line 48):  let r = a..k; k = m; if a > k { return } m.range(r)
/// bt_inclusive_joined_after_bug (line 106): bt_joined_after_bug with `a..=k`
/// ```
///
/// Before this change each was REFUTED on the free copy (`_15 = -1`, `_8 = -1`). The
/// bound's value at the read is not its value at the call, so the row declines.
#[test]
fn a_btree_bound_rewritten_before_its_call_declines() {
    both_opt_levels(|opt| {
        for (f, line) in [
            ("bt_joined_after_bug", 32),
            ("bt_stale_guard_bug", 48),
            ("bt_inclusive_joined_after_bug", 106),
        ] {
            let name = format!("{opt}_{f}");
            assert_declined(&name, Lane::BTree, line, "btree-range-bounds-unmodeled");
        }
    });
}

/// `range_join.rs::bt_cross_block_bug` (line 73) — the unguarded twin of
/// `bt_cross_block_ctl`, panics at `a > k`: refuted on a realised `a > k`.
#[test]
fn an_unguarded_joined_btree_bound_refutes_on_a_realised_value() {
    both_opt_levels(|opt| {
        let name = format!("{opt}_bt_cross_block_bug");
        let row = assert_not_proved(&name, Lane::BTree, 73);
        let c = census(std::slice::from_ref(&row));
        let a = witness_int(&row.verdict, |n| n == "a");
        let k = witness_int(&row.verdict, |n| n.starts_with("k#"));
        assert!(
            matches!((a, k), (Some(a), Some(k)) if 0 <= k && k < a),
            "{name}: the refutation must realise `a > k` on usize values: {c:#?}"
        );
    });
}

/// `range_join.rs::bt_guard_before_write_bug` (line 128) — the guard reads `k` BEFORE a
/// conditional write, the range after it (`for &c in xs { if a > k { return } if c { k
/// = n } m.range(a..k) }`, panics at `xs = [true]`, `n < a`): not proved.
#[test]
fn a_btree_guard_before_a_conditional_write_does_not_prove() {
    both_opt_levels(|opt| {
        assert_not_proved(&format!("{opt}_bt_guard_before_write_bug"), Lane::BTree, 128);
    });
}

// ── str char boundary ────────────────────────────────────────────────────────────

/// The axiom `!b || X <= len` and the violation `X > len` of a tested endpoint, as
/// `(axiom X, violation X)`.
fn axiom_and_violation_terms(f: &Formula) -> Option<(&Formula, &Formula)> {
    let Formula::And(parts) = f else { return None };
    let disjunct = |pick: fn(&Formula) -> Option<&Formula>| {
        parts.iter().find_map(|p| match p {
            Formula::Or(d) => d.iter().find_map(pick),
            _ => None,
        })
    };
    let axiom = disjunct(|x| match x {
        Formula::Le(x, _) => Some(&**x),
        _ => None,
    })?;
    let violation = disjunct(|x| match x {
        Formula::Gt(x, _) => Some(&**x),
        _ => None,
    })?;
    Some((axiom, violation))
}

/// `range_join.rs` — correct: `let e = n` (`n` multiply written), `if
/// s.is_char_boundary(e) { &s[..e] }` (line 142) and `&s[e..]` (line 152). The
/// `is_char_boundary` axiom and the bounds violation name ONE term, `n#<token>`; the
/// axiom used to name the copy `e` while the violation named `n#<token>`.
#[test]
fn a_tested_joined_endpoint_states_its_axiom_on_the_violations_term() {
    both_opt_levels(|opt| {
        for (f, line) in [("cb_join_tested_ctl", 142), ("cb_join_tested_from_ctl", 152)] {
            let name = format!("{opt}_{f}");
            let row = assert_proves(&name, Lane::Slice, line);
            let c = census(std::slice::from_ref(&row));
            let terms = axiom_and_violation_terms(body(&row));
            assert!(
                matches!(terms, Some((axiom, violation))
                    if axiom == violation && is_versioned(axiom, "n")),
                "{name}: the axiom and the violation must both read `n#<token>`: {c:#?}"
            );
        }
    });
}

/// `range_join.rs::cb_join_untested_bug` (line 162) — the slice is on the branch where
/// the test FAILED (`s = "é"`, `n = 1` panics): refuted.
#[test]
fn an_untested_joined_endpoint_refutes() {
    both_opt_levels(|opt| {
        let name = format!("{opt}_cb_join_untested_bug");
        let row = assert_not_proved(&name, Lane::Slice, 162);
        let c = census(std::slice::from_ref(&row));
        assert!(is_failed(&row.verdict), "{name}: {c:#?}");
    });
}

/// `range_join.rs::cb_join_tested_loop_ctl` (line 175) — the tested endpoint is written
/// in a loop, so the test is not credited (`char_boundary_tests_of`): the declined
/// char-boundary row, never a refutation.
#[test]
fn a_tested_endpoint_written_in_a_loop_declines() {
    both_opt_levels(|opt| {
        assert_declined(
            &format!("{opt}_cb_join_tested_loop_ctl"),
            Lane::Slice,
            175,
            "str-range-char-boundary-unmodeled",
        );
    });
}

// ── slice `..=` (the `index_range_violation` fallback) ──────────────────────────

/// `range_join.rs::sl_inclusive_ctl` (line 192) — correct: `if k >= 8 { return 0 }
/// b[..=k]` on `[u8; 8]`. Before this change it was REFUTED at `_10 = 8` (the copy
/// `_10 = copy k` free in the slice lane); it is stated on `k#<token> + 1 > 8`.
#[test]
fn a_guarded_joined_inclusive_slice_bound_proves() {
    both_opt_levels(|opt| {
        let name = format!("{opt}_sl_inclusive_ctl");
        let row = assert_proves(&name, Lane::Slice, 192);
        let c = census(std::slice::from_ref(&row));
        assert!(
            matches!(body(&row), Formula::Gt(lhs, rhs)
                if matches!(&**lhs, Formula::Add(k, one)
                    if is_versioned(k, "k") && matches!(&**one, Formula::Int(1)))
                && matches!(&**rhs, Formula::Int(8))),
            "{name}: the violation must read `k#<token> + 1 > 8`: {c:#?}"
        );
    });
}

/// `range_join.rs::sl_inclusive_joined_after_bug` (line 207) — `let r = ..=k; if c { k =
/// n } if k >= 8 { return } b[r]`, panics at `xs = [true]`, `m = 8`: declined (it was
/// refuted on the free copy, `_14 = 8`).
#[test]
fn an_inclusive_slice_bound_rewritten_before_its_call_declines() {
    both_opt_levels(|opt| {
        assert_declined(
            &format!("{opt}_sl_inclusive_joined_after_bug"),
            Lane::Slice,
            207,
            "slice-range-bounds-unresolved",
        );
    });
}

// ── VecDeque::range ─────────────────────────────────────────────────────────────

/// `deque_join.rs` — `vd_join_guard_ctl` (line 13, correct: `if k > q.len() { return 0 }
/// q.range(..k)`) proves on `k#<token>`; `vd_joined_after_bug` (line 29, the range read
/// before a conditional write) declines (it was refuted on the free copy, `_14 = 1`).
#[test]
fn the_deque_range_lane_names_the_bound_at_its_call() {
    let row = assert_proves("o0_vd_join_guard_ctl", Lane::Deque, 13);
    let c = census(std::slice::from_ref(&row));
    assert!(
        matches!(body(&row), Formula::And(parts)
            if parts.iter().any(|p| matches!(p, Formula::Gt(k, _) if is_versioned(k, "k")))),
        "the violation must read `k#<token> > len`: {c:#?}"
    );
    assert_declined("o0_vd_joined_after_bug", Lane::Deque, 29, "vecdeque-range-bounds-unmodeled");
}

// ── the yield lanes keep the fallback ───────────────────────────────────────────

/// `yield_join.rs` — the yield lanes still resolve a copy of a joined local to its bare
/// name, a fact keyed on the payload (`i < k`). `y_joined_end_ctl` (line 45, sweep p50,
/// `let k = if n > 26 { 26 } else { n }; for i in 0..k { a[i] }`) proves on it; the
/// guard-before-write probes (`if k > 8 { return } if c { k = n } let k2 = k;` then `for i
/// in 0..k2 { a[i] }`, line 17, or `a[k2]`, line 35, each panics at `xs = [true]`, `n =
/// 100`) do not.
#[test]
fn the_yield_lane_fallback_keeps_its_proof_and_proves_no_panic() {
    assert_proves("o0_y_joined_end_ctl", Lane::Index, 45);
    assert_not_proved("o0_y_guard_before_write_bug", Lane::Index, 17);
    assert_not_proved("o0_plain_guard_before_write_bug", Lane::Index, 35);
}
