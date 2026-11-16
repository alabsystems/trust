//! Trust: 2026-10-02 (class 10, false refutation) — a slice RANGE-INDEX bound that is a
//! multiply-assigned local, named by its SSA VERSION at the statement that reads it
//! INTO THE RANGE (`generate::range_bound_use`).
//!
//! Since round A5 (`0bbb2e326c`) `iterator_yield::resolve_range_bound_formula` resolves
//! a bound only when its root local is assigned exactly once. For `out[..len]` /
//! `buf[len..]` over a `len` the loop writes it returned nothing, and the range-index
//! arm of `generate::panic_calls` emitted the always-violated `Bool(true)` as a
//! REFUTABLE `SliceBoundsCheck`: a `FAILED` row with an arbitrary model (every variable
//! 0) on CORRECT code. The two real instances, from the 2026-10-02 proof-loss survey of
//! main against the seal (which proved both), are `build` (smol_str `lib.rs:156`) and
//! `shrink` (aterm-grid `presentation.rs:294`).
//!
//! The seal proved them by spelling the bound BARE, which the `1e` arm renames at the
//! INDEX CALL. That is unsound: a write and a guard on the bound local between the
//! range's construction and the call discharge a violation about a value the range does
//! not hold. The seal PROVED, with clean-kernel certificates, `stale_guard_bug`,
//! `stale_guard_from_bug` and `stale_guard_loop_bug`, whose binaries panic (an
//! independent verifier's probes; the `stale_*` probes are the guard-free versions).
//!
//! The rows below pin all three directions:
//!  * PROVE — the two survey instances: the violation is `Gt(len#<token>, N)` and the
//!    program's own guard discharges it;
//!  * NOT PROVED, NOT CERTIFIED — every stale probe, the parameter twin, the joined-guard
//!    probe, and the yield lane's `yield_reseat_bug` (that lane stays declined);
//!  * REFUTED on a realised `len` — the out-of-bounds twin of each instance;
//!  * DECLINED (Unknown, never refuted) — a bound that escapes through `&mut`, and a
//!    bound whose value at the read into the range is not its value at the call (the
//!    stale probes and the review's `joined_*_bug` false proofs).
//!
//! THE FIXTURES (`tests/fixtures/class10_*_mir.json`) are `-Ztrust-dump=mir-only`
//! captures from the main toolchain (`stage2-d36c551fac`, `-Copt-level=0`, edition 2024)
//! of the survey reproducers (`proof-loss/repro/cex/{early_return,loop_exit}.rs`), the
//! verifier's probes (`adv_cex.rs`, `adv_cex2.rs`), `c10_twins.rs` and the class-10
//! review's `rv_range.rs` (`joined_*`; `joined_after_bug_o1` at `-Copt-level=1`); each function's
//! source is quoted in its test. Span files are rewritten to `<dump-root>/` (see
//! `scripts/check_fixture_span_paths.py`). Verdicts are this crate's, through
//! `generate_vcs` and the deterministic in-process `ay` router, as in
//! `tests/escaped_local_seam_realmir.rs`; certification is `trust_certify::certify_vc`.

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
    let path = format!("{}/tests/fixtures/class10_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
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

/// The slice range-index lane's rows: the stated `SliceBoundsCheck`, or the row it
/// declined to.
fn is_range_row(kind: &VcKind) -> bool {
    match kind {
        VcKind::SliceBoundsCheck => true,
        VcKind::UnsupportedMir { kind, .. } => kind.starts_with("slice-range-"),
        _ => false,
    }
}

/// The range-index rows charged to source `line`.
fn range_rows_at(name: &str, line: u32) -> Vec<Row> {
    let rows: Vec<Row> = verdicts(name)
        .into_iter()
        .filter(|r| is_range_row(&r.vc.kind) && r.vc.location.line_start == line)
        .collect();
    assert!(!rows.is_empty(), "{name}: no range-index row at line {line}");
    rows
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

/// `body` is `Gt(len#<token>, n)`: the user's `len`, VERSIONED (never bare, never
/// renamed at the call), against the receiver's constant length.
fn is_versioned_len_gt(body: &Formula, n: i128) -> bool {
    match body {
        Formula::Gt(lhs, rhs) => {
            matches!(&**lhs, Formula::Var(name, _) if name.starts_with("len#"))
                && matches!(&**rhs, Formula::Int(k) if *k == n)
        }
        _ => false,
    }
}

/// The witness assigns some version of `len` a value in `range`.
fn witness_len_in(r: &VerificationResult, range: std::ops::RangeInclusive<i128>) -> bool {
    let VerificationResult::Failed { counterexample: Some(cex), .. } = r else { return false };
    cex.assignments.iter().any(|(name, value)| {
        name.starts_with("len#")
            && match value {
                CounterexampleValue::Int(v) => range.contains(v),
                CounterexampleValue::Uint(v) => {
                    i128::try_from(*v).is_ok_and(|v| range.contains(&v))
                }
                _ => false,
            }
    })
}

/// Every range row at `line` is STATED as `len#<token> > n` (one per receiver length in
/// `ns`, in any order) and PROVED.
fn assert_proves(name: &str, line: u32, ns: &[i128]) {
    let rows = range_rows_at(name, line);
    let c = census(&rows);
    assert_eq!(rows.len(), ns.len(), "{name}: row count at line {line} drifted: {c:#?}");
    for n in ns {
        assert!(
            rows.iter().any(|r| r
                .vc
                .obligation
                .as_ref()
                .is_some_and(|o| is_versioned_len_gt(&o.body, *n))),
            "{name}: some row must state `len#<token> > {n}`: {c:#?}"
        );
    }
    for r in &rows {
        assert!(matches!(r.vc.kind, VcKind::SliceBoundsCheck), "{name}: declined: {c:#?}");
        assert!(is_proved(&r.verdict), "{name}: a correct program must prove: {c:#?}");
    }
}

/// No range row at `line` is proved or certified (the program panics), and at least one
/// is generated.
fn assert_not_proved(name: &str, line: u32) {
    let rows = range_rows_at(name, line);
    let c = census(&rows);
    for r in &rows {
        assert!(
            !is_proved(&r.verdict) && !r.certified,
            "{name}: a program that PANICS has a proved or certified range row: {c:#?}"
        );
    }
}

/// Some range row at `line` is STATED as `len#<token> > n` and REFUTED on a counterexample
/// that puts `len` in `realised`.
fn assert_refutes(name: &str, line: u32, n: i128, realised: std::ops::RangeInclusive<i128>) {
    let rows = range_rows_at(name, line);
    let c = census(&rows);
    assert!(
        rows.iter().any(|r| r
            .vc
            .obligation
            .as_ref()
            .is_some_and(|o| is_versioned_len_gt(&o.body, n))
            && witness_len_in(&r.verdict, realised.clone())),
        "{name}: the real out-of-bounds index must keep a counterexample with len in \
         {realised:?}: {c:#?}"
    );
    let against_n =
        |r: &&Row| r.vc.obligation.as_ref().is_some_and(|o| is_versioned_len_gt(&o.body, n));
    assert!(
        rows.iter().filter(against_n).all(|r| !is_proved(&r.verdict) && !r.certified),
        "{name}: {c:#?}"
    );
}

/// Every range row at `line` is the declined `slice-range-bounds-unresolved` row, and
/// none is proved, refuted or certified.
fn assert_declined(name: &str, line: u32) {
    let rows = range_rows_at(name, line);
    let c = census(&rows);
    for r in &rows {
        assert!(
            matches!(&r.vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "slice-range-bounds-unresolved"),
            "{name}: the range row must decline: {c:#?}"
        );
        assert!(
            !is_proved(&r.verdict)
                && !matches!(r.verdict, VerificationResult::Failed { .. })
                && !r.certified,
            "{name}: a declined row is Unknown: {c:#?}"
        );
    }
}

// ── PROVE: the survey instances ──────────────────────────────────────────────────

/// `early_return.rs` (smol_str `lib.rs:156`):
///
/// ```text
/// let mut len = 0; let mut buf = [0u8; 23];
/// while let Some(ch) = iter.next() {
///     let size = ch.len_utf8();
///     if size + len > 23 { return (buf, usize::MAX); }
///     ch.encode_utf8(&mut buf[len..]);              // line 13
///     len += size;
/// }
/// ```
///
/// Main: `FAILED`, every variable 0 (the `Bool(true)` row). Seal: proved.
#[test]
fn the_early_return_bound_proves() {
    assert_proves("build", 13, &[23]);
}

/// `loop_exit.rs` (aterm-grid `presentation.rs:294`):
///
/// ```text
/// let mut len = bands.len().min(buf.len());           // buf: [_; 16]
/// buf[..len].copy_from_slice(&bands[..len]);
/// while len > 8 { buf[0].1 = buf[0].1.max(buf[1].1); len -= 1; }
/// let mut out = [(0u64, 0u64); 8];
/// out[..len].copy_from_slice(&buf[..len]);            // line 14
/// ```
///
/// Main: both line-14 rows `FAILED` on the arbitrary model. Seal: both proved.
#[test]
fn the_loop_exit_bound_proves() {
    assert_proves("shrink", 14, &[8, 16]);
}

/// `adv_cex.rs::clamp_ctl` — correct, multiply-assigned, no write between the read and
/// the index: `let mut len = n; if len > 8 { len = 8; } buf[..len].len()` (line 37).
///
/// The row is STATED (`len#s0_1_s1_0 > 8`, the joined version at the read), not the
/// arbitrary-model `Bool(true)` main emitted. Its verdict is not pinned: the encoding
/// carries no phi equation for a joined version, so the row is refuted on `len = 9`,
/// exactly as on the seal (measured on both, 2026-10-02) — a join-precision gap, not
/// this class.
#[test]
fn a_clamped_multiply_assigned_bound_is_stated_at_its_joined_version() {
    let rows = range_rows_at("clamp_ctl", 37);
    let c = census(&rows);
    assert_eq!(rows.len(), 1, "{c:#?}");
    assert!(matches!(rows[0].vc.kind, VcKind::SliceBoundsCheck), "{c:#?}");
    let body = &rows[0].vc.obligation.as_ref().expect("recorded").body;
    assert!(is_versioned_len_gt(body, 8), "{c:#?}");
    assert!(!rows[0].certified || is_proved(&rows[0].verdict), "{c:#?}");
}

// ── REFUTE: the out-of-bounds twins ──────────────────────────────────────────────

/// `c10_twins.rs::shrink_oob` — `loop_exit.rs` with `while len > 9`: `out[..9]` on
/// `[_; 8]` panics for `bands.len() >= 9`.
#[test]
fn the_loop_exit_twin_refutes_on_len_9() {
    assert_refutes("shrink_oob", 14, 8, 9..=9);
}

/// `c10_twins.rs::build_oob` — `early_return.rs` with `if size + len > 30` and
/// `buf[len..].fill(1)` (line 28) in place of `encode_utf8` (which would panic first):
/// 24 one-byte chars reach `buf[24..]` on `[u8; 23]`.
#[test]
fn the_early_return_twin_refutes_on_len_past_23() {
    assert_refutes("build_oob", 28, 23, 24..=29);
}

// ── NOT PROVED: the probes the seal proved and certified ─────────────────────────

/// `adv_cex2.rs` — a GUARD on the post-write version of the bound local between the
/// range construction and the index. Each panics for `n > 8` (`xs` with an element > 8);
/// the seal proved and certified each.
///
/// ```text
/// stale_guard_bug:      let mut len = n; let r = ..len; len = n & 3;
///                       if len > 8 { return 0; } buf[r].len() + len          // line 11
/// stale_guard_from_bug: let mut len = n; let r = len..; len = n % 5;
///                       if len > 8 { return 0; } buf[r].len() + len          // line 21
/// stale_guard_loop_bug: for &x in xs { let r = ..len; len = x;
///                       if len > 8 { return acc; } acc += buf[r].len();      // line 33
///                       len = len.wrapping_mul(2); }
/// ```
#[test]
fn a_guard_on_the_rewritten_bound_does_not_prove_the_stale_range() {
    assert_not_proved("stale_guard_bug", 11);
    assert_not_proved("stale_guard_from_bug", 21);
    assert_not_proved("stale_guard_loop_bug", 33);
}

/// The same probes DECLINE: the bound's value at the read into the range is not its
/// value at the call (`len` is rewritten in between), so the lane names neither and
/// emits the Unknown `slice-range-bounds-unresolved` row — no proof, no refutation.
///
/// Trust: 2026-10-02 (class-10 review). These were refuted on the value the range was
/// built from, by naming it with the read's version TOKEN. A token names a
/// reaching-definition set, not a value, and the review's `joined_*_bug` probes below
/// PROVED under that spelling; the bound is now named only when its `ValueId` at the
/// read IS its value at the call. Losing these refutations is lost precision, not
/// soundness: the rows stay unproved.
#[test]
fn the_stale_guard_probes_decline_the_value_the_range_was_built_from() {
    assert_declined("stale_guard_bug", 11);
    assert_declined("stale_guard_from_bug", 21);
}

/// `adv_cex.rs` — the guard-free versions: `let r = ..len; len = 0; buf[r]` (line 9),
/// `let mut len = 30; let r = len..; len = 1; buf[r]` (line 16), and the loop
/// `let r = len..; len = (x & 15) as usize; acc += buf[r].len(); len += 10;` (line 25,
/// `buf: [u8; 23]`, panics on the third element).
#[test]
fn a_rewritten_bound_does_not_prove_the_stale_range() {
    assert_not_proved("stale_to_bug", 9);
    assert_not_proved("stale_from_const_bug", 16);
    assert_not_proved("stale_loop_bug", 25);
}

/// `c10_twins.rs::param_stale_bug` — the bound is a written PARAMETER read at its ENTRY
/// value: `let r = ..n; n &= 3; if n > 8 { return 0; } buf[r].len() + n` (line 74).
/// The entry read has no version token, and the name IS versioned elsewhere, so a bare
/// spelling would be renamed at the call onto the guarded `n & 3`: declined or refuted,
/// never proved.
#[test]
fn a_stale_entry_valued_parameter_bound_is_not_proved() {
    assert_not_proved("param_stale_bug", 74);
}

/// `c10_twins.rs::joined_guard_bug` — the guard and the range read can share a
/// reaching-definition SET without sharing a value:
///
/// ```text
/// for &c in xs { if len <= 5 { if c { len = 100; } acc += buf[..len].len(); } }  // line 45
/// ```
///
/// Panics at `xs = [true]`. Must not prove.
#[test]
fn a_guard_sharing_the_reaching_set_but_not_the_value_does_not_prove() {
    assert_not_proved("joined_guard_bug", 45);
}

/// Trust: 2026-10-02 (class-10 review, FALSE PROOF) — the read into the range and a
/// guard AFTER a conditional write of the bound share a reaching-definition SET, so
/// they share a version token while reading different values. Spelled with the read's
/// token, the guard's `!(len#s0_0_s7_0 > 8)` contradicted the violation
/// `len#s0_0_s7_0 > 8` and each row PROVED with a clean-kernel certificate (measured on
/// `c888f21ea3`; origin/main `a70710983f` reported each FAILED on `Bool(true)`). The
/// review's probes (`rv_range.rs`, `buf: &[u8; 8]`, main toolchain `-Ztrust-dump=mir-only`):
///
/// ```text
/// joined_after_bug (line 12, -O0 and -O1), panics at xs = [true], m = 100, n = 0:
///     let mut len = m;
///     for &c in xs { let r = ..len; if c { len = n; }
///                    if len > 8 { return acc; } acc += buf[r].len(); }
/// joined_exit_bug (line 25), panics at c = true, m = 100, n = 0:
///     let mut len = m; let mut r;
///     loop { r = ..len; if c { len = n; } if len <= 8 { break; } }  buf[r].len()
/// joined_pair_bug (line 65): `let r = lo..8; if c { lo = n; } if lo > 8 { return acc; }`
/// ```
///
/// Each declines now: the value at the read is the loop-header join, the value at the
/// call the join after `if c`.
#[test]
fn a_guard_after_a_conditional_rewrite_does_not_prove_the_range_read_before_it() {
    assert_declined("joined_after_bug", 12);
    assert_declined("joined_after_bug_o1", 12);
    assert_declined("joined_exit_bug", 25);
    assert_declined("joined_pair_bug", 65);
}

/// `rv_range.rs::joined_after_ctl` (line 34) — the correct twin: the guard and the read
/// into the range see the same value, which the call reads too, so the bound is named and
/// the program's guard proves the row.
#[test]
fn the_guard_before_the_read_still_proves() {
    let rows = range_rows_at("joined_after_ctl", 34);
    let c = census(&rows);
    assert_eq!(rows.len(), 1, "{c:#?}");
    assert!(matches!(rows[0].vc.kind, VcKind::SliceBoundsCheck), "{c:#?}");
    assert!(
        rows[0].vc.obligation.as_ref().is_some_and(|o| is_versioned_len_gt(&o.body, 8)),
        "{c:#?}"
    );
    assert!(is_proved(&rows[0].verdict), "{c:#?}");
}

/// `adv_cex2.rs::yield_reseat_bug` — the YIELD lane stays declined for a multiply-assigned
/// range end: `let mut n = 100; for i in 0..n { n = 5; t += a[i]; }` on `&[u8; 5]`
/// (line 45) panics at `i == 5`. Its `a[i]` row must not prove.
#[test]
fn the_yield_lane_still_declines_a_reseated_range_end() {
    let rows: Vec<Row> = verdicts("yield_reseat_bug")
        .into_iter()
        .filter(|r| {
            r.vc.location.line_start == 45
                && matches!(r.vc.kind, VcKind::IndexOutOfBounds | VcKind::UnsupportedMir { .. })
        })
        .collect();
    let c = census(&rows);
    assert!(!rows.is_empty(), "yield_reseat_bug: the a[i] row vanished");
    assert!(rows.iter().all(|r| !is_proved(&r.verdict) && !r.certified), "{c:#?}");
}

// ── DECLINE: a bound no version can name ─────────────────────────────────────────

/// `c10_twins.rs::clip_escaped` — `let mut len = n; bump(&mut len); buf[..len].len()`
/// (line 86): the write through `&mut len` is invisible to the version oracle. Before
/// this fix the row was the always-violated `Bool(true)` as a `SliceBoundsCheck`, FAILED
/// on an arbitrary model; it is the declined `UnsupportedMir` row — Unknown, neither a
/// proof nor a refutation.
#[test]
fn an_escaped_bound_is_declined_not_refuted() {
    let rows = range_rows_at("clip_escaped", 86);
    let c = census(&rows);
    assert_eq!(rows.len(), 1, "{c:#?}");
    assert!(
        matches!(&rows[0].vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "slice-range-bounds-unresolved"),
        "{c:#?}"
    );
    assert!(
        !is_proved(&rows[0].verdict)
            && !matches!(rows[0].verdict, VerificationResult::Failed { .. }),
        "{c:#?}"
    );
}
