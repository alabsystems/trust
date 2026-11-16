//! Trust: 2026-09-16 — THE ESCAPE-CHANNEL CLOSURE AND ITS RECOVERY, MEASURED SIDE BY
//! SIDE ON REAL COMPILER MIR.
//!
//! `local_defs::body_unique_value_def` refuses `LocalWrite::Escape` since 2026-09-15
//! (`x3::pesc`, a kernel-certified false bounds proof on plain safe Rust). The cost
//! was every Rust `for` loop: the `Iterator::next` desugar `&mut`-borrows the loop's
//! iterator local, so the yield/trip-count tracers lost their answer and four correct
//! programs REFUTED with counterexamples. The recovery
//! (`generate::iterator_yield::iterator_origin_def`) asks the ORIGIN question under an
//! affirmative conduit allow-list and withholds the range's `start` across the hop.
//!
//! Every fixture here is a `-Ztrust-dump=mir-only` capture from the PRISTINE prebuilt
//! stage1 driver (`build/host/stage1/bin/trustc`, `-Copt-level=0`, edition 2021) of
//! the function named in each test — the exact MIR the compiler verifies, not a
//! synthesized shape. The verdict each row asserts is the one this crate produces
//! through `generate_vcs` + the deterministic in-process `ay` router; the pristine
//! compiler's own verdict on the same source is quoted in each doc so the direction
//! of every change is visible.
//!
//! CAPTURING A NEW ONE: `SourceSpan::file` records the UNREMAPPED path trustc saw, so
//! a dump taken in a scratch directory records that directory verbatim. Rewrite the
//! dump ROOT to `<dump-root>/` and keep the tail before committing — thirteen fixtures
//! here shipped an agent session path and blocked the 2026-09-21 release until they
//! were scrubbed. `scripts/check_fixture_span_paths.py` now refuses the next one; its
//! docstring records why `<dump-root>` cannot collide with `is_trusted_std_file` and
//! therefore cannot move a verdict.
//!
//! Three kinds of row, and each must keep its kind:
//!  * RECOVERED — a correct program the closure had turned into a refutation proves
//!    again (the reviewer's two named programs, and the shapes around them);
//!  * STILL CLOSED — a program that panics at runtime and that the pristine driver
//!    PROVED (2 proved, 0 failed, rc = 0) is not proved, on either the resolver
//!    channel or the recovered origin lane;
//!  * STILL REFUTED — a real out-of-bounds loop index keeps its counterexample, so the
//!    recovered yield bound cannot be a blanket one.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/pre_carrier_keys.rs"]
mod pre_carrier_keys;

fn fixture(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/escaped_seam_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    // These captures predate the extractor's `callee_key` carrier; the slice-method
    // recognizers decide on it since SLICE-INHERENT-1 (2026-10-04). Supply the key
    // today's extractor mints (see the helper).
    pre_carrier_keys::rekey_pre_carrier_dump(
        serde_json::from_str(&json).expect("the captured MIR fixture must deserialize"),
    )
}

type Row = (VcKind, VerificationResult, bool);

// The router starts each query's deadline before waiting for AY's process-local
// execution lock. Admit independent test cases before generating their queries,
// so libtest concurrency does not spend that deadline waiting on other fixtures.
// Keep the guard through certification and guard-removal rechecks; the router's
// own execution lock and every 30-second query limit remain unchanged.
static SOLVER_CASE_ADMISSION: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn verdicts(name: &str) -> Vec<Row> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let _admission = SOLVER_CASE_ADMISSION.lock().unwrap_or_else(|e| e.into_inner());
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
                    (vc.kind, r, certified)
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

fn is_add_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
}

fn rows_of(name: &str, want: fn(&VcKind) -> bool) -> Vec<Row> {
    let rows: Vec<Row> = verdicts(name).into_iter().filter(|(k, _, _)| want(k)).collect();
    assert!(!rows.is_empty(), "{name}: the obligation this row is about must be generated");
    rows
}

/// Every obligation of a correct program proves. The count is asserted too, so a
/// change that stops GENERATING an obligation reads as a failure, not a pass.
fn assert_all_proved(name: &str, expected_rows: usize) {
    let rows = verdicts(name);
    assert_eq!(rows.len(), expected_rows, "{name}: obligation count drifted; got {rows:?}");
    for (kind, verdict, _) in &rows {
        assert!(is_proved(verdict), "{name}: {kind:?} must prove; got {verdict:?}");
    }
}

/// The selected rows are NOT proved (but see the 2026-09-29 note: a proof that rests
/// on a passed runtime check is allowed) — the fail-closed direction — and no refuted row
/// is also kernel-certified.
///
/// Round A5: a row the callee-return havoc lane has DECLINED — reclassified to
/// `VcKind::UnsupportedMir` (`Unknown`, never dispatched) because its verdict was the
/// unconstrained `Some` payload of an unmodelled `Iterator::next` — is the SAME
/// obligation under its declined kind, so it is selected beside the wanted kinds and
/// counts as "not proved". A program that panics may therefore read `Unknown` here where
/// it used to read `Failed` on a witness the lane could not ground (the reseated
/// call-destination rows below); that is the honest verdict the lane's banner states,
/// and the direction this helper exists to pin — never a proof — is unchanged.
///
/// 2026-09-29: a PROVED selected row is allowed exactly when its proof rests on a
/// runtime `BoundsCheck` that PASSED — it loses the proof once the bare success
/// guards of the body's own bounds asserts are dropped from it. That is rustc's
/// "after the assert, the index is in bounds" twin of "the assert can fail": safe by
/// construction, and provable since the load/store lane carries the dominating
/// assert's definition (`_11 == (i < 5)` beside the guard `_11`). Before that, the
/// twin could never prove, so "not proved" held for it too and stood in for the
/// property checked here. And at least one selected row must stay NOT proved: the
/// program panics, so the check that faults may not be discharged.
fn assert_not_proved(name: &str, want: fn(&VcKind) -> bool) {
    let rows: Vec<(trust_types::VerificationCondition, VerificationResult, bool, bool)> =
        verdicts_with_guard_check(name)
            .into_iter()
            .filter(|(vc, _, _, _)| {
                want(&vc.kind) || matches!(vc.kind, VcKind::UnsupportedMir { .. })
            })
            .collect();
    assert!(!rows.is_empty(), "{name}: the obligation this row is about must be generated");
    let census: Vec<(VcKind, bool)> =
        rows.iter().map(|(vc, r, _, _)| (vc.kind.clone(), is_proved(r))).collect();
    assert!(
        rows.iter().any(|(_, r, _, _)| !is_proved(r)),
        "{name}: a program that PANICS has every selected obligation PROVED: {census:?}"
    );
    for (vc, verdict, certified, rests_on_a_passed_check) in &rows {
        assert!(
            !is_proved(verdict) || *rests_on_a_passed_check,
            "{name}: {:?} is PROVED again, and not by a runtime check that passed; got \
             {verdict:?}",
            vc.kind
        );
        assert!(
            !(matches!(verdict, VerificationResult::Failed { .. }) && *certified),
            "{name}: a refuted row may not also be kernel-certified"
        );
    }
}

/// [`verdicts`], each row with its verdict, its certification, and — for a PROVED
/// row — whether the proof is lost once every bare positive Boolean conjunct naming
/// the condition of one of the body's `BoundsCheck` asserts (the path guard of that
/// assert's SUCCESS edge) is replaced by `true`.
fn verdicts_with_guard_check(
    name: &str,
) -> Vec<(trust_types::VerificationCondition, VerificationResult, bool, bool)> {
    use trust_types::{AssertMessage, Formula, Operand, Sort, Terminator};
    fn drop_guards(f: &Formula, conds: &[String]) -> Formula {
        let is_guard = |g: &Formula| {
            matches!(g, Formula::Var(n, Sort::Bool)
                if conds.iter().any(|c| n.split('#').next() == Some(c.as_str())))
        };
        match f {
            Formula::And(parts) => Formula::And(
                parts
                    .iter()
                    .map(|p| if is_guard(p) { Formula::Bool(true) } else { drop_guards(p, conds) })
                    .collect(),
            ),
            Formula::Or(parts) => {
                Formula::Or(parts.iter().map(|p| drop_guards(p, conds)).collect())
            }
            other => other.clone(),
        }
    }
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let _admission = SOLVER_CASE_ADMISSION.lock().unwrap_or_else(|e| e.into_inner());
            let conds: Vec<String> = func
                .body
                .blocks
                .iter()
                .filter_map(|b| match &b.terminator {
                    Terminator::Assert {
                        cond: Operand::Copy(p) | Operand::Move(p),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        ..
                    } => Some(trust_vcgen::place_to_var_name(&func, p)),
                    _ => None,
                })
                .collect();
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
                    let rests_on_a_passed_check = is_proved(&r) && {
                        let mut stripped = vc.clone();
                        stripped.formula = drop_guards(&vc.formula, &conds);
                        let (_, again) = router
                            .verify_all(std::slice::from_ref(&stripped))
                            .into_iter()
                            .next()
                            .expect("one verdict per VC");
                        !is_proved(&again)
                    };
                    (vc, r, certified, rests_on_a_passed_check)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

// ── RECOVERED ──────────────────────────────────────────────────────────────

/// `pub fn u64_acc(a: &[u8; 64]) -> u64 { let mut t = 0; for &x in a { t += x as u64; } t }`
/// — `tests/trust-falsification/proved/wide_unsigned_accumulator.rs`, a MUST-PROVE row.
/// Pristine driver: 2 proved. With the resolver closure alone: the `Add` overflow row
/// REFUTED with `t = 18446744073709551615`, a value no execution reaches. The origin
/// hop on the iterator local restores the fixed-array trip count.
#[test]
fn for_each_accumulator_over_a_fixed_array_proves_again() {
    assert_all_proved("u64_acc", 2);
}

/// `t += (x as u128) << 4` over `&[u8; 16]` — the second half of the same corpus file.
/// Pristine driver: 4 proved. The DETERMINISTIC IN-PROCESS `ay` this harness drives
/// answers the 128-bit `Add` row `Unknown ("incomplete self-check-rejected")` — a
/// width limitation of that solver configuration, measured on this fixture, not a
/// verdict about the program — so this row asserts what the RECOVERED LANE
/// contributes and what the closure had cost: the accumulator bound
/// `t <= 0 + 16 * (255 << 4) = 65280` is minted onto the overflow obligation again
/// (it was withheld with the resolver closure alone), and NO row is a refutation.
/// The MUST-PROVE verdict on this function is the falsification gate's to measure
/// through the full compiler, where the pristine driver proves all four rows.
#[test]
fn shifted_for_each_accumulator_carries_its_bound_again_and_is_not_refuted() {
    let func = fixture("u128_shift");
    let vcs = trust_vcgen::generate_vcs(&func);
    let add_rows: Vec<_> = vcs.iter().filter(|vc| is_add_overflow(&vc.kind)).collect();
    assert!(!add_rows.is_empty(), "u128_shift: the `Add` overflow obligation must be generated");
    assert!(
        add_rows.iter().all(|vc| format!("{:?}", vc.formula).contains("Int(65280)")),
        "u128_shift: the recovered accumulator bound `t <= 65280` must be conjoined onto \
         every `Add` overflow row; got {:?}",
        add_rows.iter().map(|vc| format!("{:?}", vc.formula)).collect::<Vec<_>>()
    );
    for (kind, verdict, certified) in verdicts("u128_shift") {
        assert!(
            !matches!(verdict, VerificationResult::Failed { .. }),
            "u128_shift: {kind:?} must not be REFUTED on a correct program; got {verdict:?}"
        );
        assert!(!(matches!(verdict, VerificationResult::Failed { .. }) && certified));
    }
}

/// `for i in 0..64usize { t += a[i] as u64 }` on `&[u8; 64]`. Pristine driver: 3
/// proved. The trip count is read through the origin hop with `start` WITHHELD; for
/// an unsigned range `end` alone is a sound upper bound on the yields
/// (`loop_bounds::range_trip_count_upper_bound`), and that is all the accumulator
/// bound `t <= 0 + K * 255` needs.
#[test]
fn range_driven_accumulator_proves_again() {
    assert_all_proved("range_acc", 3);
}

/// `for i in 1..64usize { .. }` — the same with a non-zero `start`, which the origin hop
/// withholds. The upper bound is `end = 64` for 63 real trips: looser, still true, and
/// `64 * 255` still fits a `u64`. Pristine driver: 3 proved.
#[test]
fn range_from_one_accumulator_keeps_a_sound_upper_bound_trip_count() {
    assert_all_proved("range_acc_from1", 3);
}

/// `for y in 0..2usize { for x in 0..3usize { let i = y * 3 + x; s = s.wrapping_add(g[i]); } }`
/// on `&[u8; 6]` — the reviewer's second named program. Pristine driver: 4 proved. With
/// the closure alone `build_flattened_index_facts` returned `[]` and the `Mul`/`Add`
/// rows refuted. It reads only the range ENDS (`loop_var_const_range`'s `end`), which
/// the origin hop licenses.
#[test]
fn flattened_grid_index_proves_again() {
    assert_all_proved("grid_plain", 4);
}

/// `let mut it = 0..8usize; let _ = it.next(); for i in it { s += a[i] }` on `&[u8; 8]`.
/// BOTH `&mut it` conduits feed `Iterator::next`, so the origin gate passes; the loop
/// yields `1..8`, every one `< 8`, and the trip count read through the hop (8) is an
/// over-approximation of the real 7 — exactly the two facts the hop licenses and no
/// more. Pristine driver: 2 proved.
#[test]
fn a_stray_next_before_the_loop_keeps_the_end_bound() {
    assert_all_proved("stray_next", 2);
}

/// `for i in (0..8usize).rev() { s += a[i] }` on `&[u8; 8]`. `Rev::next` retracts the
/// inner `end`, so a STATE reading of the origin aggregate would be wrong here; the
/// yield-set reading (`every yield of a `Range{0, 8}` is `< 8`, reversed or not) is what
/// the tracer relies on, and it holds. Pristine driver: 2 proved.
#[test]
fn a_reversed_range_index_proves_again() {
    assert_all_proved("rev_index", 2);
}

/// `for i in 0..8usize { s += a[i] }` on `&[u8; 8]` — the plain control. Pristine
/// driver: 2 proved.
#[test]
fn a_range_index_proves_again() {
    assert_all_proved("range_index", 2);
}

/// `for (i, _) in s.iter().enumerate() { t += s[i] }` on `&[u8]`. The enumerate tracer
/// crosses the same hop; the count is `< s.len()` at every yield. Pristine driver: 2
/// proved.
#[test]
fn an_enumerate_index_proves_again() {
    assert_all_proved("enumerate_idx", 2);
}

// ── STILL REFUTED ──────────────────────────────────────────────────────────

/// `for i in 0..9usize { s += a[i] }` on `&[u8; 8]` — a REAL out-of-bounds read at
/// `i == 8`. The recovered yield bound is `i < 9`, which does not discharge `i < 8`, and
/// the row keeps its counterexample. Pristine driver: 1 proved, 1 failed. If this row
/// ever proves, the yield lane has become a blanket one.
#[test]
fn an_out_of_range_loop_index_still_refutes() {
    let rows = rows_of("range_index_oob", is_bounds);
    assert!(
        rows.iter().any(|(_, r, _)| is_refuted(r)),
        "range_index_oob: the real OOB must keep its counterexample; got {rows:?}"
    );
    assert!(rows.iter().all(|(_, r, c)| !is_proved(r) && !(is_refuted(r) && *c)));
}

// ── STILL CLOSED ───────────────────────────────────────────────────────────

/// THE WITNESS. `let mut m = 4usize; let p = &mut m; *p = pick(c); b[n % m]` on a
/// `[u8; 4]`, `pick(false) == 9`: panics at `pesc(false, 5, ..)`. Pristine driver:
/// 2 proved, kernel-certified under `-Ztrust-policy=certify`. The resolver refuses the
/// alias; the origin lane cannot admit it either — `m` is not an iterator and its
/// conduit `p` is WRITTEN THROUGH, which the conduit gate refuses outright.
#[test]
fn pesc_is_not_proved_on_either_channel() {
    assert_not_proved("pesc", is_bounds);
}

/// The same reseat with NO call: `*p = 9; b[n % m]` on a `[u8; 4]`. Pristine driver:
/// 2 proved — a second false proof from the same channel, with nothing but a constant
/// store behind it. Must not prove.
#[test]
fn pesc_without_a_call_is_not_proved() {
    assert_not_proved("pesc_nocall_bug", is_bounds);
}

/// `let mut it = 0..5usize; let p = &mut it; *p = 0..100usize; for i in it { s += a[i] }`
/// on `&[u8; 5]` — the iterator itself RESEATED through its conduit before the loop,
/// so it yields `0..100` and panics at `i == 5`. Pristine driver: 2 proved (the
/// resolver handed back `Range{0, 5}`). The resolver now refuses `it`; and the origin
/// lane's gate refuses it too, because `(*p) = ..` is a write rooted at the conduit —
/// the half of the allow-list that was missing until this change. A migration over the
/// old gate would have proved this program again; this row is what keeps that from
/// coming back.
#[test]
fn a_reseat_through_the_conduit_is_not_a_fresh_iterator() {
    assert_not_proved("reseat_through_conduit", is_bounds);
}

// ── THE CLOSURE'S RESIDUAL PRICE ON THE MODULO LANE, AGAINST ITS CONTROL ───
//
// `build_modulo_bound_facts` / `stable_min_arg_formula` resolve a divisor through
// the value resolver. An ALIASED divisor now declines there, so `n % m < K` is no
// longer minted from a stale `m = 4`. The question the review asked is what the
// row becomes on a CORRECT program: a decline, or a refutation with a witness no
// execution reaches. The answer is measured against the shape the closure moves
// the aliased divisor ONTO — the unaliased call destination `let m = pick(c)`,
// which `local_defs::body_unique_value_def` has always refused (`WholeOpaque`).

/// `let mut m = 4usize; let p = &mut m; *p = pick(c); b[n % m]` on a `[u8; 9]` —
/// CORRECT (`pick` returns 4 or 9). Pristine driver: 2 proved — through the stale
/// resolver answer, i.e. for the wrong reason (the same lane proved the `[u8; 4]`
/// witness above). Now the divisor is the unmodelled `pick(c)`, exactly as in the
/// control below, and the row is whatever that control's row is: not proved.
#[test]
fn pesc_in_range_variant_is_no_longer_proved_for_the_wrong_reason() {
    assert_not_proved("pesc_call_ok", is_bounds);
}

/// THE CONTROL: `let m = pick(c); b[n % m]` on a `[u8; 9]`, NO alias anywhere — the
/// call-destination shape the resolver has always refused. Pristine driver: 1 proved,
/// 1 failed. A correct program, refuted over the unmodelled crate-local callee's
/// return; `havoc_decline::HavocTables::reclassify` reclassifies only a
/// FOREIGN monomorphic callee's destination, so this row is a refutation BEFORE the
/// closure and independent of it. The aliased variant above now stands on this
/// footing rather than on a false proof; making this footing a decline is a change
/// to the callee-return havoc lane, not to the escape channel, and is recorded here
/// as the residual rather than absorbed.
#[test]
fn the_unaliased_call_divisor_control_is_the_baseline_this_lane_now_stands_on() {
    assert_not_proved("ctl_call_ok", is_bounds);
}

/// `let m = pick(c); b[n % m]` on a `[u8; 4]` — the control's genuine bug (`n % 9`
/// reaches 8). Pristine driver: 1 proved, 1 failed. Stays refuted.
#[test]
fn the_unaliased_call_divisor_bug_still_refutes() {
    let rows = rows_of("ctl_call_bug", is_bounds);
    assert!(
        rows.iter().any(|(_, r, _)| is_refuted(r)),
        "ctl_call_bug: the real OOB must keep its counterexample; got {rows:?}"
    );
    assert!(rows.iter().all(|(_, r, c)| !is_proved(r) && !(is_refuted(r) && *c)));
}

/// `let mut m = 4usize; let p = &mut m; *p = 8; b[n % m]` on a `[u8; 8]` — CORRECT,
/// no call, a constant store through the alias. Pristine driver: 2 proved (for the
/// wrong reason: the stale `4`). The resolver declines `m`; what the row becomes is
/// then up to the block encoder, which folds the single-borrow deref store
/// `(*p) = 8` onto `m` (`canonicalize_deref`) — so the block formula carries the
/// TRUE value and the row may still prove, honestly. This test asserts only the
/// fail-closed direction it must never lose: whatever it is, it is not a
/// kernel-certified refutation, and the `[u8; 4]` twin above is not proved.
#[test]
fn pesc_in_range_constant_store_variant_is_measured_not_assumed() {
    let rows = rows_of("pesc_nocall_ok", is_bounds);
    assert!(
        rows.iter().all(|(_, r, c)| !(matches!(r, VerificationResult::Failed { .. }) && *c)),
        "pesc_nocall_ok: a refuted row may not also be kernel-certified; got {rows:?}"
    );
}

// ── RESEATED CALL DESTINATIONS — the second adversarial review's finding ──────
//
// The recovery's tracers resolve an iterator local through the value resolver, then
// the origin question, and — when both decline because the local is a CALL
// DESTINATION — hopped into the producing call's `args[0]`. That hop was a bare block
// scan that took the FIRST call writing the local, so a call-dest iterator RESEATED
// after its constructor (by a second assignment, or through a `&mut` conduit) traced
// to the constructor. Every row below was PROVED, kernel-certified, on the pristine
// driver (2 proved, 0 failed, rc = 0) and panics at runtime. The hop is now
// `generate::iterator_yield::call_dest_hop` = `local_defs::unique_value_call`: the
// call must be the local's ONLY write channel. Fixtures are `-Copt-level=0` captures
// of the functions named in each doc.
//
// Round A5: with the hop refused, the payload of these `next` calls is the bare result
// of an unmodelled foreign `Iterator::next`, and `havoc_decline` now reclassifies the
// bounds row to `UnsupportedMir` (Unknown) rather than refuting it on a witness the
// lane cannot ground — `assert_not_proved` selects the declined row beside the bounds
// kinds. The direction each row pins is unchanged: never a proof.

/// `let mut r = (0..5usize).rev(); r = (0..100usize).rev(); for i in r { s += a[i] }`
/// on `&[u8; 5]` — `_3 = rev(Range{0,5})`, then `_3 = move _5` with `_5 =
/// rev(Range{0,100})`: a NAMED second write beside the call. Pristine: PROVED
/// `IndexOutOfBounds`, certified; runtime panics at `i == 99`. Now: not proved.
#[test]
fn a_call_dest_iterator_reseated_by_assignment_is_not_proved_rev() {
    assert_not_proved("dbl_rev", is_bounds);
}

/// The `into_iter` spelling of the same: `let mut r = (0..5usize).into_iter(); r =
/// (0..100usize).into_iter(); for i in r { .. }`. Pristine: PROVED, certified. Now: not
/// proved.
#[test]
fn a_call_dest_iterator_reseated_by_assignment_is_not_proved_into_iter() {
    assert_not_proved("dbl_into", is_bounds);
}

/// `let mut r = (0..5usize).rev(); let p = &mut r; *p = (0..100usize).rev(); for i in r
/// { .. }` — the reseat arrives THROUGH THE CONDUIT, naming `p` as its place; the only
/// trace on `r` is the `&mut r` itself (`LocalWrite::Escape`). Pristine: PROVED,
/// certified. Now: not proved — the hop refuses on the alias alone.
#[test]
fn a_call_dest_iterator_reseated_through_a_conduit_is_not_proved_rev() {
    assert_not_proved("alias_rev", is_bounds);
}

/// `let mut r = (0..5usize).into_iter(); let p = &mut r; *p = 0..100usize; for i in r
/// { .. }`. Pristine: PROVED, certified; panics at `i == 5`. Now: not proved.
#[test]
fn a_call_dest_iterator_reseated_through_a_conduit_is_not_proved_into_iter() {
    assert_not_proved("alias_into", is_bounds);
}

/// `let mut it = a.iter().enumerate(); let p = &mut it; *p = b.iter().enumerate(); for
/// (i, _) in it { s += a[i] }` on `a: &[u8; 5], b: &[u8; 100]` — the ENUMERATE tracer's
/// hop, reseated onto a longer slice. Pristine: PROVED `SliceBoundsCheck`, certified;
/// panics at `i == 5`. Now: not proved.
#[test]
fn a_reseated_enumerate_chain_is_not_proved() {
    assert_not_proved("enum_reseat", is_bounds);
}

/// The `windows`/`chunks` tracer's hop, both directions. `let mut w = a.windows(3); let
/// p = &mut w; *p = b.windows(2); for win in w { win[2] }` yields 2-windows and panics;
/// pristine PROVED the `[slice]` row on `win__slice_len = 3` from the FIRST constructor
/// (2 proved, 1 failed — the failed row is the unbounded remainder, not this one). Now:
/// not proved.
#[test]
fn a_reseated_windows_iterator_is_not_proved() {
    assert_not_proved("windows_reseat_bug", is_bounds);
}

/// The twin with the sizes swapped — `a.windows(2)` reseated to `b.windows(3)`, then
/// `win[2]` — is CORRECT, and the pristine driver REFUTED it (1 proved, 2 failed,
/// `win__slice_len#s7_0 = 2`): a false refutation on a correct program, from the same
/// first-constructor read. With the hop refused the length is unmodelled, and this row
/// asserts only what must never come back: no kernel-certified refutation, and the
/// bounds row is decided by the unmodelled length, never by `2`.
#[test]
fn the_correct_windows_reseat_twin_is_no_longer_refuted_on_the_stale_length() {
    let rows = rows_of("windows_reseat", is_bounds);
    assert!(
        rows.iter().all(|(_, r, c)| !(matches!(r, VerificationResult::Failed { .. }) && *c)),
        "windows_reseat: a refuted row may not also be kernel-certified; got {rows:?}"
    );
    // Measured under this tree: both rows `Failed` on `("win__slice_len#s7_0", Int(0))` —
    // the unmodelled length, the same footing as any slice the tracers cannot bound.
    // The stale first-constructor length would read `Int(2)` on that symbol.
    for (_, r, _) in &rows {
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = r {
            let cex = format!("{cex:?}");
            assert!(
                cex.contains("win__slice_len"),
                "windows_reseat: the witness no longer names the slice length; re-measure: {cex}"
            );
            assert!(
                !cex.contains("(\"win__slice_len#s7_0\", Int(2))"),
                "windows_reseat: the stale first-constructor length 2 is back in a witness: {cex}"
            );
        }
    }
}

// ── THE CONTROLS FOR THAT GATE ───────────────────────────────────────────────

/// `for i in (0..5usize).rev() { s += a[i] }` on `&[u8; 5]` — ONE constructor, ONE
/// write per local along the whole chain (`rev` dest, `into_iter` dest, the loop's
/// iterator copy). Pristine: 2 proved. The gate passes every hop and the row still
/// proves; if this row declines, the gate has become a blanket refusal of call-dest
/// iterators rather than of RESEATED ones.
#[test]
fn a_single_constructor_reversed_range_still_proves() {
    assert_all_proved("ctl_rev_ok", 2);
}

/// `for i in (0..10usize).step_by(2) { s += a[i] }` on `&[u8; 10]` — the 2-arg
/// `step_by` hop. Pristine: the `IndexOutOfBounds` row proved (the driver's rc = 1 there
/// is a runtime-checked panic-freedom row for the absent `step_by` callee, not this
/// row). The bounds row must still prove through the gated hop.
#[test]
fn a_single_constructor_step_by_range_still_proves_its_bounds_row() {
    let rows = rows_of("stepby_acc", is_bounds);
    for (kind, verdict, _) in &rows {
        assert!(is_proved(verdict), "stepby_acc: {kind:?} must prove; got {verdict:?}");
    }
}

// ── THE ENTRANCE HOP — the third adversarial review's finding ─────────────────
//
// The tracers are ENTERED from the `next` RESULT local: `_i = ((_o as Some).0)` asks
// "which iterator did `_o` come out of". That entrance was a bare first-call scan in
// four tracers (`next_call_range_operands`, `next_call_enumerated_slice`,
// `container_len::slice_iter_next_kind`, `loop_bounds::next_call_to_array_operand`)
// and in the bridge's `acc_*` port, and it asked nothing about `_o`'s OTHER writes.
// rustc's `expr_into_dest` lowering of `let o = if c { small.next() } else {
// big.next() }` writes `_o` from two `next` calls in two branches; the scan attributed
// the payload to whichever call came first in block order. Every row below was PROVED,
// kernel-certified, on the pristine driver (`-Ztrust-policy=strict`, rc = 0 where the
// bounds row was the only one) and panics at runtime; exchanging the arms flipped the
// verdict to a refutation, so the verdict depended on nothing but block order. The
// entrance is now `iterator_yield::next_call_receiver` = `local_defs::unique_value_call`
// on the Option local. Fixtures are `-Copt-level=0` captures of the functions named in
// each doc, dumped from the pristine stage1 driver.

/// THE WITNESS. `let mut small = 0..5usize; let mut big = 50..100usize; let o = if c {
/// small.next() } else { big.next() }; if let Some(i) = o { a[i] } else { 0 }` on
/// `&[u8; 5]`. Pristine: 2 proved, 2 kernel-certified; `two_next_if(false, ..)` panics
/// "index out of bounds: the len is 5 but the index is 50". Now: not proved.
#[test]
fn a_payload_written_by_two_next_calls_is_not_attributed_to_the_first_range() {
    assert_not_proved("two_next_if", is_bounds);
}

/// The arms exchanged (`big.next()` in the THEN arm). Pristine: 1 proved, 1 FAILED —
/// the same program, up to which branch is spelled first, was REFUTED, which is what
/// shows the proof above was about block order and nothing else. The bug is real
/// (`c == true` panics), so a refutation stays honest; what may never come back is a
/// proof, or a kernel-certified refutation.
#[test]
fn the_arm_exchanged_twin_stays_unproved() {
    assert_not_proved("two_next_if_swapped", is_bounds);
}

/// `loop { let o = if c { small.next() } else { big.next() }; match o { Some(i) => s =
/// s.wrapping_add(a[i]), None => break } }` — the same two writes inside a loop.
/// Pristine: 2 proved, certified; panics at 50. Now: not proved.
#[test]
fn a_loop_selected_next_payload_is_not_attributed_to_the_first_range() {
    assert_not_proved("two_next_loop", is_bounds);
}

/// `let o = match k { 0 => big.next(), _ => small.next() }` — the `match` lowering puts
/// the `_` arm FIRST in block order, so the scan read `small` here. Pristine: 2 proved,
/// certified; `two_next_match_bug(0, ..)` panics at 50. Now: not proved.
#[test]
fn a_match_selected_next_payload_is_not_attributed_to_the_first_range() {
    assert_not_proved("two_next_match_bug", is_bounds);
}

/// The `match` twin with the arms exchanged (`0 => small.next(), _ => big.next()`):
/// pristine 1 proved, 1 failed — refuted for the block-order reason, honest by luck
/// (`k != 0` panics). Stays unproved.
#[test]
fn the_match_arm_exchanged_twin_stays_unproved() {
    assert_not_proved("two_next_match", is_bounds);
}

/// The ENUMERATE tracer's entrance: `let mut e1 = a.iter().enumerate(); let mut e2 =
/// b.iter().enumerate(); let _ = e2.nth(49); let o = if c { e1.next() } else {
/// e2.next() }; if let Some((i, _)) = o { a[i] }` on `a: &[u8; 5], b: &[u8; 100]`.
/// Pristine: `IndexOutOfBounds` proved, certified; panics at 50. Now: not proved.
#[test]
fn a_two_next_enumerate_payload_is_not_attributed_to_the_first_slice() {
    assert_not_proved("two_next_enum", is_bounds);
}

/// The same in `loop` form without the `nth`: `loop { let o = if c { e1.next() } else
/// { e2.next() }; match o { Some((i, _)) => .. a[i] .., None => break } }`. Pristine: 2
/// proved, certified; `two_next_enum_loop(false, ..)` panics at `i == 5`. Now: not
/// proved.
#[test]
fn a_loop_selected_enumerate_payload_is_not_attributed_to_the_first_slice() {
    assert_not_proved("two_next_enum_loop", is_bounds);
}

/// The `windows`/`chunks` tracer's entrance: `let mut w1 = a.windows(3); let mut w2 =
/// b.windows(2); let o = if c { w1.next() } else { w2.next() }; if let Some(w) = o {
/// w[2] }`. Pristine: BOTH `SliceBoundsCheck` rows proved, certified, on the stale
/// `w__slice_len = 3` from the FIRST constructor; panics "the len is 2 but the index
/// is 2". The two rows are not alike: one is the bounds `Assert` itself (`2 < len(w)`),
/// the other is the `w[2]` READ in the block that `Assert` guards — the read row
/// carries the assert's edge fact `_15` as a premise and proves honestly whatever
/// `len(w)` is. So the pin is on the ASSERT row and on the LENGTH: the assert row is
/// not proved, no row is a kernel-certified refutation, and no bounds row constrains
/// the payload length to the first constructor's `3` (measured: the length symbol
/// `w__slice_len#s6_0` is unconstrained in both rows; the assert row is a refutation
/// with `_14 = 0`, which the program's `w2` branch realises up to `len = 2`).
///
/// Round A5: the entrance is now the JOIN (`iterator_yield::next_call_receivers`), so
/// the rows carry `len(w) == 3 ∨ len(w) == 2` — BOTH constructors, as one disjunction —
/// and the assert row refutes on `len = 2`, the witness the program realises. What may
/// never come back is either constructor's `n` asserted ALONE: the pin is that every
/// occurrence of `Eq(len(w), 3)` / `Eq(len(w), 2)` is inside that joined disjunction.
#[test]
fn a_two_next_windows_payload_is_not_attributed_to_the_first_window_length() {
    let func = fixture("two_next_win");
    let vcs = trust_vcgen::generate_vcs(&func);
    let bounds: Vec<_> = vcs.iter().filter(|vc| is_bounds(&vc.kind)).collect();
    // 2026-09-20: the guarded read is suppressed as the rvalue twin of the
    // assert that covers it, so the assert row is the only one left — and it is
    // the row this test is about (its body is `Ge(_13, _14)`, the assert's
    // negation). The join-pinning check below reads it exactly as before.
    assert_eq!(bounds.len(), 1, "two_next_win: the assert row; got {bounds:?}");
    const JOIN: &str = "Or([And([Eq(Var(\"w__slice_len#s6_0\", Int), Int(3))]), \
                        And([Eq(Var(\"w__slice_len#s6_0\", Int), Int(2))])])";
    for vc in &bounds {
        let f = format!("{:?}", vc.formula);
        let outside_join = f.replace(JOIN, "");
        assert!(
            !outside_join.contains("Eq(Var(\"w__slice_len#s6_0\", Int), Int(3))")
                && !outside_join.contains("Eq(Var(\"w__slice_len#s6_0\", Int), Int(2))"),
            "two_next_win: a bounds row pins the window length to ONE constructor's `n` \
             outside the join: {f}"
        );
    }
    let rows = rows_of("two_next_win", is_bounds);
    assert!(
        rows.iter().any(|(_, r, _)| !is_proved(r)),
        "two_next_win: the bounds `Assert` row is PROVED again; got {rows:?}"
    );
    assert!(
        rows.iter().all(|(_, r, c)| !(matches!(r, VerificationResult::Failed { .. }) && *c)),
        "two_next_win: a refuted row may not also be kernel-certified; got {rows:?}"
    );
}

/// The CORRECT twin of the witness: `big = 2..5usize`, both ranges inside `[0, 5)`.
/// Pristine: 2 proved — for the WRONG reason (`small`'s fact `i < 5` happened to hold
/// of `big` too). The third round refused the entrance and MEASURED `Failed` with a
/// counterexample (`_8 = 1`, the unconstrained payload) — a refutation of a correct
/// program, recorded then as the residual. Round A5 built the sound recovery that doc
/// named: the JOIN of every producing `next`'s yield set when EVERY write channel of
/// the Option local is such a call (`local_defs::value_calls` →
/// `iterator_yield::next_call_receivers`), so the row carries `(0 <= i < 5) ∨ (2 <= i <
/// 5)` and PROVES — for the right reason this time. The `a5_two_next_if_ok` row pins
/// the same program from the A5 pin crate; this one keeps the third round's fixture.
#[test]
fn the_in_range_two_next_twin_proves_through_the_join() {
    assert_all_proved("two_next_if_ok", 2);
}

// ── THE CONTROLS FOR THE ENTRANCE GATE ───────────────────────────────────────

/// `let mut small = 0..5usize; if c { let _ = small.next(); } let o = small.next(); if
/// let Some(i) = o { a[i] } else { 0 }` on `&[u8; 5]` — ONE `next` call writes `o`
/// (the stray `next` writes a different temp), and BOTH `&mut small` conduits feed
/// `next`. Pristine: 2 proved. The entrance passes and the row still proves; if this
/// row declines, the gate has become a blanket refusal of `next` results rather than of
/// MULTIPLY-WRITTEN ones.
#[test]
fn a_single_next_written_payload_still_proves() {
    assert_all_proved("two_next_single", 2);
}

/// `let mut w1 = a.windows(3); let o = w1.next(); if let Some(w) = o { w[2] }` on
/// `&[u8; 5]` — the `windows` tracer's single-write control. Pristine: 3 proved (the
/// driver's fourth row is a runtime-checked panic-freedom row for the absent `windows`
/// callee, not generated by this crate's pipeline). Both `SliceBoundsCheck` rows and
/// the `Unreachable` row must still prove through the gated entrance.
#[test]
fn a_single_next_written_window_payload_still_proves() {
    // 2026-09-20: two rows, not three — the guarded read is now suppressed as
    // the rvalue twin of the `BoundsCheck` assert that covers it (same note as
    // `a8_the_bare_bound_arm_is_measured_against_a_sibling_lane`). What this
    // test is about is unchanged: the single-`next` payload still PROVES.
    assert_all_proved("two_next_win_single", 2);
}

// ── THE `start` DECISION, PINNED WITH ITS MEASUREMENT ────────────────────────

/// `for i in 0..5i32 { s += a[i as usize] }` on `&[u8; 5]`. Pristine: 2 proved. With
/// `start` WITHHELD across the origin hop (the first recovery) this row went to
/// UNKNOWN: the bounds obligation needs `i >= 0` before the `as usize` cast, and only
/// `i < 5` was minted — a measured over-refusal. `start` is now admitted as a YIELD
/// lower bound (`iterator_yield::RangeOrigin` carries the argument: every yield of a
/// `Range{s, e}`, however far consumed, lies in `[s, e)`), and the row proves again.
/// `a_stray_next_before_the_loop_keeps_the_end_bound` above is the row that keeps this
/// from being read as position: a `next` before the loop is admitted and the bound
/// still holds of every yield.
#[test]
fn a_signed_range_index_cast_to_usize_proves_again() {
    assert_all_proved("signed_range", 2);
}

// ── ROUND A5: THE PAYLOAD LOCAL — the fourth adversarial review's finding ───────
//
// The three yield-fact builders (`build_range_yield_guard_map`,
// `build_enumerate_yield_guard_map`, `container_len::build_slice_iter_yield_guard_map`)
// took `dest.local` of `_p = ((_o as Some).0)` and attached `start <= _p < end` /
// `0 <= _p < len` / `len(_p) == n` to every block mentioning `_p` — conjoined by
// `safety.rs` AFTER the version rename — with NO check that `_p` has one write. A
// `mut` pattern binding falsifies the module banner's "assigned exactly once": `for
// mut i in 0..5usize { i = n; t = a[i]; }` lowers to `_10 = ((_7 as Some).0); _10 =
// _2; _12 = _10; assert(Lt(_12, 5))`, and the fact minted `Ge(i#s5_1, 0) ∧ Lt(i#s5_1,
// 5) ∧ Eq(i#s5_1, n)` on the POST-reassignment version: UNSAT, PROVED, kernel-
// certified — on the pristine driver AND on the previous round of this tree — while
// the program panics at `n = 50`. Eleven probes proved that way. The gate is now
// `iterator_yield::payload_carries_global_fact` = `local_defs::is_single_static_assignment`
// on the payload local, in all three builders; a payload with a second whole write, a
// projected write, an alias or an unlocatable write gets NO fact. Fixtures are
// `-Copt-level=0` captures of `a5_pins.rs` (crate `a5_pins`) from the stage1 driver;
// the runtime oracle for every row is recorded in its doc.

/// `for mut i in 0..5usize { i = n; t = a[i]; }` on `&[u8; 5]`. Previous round: PROVED,
/// certified. Oracle: `payload_param_for(&a, 50)` PANICS "the len is 5 but the index is
/// 50". Now: not proved (a refutation on the unconstrained payload, uncertified).
#[test]
fn a5_payload_reassigned_from_a_parameter_in_a_for_loop_is_not_proved() {
    assert_not_proved("a5_payload_param_for", is_bounds);
}

/// `for mut i in 0..5usize { if c { i = n; } t = a[i]; }`. Previous round: PROVED,
/// certified. Oracle: PANICS at `(n = 50, c = true)`. Now: not proved.
#[test]
fn a5_payload_conditionally_reassigned_from_a_parameter_is_not_proved() {
    assert_not_proved("a5_payload_param_cond", is_bounds);
}

/// `for mut i in 0..5usize { i += 1; t = a[i]; }` — the increment is a second whole
/// write (`_10 = move (_14.0)`) of the payload. Previous round: BOTH the bounds row and
/// the `Add` overflow row PROVED, certified. Oracle: PANICS at `i == 5`. Now: not proved.
#[test]
fn a5_payload_incremented_in_place_is_not_proved() {
    assert_not_proved("a5_payload_incr", is_bounds);
}

/// `if let Some(mut i) = small.next() { i = n; a[i] }` — the single-`next` `if let`
/// form. Previous round: PROVED, certified. Oracle: PANICS at `n = 50`. Now: not proved.
#[test]
fn a5_if_let_payload_reassigned_from_a_parameter_is_not_proved() {
    assert_not_proved("a5_iflet_payload_param", is_bounds);
}

/// `for mut i in 0..5i32 { i = n; t = a[i as usize]; }` — the SIGNED range, whose
/// `start` fact `i >= 0` is what the cast needs. Previous round: PROVED, certified.
/// Oracle: PANICS at `n = -1` (index 18446744073709551615) and at `n = 50`. Now: not
/// proved.
#[test]
fn a5_signed_payload_reassigned_from_a_parameter_is_not_proved() {
    assert_not_proved("a5_signed_payload_param", is_bounds);
}

/// `for (mut i, _) in a.iter().enumerate() { i = n; t = a[i]; }` — the ENUMERATE
/// builder's payload. Previous round: PROVED, certified. Oracle: PANICS at `n = 50`.
/// Now: not proved.
#[test]
fn a5_enumerate_index_reassigned_from_a_parameter_is_not_proved() {
    assert_not_proved("a5_enum_payload_param", is_bounds);
}

/// `for mut w in a.windows(3) { w = s; t = w[2]; }` — the WINDOWS builder's payload,
/// reseated to a parameter slice. Previous round: the bounds `Assert` row PROVED with
/// `Eq(w__slice_len#s6_1, 3)` minted on the post-reseat version, certified. Oracle:
/// PANICS with `s = &a8[..1]` ("the len is 1 but the index is 2"). Now: no bounds row
/// proves and no row is a kernel-certified refutation. Measured under this tree: both
/// `SliceBoundsCheck` rows `Failed` on the unmodelled length, uncertified.
#[test]
fn a5_windows_payload_reseated_to_a_parameter_slice_is_not_proved() {
    assert_not_proved("a5_win_payload_param", is_bounds);
}

/// The constant-index variants (`i = 50`), each PROVED and certified on the previous
/// round and each a runtime PANIC: `for` form, `if let` form, conditional form, and
/// the `enumerate` form. Now: none proved.
#[test]
fn a5_constant_reassignments_of_the_payload_are_not_proved() {
    for name in [
        "a5_payload_reassign_for",
        "a5_payload_reassign_iflet",
        "a5_payload_reassign_cond",
        "a5_enum_payload_reassign",
    ] {
        assert_not_proved(name, is_bounds);
    }
}

/// THE CONTROL: `for mut i in 0..5usize { if c { i = 4; } t = a[i]; }` — CORRECT
/// (oracle: ok for both `c`). Previous round: PROVED — for the WRONG reason (the fact
/// bound the post-reassignment version, and `4 < 5` happened to hold). The payload now
/// fails the gate and carries no fact; the honest verdict is Unknown, and what the row
/// may never be is a kernel-certified refutation. Measured under this tree: `Failed`
/// on the unconstrained payload, uncertified — the same footing as `ctl_call_ok`.
#[test]
fn a5_the_conditional_in_range_reassignment_control_is_never_a_certified_refutation() {
    let rows = rows_of("a5_ctl_cond_reassign_ok", is_bounds);
    for (kind, verdict, certified) in &rows {
        assert!(
            !(matches!(verdict, VerificationResult::Failed { .. }) && *certified),
            "a5_ctl_cond_reassign_ok: a refuted row may not be kernel-certified; got {kind:?} {verdict:?}"
        );
    }
}

/// The payload gate must NOT refuse the un-reassigned binding: every RECOVERED row above
/// (`u64_acc`, `range_acc`, `grid_plain`, `ctl_rev_ok`, `stepby_acc`, `signed_range`,
/// `enumerate_idx`, `rev_index`, `stray_next`, `two_next_single`, `two_next_win_single`)
/// still runs through `assert_all_proved` in its own test. This row adds the plain
/// `for`-loop control from the same pin crate, so a regression of the gate to a
/// blanket refusal fails beside the `a5_*` rows it belongs with.
#[test]
fn a5_the_plain_for_loop_payload_still_proves() {
    assert_all_proved("a5_acc_elem_ctl", 2);
}

// ── ROUND A5: THE RANGE BOUND — `resolve_range_bound_formula` ─────────────────────

/// `let mut n = 5usize; for i in 0..n { n = 100; t = a[i]; }` on `&[u8; 5]` — CORRECT
/// (oracle: ok 105). Previous round: `Failed` with a counterexample — the bound `end`
/// resolved to the BARE `n`, the version rename bound it to the post-store `100`, and
/// `i < 100` no longer discharged `i < 5`: a false refutation. Now the multiply-written
/// `n` does not resolve, no yield fact is minted, and the payload is the bare result of
/// an unmodelled foreign `Iterator::next` — which `havoc_decline` reclassifies to
/// `UnsupportedMir` (Unknown). The row must not be a refutation.
#[test]
fn a5_a_range_end_reassigned_inside_the_loop_does_not_refute_the_correct_program() {
    let rows = rows_of("a5_ctl_end_reassign_ok", |k| {
        is_bounds(k) || matches!(k, VcKind::UnsupportedMir { .. })
    });
    assert!(
        rows.iter().all(|(_, r, _)| !matches!(r, VerificationResult::Failed { .. })),
        "a5_ctl_end_reassign_ok: a correct program is REFUTED; got {rows:?}"
    );
}

/// The mirror: `let mut n = 100usize; for i in 0..n { n = 5; t = a[i]; }` — PANICS at
/// `i == 5` (oracle). The same bare-name fallback read in the PROVING direction (`i <
/// n` renamed to the post-store `5`) would discharge the bounds row. Must not prove.
#[test]
fn a5_a_range_end_reassigned_inside_the_loop_does_not_prove_the_panicking_program() {
    assert_not_proved("a5_end_reassign", is_bounds);
}

/// `fn f(a, mut n: usize) { for i in 0..n { n = 5; t = a[i]; } }` — a PARAMETER end
/// with a body write; PANICS at `n = 100` (oracle). Must not prove.
#[test]
fn a5_a_reassigned_parameter_range_end_does_not_prove_the_panicking_program() {
    assert_not_proved("a5_end_param_reassign", is_bounds);
}

// ── ROUND A5: THE JOINED ENTRANCE ─────────────────────────────────────────────────

/// `let o = if c { small.next() } else { big.next() }` with `small = 0..5`, `big =
/// 2..5`, `a: &[u8; 5]` — CORRECT (oracle: ok for both `c`). Pristine: PROVED for the
/// wrong reason (`small`'s fact alone). Previous round: `Failed` with `_8 = 1` — a false
/// refutation over the unmodelled payload. Now: PROVED for the right reason — the
/// entrance is the JOIN `(0 <= i < 5) ∨ (2 <= i < 5)` (`local_defs::value_calls`: the
/// two `next` calls are `_o`'s only write channels; both receivers trace).
#[test]
fn a5_the_in_range_two_next_twin_proves_through_the_join() {
    assert_all_proved("a5_two_next_if_ok", 2);
}

/// The same with symbolic ends: `0..a.len()` against `1..m` under `if m > n { return }`
/// on `a: &[u8]`. The join carries `(0 <= i < len(a)) ∨ (1 <= i < m)` and the guard
/// supplies `m <= len(a)`. CORRECT (oracle: ok for `m in 0..=5`, `m = 9`). Now: the
/// bounds row proves.
#[test]
fn a5_the_symbolic_two_next_join_proves_under_the_guard() {
    let rows = rows_of("a5_two_next_if_ok_sym", is_bounds);
    for (kind, verdict, _) in &rows {
        assert!(is_proved(verdict), "a5_two_next_if_ok_sym: {kind:?} must prove; got {verdict:?}");
    }
}

/// THE BUG under the join: `big = 50..100`. The joined fact `(0 <= i < 5) ∨ (50 <= i <
/// 100)` leaves the bounds row REFUTED — now on a witness the program realises (`i >=
/// 50`), where the previous round's witness was the unconstrained `_8 = 1`. Oracle:
/// PANICS at `c = false`.
#[test]
fn a5_the_two_next_witness_still_refutes_with_a_grounded_witness() {
    let rows = rows_of("a5_two_next_if", is_bounds);
    assert!(
        rows.iter().any(|(_, r, _)| is_refuted(r)),
        "a5_two_next_if: the real OOB must keep its counterexample; got {rows:?}"
    );
    for (_, r, c) in &rows {
        assert!(!is_proved(r) && !(is_refuted(r) && *c));
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = r {
            let grounded = cex.assignments.iter().any(|(_, v)| {
                matches!(v, trust_types::CounterexampleValue::Int(k) if (50..100).contains(k))
            });
            assert!(
                grounded,
                "a5_two_next_if: the witness must realise the `big` branch; got {cex:?}"
            );
        }
    }
}

/// The join WITHHELD: `let _ = big.nth(0);` before the `if` — `big`'s conduit feeds
/// `nth`, so `big` does not trace and no fact is minted on the payload. CORRECT
/// (oracle: ok for both `c`). Previous round's footing for this shape: `Failed` over
/// the unmodelled payload. Now: the payload is the bare result of unmodelled foreign
/// `Iterator::next` calls and nothing pins it, so `havoc_decline` reclassifies the
/// bounds row to `UnsupportedMir` (Unknown). Never a refutation.
#[test]
fn a5_a_declined_two_next_entrance_is_unknown_not_refuted() {
    let rows = rows_of("a5_two_next_if_ok_nth", |k| {
        is_bounds(k) || matches!(k, VcKind::UnsupportedMir { .. })
    });
    assert!(
        rows.iter().all(|(_, r, _)| !matches!(r, VerificationResult::Failed { .. })),
        "a5_two_next_if_ok_nth: a correct program is REFUTED; got {rows:?}"
    );
    assert!(
        rows.iter().any(|(k, _, _)| matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "UnmodeledCalleeReturn")),
        "a5_two_next_if_ok_nth: the bounds row must be the havoc-declined Unknown; got {rows:?}"
    );
}

// ── ROUND A5: THE ACCUMULATOR TWIN ────────────────────────────────────────────────

/// `for &x in a { let mut y = x as u64; y = n; t += y; }` on `&[u8; 64]`, `n: u64` — the
/// reduction addend RESEATED to a parameter, so `t <= 0 + 64 * 255` is FALSE (oracle:
/// `n = u64::MAX` overflows). `build_accumulator_bound_facts` resolves the addend
/// through the value resolver, which refuses the two-write `y`; the `Add` row must not
/// prove and no formula may carry the bound.
#[test]
fn a5_a_reseated_reduction_addend_mints_no_accumulator_bound() {
    let func = fixture("a5_acc_elem_reseat");
    let vcs = trust_vcgen::generate_vcs(&func);
    for vc in vcs.iter().filter(|vc| is_add_overflow(&vc.kind)) {
        let f = format!("{:?}", vc.formula);
        assert!(!f.contains("Int(16320)"), "a5_acc_elem_reseat: the false bound is minted: {f}");
    }
    assert_not_proved("a5_acc_elem_reseat", is_add_overflow);
}

// ── THE PRE-EXISTING SHAPE, FOR CONTRAST ───────────────────────────────────

/// `for &x in a { t += x as u64 }` over an UNBOUNDED `&[u8]`. There is no trip count to
/// recover — the accumulator genuinely may overflow in the abstract model — and the
/// pristine driver already reported this row `1 proved, 1 failed`. It is here so the
/// recovered rows above are read against the right baseline: a loop the tracers cannot
/// bound was a refutation before the closure and stays one; the closure's cost was
/// confined to loops that ARE bounded, and that cost is repaid above.
#[test]
fn an_unbounded_slice_accumulator_is_the_baseline_refutation_not_a_regression() {
    assert_not_proved("slice_acc", is_add_overflow);
}

// ── ROUND A6: THE `__slice_len` ROOT — the fifth adversarial review's finding ───────
//
// `resolve_range_bound_formula` canonicalizes a `PtrMetadata`/`Len` range END to the
// `{root}__slice_len` term the index VC uses, and `build_enumerate_yield_guard_map`
// inlines `slice_len_formula(s)` of the enumerated slice. Both are NAMES: a whole write
// of `s` versions `s__slice_len` (`path_defs::write_covers_derived_slice_len`), and the
// payload fact `i < s__slice_len` is conjoined after the rename, so it bound to the
// POST-reseat version. At `-Copt-level=1` rustc emits `PtrMetadata(copy s)` on the
// user's local directly and every row below PROVED, kernel-certified, on the pristine
// driver and on the previous round of this tree; at `-O0` the copy temp (`_7 = copy _2;
// PtrMetadata(move _7)`) keyed the name on a single-write temp and the rows were
// refuted BY ACCIDENT of the lowering, not by any gate. The licence is now
// `iterator_yield::licensed_slice_len_formula` = `slice_len_name_is_stable`: the keyed
// local and every whole-local `Use`/`Ref` hop of its definition chain must be
// single-static-assignment with no projected write. Fixtures: `a7_pins.rs` (crate
// `a7_pins`) dumped from the stage1 driver at BOTH `-Copt-level=0` (`_o0`) and
// `-Copt-level=1` (`_o1`); the runtime oracle for every row is in its doc.

/// `let mut s: &[u8] = a; for i in 0..s.len() { s = &a[..1]; t += s[i]; }` — PANICS at
/// `i == 1` (oracle). Previous round at `-O1`: BOTH `SliceBoundsCheck` rows PROVED,
/// certified (`Lt(i, s__slice_len#s5_t)` bound to the post-reseat version). Now: not
/// proved at either level.
#[test]
fn a7_a_range_end_read_off_a_reseated_local_slice_is_not_proved() {
    assert_not_proved("a7_len_method_reseat_o1", is_bounds);
    assert_not_proved("a7_len_method_reseat_o0", is_bounds);
    assert_not_proved("a7_len_ufcs_reseat_o1", is_bounds);
    assert_not_proved("a7_len_ufcs_reseat_o0", is_bounds);
}

/// THE REVIEWER'S COUNTEREXAMPLE. `fn f(mut s: &[u8], b: &[u8]) { for i in
/// 0..<[u8]>::len(s) { s = b; t += s[i]; } }` — a `mut` PARAMETER reseated to another
/// parameter; `f(&[1,2,3,4,5], &[1])` PANICS at `i == 1`. Real compiler, `-O1`,
/// `-Ztrust-policy=certify`: rc = 0, "3 proved … 3 kernel-certified" on the previous
/// round AND on the pristine sealed driver. Now: not proved at either level.
#[test]
fn a7_a_range_end_read_off_a_reseated_parameter_slice_is_not_proved() {
    assert_not_proved("a7_len_ufcs_param_reseat_o1", is_bounds);
    assert_not_proved("a7_len_ufcs_param_reseat_o0", is_bounds);
}

/// `let mut s = a; let n = s.len(); for i in 0..n { s = &a[..1]; t += s[i]; }` — the
/// bound is the SSA local `n`, whose one definition is `PtrMetadata` of the reseatable
/// `s`. Previous round at `-O1`: PROVED, certified — the canonicalization substituted
/// `s__slice_len` for the sound bare `n`. Now: the root fails the licence and the bound
/// resolves to NOTHING (not to the bare `n` either, which would pin the payload to a
/// length the obligation never reads and keep the havoc lane from declining); the
/// row is not proved. PANICS at `i == 1` (oracle).
#[test]
fn a7_a_bound_defined_as_the_length_of_a_reseated_root_is_not_canonicalized_onto_it() {
    assert_not_proved("a7_let_n_reseat_o1", is_bounds);
    assert_not_proved("a7_let_n_reseat_o0", is_bounds);
}

/// The ENUMERATE lane: `for (i, _) in <[u8]>::iter(s).enumerate() { s = &a[..1]; t +=
/// s[i]; }` and the method spelling. Previous round at `-O1`: the `s[i]` row PROVED,
/// certified, on `Lt(i, s__slice_len#s7_t)`. Now: not proved at either level. PANICS
/// at `i == 1` (oracle).
#[test]
fn a7_an_enumerate_index_bounded_by_a_reseated_slice_is_not_proved() {
    assert_not_proved("a7_enum_ufcs_reseat_o1", is_bounds);
    assert_not_proved("a7_enum_ufcs_reseat_o0", is_bounds);
    assert_not_proved("a7_enum_method_reseat_o1", is_bounds);
    assert_not_proved("a7_enum_method_reseat_o0", is_bounds);
}

/// The `as_bytes` REDIRECT: `let mut s: &str = a; for i in 0..s.as_bytes().len() { s =
/// b; t += s.as_bytes()[i]; }`. `slice_len_formula` keys an `as_bytes()` result on its
/// RECEIVER's length, so the name inlined was `s__slice_len` of the reseated `s`.
/// Previous round at `-O1`: BOTH rows PROVED, certified. Now: the licence follows the
/// redirect to the receiver and refuses. PANICS (oracle: `("hello", "h")`).
#[test]
fn a7_an_as_bytes_length_of_a_reseated_str_is_not_proved() {
    assert_not_proved("a7_str_bytes_len_reseat_o1", is_bounds);
    assert_not_proved("a7_str_bytes_len_reseat_o0", is_bounds);
}

/// A slice in a struct FIELD written inside the loop: `for i in 0..h.s.len() { h.s = b;
/// t += h.s[i]; }` on `h: &mut H`. The length temp's definition chain lands on the
/// projected slot `(*h).s`, whose root `h` has a projected write. Refuted on both
/// rounds (the chain's ROOT gate is what would refuse it if the encoder ever tied the
/// slot's length); pinned as not proved. PANICS (oracle).
#[test]
fn a7_a_field_slice_reseated_in_the_loop_is_not_proved() {
    assert_not_proved("a7_field_len_reseat_o1", is_bounds);
    assert_not_proved("a7_field_len_reseat_o0", is_bounds);
}

/// The reseat AFTER the read (`t += s[i]; s = &a[..1];` — the previous iteration's
/// reseat is live at the next read). Refuted on both rounds; stays not proved. PANICS.
#[test]
fn a7_a_reseat_after_the_read_is_not_proved() {
    assert_not_proved("a7_len_method_reseat_after_o1", is_bounds);
    assert_not_proved("a7_len_method_reseat_after_o0", is_bounds);
}

// ── THE CONTROLS FOR THE ROOT LICENCE — MUST PROVE at BOTH optimisation levels ────

/// `for i in 0..s.len() { t += s[i] }` / UFCS `len` / `let n = s.len()` / a local copy
/// `let s: &[u8] = a` / the enumerate spellings, all on a never-written `s: &[u8]`.
/// Oracle: ok 15 each. If any of these declines, the licence has become a blanket
/// refusal of `__slice_len` bounds rather than of REBINDABLE ones. The `-O1` dumps are
/// the ones where `PtrMetadata(copy s)` names the parameter directly.
#[test]
fn a7_the_stable_slice_length_controls_still_prove() {
    for name in [
        "a7_ctl_len_method_o1",
        "a7_ctl_len_method_o0",
        "a7_ctl_len_ufcs_o1",
        "a7_ctl_len_ufcs_o0",
        "a7_ctl_let_n_len_o1",
        "a7_ctl_let_n_len_o0",
        "a7_ctl_local_copy_len_o1",
        "a7_ctl_local_copy_len_o0",
        "a7_ctl_enum_ufcs_o1",
        "a7_ctl_enum_ufcs_o0",
        "a7_ctl_enum_method_o1",
        "a7_ctl_enum_method_o0",
        "a7_ctl_param_end_guard_o1",
        "a7_ctl_param_end_guard_o0",
        "a7_ctl_str_bytes_len_o1",
        "a7_ctl_str_bytes_len_o0",
    ] {
        let rows = rows_of(name, is_bounds);
        for (kind, verdict, _) in &rows {
            assert!(is_proved(verdict), "{name}: {kind:?} must prove; got {verdict:?}");
        }
    }
}

/// `let mut s = a; for i in 0..s.len() { t += s[i]; } s = b;` — CORRECT (oracle: ok 16),
/// the root written only AFTER the loop. The chain licence refuses the two-write `s`
/// and the payload carries no fact. The pristine driver and rounds A5–A7 REFUTED it on
/// both levels: the callee-return havoc lane reclassified `IndexOutOfBounds` only, and
/// this is a `SliceBoundsCheck` row over a free `s__slice_len` its single-variable
/// probe could not decide. Round A8 admits `SliceBoundsCheck` and treats a free
/// `__slice_len` symbol as a second havoc for the probe: the row is now Unknown
/// (`UnmodeledCalleeReturn`), never a refutation and never a proof.
#[test]
fn a7_a_root_reseated_after_the_loop_is_never_a_certified_refutation() {
    for name in ["a7_len_reseat_after_loop_o1", "a7_len_reseat_after_loop_o0"] {
        let rows = rows_of(name, |k| is_bounds(k) || matches!(k, VcKind::UnsupportedMir { .. }));
        assert!(
            rows.iter().all(|(_, r, _)| !matches!(r, VerificationResult::Failed { .. })),
            "{name}: a correct program is REFUTED; got {rows:?}"
        );
        assert!(rows.iter().all(|(_, r, _)| !is_proved(r)), "{name}: nothing to prove here");
    }
}

// ── ROUND A6: THE CALL-THROUGH-TEMP ENTRANCE ─────────────────────────────────────────

/// `let mut it = 0..5usize; let mut o = it.next(); while let Some(i) = o { t += a[i]; o =
/// it.next(); }` on `&[u8; 5]` — CORRECT (oracle: ok 15). rustc's `-O0` lowering spells
/// the second `next` as `_12 = next(move _13); _4 = move _12`, a `WholeNamed` write
/// beside `_4`'s direct call: the previous round's `value_calls` declined, no join and
/// no havoc candidate followed, and the real compiler REFUTED the bounds row ("1 failed;
/// counterexample i = 5", `-O0` strict, build failed) where the pristine driver had
/// proved it. Now: `local_defs::body_call_through_temp_index` admits the temp's call as
/// a second producing call, the join of two identical `[0, 5)` groups is minted, and
/// the row PROVES again. At `-O1` the copy is folded and the row proved on both rounds.
#[test]
fn a7_the_loop_carried_next_result_proves_through_the_temp_admission() {
    assert_all_proved("a7_ctl_two_next_loopcarried_o0", 2);
    assert_all_proved("a7_ctl_two_next_loopcarried_o1", 2);
    // Two DIFFERENT receivers, both in range (`0..5` then `2..5`; oracle: ok 13): the
    // join `(0 <= i < 5) ∨ (2 <= i < 5)` through the same spelling.
    assert_all_proved("a7_ctl_two_next_loopcarried_two_o0", 2);
    assert_all_proved("a7_ctl_two_next_loopcarried_two_o1", 2);
}

/// THE BUG under the same spelling: `o = big.next()` with `big = 50..100`. The join
/// `(0 <= i < 5) ∨ (50 <= i < 100)` leaves the row REFUTED on a witness the program
/// realises (`i >= 50`). Oracle: PANICS.
#[test]
fn a7_the_loop_carried_out_of_range_receiver_still_refutes() {
    for name in ["a7_two_next_loopcarried_bug_o0", "a7_two_next_loopcarried_bug_o1"] {
        let rows = rows_of(name, is_bounds);
        assert!(
            rows.iter().any(|(_, r, _)| is_refuted(r)),
            "{name}: the real OOB must keep its counterexample; got {rows:?}"
        );
        assert!(rows.iter().all(|(_, r, c)| !is_proved(r) && !(is_refuted(r) && *c)));
    }
}

/// What the admission must NOT let through, each a runtime PANIC (oracle): the carried
/// value is `Some(i + 50)` — a `WholeNamed` write that is no call's result
/// (`loopcarried_some_bug`); the Option local is ALIASED and laundered through `*p =
/// Some(50)` (`loopcarried_alias_bug`); the carried payload is a `mut` binding
/// reassigned to a parameter (`loopcarried_payload_param`, the payload gate). None may
/// prove.
#[test]
fn a7_the_temp_admission_refuses_every_non_carrier_spelling() {
    for name in [
        "a7_loopcarried_some_bug_o0",
        "a7_loopcarried_some_bug_o1",
        "a7_loopcarried_alias_bug_o0",
        "a7_loopcarried_alias_bug_o1",
        "a7_loopcarried_payload_param_o0",
        "a7_loopcarried_payload_param_o1",
    ] {
        assert_not_proved(name, is_bounds);
    }
}

// ── ROUND A8: THE `__slice_len` NAME LICENCE, SHARED — the second adversarial review ──
//
// Three findings, all reproduced through the real compiler on the reviewer's probes
// (`scratchpad/r{1,2,3}`), every fixture below a `-Ztrust-dump=mir-only` capture from
// the stage1 driver at BOTH `-Copt-level=0` (`_o0`) and `-Copt-level=1` (`_o1`); the
// runtime oracle (`-Ztrust-verify=off` bin) for every row is in its doc.
//
//  1. FALSE PROVE, kernel-certified, pre-existing on the sealed driver: the `Ord::min`
//     lane (`callee_summaries::param_slice_len` → `value_facts::build_min_max_facts`)
//     licensed its root by `is_parameter` alone and inlined `{s}__slice_len` into a
//     GLOBAL fact; a `mut s` parameter reseated in the body passed it. The licence is
//     now ONE question for every producer (`generate::slice_len_licence`), and the
//     per-call lane states the bound VERSIONED at the call instead.
//  2. FALSE REFUTATION introduced by round A7: the licence refused every `&mut [T]`
//     root (the element store as a projected write, the `&raw const (*s)` reborrow as
//     an `Escape`). The licence now asks the PATH question
//     (`local_defs::path_is_single_static_assignment`): writes strictly inside the
//     metadata owner are ignored.
//  3. FALSE REFUTATION introduced by round A5: a payload that fails the gate could not
//     be declined by the havoc lane (which required the gate). The candidate is now the
//     field regardless of the alias's gate, `SliceBoundsCheck` is admitted, and a free
//     `__slice_len` symbol is a second havoc for the probe.

/// The `SliceBoundsCheck` rows only (the `Ord::min` lane's obligations are these).
fn is_slice_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::SliceBoundsCheck)
}

/// The program is REFUSED on this obligation kind: at least one such row is NOT
/// proved, no row is a certified refutation. Used where a sibling row of the same
/// kind legitimately proves beside the violated one (the read guarded by the very
/// assert that fails, the `n - 1` overflow under `n != 0`).
fn assert_refused(name: &str, want: fn(&VcKind) -> bool) {
    let rows: Vec<Row> = verdicts(name)
        .into_iter()
        .filter(|(k, _, _)| want(k) || matches!(k, VcKind::UnsupportedMir { .. }))
        .collect();
    assert!(!rows.is_empty(), "{name}: the obligation this row is about must be generated");
    assert!(
        rows.iter().any(|(_, r, _)| !is_proved(r)),
        "{name}: EVERY row proves — the program is accepted; got {rows:?}"
    );
    for (_, r, c) in &rows {
        assert!(!(is_refuted(r) && *c), "{name}: a refuted row may not also be kernel-certified");
    }
}

/// No selected row is `Failed`: the honest verdict for a correct program the lane
/// cannot prove is Unknown, never a witness no execution realises.
fn assert_never_refuted(name: &str, want: fn(&VcKind) -> bool) {
    let rows: Vec<Row> = verdicts(name)
        .into_iter()
        .filter(|(k, _, _)| want(k) || matches!(k, VcKind::UnsupportedMir { .. }))
        .collect();
    assert!(!rows.is_empty(), "{name}: the obligation this row is about must be generated");
    assert!(
        rows.iter().all(|(_, r, _)| !matches!(r, VerificationResult::Failed { .. })),
        "{name}: a correct program is REFUTED; got {rows:?}"
    );
}

/// THE REVIEWER'S COUNTEREXAMPLE. `fn f(mut s: &[u8], b: &[u8]) -> u8 { let n =
/// s.len().min(100); s = b; s[..n].len() as u8 }` — `f(&[1,2,3,4,5], &[1])` PANICS
/// "range end index 5 out of range for slice of length 1". Sealed driver AND stage1,
/// `-O0` and `-O1`: `SliceBoundsCheck proved, assurance=Certified,
/// validation=KernelRechecked` — the global fact `n <= s__slice_len` renamed onto the
/// post-reseat version made the `RangeTo` violation UNSAT. Now: refuted (uncertified)
/// at both levels. `min_reseat_local_bug` is the `let mut s = a` spelling that `-O1`
/// copy-propagates onto the parameter (pristine: PROVED certified at `-O1`);
/// `max_reseat_slice_bug` the `max(0)` twin.
#[test]
fn a8_the_min_lane_no_longer_proves_a_reseated_root() {
    for name in [
        "a8_min_reseat_slice_bug_o0",
        "a8_min_reseat_slice_bug_o1",
        "a8_min_reseat_local_bug_o0",
        "a8_min_reseat_local_bug_o1",
        "a8_max_reseat_slice_bug_o0",
        "a8_max_reseat_slice_bug_o1",
    ] {
        assert_not_proved(name, is_slice_bounds);
    }
}

/// `let n = s.len().min(100); s = b; if n == 0 { return 0 } s[n - 1]` — PANICS
/// (oracle). Pristine `-O0`: all three rows PROVED, two kernel-certified (the whole
/// program accepted). Now the bounds ASSERT row is refuted; the two rows that still
/// prove are legitimate — the read `(*s)[n-1]` is guarded by that very assert, and
/// `n - 1` cannot overflow under `n != 0`.
#[test]
fn a8_the_min_lane_index_twin_is_refused() {
    assert_refused("a8_min_reseat_index_bug_o0", is_slice_bounds);
    assert_refused("a8_min_reseat_index_bug_o1", is_slice_bounds);
}

/// THE LOOP FORM, squarely inside the yield lane: `let n = s.len().min(100); for i in
/// 0..n { s = b; t += s[i] }` (`min_loop_bug`; `min_loop_range_bug` indexes `s[i..n]`).
/// The yield lane minted `i < _5` on the bare `min` destination and the min lane
/// minted `_5 <= s__slice_len` — a NAME — and the composition proved the assert-derived
/// row kernel-certified at both levels on the sealed driver, stage1 and round A7.
/// PANICS (oracle). Now: not proved at either level.
#[test]
fn a8_the_min_lane_loop_form_is_not_proved() {
    for name in [
        "a8_min_loop_bug_o0",
        "a8_min_loop_bug_o1",
        "a8_min_loop_range_bug_o0",
        "a8_min_loop_range_bug_o1",
    ] {
        assert_not_proved(name, is_bounds);
    }
}

/// THE MIN-LANE CONTROLS — MUST PROVE. `ctl_min_slice` (`s[..n]`), `ctl_min_index`
/// (`s[n-1]` under `n != 0`), `ctl_min_loop` (`for i in 0..n { s[i] }`) on a
/// never-written `s`, and `ctl_min_after_reseat` (`s = b; let n = s.len().min(100);
/// s[..n]`) — the reseat BEFORE the `min`, which the pristine driver proved only through
/// the unlicensed global fact's lucky rename and which now proves through the
/// call-point twin `n <= s__slice_len#<at the call>` (`callee_summaries::
/// call_point_slice_len_of_arg`) plus, at `-O0`, the argument temp's copy tie
/// (`guards::push_copy_slice_len`, conjoined for the range-index obligation by
/// `block_defs::v2_formula_with_slice_len_ties`). Oracle: ok for all four.
///
/// At `-O0` every `SliceBoundsCheck` row proves. At `-O1` `ctl_min_index` carries one
/// row the in-process solver answers Unknown on and `ctl_min_loop` one row the
/// loop-join weakening refutes — both pre-existing on the pristine driver (`Slice:F`
/// there) and untouched here; the min-lane row proves and nothing is a certified
/// refutation.
#[test]
fn a8_the_min_lane_controls_still_prove() {
    for name in [
        "a8_ctl_min_slice_o0",
        "a8_ctl_min_index_o0",
        "a8_ctl_min_loop_o0",
        "a8_ctl_min_after_reseat_o0",
        "a8_ctl_min_slice_o1",
        "a8_ctl_min_after_reseat_o1",
    ] {
        let rows = rows_of(name, is_slice_bounds);
        for (kind, verdict, _) in &rows {
            assert!(is_proved(verdict), "{name}: {kind:?} must prove; got {verdict:?}");
        }
    }
    for name in ["a8_ctl_min_index_o1", "a8_ctl_min_loop_o1"] {
        let rows = rows_of(name, is_slice_bounds);
        assert!(
            rows.iter().any(|(_, r, _)| is_proved(r)),
            "{name}: the min-bounded row must prove; got {rows:?}"
        );
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: never a certified refutation"
        );
    }
}

/// THE `&mut [T]` IDIOM — MUST PROVE at both levels. `for i in 0..s.len() { s[i] = 0 }`
/// and its spellings (`let n = s.len()`, UFCS `len`, `.rev()`, `.step_by(2)`, `+= 1`,
/// `if s[i] == 0 { s[i] = 1 }`, a read-then-store, `v.as_mut_slice()`, `as_mut_ptr`
/// beside it, a `&mut [u8]` from a `Vec`, a `&mut` reborrow, a 2-D `g[i][0] = 1`, two
/// slices, a plain read). Round A7 refused every one at `-O1` (fifteen functions,
/// nineteen rows, PROVED on the pristine driver → refuted). At `-O0` the pristine
/// driver refuted them all (the fact was keyed on the shared-reborrow temp `_5 = &(*s)`
/// while the check reads the root through `&raw const (*s)`), so `-O0` is a recovery
/// beyond the baseline: the yield fact is now stated on EVERY licensed name of the end
/// (`resolve_range_bound_alias_formulas`). Oracle: ok for every row.
///
/// Pinned at `-O0`: EVERY bounds row proves (the bounds check is spelled as
/// `IndexOutOfBounds` there and is the only row). At `-O1` the `IndexOutOfBounds` twin
/// on `(*s)[i]` was ALREADY refuted on the pristine driver (its guard definition is
/// dropped by the loop-join weakening — pre-existing, not this round's), so the pin
/// is the `SliceBoundsCheck` row the licence is about: it proves, and no row is a
/// certified refutation. The same weaker form covers the `-O0` rows that carry a
/// second `len` read of the same slice the encoder does not tie (`2d`, `windows`).
#[test]
fn a8_the_mutable_slice_idiom_proves_at_both_levels() {
    for name in [
        "a8_ctl_mut_store_o0",
        "a8_ctl_mut_let_n_o0",
        "a8_ctl_mut_ufcs_o0",
        "a8_ctl_mut_rev_o0",
        "a8_ctl_mut_stepby_o0",
        "a8_ctl_mut_slice_of_vec_o0",
        "a8_ctl_mut_addassign_o0",
        "a8_ctl_mut_str_bytes_o0",
        "a8_ctl_mut_enum_read_then_store_o0",
        "a8_ctl_mut_reborrow_store_o0",
        "a8_ctl_mut_two_slices_o0",
        "a8_ctl_mut_as_mut_ptr_o0",
        "a8_ctl_mut_local_from_vec_o0",
        "a8_ctl_mut_read_o0",
        "a8_ctl_mut_windows_o1",
    ] {
        let rows = rows_of(name, is_bounds);
        for (kind, verdict, _) in &rows {
            assert!(is_proved(verdict), "{name}: {kind:?} must prove; got {verdict:?}");
        }
    }
    for name in [
        "a8_ctl_mut_store_o1",
        "a8_ctl_mut_let_n_o1",
        "a8_ctl_mut_ufcs_o1",
        "a8_ctl_mut_rev_o1",
        "a8_ctl_mut_stepby_o1",
        "a8_ctl_mut_slice_of_vec_o1",
        "a8_ctl_mut_addassign_o1",
        "a8_ctl_mut_str_bytes_o1",
        "a8_ctl_mut_enum_read_then_store_o1",
        "a8_ctl_mut_reborrow_store_o1",
        "a8_ctl_mut_two_slices_o1",
        "a8_ctl_mut_as_mut_ptr_o1",
        "a8_ctl_mut_local_from_vec_o1",
        "a8_ctl_mut_read_o1",
        "a8_ctl_mut_2d_o0",
        "a8_ctl_mut_2d_o1",
        "a8_ctl_mut_windows_o0",
    ] {
        let rows = rows_of(name, is_slice_bounds);
        assert!(
            rows.iter().any(|(_, r, _)| is_proved(r)),
            "{name}: the licensed row must prove; got {rows:?}"
        );
        let all = rows_of(name, is_bounds);
        assert!(
            all.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: never a certified refutation"
        );
    }
}

/// `for i in 0..h.s.len() { h.s[i] = 0 }` on `h: &mut H` — the slice in a struct
/// FIELD, refuted on the pristine driver at both levels and unchanged here (the
/// encoder ties the field's length to nothing); recorded as the residual it is,
/// pinned in the direction that must hold. `ctl_mut_local` at `-O1` has its range
/// constant-folded to an opaque constant and is Unknown, never a refutation.
#[test]
fn a8_the_mutable_slice_residuals_are_never_certified_refutations() {
    for name in ["a8_ctl_mut_field_o0", "a8_ctl_mut_field_o1", "a8_ctl_mut_local_o1"] {
        let rows = rows_of(name, |k| is_bounds(k) || matches!(k, VcKind::UnsupportedMir { .. }));
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: never a certified refutation"
        );
    }
    // `Unreachable` + `IndexOutOfBounds`, all proved. The `SliceBoundsCheck`
    // that used to ride along was the rvalue-side twin of the `BoundsCheck`
    // assert covering the same read; see the note in
    // `a8_the_bare_bound_arm_is_measured_against_a_sibling_lane`. The soundness
    // assertion this test is named for — never a certified refutation — is
    // above and is unaffected by the count.
    assert_all_proved("a8_ctl_mut_local_o0", 2);
}

/// `let mut s: &[u8] = a; for i in 0..s.len() { s = b; t += s[i] }` with BOTH arrays
/// `&[u8; 5]` (`ctl_unsize`) — a real reseat, so no yield fact, and the CORRECT
/// program's rows must be Unknown, never a witness; and `for mut i in 0..5usize { i +=
/// 1; t += a[i] }` on `[u8; 6]` (`ctl_incr_six`), whose payload has two writes: the
/// pristine driver proved it at `-O0` by binding the fact to the post-increment
/// version, round A5 refused the fact and REFUTED it on an unrealisable witness. Now
/// both rows decline at `-O0` (the checked-add result is a derived candidate of the
/// field; the copy chain is transitively dead). At `-O1` rustc increments the payload
/// in place under the modular-wrap encoding, which the probe does not see through:
/// the pristine driver refuted all three rows there, one now declines, and the pin is
/// the direction that must hold.
#[test]
fn a8_a_gate_miss_declines_instead_of_refuting() {
    assert_never_refuted("a8_ctl_unsize_o0", is_bounds);
    assert_never_refuted("a8_ctl_unsize_o1", is_bounds);
    assert_never_refuted("a8_ctl_incr_six_o0", |k| is_bounds(k) || is_add_overflow(k));
    let rows = rows_of("a8_ctl_incr_six_o1", |k| {
        is_bounds(k) || is_add_overflow(k) || matches!(k, VcKind::UnsupportedMir { .. })
    });
    assert!(
        rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
        "a8_ctl_incr_six_o1: a refuted row may not also be kernel-certified; got {rows:?}"
    );
    assert!(
        rows.iter().any(|(k, _, _)| matches!(k, VcKind::UnsupportedMir { .. })),
        "a8_ctl_incr_six_o1: the `Add` overflow row must decline; got {rows:?}"
    );
    // The panicking twin on `[u8; 5]` (`incr_bug`) is never proved.
    assert_not_proved("a8_incr_bug_o0", |k| is_bounds(k) || is_add_overflow(k));
    assert_not_proved("a8_incr_bug_o1", |k| is_bounds(k) || is_add_overflow(k));
}

/// The rows the yield lane's bare-bound arm shares with the min lane and the copy tie:
/// `min_end_bug` (`for i in 0..s.len().min(100) { s = b; s[i] }`, PANICS; pristine
/// `-O1` PROVED certified), `call_chain_bug` (`let h = s.split_at(s.len()).0; for i in
/// 0..h.len() { s = b; s[i] }`, PANICS — the `split_at(s, s.len())` row is a TRUE
/// proof the copy tie enables, the loop rows stay refuted), `mut_reseat_bug` /
/// `mut_reseat_local_bug` (`&mut` roots reseated inside the loop, PANIC), and the
/// control `ctl_call_chain` (MUST PROVE, all three rows, both levels; refuted on the
/// pristine driver before the copy tie).
#[test]
fn a8_the_bare_bound_arm_is_measured_against_a_sibling_lane() {
    assert_not_proved("a8_min_end_bug_o0", is_bounds);
    assert_not_proved("a8_min_end_bug_o1", is_bounds);
    assert_refused("a8_call_chain_bug_o0", is_bounds);
    assert_refused("a8_call_chain_bug_o1", is_bounds);
    for name in [
        "a8_mut_reseat_bug_o0",
        "a8_mut_reseat_bug_o1",
        "a8_mut_reseat_local_bug_o0",
        "a8_mut_reseat_local_bug_o1",
    ] {
        assert_not_proved(name, is_bounds);
    }
    // `Unreachable` + the `SliceBoundsCheck` rows, all proved.
    //
    // Trust (2026-09-20): o0 lost ONE row and o1 kept all of its. Neither is
    // drift. `v2_assert_len_binding_holds` now asks whether the indexed slice's
    // fat pointer can be rebound BETWEEN the length read and the access rather
    // than anywhere in the function, so where rustc's own `BoundsCheck` assert
    // exactly covers the read, the rvalue-side twin of that assert is suppressed
    // — the double-emission the lane's own comment says it is there to avoid.
    // Checked per fixture, not inferred: each has an assert block with no index
    // statement whose TARGET block carries the index at stmt 0, so the dropped
    // row is the guarded read and the retained one is the assert. The o0/o1
    // split is the suppression's shape sensitivity failing closed: at `-O1` the
    // exact binding declines and the row stays.
    assert_all_proved("a8_ctl_call_chain_o0", 3);
    assert_all_proved("a8_ctl_call_chain_o1", 4);
}

/// A temp copied into TWO Option locals (`let r = it.next(); q = r; o = r;` — `_6 = copy
/// _13; _4 = copy _13`): the temp is still a pure carrier, so `o`'s row proves through
/// the admission. CORRECT (oracle: ok 15); pinned in the direction that matters — never
/// a certified refutation — and the `o` row (the first bounds row) must prove.
#[test]
fn a7_a_temp_copied_into_two_option_locals_is_still_admitted() {
    for name in ["a7_two_next_temp_shared_o0", "a7_two_next_temp_shared_o1"] {
        let rows = rows_of(name, is_bounds);
        assert!(
            rows.iter().all(|(_, r, c)| !(matches!(r, VerificationResult::Failed { .. }) && *c)),
            "{name}: a refuted row may not also be kernel-certified; got {rows:?}"
        );
        assert!(
            rows.iter().any(|(_, r, _)| is_proved(r)),
            "{name}: the `o` row must prove through the temp admission; got {rows:?}"
        );
    }
}

// ── ROUND A9: THE INDEX LOCAL INSIDE A PROJECTION ─────────────────────────────
//
// The block encoder spells `(*s)[j]` as `s*[_<j>]` — the index local embedded BY
// NUMBER — and the version rename rebound `j` on every write but never the segment,
// so two reads of `s[j]` across `j = k` were ONE name. Every fact, tie and licence
// keyed on such a name was a claim about both reads. Fixtures: `-Ztrust-dump`
// captures from the stage1 driver of `r5b_pins.rs` / `r5c_pins.rs` / `r5_pins.rs`
// at `-Copt-level=0` and `-Copt-level=1`; every `_bug` row PANICS under the runtime
// oracle (`-Ztrust-verify=off`), every `ctl_` row returns.

fn is_index_oob(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds)
}

/// At least `n` of the selected rows (declined `UnsupportedMir` rows included) are
/// NOT proved, and no refuted row is kernel-certified. For a program whose bug row
/// sits beside legitimately-proved rows (the read guarded by the very assert that
/// refutes), the count is what says the bug row did not join them.
fn assert_at_least_n_not_proved(name: &str, want: fn(&VcKind) -> bool, n: usize) {
    let rows: Vec<Row> = verdicts(name)
        .into_iter()
        .filter(|(k, _, _)| want(k) || matches!(k, VcKind::UnsupportedMir { .. }))
        .collect();
    let not_proved = rows.iter().filter(|(_, r, _)| !is_proved(r)).count();
    assert!(
        not_proved >= n,
        "{name}: expected at least {n} rows not proved, got {not_proved}; rows {rows:?}"
    );
    for (_, r, c) in &rows {
        assert!(!(is_refuted(r) && *c), "{name}: a refuted row may not also be kernel-certified");
    }
}

/// THE REVIEWER'S FIRST COUNTEREXAMPLE (the copy tie). `let mut j = 0; let n =
/// s[j].len().min(100); j = k; s[j][..n].len() as u8` on `s: &[&[u8]]` —
/// `f(&[&[1,2,3,4,5], &[9]], 1)` PANICS. Round A8's `push_copy_slice_len` tied
/// `_12__slice_len` (taken at `j = 0`) and `_13__slice_len` (at `j = k`) to the ONE
/// name `s*[_3]__slice_len`, `v2_formula_with_slice_len_ties` conjoined both, and the
/// `RangeTo` row PROVED kernel-certified at `-O1`. `index_local_min_let_bug` copies
/// the fat pointers into `let t: &[u8] = s[j]` / `let u = s[j]` first. Now: at `-O1`
/// the two guarded reads still prove (each under its own assert) and the two asserts
/// plus the `RangeTo` row refute — three rows not proved; at `-O0` all three rows
/// refute.
#[test]
fn a9_the_copy_tie_no_longer_equates_two_slots_of_a_reseated_index() {
    for name in [
        "r5b_index_local_min_bug_o0",
        "r5b_index_local_min_bug_o1",
        "r5c_index_local_min_let_bug_o0",
        "r5c_index_local_min_let_bug_o1",
    ] {
        assert_at_least_n_not_proved(name, is_slice_bounds, 3);
    }
}

/// THE REVIEWER'S SECOND COUNTEREXAMPLE (the projected range end, pre-existing on the
/// pristine driver). `let mut j = 0; if a[j] > 5 { return 0 } j = k; for i in 0..a[j]
/// { t += b[i] }` with `b: &[u8; 5]` — `f(&[3, 100], &b, 1)` PANICS. The yield
/// lane's projected-operand arm admitted `a*[_4]` as the range end with `j` reseated
/// between the guard and the loop, and the `b[i]` row PROVED kernel-certified at `-O1`
/// on the pristine driver, on stage1 and on round A8. Twins: the `mut j` parameter
/// spelling, the struct-field `h.v[j]`, and the length form `s[j].len()` of `r5c`.
/// Now the `b[i]` row is never proved (it declines: the payload's bound is withheld).
#[test]
fn a9_a_projected_range_end_over_a_reseated_index_never_proves_the_payload() {
    for name in [
        "r5b_index_elem_end_bug_o0",
        "r5b_index_elem_end_bug_o1",
        "r5b_index_elem_end_param_bug_o0",
        "r5b_index_elem_end_param_bug_o1",
        "r5b_field_index_end_bug_o0",
        "r5b_field_index_end_bug_o1",
        "r5c_index_local_len_end_bug_o0",
        "r5c_index_local_len_end_bug_o1",
    ] {
        assert_not_proved(name, is_index_oob);
    }
    // `a: &[usize; 2]` — every bounds row is `IndexOutOfBounds`, and the reads guarded
    // by their own asserts legitimately prove; the `a[k]` assert refutes and the `b[i]`
    // row must not join the proved ones: two rows not proved at both levels.
    assert_at_least_n_not_proved("r5b_index_elem_end_arr_bug_o0", is_index_oob, 2);
    assert_at_least_n_not_proved("r5b_index_elem_end_arr_bug_o1", is_index_oob, 2);
}

/// The other name-keyed lanes over the same slot: the modulo divisor `b[n % a[j]]`
/// (`index_modulo_bug`, `RemainderByZero` PROVED at `-O1` on the pristine driver),
/// the `windows(a[j])` size (`index_windows_bug`, `DivisionByZero` proved) and the
/// enumerate index over `s[j]` (`index_local_enum_bug`). Never proved now.
#[test]
fn a9_the_divisor_and_window_size_lanes_refuse_a_reseated_index() {
    for name in ["r5b_index_modulo_bug_o0", "r5b_index_modulo_bug_o1"] {
        assert_not_proved(name, |k| matches!(k, VcKind::RemainderByZero));
    }
    for name in ["r5b_index_windows_bug_o0", "r5b_index_windows_bug_o1"] {
        assert_not_proved(name, |k| matches!(k, VcKind::DivisionByZero));
    }
    for name in [
        "r5b_index_local_enum_bug_o0",
        "r5b_index_local_enum_bug_o1",
        "r5b_index_local_len_bug_o0",
        "r5b_index_local_len_bug_o1",
        "r5b_index_local_len_pre_bug_o0",
        "r5b_index_local_len_pre_bug_o1",
    ] {
        assert_at_least_n_not_proved(name, is_slice_bounds, 3);
    }
}

/// THE SSA-INDEX CONTROLS — MUST PROVE. `j` is a never-written parameter, guarded by
/// `j >= s.len()` / `j >= a.len()` (`ctl_index_local_len_end`,
/// `ctl_index_elem_end_guarded`: every bounds row proves at both levels), or
/// unguarded (`ctl_index_elem_end_ssa`: the `b[i]` row proves; the `a[j]` assert on an
/// unconstrained parameter is a real refutation on the pristine driver too). Oracle:
/// ok for all.
#[test]
fn a9_the_ssa_index_controls_still_prove() {
    for name in [
        "r5c_ctl_index_local_len_end_o0",
        "r5c_ctl_index_local_len_end_o1",
        "r5c_ctl_index_elem_end_guarded_o0",
        "r5c_ctl_index_elem_end_guarded_o1",
    ] {
        let rows = rows_of(name, is_bounds);
        for (kind, verdict, _) in &rows {
            assert!(is_proved(verdict), "{name}: {kind:?} must prove; got {verdict:?}");
        }
    }
    for name in ["r5b_ctl_index_elem_end_ssa_o0", "r5b_ctl_index_elem_end_ssa_o1"] {
        let rows = rows_of(name, is_index_oob);
        for (kind, verdict, _) in &rows {
            assert!(is_proved(verdict), "{name}: {kind:?} must prove; got {verdict:?}");
        }
    }
    for name in ["r5b_ctl_index_local_len_ssa_o0", "r5b_ctl_index_local_len_ssa_o1"] {
        let rows = rows_of(name, is_slice_bounds);
        assert!(
            rows.iter().any(|(_, r, _)| is_proved(r)),
            "{name}: a licensed row must prove; got {rows:?}"
        );
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: never a certified refutation"
        );
    }
    // The non-SSA controls (`j` reseated BEFORE every read — correct) keep whatever
    // they had and are never certified refutations; `ctl_index_elem_end` at `-O1`
    // trades its `b[i]` proof for a decline (the index local has two writes, so the
    // global fact is withheld — recorded, not hidden).
    for name in [
        "r5b_ctl_index_elem_end_o0",
        "r5b_ctl_index_elem_end_o1",
        "r5b_ctl_index_local_len_o0",
        "r5b_ctl_index_local_len_o1",
        "r5c_index_local_len_guard_bug_o0",
        "r5c_index_local_len_guard_bug_o1",
    ] {
        let rows = rows_of(name, |k| is_bounds(k) || matches!(k, VcKind::UnsupportedMir { .. }));
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: never a certified refutation"
        );
    }
    assert_never_refuted("r5b_ctl_index_elem_end_o1", is_index_oob);
}

/// `for mut i in 0..5usize { i = i + 1; t += a[i] }` on `[u8; 6]` (`ctl_plus_one_six`,
/// CORRECT, oracle ok 20). rustc spells `i = i + 1` at `-O0` through a whole-local
/// copy (`_10 = copy i; _11 = AddWithOverflow(move _10, 1)`), the havoc carry stopped
/// at the copy, and the row was REFUTED on the free `_10` while the `i += 1` twin
/// (`a8_ctl_incr_six_o0`) declined — a decision made by spelling. Now both decline;
/// the panicking twin on `[u8; 5]` (`plus_one_bug`) is never proved. At `-O1` the
/// payload is incremented in place under the modular-wrap encoding (the pristine
/// driver refuted all three rows; pre-existing), pinned only as never certified.
#[test]
fn a9_the_plus_one_spelling_declines_exactly_like_the_add_assign_spelling() {
    assert_never_refuted("r5_ctl_plus_one_six_o0", |k| is_bounds(k) || is_add_overflow(k));
    assert_not_proved("r5_plus_one_bug_o0", |k| is_bounds(k) || is_add_overflow(k));
    assert_not_proved("r5_plus_one_bug_o1", |k| is_bounds(k) || is_add_overflow(k));
    let rows = rows_of("r5_ctl_plus_one_six_o1", |k| {
        is_bounds(k) || is_add_overflow(k) || matches!(k, VcKind::UnsupportedMir { .. })
    });
    assert!(rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)), "never a certified refutation");
}

// ── ROUND A10: THE INDEX-SEGMENT RELATION IS DIRECTIONAL ──────────────────────
//
// Round A9 put the `[_l]` index-segment relation INSIDE the symmetric
// `place_names_overlap`, whose call sites pass (written, read) in both orders. An
// ELEMENT STORE `(*a)[_11] = 1` then counted as a write of its own index local `_11`
// — exactly when that local's canonical spelling IS the fallback `_11` (a source name
// shared by two locals: `let i = i + 1` shadowing the loop's `i`, or two sibling
// `for i` loops) — and `v2_live_path_defs` killed the entry defs `_11 == _12.0`,
// `_13 == _11 < 8` at the store's block; the next read's bounds row was refuted on a
// free `_11`. The relation now lives in `write_rebinds(written, read)` and every
// "does this write affect this read" site calls it written-first. Fixtures:
// `-Ztrust-dump` captures from the stage1 driver of `rev9b_pins.rs` /
// `rev9c_pins.rs` at `-Copt-level=0` and `-Copt-level=1`; every function here is
// CORRECT for every input (runtime oracle, `-Ztrust-verify=off`: `ctl_shadow_store_loop`
// ok 35, `ctl_shadow_store_read_loop` ok 7, `ctl_named_store_loop` ok 35,
// `ctl_two_loops_shifted` ok 24 / 4 / 254 over three inputs).

type RowAt = (VcKind, VerificationResult, bool, (usize, usize));

fn verdicts_at(name: &str) -> Vec<RowAt> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let _admission = SOLVER_CASE_ADMISSION.lock().unwrap_or_else(|e| e.into_inner());
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

/// The `IndexOutOfBounds` row of the READ at `(line, col)` — the read after the
/// element store through the same (demoted) index local — is PROVED, and no refuted
/// row of the body is kernel-certified.
fn assert_read_after_store_proves(name: &str, at: (usize, usize)) {
    let rows = verdicts_at(name);
    let read: Vec<&RowAt> =
        rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == at).collect();
    assert_eq!(read.len(), 1, "{name}: exactly one bounds row at {at:?}; rows {rows:?}");
    let (_, verdict, _, _) = read[0];
    assert!(is_proved(verdict), "{name}: the read at {at:?} must PROVE; got {verdict:?}");
    for (_, r, c, _) in &rows {
        assert!(!(is_refuted(r) && *c), "{name}: a refuted row may not also be kernel-certified");
    }
}

/// At `-O1` the loop payload's read is declined (`UnmodeledCalleeReturn`) rather than
/// proved: pin that it is never REFUTED and nothing is a certified refutation.
fn assert_read_after_store_never_refuted(name: &str, at: (usize, usize)) {
    let rows = verdicts_at(name);
    for (k, r, c, loc) in &rows {
        assert!(!(is_refuted(r) && *c), "{name}: a refuted row may not also be kernel-certified");
        if *loc == at {
            assert!(!is_refuted(r), "{name}: the read at {at:?} ({k:?}) is REFUTED; got {r:?}");
        }
    }
}

/// `for i in 0..7usize { let i = i + 1; a[i] = 1; t = t.wrapping_add(b[i]); }` on
/// `[u8; 8]` — both `i` locals are named `i`, so `place_to_var_name` demotes them to
/// `_10` / `_11`; the store `(*_1)[_11] = 1` precedes the read `(*_2)[_11]`. Pristine
/// driver -O0: Arith:P Index:F Index:P (the store row's refutation is pristine's own —
/// pre-existing, reported, not this round's). With the symmetric clause the read row
/// `@L15:149` FAILED with a counterexample; now it PROVES again.
#[test]
fn a10_an_element_store_through_a_demoted_index_local_does_not_rebind_the_local() {
    assert_read_after_store_proves("rev9_ctl_shadow_store_loop_o0", (15, 149));
    assert_read_after_store_never_refuted("rev9_ctl_shadow_store_loop_o1", (15, 149));
}

/// The same loop reading back the stored element (`t += a[i]`): read `@L16:141`.
#[test]
fn a10_the_read_back_of_the_stored_element_proves_again() {
    assert_read_after_store_proves("rev9_ctl_shadow_store_read_loop_o0", (16, 141));
    assert_read_after_store_never_refuted("rev9_ctl_shadow_store_read_loop_o1", (16, 141));
}

/// Two sibling `for i` loops on `[u8; 6]` (the second `i` demotes the first): the
/// first loop's read `@L5:149` and the second loop's read `@L5:198` both prove.
#[test]
fn a10_two_sibling_loops_sharing_a_source_name_keep_both_reads() {
    assert_read_after_store_proves("rev9_ctl_two_loops_shifted_o0", (5, 149));
    assert_read_after_store_proves("rev9_ctl_two_loops_shifted_o0", (5, 198));
    assert_read_after_store_never_refuted("rev9_ctl_two_loops_shifted_o1", (5, 149));
    assert_read_after_store_never_refuted("rev9_ctl_two_loops_shifted_o1", (5, 198));
}

/// THE NAMED TWIN: `for k in 0..7usize { let i = k + 1; ... }` — `i` is unique, keeps
/// its source spelling, and its read `@L21:148` proved through every round. It stays
/// beside the shadow rows so a change that fixes the demoted spelling by breaking the
/// named one is visible.
#[test]
fn a10_the_named_twin_still_proves() {
    assert_read_after_store_proves("rev9_ctl_named_store_loop_o0", (21, 148));
    assert_read_after_store_never_refuted("rev9_ctl_named_store_loop_o1", (21, 148));
}

// ── ROUND A11: A DEFINITION MAY NOT OUTLIVE A WRITE INSIDE OR ABOVE ITS SUBJECT ──
//
// The round-A10 review (rev11): a def keyed on a PROJECTED name — the element
// store `s*[_4] == 3`, the field store `p.0 == 3` — survived a LATER write of a
// name inside or above it (`j = k` rebinding `s*[_4]` through the index segment,
// `p = q` rebinding `p.0` through the prefix) on three channels at once:
//  (a) `guards::extract_block_definitions_until_impl` exempted a def's OWN lhs
//      from the clobber test, so a def whose only free variable is its subject was
//      never dropped;
//  (b) `v2_path_def_fixpoint` threaded a block's own defs as ONE batch, killing
//      incoming facts only, so the stale def outflowed to the successor;
//  (c) `conjoin_preconditions_versioned_recorded` renamed it at the use point onto
//      the successor-entry UNION token (`s*[_4]#s1_0_s1_1`) — the token the
//      post-reseat read carries too — and `_7 == 3 < 4` PROVED kernel-certified;
//  (d) `block_def_establish_stmt`, searching from the block END for the latest
//      ancestor write, pinned the field def at the later reseat `p = q` itself.
// Every `_bug` row below PANICS under the runtime oracle (`-Ztrust-verify=off`:
// `store_reseat_read_bug(&mut [0, 9], &[1, 2, 3, 4], 1)` indexes `t[9]`); every
// `_ctl` row returns (`ok 4`). Fixtures: `-Ztrust-dump` captures from the stage1
// driver of `rev11c_pins.rs` / `rev11d_pins.rs` / `rev11e_pins.rs` at
// `-Copt-level=0` and `-Copt-level=1`.

/// Every bounds row at `(line, col)` — the READ after the store-then-reseat — is
/// NOT proved, and no refuted row of the body is kernel-certified. The store's own
/// bounds row (a real refutation: `k` is unconstrained) sits beside it and is not
/// what this asserts.
fn assert_read_after_reseat_not_proved(name: &str, at: (usize, usize)) {
    let rows = verdicts_at(name);
    let read: Vec<&RowAt> =
        rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == at).collect();
    assert!(!read.is_empty(), "{name}: the read row at {at:?} must be generated; rows {rows:?}");
    for (kind, verdict, certified, _) in &read {
        assert!(
            !is_proved(verdict),
            "{name}: the read at {at:?} ({kind:?}) is PROVED again on a panicking program; got {verdict:?}"
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

/// THE REVIEWER'S COUNTEREXAMPLE. `let mut j = 0usize; s[j] = 3; j = k; t[s[j] as
/// usize]` on `s: &mut [u8]`, `t: &[u8; 4]` — bb1 `(*_1)[_4] = 3; _4 = copy _3`, bb2
/// `_8 = copy (*_1)[_4]; Assert(_7 < 4)`. Stage1 (A5-era) -O1: the read row
/// `@L11:111` PROVED kernel-certified; the pristine driver read Unknown. Twins: the
/// local array `a[_5]` (no `&mut` anywhere), and the guarded `iv_*` shapes of
/// `rev11c` (a mutable slice parameter, a local array, and a reseat through
/// `let p = &mut j; *p = k` that `-O1` folds to a whole write).
#[test]
fn a11_a_store_def_does_not_outlive_the_reseat_of_its_index_local() {
    for (name, at) in [
        ("rev11d_store_reseat_read_bug_o0", (11, 111)),
        ("rev11d_store_reseat_read_bug_o1", (11, 111)),
        ("rev11d_arr_store_reseat_read_bug_o0", (14, 160)),
        ("rev11d_arr_store_reseat_read_bug_o1", (14, 160)),
        ("rev11c_iv_store_reseat_bug_o0", (8, 168)),
        ("rev11c_iv_store_reseat_bug_o1", (8, 168)),
        ("rev11c_iv_arr_store_reseat_bug_o0", (11, 162)),
        ("rev11c_iv_arr_store_reseat_bug_o1", (11, 162)),
        ("rev11c_iv_ptr_store_reseat_bug_o0", (16, 189)),
        ("rev11c_iv_ptr_store_reseat_bug_o1", (16, 189)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
}

/// THE PREFIX CHANNEL, at `-O0` in ONE block. `let mut p = (0u8, 0u8); p.0 = 3; p =
/// q; t[p.0 as usize]` — `block_def_establish_stmt` took the later `p = q` as the
/// field def's establish point and stamped `p.0#s0_2 == 3` onto the post-reseat
/// version the read `_5 = copy (p.0)` carries: PROVED kernel-certified on stage1 AND
/// on the pristine driver (`@L3:104`). `a[0] = 3; a = q; t[a[0] as usize]` is the
/// same shape through a constant index (`@L5:108`, PROVED at `-O1` on both). Now the
/// def is pinned at ITS OWN statement (`p.0#s0_1`), name-disjoint from the read.
#[test]
fn a11_a_field_def_is_pinned_at_its_own_store_not_at_a_later_reseat() {
    for (name, at) in [
        ("rev11e_field_store_reseat_bug_o0", (3, 104)),
        ("rev11e_field_store_reseat_bug_o1", (3, 104)),
        ("rev11e_arr_const_store_reseat_bug_o0", (5, 108)),
        ("rev11e_arr_const_store_reseat_bug_o1", (5, 108)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
}

/// THE CONTROLS. `p = q; p.0 = 3; t[p.0 as usize]` (`field_store_reseat_ctl`, ok 4)
/// MUST PROVE at both levels: the def pinned at its own store IS the value the read
/// carries. `j = k; s[j] = 3; t[s[j] as usize]` (`store_reseat_read_ctl`,
/// `iv_store_reseat_ctl`, both ok 4): rustc spells the store's index and the read's
/// index through DIFFERENT copies of `j` (`(*_1)[_5] = 3` … `_9 = copy (*_1)[_4]`),
/// so the encoder's index-by-number names `s*[_5]` / `s*[_4]` never meet — the read
/// row REFUTED on the pristine driver (`-O1`), on stage1 and on every round since; a
/// pre-existing false refutation of the `&mut [u8]` element-store-then-read idiom,
/// recorded, not this round's. Pinned in the direction that matters: never a
/// certified refutation, and the rows this round did not touch keep their proofs.
#[test]
fn a11_the_store_reseat_controls_keep_their_proofs() {
    assert_all_proved("rev11e_field_store_reseat_ctl_o0", 1);
    assert_all_proved("rev11e_field_store_reseat_ctl_o1", 1);
    for name in [
        "rev11d_store_reseat_read_ctl_o0",
        "rev11d_store_reseat_read_ctl_o1",
        "rev11c_iv_store_reseat_ctl_o0",
        "rev11c_iv_store_reseat_ctl_o1",
        "rev11c_iv_arr_store_reseat_ctl_o0",
        "rev11c_iv_arr_store_reseat_ctl_o1",
    ] {
        let rows = rows_of(name, is_bounds);
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: a refuted row may not also be kernel-certified; got {rows:?}"
        );
    }
    // The local-array control (`j = k; if j >= 4 { return 0 } a[j] = 3; t[a[j]]`):
    // the read `@L12:164` proves through the same index local at both levels (`-O1`
    // carries two rows at that location; every one of them proves).
    for name in ["rev11c_iv_arr_store_reseat_ctl_o0", "rev11c_iv_arr_store_reseat_ctl_o1"] {
        let rows = verdicts_at(name);
        let read: Vec<&RowAt> =
            rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == (12, 164)).collect();
        assert!(
            !read.is_empty(),
            "{name}: the read row at (12, 164) must be generated; rows {rows:?}"
        );
        for (_, verdict, _, _) in &read {
            assert!(
                is_proved(verdict),
                "{name}: the read at (12, 164) must PROVE; got {verdict:?}"
            );
        }
    }
}

// ── ROUND A12: THE REFERENT FOLD IS AN ALIAS FACT, AND IT IS VERSION-SENSITIVE ──
//
// The round-A11 review (rev12): `lib.rs::resolve_referent` folded `*r` to the place
// `P` its unique def `r = &P` / `&raw P` borrows, and spelled every later read or
// store through `r` by `P`'s name — versioned at the USE point with whatever token
// `P`'s locals carried THERE. The alias `r* ≡ P` is a fact keyed on a projected name
// that OUTLIVED a write of a name inside or above it: `let r = &mut p.a; p = o;
// *r = 3; t[p.a as usize]` spelled the store `p*.0` at the post-reseat token, the
// read `_6 = copy (*_1).0` got the same token, `_5 == 3 < 4`, and the row PROVED
// kernel-certified while the store hit the OLD `p` (`sf_field_reseat_bug`, both
// levels; pre-existing on the sealed driver). The index-segment twin `let r = &mut
// s[j]; j = k; *r = 3; t[s[j]]` (`br_store_bug`, `-O1`) landed `Eq(s*[_4]#s3_2, 3)`
// on the read's union token the same way. `referent_fold::is_stable` now refuses the
// fold whenever a guard of the referent — the pointer at a `Deref` prefix, an `Index`
// local — is rebound on a path from the borrow to a use of `r`; `*r` then stays the
// opaque `r*`, `deref_pointer_is_opaque` is true and the store havocs instead of
// defining. Every `_bug` row PANICS under the runtime oracle
// (`rev12/rev12_oracle.out`, `rev12b_oracle.out`, `rev13_oracle.out`); every `_ctl`
// returns (`ok`). Fixtures: `-Ztrust-dump` captures from the stage1 driver of the
// reviewer's `rev12_pins.rs` / `rev12b_pins.rs` and this round's `rev13_pins.rs`
// at `-Copt-level=0` and `-Copt-level=1`.

/// THE REVIEWER'S WITNESSES. The panicking `t[..]` read of every borrow-before-
/// reseat shape is NOT proved and never kernel-certified: the reseat by statement
/// (`br_store_bug`), on a local array (`br_arr_store_bug`), through a nested index
/// (`br_nested_store_bug`), through `&raw mut` (`br_raw_store_bug`,
/// `br_raw_read_after_store_bug` — the one row NEWLY minted inside the A5..A11 set
/// relative to the sealed driver), by a call (`br_store_call_bug`), the deref
/// channel (`rp_deref_read_bug`), the prefix channel (`sf_field_reseat_bug`) and the
/// whole-slice reseat (`sf_slice_reseat_bug`). Stage1 (A5-era) and the A11 tree
/// PROVED every one of these rows kernel-certified at `-O1` (the field and deref
/// shapes at `-O0` too).
#[test]
fn a12_a_fold_through_a_reseated_referent_local_is_never_proved() {
    for (name, at) in [
        ("rev12_br_store_bug_o0", (5, 178)),
        ("rev12_br_store_bug_o1", (5, 178)),
        ("rev12_br_arr_store_bug_o0", (11, 168)),
        ("rev12_br_arr_store_bug_o1", (11, 168)),
        ("rev12_br_nested_store_bug_o0", (12, 193)),
        ("rev12_br_nested_store_bug_o1", (12, 193)),
        ("rev12_br_raw_store_bug_o0", (9, 197)),
        ("rev12_br_raw_store_bug_o1", (9, 197)),
        ("rev12_br_raw_read_after_store_bug_o0", (10, 199)),
        ("rev12_br_raw_read_after_store_bug_o1", (10, 199)),
        ("rev12_rp_deref_read_bug_o0", (18, 139)),
        ("rev12_rp_deref_read_bug_o1", (18, 139)),
        ("rev12_br_read_bug_o0", (7, 188)),
        ("rev12_br_read_bug_o1", (7, 188)),
        ("rev12b_sf_field_reseat_bug_o0", (12, 117)),
        ("rev12b_sf_field_reseat_bug_o1", (12, 117)),
        ("rev12b_sf_slice_reseat_bug_o0", (9, 168)),
        ("rev12b_sf_slice_reseat_bug_o1", (9, 168)),
        ("rev12b_br_store_call_bug_o0", (15, 205)),
        ("rev12b_br_store_call_bug_o1", (15, 205)),
        ("rev12b_br_store_blocks_bug_o0", (18, 203)),
        ("rev12b_br_store_blocks_bug_o1", (18, 203)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
}

/// THIS ROUND'S OWN PROBES of the walk's region: the reseat on ONE path of a
/// diamond (`fs_diamond_reseat_bug`), through a reborrowed slice local
/// (`fs_reborrow_chain_bug`), a shared borrow of a field of a reseated pointer
/// (`fs_shared_field_reseat_bug`) — all three PROVED kernel-certified at `-O1` on the
/// SEALED driver — plus a COPY of the reference dereferenced after the reseat
/// (`fs_copied_ref_bug`), a reseat through a raw alias of the index local created
/// BEFORE the borrow (`fs_alias_reseat_bug`), by a `&mut` callee
/// (`fs_call_reseat_after_borrow_bug`), and inside a loop on the second iteration
/// (`fs_loop_borrow_reseat_bug`).
#[test]
fn a12_the_regions_own_probes_are_never_proved() {
    for (name, at) in [
        ("rev13_fs_diamond_reseat_bug_o0", (12, 221)),
        ("rev13_fs_diamond_reseat_bug_o1", (12, 221)),
        ("rev13_fs_reborrow_chain_bug_o0", (16, 209)),
        ("rev13_fs_reborrow_chain_bug_o1", (16, 209)),
        ("rev13_fs_shared_field_reseat_bug_o0", (21, 130)),
        ("rev13_fs_shared_field_reseat_bug_o1", (21, 130)),
        ("rev13_fs_copied_ref_bug_o0", (18, 206)),
        ("rev13_fs_copied_ref_bug_o1", (18, 206)),
        ("rev13_fs_alias_reseat_bug_o0", (14, 217)),
        ("rev13_fs_alias_reseat_bug_o1", (14, 217)),
        ("rev13_fs_call_reseat_after_borrow_bug_o0", (24, 209)),
        ("rev13_fs_call_reseat_after_borrow_bug_o1", (24, 209)),
        ("rev13_fs_loop_borrow_reseat_bug_o0", (10, 265)),
        ("rev13_fs_loop_borrow_reseat_bug_o1", (10, 265)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
}

/// THE CONTROLS. The fold is REFUSED only inside the region from the borrow to a
/// use of the reference, so a reseat BEFORE the borrow keeps its fold and its
/// proof: `p = o; let r = &mut p.a; *r = 3; t[p.a]` (`sf_field_reseat_ctl`, ok 4)
/// MUST PROVE at both levels; `s = o; let r = &mut s[0]; *r = 3; t[s[0]]`
/// (`sf_slice_reseat_ctl`, ok 4) MUST PROVE its read at `-O1` (at `-O0` rustc spells
/// the borrow's slice through a different reborrow temp — the pre-existing
/// distinct-temp refutation, `F` on the sealed driver too); `j = k; let r = &s[j];
/// if s[j] >= 4 { return 0 } t[*r]` (`br_read_ctl`, ok 1) MUST PROVE at `-O1`; and
/// `p = o; let r = &p.a; if p.a >= 4 { return 0 } t[*r]` (`fs_shared_field_ctl`,
/// ok 1) MUST PROVE at both levels. The loop idiom `for i in 0..s.len() { let e =
/// &mut s[i]; *e = 1; acc += t[*e] }` (`fs_loop_elem_borrow_ctl`, ok 6): `i` is
/// rebound on the back edge only AFTER every use of the per-iteration borrow, and
/// the walk stops at the re-borrow, so the `t[*e]` read keeps its proof at both
/// levels (the sealed driver proves it too).
#[test]
fn a12_a_reseat_before_the_borrow_keeps_the_fold_and_the_proof() {
    assert_all_proved("rev12b_sf_field_reseat_ctl_o0", 1);
    assert_all_proved("rev12b_sf_field_reseat_ctl_o1", 1);
    assert_all_proved("rev13_fs_shared_field_ctl_o0", 1);
    assert_all_proved("rev13_fs_shared_field_ctl_o1", 1);
    for (name, at) in [
        ("rev12b_sf_slice_reseat_ctl_o1", (10, 168)),
        ("rev12_br_read_ctl_o1", (8, 188)),
        ("rev13_fs_loop_elem_borrow_ctl_o0", (9, 157)),
        ("rev13_fs_loop_elem_borrow_ctl_o1", (9, 157)),
    ] {
        let rows = verdicts_at(name);
        let read: Vec<&RowAt> =
            rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == at).collect();
        assert!(
            !read.is_empty(),
            "{name}: the read row at {at:?} must be generated; rows {rows:?}"
        );
        for (_, verdict, _, _) in &read {
            assert!(is_proved(verdict), "{name}: the read at {at:?} must PROVE; got {verdict:?}");
        }
        for (_, r, c, _) in &rows {
            assert!(
                !(is_refuted(r) && *c),
                "{name}: a refuted row may not also be kernel-certified"
            );
        }
    }
    // The `-O0` twins of the two index-shaped controls carry the pre-existing
    // distinct-temp refutation (recorded, not this round's); pinned in the direction
    // that matters — never a certified refutation.
    for name in [
        "rev12b_sf_slice_reseat_ctl_o0",
        "rev12_br_read_ctl_o0",
        "rev12_br_store_ctl_o0",
        "rev12_br_store_ctl_o1",
    ] {
        let rows = rows_of(name, is_bounds);
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: a refuted row may not also be kernel-certified; got {rows:?}"
        );
    }
}

/// THE REFERENCE-OF-REFERENCE CHAIN (`referent_of_source`'s `[Deref]` arm): `let x =
/// &s[j]; let m = &x; let l: &u8 = *m; j = k; .. t[*l]` — `l`'s referent is `x`'s
/// (`s*[_j]`), read out of `x`'s storage through `m`. The walk on `x` (its def to
/// `m = &x`) and on `l` (its def to `t[*l]`) leave the hop through `m` uncovered, so
/// `referent_of_source` walks `m`'s region on the same referent too; the reseat
/// between the hop and the def of `l` (`fs_ref_of_ref_mid_bug`) is the row that
/// needs it. Both PANIC (`rev13b_oracle.out`); neither is proved. The control with
/// the reseat before the chain (`fs_ref_of_ref_chain_ctl`, ok 1) proves its read at
/// `-O1` (`-O0`: the distinct-temp refutation, `F` on the sealed driver too), and the
/// closure-env upvar idiom (`if acc < 3 { acc += 1 }` through two copies of the
/// captured `&mut`) keeps its `-O0` overflow proof — the `[Deref, Field]` arm's fold
/// is walked on the env slot `(*_1).0`, which nothing in the body rebinds.
#[test]
fn a12_the_reference_of_reference_chain_is_walked_at_every_hop() {
    for (name, at) in [
        ("rev13b_fs_ref_of_ref_chain_bug_o0", (5, 229)),
        ("rev13b_fs_ref_of_ref_chain_bug_o1", (5, 229)),
        ("rev13b_fs_ref_of_ref_mid_bug_o0", (8, 227)),
        ("rev13b_fs_ref_of_ref_mid_bug_o1", (8, 227)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
    let rows = verdicts_at("rev13b_fs_ref_of_ref_chain_ctl_o1");
    let read: Vec<&RowAt> =
        rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == (6, 229)).collect();
    assert!(!read.is_empty(), "the control's read row must be generated; rows {rows:?}");
    assert!(
        read.iter().all(|(_, r, _, _)| is_proved(r)),
        "the control's read must PROVE; got {read:?}"
    );
    for name in ["rev13b_fs_ref_of_ref_chain_ctl_o0", "rev13b_fs_ref_of_ref_chain_ctl_o1"] {
        let rows = rows_of(name, is_bounds);
        assert!(
            rows.iter().all(|(_, r, c)| !(is_refuted(r) && *c)),
            "{name}: never a certified refutation"
        );
    }
    assert_all_proved("rev13b_fs_closure_upvar_ctl_closure_o0", 1);
}

/// Trust: 2026-09-17 (round A12, fixer) — EVERY CARRIER OF A SLOT'S ADDRESS. A
/// referent read OUT OF a slot (`let x = &*q; let m = &x; .. **m`, or through a copy
/// `let m2 = &x; q = o; let m = m2; let l = *m; .. *l`) is walked on `x` (its def to
/// the borrow `&x`) and on the local that finally holds it, but the pointer stored in
/// `x` is read at a use of the CARRIER (`m`, `m2`) — so `referent_of_source`'s `[Deref]`
/// arms and a multi-`Deref` place in `canonicalize_deref` now RE-RESOLVE the carrier's
/// whole chain with the read referent's guards (`reread_through`). Captures
/// (`rev14b_pins.rs`, `rev14_pins.rs`, stage1 dumps at `-O0`/`-O1`): the root reseated
/// after the borrow and read through a two-deref place (`cq_dd_bug`, `cr_dd_read_bug`),
/// through a copy carrier (`cq_copy_carrier_bug`, `cr_copy_carrier_bug`), the reseat
/// between the hop and the def of the final local (`cq_mid_bug`), a triple chain
/// (`cq_triple_bug`, `cr_triple_bug`), and the raw-pointer twins (`cq_raw_dd_bug`,
/// `cq_raw_copy_bug`). Every one PANICS under the runtime oracle
/// (`rev14*_oracle.out`), and the SEALED driver PROVES the two raw twins' read at both
/// levels (`pristine_rev14b_{0,1}.tbl`); this tree refutes every read. No row here was
/// proved on the tree before the carrier re-walk either, so these pin the direction
/// (never proved) rather than a reproduced false proof. The controls with the reseat
/// before the chain keep their proofs: `cq_raw_copy_ctl` (ok 0) and `cr_dd_read_ctl`
/// (ok 0) at both levels.
#[test]
fn a12_every_carrier_of_a_slot_address_is_walked() {
    for (name, at) in [
        ("rev14b_cq_dd_bug_o0", (3, 133)),
        ("rev14b_cq_dd_bug_o1", (3, 133)),
        ("rev14b_cq_copy_carrier_bug_o0", (5, 173)),
        ("rev14b_cq_copy_carrier_bug_o1", (5, 173)),
        ("rev14b_cq_mid_bug_o0", (6, 151)),
        ("rev14b_cq_mid_bug_o1", (6, 151)),
        ("rev14b_cq_triple_bug_o0", (7, 149)),
        ("rev14b_cq_triple_bug_o1", (7, 149)),
        ("rev14b_cq_raw_dd_bug_o0", (8, 147)),
        ("rev14b_cq_raw_dd_bug_o1", (8, 147)),
        ("rev14b_cq_raw_copy_bug_o0", (9, 174)),
        ("rev14b_cq_raw_copy_bug_o1", (9, 174)),
        ("rev14_cr_dd_read_bug_o0", (5, 203)),
        ("rev14_cr_dd_read_bug_o1", (5, 203)),
        ("rev14_cr_copy_carrier_bug_o0", (8, 273)),
        ("rev14_cr_copy_carrier_bug_o1", (8, 273)),
        ("rev14_cr_triple_bug_o0", (10, 214)),
        ("rev14_cr_triple_bug_o1", (10, 214)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
    for (name, at) in [
        ("rev14b_cq_raw_copy_ctl_o0", (10, 174)),
        ("rev14b_cq_raw_copy_ctl_o1", (10, 174)),
        ("rev14_cr_dd_read_ctl_o0", (6, 166)),
        ("rev14_cr_dd_read_ctl_o1", (6, 166)),
    ] {
        let rows = verdicts_at(name);
        let read: Vec<&RowAt> =
            rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == at).collect();
        assert!(
            !read.is_empty(),
            "{name}: the read row at {at:?} must be generated; rows {rows:?}"
        );
        for (_, verdict, _, _) in &read {
            assert!(
                is_proved(verdict),
                "{name}: the control's read at {at:?} must PROVE; got {verdict:?}"
            );
        }
    }
}

// ─── Round A12, PASS 2 ────────────────────────────────────────────────────────
//
// The round A12 review measured two rows the walk itself did not decide, one in each
// direction, and both are closed here on real compiler MIR at both `-O` levels.

/// SITE 1 — THE FALSE REFUTATION, and the precision floor beside it.
///
/// `pub fn x3_ctl(src: &[u8; 4], t: &[u8; 4], j: usize) -> u8 { let mut arr = *src;
/// let a = &mut arr; if j >= 4 { return 0; } let r = &mut a[j]; *r = 3;
/// t[arr[j] as usize] }` — plain safe Rust, no `unsafe`, no contracts. `arr[j] == 3`
/// after the store, so `t[3]` is in bounds for every input and the runtime oracle
/// never panics (`rev15d_oracle.out`: `x3_ctl: ok 0`). The SEALED pristine driver
/// PROVES all three bounds rows at both levels (`pristine_rev15d_{0,1}.tbl`).
///
/// This tree REFUTED the `t[..]` row at `-O0` with a counterexample: `&mut (*_5)[_4]`
/// — a borrow of the POINTEE — was counted by `trust_types::Statement::escapes_local`
/// as an escape of `_5`, so `unique_value_def(_5)` was `None` and `*_5` never folded.
/// The store then defined `a*[_3]` while the read spelled `arr[_3]`, nothing tied
/// them, and `Ge(_9, 4)` was satisfiable. Measured, not argued: `place_to_var_name`
/// on `(*_5)[_4]` answered `a*[_4]` in `x3_ctl` and `arr[_4]` in `x2_ctl`, two bodies
/// that differ only by that one `Rvalue::Ref`.
///
/// `local_defs::unique_value_def_modulo_pointee_borrows` is the resolver question the
/// fold now asks; `x1_ctl` (`let a = &mut arr; let b = &mut *a; let r = &mut b[j];`)
/// is the same defect one hop deeper. `x2_ctl` (the projected store `a[j] = 3`) and
/// `x4_ctl` (no intermediate pointer at all) never lost their proofs and are the
/// floor: this change may not cost them.
#[test]
fn a12p2_a_borrow_of_the_pointee_does_not_refuse_the_fold() {
    for (name, at) in [
        ("rev15d_x3_ctl_o0", (5, 149)),
        ("rev15d_x3_ctl_o1", (5, 149)),
        ("rev15b_x1_ctl_o0", (35, 148)),
        ("rev15b_x1_ctl_o1", (35, 148)),
    ] {
        let rows = verdicts_at(name);
        let read: Vec<&RowAt> =
            rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == at).collect();
        assert!(
            !read.is_empty(),
            "{name}: the read row at {at:?} must be generated; rows {rows:?}"
        );
        for (_, verdict, _, _) in &read {
            assert!(
                is_proved(verdict),
                "{name}: the read at {at:?} is a CORRECT program the sealed driver proves — a \
                 refutation here is the pointee-borrow escape back; got {verdict:?}"
            );
        }
    }
    // THE FLOOR — the two shapes that never lost the proof keep every bounds row
    // PROVED. The counts are the measured ones and are asserted so that a change
    // which stops GENERATING a row reads as a failure rather than a pass: three rows
    // at `-O0`, two at `-O1`, where the optimizer has already folded the guarded
    // read (the sealed driver reports the same two, `pristine_rev15d_1.tbl`).
    for (name, count) in [
        ("rev15d_x2_ctl_o0", 3),
        ("rev15d_x2_ctl_o1", 2),
        ("rev15d_x4_ctl_o0", 3),
        ("rev15d_x4_ctl_o1", 2),
    ] {
        let rows = rows_of(name, is_index_oob);
        assert_eq!(rows.len(), count, "{name}: the bounds-row count drifted; got {rows:?}");
        assert!(
            rows.iter().all(|(_, r, _)| is_proved(r)),
            "{name}: a control that always proved must keep proving; got {rows:?}"
        );
    }
}

/// SITE 2 — THE FOLD'S OWN RESIDUAL: a guard rebound through an alias created by a
/// SHARED borrow.
///
/// ```ignore
/// #[inline(never)] pub fn launder(p: *const usize) -> *mut usize { p as *mut usize }
/// pub fn u1_shared_cast_bug(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 {
///     if s.len() < 2 { return 0; }
///     let mut j = 0usize;
///     let pj = launder(&j);       // the ONLY alias of `j`, and it is `&j`
///     let r = &mut s[j];          // referent `(*s)[j]`, guard `j`
///     unsafe { *pj = k };         // rebinds `j`
///     *r = 3;                     // spelled `s*[j]` with `j == k`; lands in `s[0]`
///     if j >= s.len() { return 0; }
///     t[s[j] as usize]
/// }
/// ```
///
/// Runtime oracle: `u1_shared_cast_bug: PANIC` (`s = [0, 9]`, `k = 1` → `t[9]`). The
/// `-O0` row `@L25:219` was PROVED kernel-certified on this tree — and is
/// byte-identical on the SEALED driver (`pristine_rev15b_0.tbl`: `Index:P@L25:219`),
/// so it is a residual this campaign inherited, not one it minted.
///
/// `referent_fold::written_place_rebinds` could not attribute the store through `pj`
/// (a `Call` destination), fell back to `guard_reachable_by_pointer(j)`, and
/// `slot_is_aliased_anywhere` scanned only `Rvalue::Ref { mutable: true }` /
/// `AddressOf` — so the one alias of `j` was invisible and the rebind was dismissed.
/// The write is UB under Stacked/Tree Borrows, so this is hardening; it is done
/// anyway because a name minted under "the program contains no UB" is an assumption
/// the verifier does not check. `-O1` already refuted the row and must keep doing so.
#[test]
fn a12p2_a_guard_aliased_by_a_shared_borrow_is_pointer_reachable() {
    for (name, at) in
        [("rev15b_u1_shared_cast_bug_o0", (25, 219)), ("rev15b_u1_shared_cast_bug_o1", (25, 219))]
    {
        assert_read_after_reseat_not_proved(name, at);
    }
}

// ─── Round A13 ────────────────────────────────────────────────────────────────
//
// The round-A12 review's own witness, closed. Source of record beside the fixtures:
// `tests/fixtures/escaped_seam_rev17c_pins.rs`.

/// THE FALSE REFUTATION A VALUE-BLIND WALK MINTS.
///
/// ```ignore
/// pub fn n1_restore_ctl(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 {
///     let mut j = 0usize;
///     if s.len() < 2 { return 0; }
///     let r = &mut s[j];   // referent `(*s)[j]`, guard `j`, borrow-time value 0
///     j = k;               // rebound
///     j = 0;               // and RESTORED to its borrow-time value
///     *r = 3;              // lands in `s[0]`, which is what `s[j]` names here
///     t[s[j] as usize]     // reads 3; `t[3]` is in bounds for every input
/// }
/// ```
///
/// Plain safe Rust, no `unsafe`, no contracts; the runtime oracle never panics
/// (`rev17c_oracle.out`: `n1_restore_ctl: ok 4`). The SEALED driver PROVES the
/// `t[..]` row at `-O1` (`pristine_rev17c_1.tbl`: `Index:P@L10:157`) and so does the
/// A5-era stage1 (`pristine_s1rev17c_1.tbl`); this tree answered `FAILED` with a
/// counterexample, because `referent_fold::walk` carried ONE boolean for ALL guards,
/// set it at any statement whose written place overlaps a guard NAME, and never
/// cleared it. `resolve_referent` then returned `None`, `*r` was spelled by the
/// opaque `r*`, the store havocked instead of defining, and the later read got an
/// unconstrained token. `d4_reseat_then_restore_ctl` (`rev17_pins.rs:44`) is the same
/// channel and moves with it.
///
/// The `-O0` twin is `Failed` on the SEALED driver too (`pristine_rev17c_0.tbl`:
/// `Index:F@L10:157`), so it is pinned only for what this campaign owes: a refutation
/// there may never be kernel-certified.
#[test]
fn a13_a_guard_restored_to_its_borrow_time_constant_keeps_the_fold() {
    let rows = verdicts_at("rev17c_n1_restore_ctl_o1");
    let read: Vec<&RowAt> =
        rows.iter().filter(|(k, _, _, loc)| is_index_oob(k) && *loc == (10, 157)).collect();
    assert!(!read.is_empty(), "n1_restore_ctl@-O1: the read row must be generated; rows {rows:?}");
    for (_, verdict, _, _) in &read {
        assert!(
            is_proved(verdict),
            "n1_restore_ctl@-O1: `j` holds its borrow-time value 0 at every use of `r`, the \
             program never panics, and BOTH baselines prove this row — a refutation here is the \
             value-blind walk back; got {verdict:?}"
        );
    }
    // The `-O0` twin: no claim about the direction, only that a refutation is never
    // dressed as kernel-certified.
    for (_, verdict, certified, _) in verdicts_at("rev17c_n1_restore_ctl_o0") {
        assert!(
            !(is_refuted(&verdict) && certified),
            "n1_restore_ctl@-O0: a refuted row may not also be kernel-certified"
        );
    }
}

/// THE NEGATIVE CONTROL THAT MUST KEEP ITS REFUTATION — the one-character twin.
///
/// `n8_restore_wrong_bug` is `n1_restore_ctl` with `j = k; j = 1;`: the guard is
/// restored to the WRONG value, so `*r = 3` lands in `s[0]` while `s[j]` reads
/// `s[1]`, and the oracle PANICS (`rev17c_oracle.out`). BOTH baselines PROVE the
/// `t[..]` row at `-O1` (`pristine_rev17c_1.tbl` and `pristine_s1rev17c_1.tbl`:
/// `Index:P@L24:163`) — a false proof this campaign closes and this round may not
/// reopen. `borrow_time_constant` is what separates the two bodies: `c0(j) == 0`, and
/// `j = 1` is a constant that is not it.
#[test]
fn a13_a_guard_restored_to_the_wrong_constant_keeps_its_refutation() {
    for name in ["rev17c_n8_restore_wrong_bug_o0", "rev17c_n8_restore_wrong_bug_o1"] {
        assert_read_after_reseat_not_proved(name, (24, 163));
    }
}

/// THE FLOOR beside both: the guard written at all is what the walk is about, so the
/// body that never writes it must keep every row proved — three at `-O0`, four at
/// `-O1`, the counts asserted so that a change which stops GENERATING a row reads as
/// a failure rather than a pass.
#[test]
fn a13_the_never_written_guard_baseline_keeps_every_proof() {
    for (name, count) in [("rev17c_n6_baseline_ctl_o0", 3), ("rev17c_n6_baseline_ctl_o1", 4)] {
        let rows = verdicts(name);
        assert_eq!(rows.len(), count, "{name}: the row count drifted; got {rows:?}");
        assert!(
            rows.iter().all(|(_, r, _)| is_proved(r)),
            "{name}: the baseline control must keep every proof; got {rows:?}"
        );
    }
}

/// THE SOUNDNESS MARGIN OF THE RE-ESTABLISHMENT RULE, on two programs the SEALED
/// driver proves and that PANIC. Source of record:
/// `tests/fixtures/escaped_seam_rev18_pins.rs`.
///
/// Both write the guard with a CONSTANT before the deref — the shape round A13 admits
/// — and in both the guard's BORROW-TIME value is not that constant, so `c0(g)` is the
/// only thing that separates them from `n1_restore_ctl`:
///
/// ```ignore
/// // p1: the borrow-time value is a PARAMETER, so c0(j) is no constant at all.
/// let mut j = k; … let r = &mut s[j];  j = 0;  *r = 3;  t[s[j] as usize]
/// // p2: TWO different constants reach the borrow, so c0(j) is Top.
/// let mut j = 0; … if c { j = 1; }  let r = &mut s[j];  j = 0;  *r = 3;  t[s[j] as usize]
/// ```
///
/// Runtime oracle (`rev18_oracle.out`): both PANIC — `p1` with `s = [9, 0]`, `k = 1`,
/// `p2` with `s = [9, 0]`, `c = true`, each storing into `s[1]` and then reading
/// `s[0] == 9` into `t[..]`. The SEALED driver PROVES both bug rows at `-O1`
/// (`pristine_rev18_1.tbl`: `Index:P@L8:190`, `Index:P@L10:175`) — two more false
/// proofs of the pre-campaign baseline. This tree refutes both at BOTH levels, and
/// this row is what keeps `borrow_time_constant` from being widened into them.
#[test]
fn a13_a_constant_that_is_not_the_borrow_time_value_re_establishes_nothing() {
    for (name, at) in [
        ("rev18_p1_param_guard_then_const_bug_o0", (8, 190)),
        ("rev18_p1_param_guard_then_const_bug_o1", (8, 190)),
        ("rev18_p2_two_consts_before_bug_o0", (10, 175)),
        ("rev18_p2_two_consts_before_bug_o1", (10, 175)),
    ] {
        assert_read_after_reseat_not_proved(name, at);
    }
}

// ─── Round A13, pass 2 ────────────────────────────────────────────────────────
//
// The capability split in `referent_fold::callee_may_rebind`. Source of record beside
// the fixtures: `tests/fixtures/escaped_seam_rev19b_pins.rs`; runtime oracle
// `rev19b_oracle.out` (v1/v2/v5/v6/v7 `ok 13`, v3/v4 `PANIC`).

/// EVERY bounds row at `(line, col)` PROVES, and no refuted row of the body is
/// kernel-certified. The location form of [`assert_all_proved`], for a body whose
/// other rows legitimately differ between `-O` levels.
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

/// THE FALSE REFUTATION A CAPABILITY-BLIND ALIAS SCAN MINTS.
///
/// ```ignore
/// pub fn v7_shared_param_borrow_after_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
///     if s.len() < 4 { return 0; }
///     if j >= s.len() { return 0; }
///     let r = &mut s[j];   // referent `(*s)[j]`, guards `s` and the PARAMETER `j`
///     nothing();           // a call inside the region
///     *r = 3;              // s[j] = 3, so `s[j] as usize == 3 < 4`
///     let v = t[s[j] as usize];   // L92: BOTH rows refuted before this pass
///     let q = &j;          // the ONLY borrow of `j`, and it executes AFTER the read
///     let _z = sink(q);
///     v
/// }
/// ```
///
/// Plain safe Rust, no `unsafe`; the oracle never panics (`v7_..._ctl: ok 13`), and
/// BOTH baselines prove both rows at BOTH `-O` levels (the SEALED driver and the
/// A5-era stage1). This tree answered `FAILED(cex)` at both levels.
///
/// The chain, measured: round A13 added `!local_storage_borrowed_anywhere` to the
/// guard filter, so the never-written parameter `j` — previously DROPPED — is now
/// KEPT as a guard (it must be: `v3_shared_param_cast_store_bug` below is why).
/// `callee_may_rebind` then asked `guard_reachable_by_pointer`, whose
/// `slot_is_aliased_anywhere` counts a borrow of ANY mutability, so the single shared
/// `&j` made EVERY `Call`/`Drop` in the region mark `j` `Unknown`, the mention of `r`
/// refused the fold, `*r = 3` fell back to the opaque deref-store havoc, and the read
/// got an unconstrained token. A callee handed a `&usize` of `j`'s own storage cannot
/// rebind `j`; `slot_is_writably_aliased_anywhere` is that question.
///
/// `v2_shared_param_call_ctl` is the same channel with the borrow taken BEFORE the
/// region and passed to the call, and `v6_shared_param_drop_ctl` with a `Drop`
/// terminator — the two rows that say this is about the capability, not about where
/// the borrow sits.
#[test]
fn a13p2_a_shared_borrow_is_not_a_callee_write_capability() {
    for name in
        ["rev19b_v7_shared_param_borrow_after_ctl_o0", "rev19b_v7_shared_param_borrow_after_ctl_o1"]
    {
        assert_bounds_rows_prove(name, (92, 12));
        assert_bounds_rows_prove(name, (92, 14));
    }
    for name in ["rev19b_v2_shared_param_call_ctl_o0", "rev19b_v2_shared_param_call_ctl_o1"] {
        assert_bounds_rows_prove(name, (33, 4));
        assert_bounds_rows_prove(name, (33, 6));
    }
    // `v6` carries a `vec![..]`, whose desugar contains a store through a raw pointer
    // this seam cannot attribute (`(*_28).1.0.0 = [1, 2, 3]`). At `-O1` that store is
    // gone and the rows prove; at `-O0` it reaches the WIDE `guard_reachable_by_pointer`
    // inside `written_place_rebinds` — which is a different channel from this pass's,
    // and the one `v3` needs — so the `-O0` twin is pinned only for what is owed: a
    // refutation there may never be kernel-certified. See the round-A13 pass-2 open
    // item on the unattributable-store arm.
    assert_bounds_rows_prove("rev19b_v6_shared_param_drop_ctl_o1", (82, 4));
    assert_bounds_rows_prove("rev19b_v6_shared_param_drop_ctl_o1", (82, 6));
    for (_, r, c, _) in verdicts_at("rev19b_v6_shared_param_drop_ctl_o0") {
        assert!(!(is_refuted(&r) && c), "v6@-O0: a refuted row may not also be kernel-certified");
    }
}

/// THE ROW THE SPLIT MAY NOT REACH — the store this body SPELLS.
///
/// ```ignore
/// // v3: the shared borrow of the parameter guard, laundered to `*mut` and written.
/// let pj = launder(&j);      // `launder(p: *const usize) -> *mut usize`
/// let r  = &mut s[j];
/// unsafe { *pj = k };        // unattributable: `resolve_referent(pj)` is None
/// *r = 3;
/// if j >= s.len() { return 0; }
/// t[s[j] as usize]           // L46:4 — PANICS (`v3_..._bug: PANIC`)
/// ```
///
/// The SEALED driver PROVES this row at `-O0` (a false proof of the pre-campaign
/// baseline). It stays closed because `written_place_rebinds` keeps asking the WIDE
/// `guard_reachable_by_pointer` on its unattributable-store arm: no capability
/// argument is available for a store whose pointer resolves to nothing. Only
/// `callee_may_rebind` narrowed. Measured causally by the pass-1 review: with the
/// guard filter's fourth conjunct replaced by `true`, this row flips `Unknown` ->
/// `Proved` at `-O0`.
///
/// `v4_mut_param_guard_bug` is the `&mut` twin, closed by the split's own predicate
/// (`Ref { mutable: true }` is a write capability), so it says the split did not
/// simply delete the alias question.
#[test]
fn a13p2_a_laundered_shared_borrow_written_through_keeps_its_refusal() {
    for name in
        ["rev19b_v3_shared_param_cast_store_bug_o0", "rev19b_v3_shared_param_cast_store_bug_o1"]
    {
        assert_read_after_reseat_not_proved(name, (46, 4));
    }
    for name in ["rev19b_v4_mut_param_guard_bug_o0", "rev19b_v4_mut_param_guard_bug_o1"] {
        assert_read_after_reseat_not_proved(name, (58, 4));
    }
}

/// THE TWO CONTROLS THAT MAKE THE PAIR DIAGNOSTIC: `v1` is `v2` without the call in
/// the region, `v5` is `v2` without the `&j`. Both proved through every round and
/// must keep doing so — a "fix" that recovers `v2`/`v7` by disabling the guard filter
/// or the walk would take these with it, and a regression here separates "the
/// capability question was narrowed" from "the question stopped being asked".
#[test]
fn a13p2_the_two_controls_that_isolate_shared_borrow_times_call() {
    for name in ["rev19b_v1_shared_param_no_call_ctl_o0", "rev19b_v1_shared_param_no_call_ctl_o1"] {
        assert_bounds_rows_prove(name, (22, 4));
        assert_bounds_rows_prove(name, (22, 6));
    }
    for name in ["rev19b_v5_plain_param_call_ctl_o0", "rev19b_v5_plain_param_call_ctl_o1"] {
        assert_bounds_rows_prove(name, (68, 4));
        assert_bounds_rows_prove(name, (68, 6));
    }
}
