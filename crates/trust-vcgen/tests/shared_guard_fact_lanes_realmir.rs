// Real-MIR cover for the THREE consumers of `v2_dominating_linear_facts_*`, and
// for the name space each of them asks its facts in.
//
// AMENDED 2026-10-01: the miner this file names is retired. `v2_dominating_linear_facts_*`,
// `v2_live_copy_source_name{,_reaching}`, `v2_local_unstable_only_by_plain_stores` and
// `V2GuardSubject` were replaced by `generate::dominating_facts` — guard facts built ONCE
// per function from DOMINATING guarded edges and keyed on the SSA VALUE their subject
// holds (`version_ssa::ValueId`), the copy hop decided by the same value identity, the
// name-space choice now `dominating_facts::GuardSubject`. The retired miner compared
// reaching-def SETS, which a loop can make equal across a write (`tests/
// dominating_guard_value_identity_realmir.rs` is the false proof that measured it). Every
// pin in this file holds unchanged on the new index; the narrative below is the history
// of the shapes, and the function names in it are the retired ones.
//
// 5445c64d21b (the `g7` false refutation) wired a one-hop live-COPY resolution of
// the GUARD's SUBJECT into the shared `v2_dominating_linear_facts_for_var`. Its
// commit body describes the multiply lane only — and says in as many words that
// the signed corner arm is unchanged — but that helper has THREE callers:
//
//   * `v2_mul_dominating_operand_facts`   the multiply facts (the intended one),
//   * `v2_dominating_strict_upper_bound`  the shift-amount bound,
//   * `v2_signed_mul_dominating_facts`    the signed corner arm.
//
// So two consumers silently began receiving dominating facts they had never
// received before, with no test covering either under a per-guard copy.
//
// WHY THE HOP BELONGS TO ONE CALLER. It is not a precision dial; it records which
// NAME SPACE the caller's `var` is written in. `v2_mul_dominating_operand_facts`
// walks its OWN operand one live pure-copy hop and then asks under the SOURCE
// name, so the guard's subject has to be walked the same hop or the two names can
// never meet — debug rustc gives the short-circuit `&&` its own copy of the value
// (`_5 = copy _2; _4 = Lt(_5, 1000)`) and the multiply its own copy again. The
// other two callers pass a RAW MIR local — the shift amount and its `amount =
// source - c` source, a signed multiply's operand — and a raw local meets a guard
// only when the guard names it. `V2GuardSubject` makes that a call-site decision
// again; this file pins both sides of it.
//
// WHAT REACHES THE SHIFT LANE AT ALL. The dominating shift-amount bound is
// emitted by `v2_collect_bv_shl_blockdef`, which runs for a SIGNED 128-bit
// overflow row whose operand is defined by `Shl(const, amount)` — the `signed_max`
// shape. So these fixtures are `(1i128 << (width - 1)) - 1`: the row is provable
// exactly when a dominating bound puts the amount below 127, because at
// `amount = 127` the shift result is `i128::MIN` and `- 1` really underflows.
//
// MEASURED (see `the_fixtures_carry_only_the_copy_shape_that_really_arises`):
// Trust's extraction emits a guard-subject COPY only for a local with more than
// one definition — `let g = w;` is coalesced into a single local in BOTH lanes —
// and a multi-def local's reaching version at the guard is a JOIN, which the copy
// resolver refuses. Flipping `V2GuardSubject::ExactName` back to
// `LiveCopyOfBase` at this caller and re-running this file's bound assertions
// reproduces them byte for byte. That is the point of the narrowing: it turns a
// consumer that is inert BY ACCIDENT into one that is inert BY CONTRACT, so the
// next relaxation of `guards::value_local_is_unstable` (the signed g7 twin did
// exactly that for the multiply lane) cannot switch it on unobserved.
//
// Fixtures are the stage1 compiler's OWN extraction, both lanes, of
// `fixtures/shift_amount_guard_copy.rs`:
//
//   trustc --edition 2021 --crate-type lib     -Ztrust-dump=mir:<dir> <src>
//   trustc --edition 2021 --crate-type lib -O  -Ztrust-dump=mir:<dir> <src>
//
// and that compilation is itself a measurement: the two `_safe` functions verify
// in both lanes and the two `_unsafe` ones are rejected in both.
use trust_types::{
    Operand, Rvalue, Statement, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(path_stem: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{path_stem}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn shift(name: &str, lane: &str) -> VerifiableFunction {
    load(&format!("shift_amount_guard_copy_{name}_{lane}"))
}

const LANES: [&str; 2] = ["default", "release"];

/// The 128-bit `Sub` overflow row — `(1i128 << (width - 1)) - 1`, the row whose
/// provability is exactly "is the shift amount bounded below 127?". The `u32`
/// `width - 1` row is a different obligation and is filtered out.
fn wide_sub_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let rows: Vec<VerificationCondition> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| match &vc.kind {
            VcKind::ArithmeticOverflow { op, operand_tys, .. } => {
                format!("{op:?}") == "Sub" && format!("{operand_tys:?}").contains("width: 128")
            }
            _ => false,
        })
        .collect();
    assert!(!rows.is_empty(), "the fixture's whole value is its 128-bit `Sub` overflow row");
    rows
}

/// The first two backends of
/// `rustc_mir_transform::trust_verify::discover_router_backends`, in its order:
/// the cheap in-process interval/range backend, then in-process ay. This
/// mirrors that backend LIST only. That inventory feeds the compiler's Liskov
/// check and nothing else, so it is not the lane that decides these wide-sub
/// safety rows in the compiler. The in-process lane computes UNSAT on these
/// rows and then fails its own strict certification, so the SAFE rows are
/// pinned here at "never REFUTED", and their real verdict is pinned by the
/// fixture source compiling clean under the stage1 compiler; the exact bound
/// conjunct below is what pins this lane's own output, and it is
/// router-independent.
fn router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(test_router::test_ay_backend()),
    ])
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// Every `bvult(__trust_ovf_bv_amt_*, <K>)` bound this row carries, as the `K`s.
/// This IS the output of `v2_dominating_shift_amount_bound`, read back off the
/// rendered row, so it observes the extra caller directly instead of through a
/// solver's opinion of it.
fn amount_bounds(vc: &VerificationCondition) -> Vec<i128> {
    const NEEDLE: &str = "BvULt(Var(\"__trust_ovf_bv_amt_";
    const VALUE: &str = "BitVec { value: ";
    let rendered = format!("{:?}", vc.formula);
    let mut bounds = Vec::new();
    let mut from = 0usize;
    while let Some(offset) = rendered[from..].find(NEEDLE) {
        let start = from + offset;
        if let Some(value_at) = rendered[start..].find(VALUE) {
            let tail = &rendered[start + value_at + VALUE.len()..];
            let end = tail.find(|c: char| !c.is_ascii_digit() && c != '-').unwrap_or(tail.len());
            if let Ok(value) = tail[..end].parse::<i128>() {
                bounds.push(value);
            }
        }
        from = start + NEEDLE.len();
    }
    bounds.sort_unstable();
    bounds.dedup();
    bounds
}

/// `(destination local, source local)` of every projection-free whole-local copy.
fn whole_local_copies(func: &VerifiableFunction) -> Vec<(usize, usize)> {
    func.body
        .blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .filter_map(|stmt| match stmt {
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } if place.projections.is_empty() && src.projections.is_empty() => {
                Some((place.local, src.local))
            }
            _ => None,
        })
        .collect()
}

fn projection_free_def_count(func: &VerifiableFunction, local: usize) -> usize {
    func.body
        .blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .filter(|stmt| {
            matches!(stmt, Statement::Assign { place, .. }
                if place.local == local && place.projections.is_empty())
        })
        .count()
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY — the fixtures must still be the shapes this file is about.
// ---------------------------------------------------------------------------

/// The measurement the narrowing rests on, pinned so it cannot go stale:
///
///   * the `signed_max_safe` fixtures carry NO whole-local copy at all — `let g =
///     w;` is coalesced, so an ordinary alias never reaches this lane as a copy;
///   * the `joined_copy` fixtures DO carry one, and its destination has more than
///     one definition. That JOIN is the only copy shape that really arrives here,
///     and it is the one a hop must refuse.
///
/// If rustc's lowering ever starts emitting a SINGLE-def guard-subject copy, the
/// second assertion fails and whoever sees it has to decide what this caller
/// should do about it — which is exactly the decision 5445c64d21b made silently.
#[test]
fn the_fixtures_carry_only_the_copy_shape_that_really_arises() {
    for lane in LANES {
        let safe = shift("signed_max_safe", lane);
        assert_eq!(
            whole_local_copies(&safe),
            Vec::new(),
            "signed_max_safe_{lane}: the extraction coalesces a plain alias — a copy \
             statement here would mean this file's measurement has gone stale"
        );

        for name in ["signed_max_joined_copy_unsafe", "signed_max_joined_copy_safe"] {
            let func = shift(name, lane);
            let copies = whole_local_copies(&func);
            assert!(
                !copies.is_empty(),
                "{name}_{lane}: the extraction must still keep `g = width` as a real \
                 whole-local copy statement"
            );
            assert!(
                copies.iter().any(|(dst, _)| projection_free_def_count(&func, *dst) > 1),
                "{name}_{lane}: the copy this file is about is the one whose destination \
                 is JOINED from two definitions; found copies {copies:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// THE SHIFT-AMOUNT CONSUMER — `v2_dominating_strict_upper_bound`.
//
// The bound conjunct is this caller's own output. 128 is the `Overflow(Shl)`
// assert's own bound, which every one of these rows has; 127 is the DOMINATING
// bound, the only thing that makes the row provable.
// ---------------------------------------------------------------------------

/// SAFE, both entries to the helper: the direct dominating bound on the amount,
/// and the bound established on the `amount = width - 1` SOURCE and carried
/// through the subtraction (`width <= 127` ⇒ `amount <= 126` ⇒ `amount < 127`).
/// `joined_copy_safe` has the same direct bound with the joined copy also in
/// scope — it must land on 127 too, i.e. the joined copy neither helps nor hurts.
#[test]
fn the_dominating_shift_amount_bound_is_mined_for_the_safe_shapes() {
    for name in ["signed_max_safe", "signed_max_joined_copy_safe"] {
        for lane in LANES {
            for vc in wide_sub_rows(&shift(name, lane)) {
                assert!(
                    amount_bounds(&vc).contains(&127),
                    "{name}_{lane}: the dominating `width <= 127` must reach the shift \
                     amount as `bvult(amt, 127)`; got bounds {:?}",
                    amount_bounds(&vc)
                );
            }
        }
    }
}

/// UNSAFE twins. Neither may acquire a bound tighter than the `Overflow(Shl)`
/// assert's own 128 — there is no true dominating fact to mine:
///
///   * `signed_max_unbounded_unsafe`: no upper guard on `width` at all;
///   * `signed_max_joined_copy_unsafe`: the guard bounds `g`, a TWO-def local one
///     of whose definitions is `g = width`. Attributing `g <= 127` to the shift
///     amount would PROVE a row that really underflows at `width = 128` — the
///     unsound green a guard-subject copy hop must never produce here.
#[test]
fn no_bound_tighter_than_the_shl_assert_is_mined_for_the_unsafe_shapes() {
    for name in ["signed_max_unbounded_unsafe", "signed_max_joined_copy_unsafe"] {
        for lane in LANES {
            for vc in wide_sub_rows(&shift(name, lane)) {
                let bounds = amount_bounds(&vc);
                assert!(
                    bounds.iter().all(|b| *b >= 128),
                    "{name}_{lane}: nothing here dominates the shift amount below the \
                     `Overflow(Shl)` assert's own 128; got bounds {bounds:?}"
                );
            }
        }
    }
}

/// And the verdicts, in the direction each shape is allowed to move: a SAFE row
/// is never refuted (a refutation is a build error on valid Rust), an UNSAFE row
/// is never proved (a proof is an unsound green).
#[test]
fn the_shift_lane_verdicts_stay_on_the_right_side() {
    for name in ["signed_max_safe", "signed_max_joined_copy_safe"] {
        for lane in LANES {
            for vc in wide_sub_rows(&shift(name, lane)) {
                let result = verdict(&vc);
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{name}_{lane}: `width <= 127` makes `1i128 << (width-1)` at most 2^126, \
                     so `- 1` cannot underflow; got {result:?}"
                );
            }
        }
    }
    for name in ["signed_max_unbounded_unsafe", "signed_max_joined_copy_unsafe"] {
        for lane in LANES {
            for vc in wide_sub_rows(&shift(name, lane)) {
                let result = verdict(&vc);
                assert!(
                    !matches!(result, VerificationResult::Proved { .. }),
                    "{name}_{lane}: `width = 128` gives `1i128 << 127 == i128::MIN`, and \
                     `i128::MIN - 1` underflows; got {result:?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// THE OTHER TWO CONSUMERS — the lane that keeps the hop, and the one that does
// not. Both are pinned here so the contrast lives in one place.
// ---------------------------------------------------------------------------

fn mul_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let rows: Vec<VerificationCondition> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if format!("{op:?}") == "Mul")
        })
        .collect();
    assert!(!rows.is_empty(), "the fixture must still emit its `Mul` overflow row");
    rows
}

/// The COPY-TIED-BASE lane keeps its hop: `g7` is the row 5445c64d21b fixed, and
/// narrowing the helper must not take it back. (`reassigned_param_mul_realmir`
/// owns this shape; the row is repeated here because it is the other half of the
/// `V2GuardSubject` contract.)
#[test]
fn the_multiply_lane_still_gets_the_guard_subject_hop() {
    let func = load("reassigned_param_mul_g7_safe_default");
    for vc in mul_rows(&func) {
        let result = verdict(&vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "g7: the multiply lane asks under the copy-resolved base, so the guard's own \
             per-guard copy must still be resolved one hop; got {result:?}"
        );
    }
}

/// The SIGNED corner arm is an EXACT-NAME caller — it passes the multiply's RAW
/// operand locals — and its verdicts are exactly what they were.
/// (`signed_reassigned_param_mul_realmir` owns these shapes end to end; the rows
/// here pin that narrowing the shared helper moved none of them.)
#[test]
fn the_signed_corner_arm_verdicts_are_unchanged() {
    for name in ["signed_param_mul_mut_safe_default", "signed_param_mul_neg_safe_default"] {
        for vc in mul_rows(&load(name)) {
            let result = verdict(&vc);
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "{name}: |a*b| < 10^6 fits an i64 with bits to spare; got {result:?}"
            );
        }
    }
    for vc in mul_rows(&load("signed_param_mul_onesided_unsafe_default")) {
        let result = verdict(&vc);
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "signed_param_mul_onesided_unsafe: nothing bounds either operand from below and \
             two large negatives overflow; got {result:?}"
        );
    }
}
