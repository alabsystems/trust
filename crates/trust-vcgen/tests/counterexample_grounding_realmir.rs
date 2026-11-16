// Real-MIR cover for a TRUE refutation delivered with a counterexample that
// CONTRADICTS the program — and for the grounding that now stands between the
// solver's model and the user.
//
//   pub fn castu_unminable(a: i64, mut b: i64) -> i64 {
//       let lim = (-1i32) as u32 as i64;          // lim IS 4294967295
//       if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//       b
//   }
//
// `|a|, |b| < 2^32` really can overflow `i64`, so `[overflow:mul] FAILED` is
// CORRECT. What the strict lane printed beside it was not — measured on this
// tree's stage1 before this change:
//
//   [overflow:mul] FAILED (ay-in-process); counterexample:
//     _10 = 0, _11 = -1, _12 = false, _13 = true, _14 = 0, _4 = 1, _5 = true,
//     _6 = -1, _7 = false, _8 = true, _9 = true,
//     __trust_ovf_bv_lhs_a = 18446744073709551615,
//     __trust_ovf_bv_rhs__15 = 9223372036854775808, a = 0, b = 0, lim = 1
//
// `0 * 0` does not overflow. `lim` is 4294967295 and cannot be 1. `_4` is
// `(-1i32) as u32` and cannot be 1. And `__trust_ovf_bv_lhs_a` — the fresh
// bitvector variable that STANDS FOR `a` — is `-1` beside `a = 0`.
//
// WHY. The signed multiply's violation formula is a conjunction over DISJOINT
// variable sets: a QF_BV overflow core over fresh `__trust_ovf_bv_*` operand
// vars, and the Int-sorted rendering of the dominating guards over the program's
// own locals. ay cannot dispatch the mixture whole, so
// `trust_router::disjoint_components` refutes it component-wise and returns the
// UNION of the component models. That union is a model of the FORMULA — the
// composition is exactly valid — but the formula is weaker than the program: the
// Int half witnesses the guards while the BV half witnesses the overflow, and
// nothing ties the two halves to the same values. When the guard bound cannot be
// MINED either, even `lim` is free.
//
// AMENDED 2026-09-21 — and this shape is no longer one of those. `(-1i32) as
// u32 as i64` is not value-preserving, which is why the fold used to decline it,
// but it IS exactly computable, so `lim == 4294967295` is a true hypothesis and
// `trust_vcgen::const_expr::v2_const_expr_cast_int` now mines it. Measured on
// this tree's own fixtures, that changes the row END TO END:
//
//   * the raw model now names `_4 = 4294967295` and `_11 = -4294967295` — the
//     cast and `-lim` — instead of leaving them free at `_4 = 1, lim = 1`;
//   * `lim` no longer appears as a contradiction at all; the only contradiction
//     left is the BV/Int decorrelation this file was written for;
//   * and the REPAIR now finds a real execution where it previously could not:
//     `a = 2468347912, b = -4264918149`, both inside `|x| < 4294967295`, whose
//     product is past `i64::MIN`. The row delivers that witness instead of the
//     `UNGROUNDED` label.
//
// The name `castu_unminable` (and its fixture filenames) is therefore
// HISTORICAL: it records what the shape was when this file was written. The
// still-unminable shape is `mutescape_unminable`, and it is unminable for a
// reason no fold may ever widen away — the `&mut` alias may have written the
// bound, so the one `Assign` the scan saw is not the local's value.
//
// THE FIX is `trust_vcgen::counterexample_grounding`, applied at DELIVERY: every
// refuted row's model is REPLAYED through the function's own definitions before
// anyone sees it.
//
//   * replays to a failing assert -> delivered as-is, with the fresh bitvector
//     operand vars projected onto the source names they stand for;
//   * a REPAIR built from those operand vars replays to a failing assert ->
//     that repaired input assignment is delivered instead, and it is a real
//     execution (`unguarded` and `shift62_minable` below both recover one);
//   * neither -> the row carries one explicit `UNGROUNDED` entry naming the
//     contradiction and the fix (v7/D3), and NO assignment at all.
//
// Mining a bound MOVES a row between the second and third of those, and only
// between those. It never moves the verdict, which
// `grounding_never_costs_a_refutation` below pins across all four shapes.
//
// The verdict never moves. `Failed` stays `Failed` in every case; only the
// witness changes.
//
// Fixtures are this tree's stage1's own extraction:
//
//   rustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> probes.rs
//
// probes.rs:
//   pub fn castu_unminable(a: i64, mut b: i64) -> i64 {
//       let lim = (-1i32) as u32 as i64;
//       if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//       b
//   }
//   #[inline(never)] pub fn bump(x: &mut i64) { *x += 0; }
//   pub fn mutescape_unminable(a: i64, mut b: i64) -> i64 {
//       let mut lim = 1i64 << 40;
//       bump(&mut lim);                       // `lim`'s address escapes
//       if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//       b
//   }
//   pub fn shift62_minable(a: i64, mut b: i64) -> i64 {
//       let lim = (1u64 << 62) as i64;        // the bound DOES fold
//       if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//       b
//   }
//   pub fn unguarded(a: i64, b: i64) -> i64 { a * b }

// WALL-CLOCK DEPENDENCE — OPEN, and disclosed (review of cf9ce551b45, 2026-10-01). Four
// tests below consume `castu_unminable`'s SOLVED verdict, and that solve is a bounded
// 64-bit multiply search measured at 8.5 s at load ~35 (12.99 s for the whole file at load
// ~7). Each solve runs under the in-process backend's 30 s wall-clock timeout, and a
// timeout reads as a lost refutation — so under enough load those four can fail for a
// reason that is not this file's subject. That is a wall clock in a verdict, which the
// 2026-09-30 budget ruling forbids; the remedy is the deterministic, SIZE-SCALED solver
// effort bound approved with 8e (2026-10-01), not yet on main. Until it lands:
//   * `solved_rows` solves each row ONCE per process (not seven times concurrently);
//   * `the_castu_row_carries_the_mined_bound_without_solving` and
//     `the_castu_repair_replays_a_hand_built_model_without_solving` pin the cast fix's
//     STRUCTURAL effect — the mined bound in the row, and the repair — with no solve.
// When the effort bound lands, the solve-dependent assertions move onto it.
//
// MOVED 2026-11-02 (VCGEN-TEST-BACKSTOP-1): the effort bound is on main, and `router()`'s
// ay now carries the test router's ten-minute hang backstop (`support/test_router.rs`),
// so no test clock decides these verdicts. Measured on that change at load ~90: the
// whole file 10 passed in 1.72 s. NARROWED, NOT CLOSED: the count does not yet decide
// alone (`EffortScale`'s T2 dependencies, `trust-types/src/determinism.rs`). ay-sat's
// wall-capped restart inprocessing moves where the count stops a search, and this file's
// `castu_unminable` VC 2 is the measured case: refuted at k = 192 alone, it came back
// `incomplete` in 2 of 4 runs of this file at eight threads, and in 0 of 5 at the builtin
// k = 384. A lost refutation here under load with no `[stop:wall-backstop]` in its
// reason is that residue: rerun it idle before reading it as a regression.

use std::sync::OnceLock;

use trust_types::{
    BinOp, Counterexample, CounterexampleValue, Rvalue, Statement, VcKind, VerifiableFunction,
    VerificationCondition, VerificationResult,
};
use trust_vcgen::counterexample_grounding::{
    UNGROUNDED_LABEL, WitnessGrounding, deliver_counterexample, ground_counterexample,
};

#[path = "support/test_router.rs"]
mod test_router;

const SHAPES: [&str; 4] =
    ["castu_unminable", "mutescape_unminable", "shift62_minable", "unguarded"];

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/cex_grounding_{name}_default_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every multiply-overflow row of the fixture.
fn mul_rows(name: &str) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(&load(name))
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .collect()
}

/// The DEPLOYED backend set, in the compiler's own order — the same pair
/// `rustc_mir_transform::trust_verify::discover_router_backends` builds, so this
/// measures the lane that produced the report and not a substitute.
fn router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(test_router::test_ay_backend()),
    ])
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// Every multiply row of `name` with its deployed verdict, solved ONCE per test
/// process and shared by every test below.
///
/// WHY. The rows are a pure function of the checked-in fixture, and every test
/// here reads the same verdicts; solving them per test solved each row about
/// seven times, concurrently, in one binary. Since `castu_unminable`'s bound is
/// mined (2026-09-21 cast widening) its row is the query a LITERAL bound
/// `let lim = 4294967295i64` always produced — measured byte-identical — and
/// the bounded 64-bit multiply search it asks for takes seconds, not
/// milliseconds (8.5 s per solve at load ~35, against 0.25-0.55 s for the other
/// three shapes). Seven concurrent copies of it pushed single solves past the
/// 30 s backend timeout under load, which read as a lost refutation. One solve
/// per row is the honest cost of the question.
fn solved_rows(name: &str) -> &'static [(VerificationCondition, VerificationResult)] {
    static SOLVED: [OnceLock<Vec<(VerificationCondition, VerificationResult)>>; SHAPES.len()] =
        [const { OnceLock::new() }; SHAPES.len()];
    let index = SHAPES.iter().position(|shape| *shape == name).expect("a fixture shape");
    SOLVED[index].get_or_init(|| {
        mul_rows(name)
            .into_iter()
            .map(|vc| {
                let result = verdict(&vc);
                (vc, result)
            })
            .collect()
    })
}

/// The RAW model the deployed backends return for a refuted row — the
/// pre-grounding delivery, i.e. exactly what a user used to be shown.
fn raw_refutations(name: &str) -> Vec<Counterexample> {
    solved_rows(name)
        .iter()
        .filter_map(|(_, result)| match result {
            VerificationResult::Failed { counterexample, .. } => counterexample.clone(),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY — the fixtures must still be the shapes this file is about.
// ---------------------------------------------------------------------------

/// Every shape must still raise a multiply-overflow row and that row must still
/// be REFUTED. With any of them proved or unknown the grounding assertions below
/// would pass while measuring nothing — and a flip to `Unknown` would be the one
/// outcome this change must never cause.
#[test]
fn every_shape_still_refutes_its_multiply_row() {
    for shape in SHAPES {
        let rows = solved_rows(shape);
        assert!(!rows.is_empty(), "{shape}: the multiply must still raise an overflow row");
        let verdicts: Vec<VerificationResult> =
            rows.iter().map(|(_, result)| result.clone()).collect();
        assert!(
            verdicts.iter().any(|v| matches!(v, VerificationResult::Failed { .. })),
            "{shape}: the multiply really can overflow and this row must stay REFUTED — \
             grounding must never cost a refutation: {verdicts:?}"
        );
        assert!(
            !raw_refutations(shape).is_empty(),
            "{shape}: and the refutation must still carry a model to ground"
        );
    }
}

/// The three guarded shapes must still carry their bound as an UNFOLDED
/// expression over constants reaching the guard through a cast or a call: with
/// the bound arriving as a literal, the mining gap this file is about is not in
/// the fixture at all.
#[test]
fn the_guarded_fixtures_still_carry_an_unfolded_bound() {
    for (shape, needle) in
        [("castu_unminable", "Cast"), ("mutescape_unminable", "Shl"), ("shift62_minable", "Shl")]
    {
        let func = load(shape);
        let found = func.body.blocks.iter().flat_map(|b| b.stmts.iter()).any(|stmt| {
            let Statement::Assign { rvalue, .. } = stmt else { return false };
            match (needle, rvalue) {
                ("Cast", Rvalue::Cast(..)) => true,
                ("Shl", Rvalue::BinaryOp(BinOp::Shl, ..)) => true,
                _ => false,
            }
        });
        assert!(
            found,
            "{shape}: the debug MIR must still carry its bound as an unfolded `{needle}`"
        );
    }
}

// ---------------------------------------------------------------------------
// THE PRE-FIX BEHAVIOUR, measured — every raw model FAILS the new check.
// ---------------------------------------------------------------------------

/// THE REGRESSION THIS FILE EXISTS FOR, and the confirmation that the new check
/// FAILS on the pre-fix behaviour: the model the deployed backends actually
/// return for each of these rows does NOT reach the panicking state when it is
/// replayed against the function's own definitions.
///
/// This is the whole defect, stated as a measurement rather than as prose. Every
/// one of these four rows is a TRUE refutation, and every one of them came with
/// a model that is not an execution of its function.
#[test]
fn the_raw_model_every_backend_returns_is_not_an_execution() {
    for shape in SHAPES {
        let func = load(shape);
        let models = raw_refutations(shape);
        assert!(!models.is_empty(), "{shape}: nothing to measure");
        for model in &models {
            let grounding = ground_counterexample(&func, model);
            assert!(
                matches!(grounding, WitnessGrounding::Ungrounded { .. }),
                "{shape}: the RAW model must be caught as ungrounded — if this ever passes, \
                 either the encoding gained the fact it was missing (good, and this file must \
                 then be rewritten to say so) or the check stopped working: {model:?} => \
                 {grounding:?}"
            );
        }
    }
}

/// And the exact contradiction for the report's own shape, named rather than
/// merely counted.
///
/// AMENDED 2026-09-21 (the closed-constant cast widening). This used to assert
/// that the `lim` contradiction was named: the bound could not be mined, so the
/// Int half of the model left `lim` free and the solver set it to `1`, which the
/// function's own entry-block definition refutes. `const_expr` now mines
/// `lim == 4294967295`, so that contradiction is GONE FROM THE FORMULA rather
/// than merely undetected — which is the stronger outcome, and the assertion is
/// inverted to pin it. What remains is the decorrelation this file is actually
/// about: a fresh `__trust_ovf_bv_*` operand var disagreeing with the source
/// name it stands for.
#[test]
fn the_reported_shape_names_its_contradiction_exactly() {
    let func = load("castu_unminable");
    let models = raw_refutations("castu_unminable");
    assert!(!models.is_empty());
    let mut named_lim = 0usize;
    let mut named_operand = 0usize;
    let mut bound_in_model = 0usize;
    for model in &models {
        // The mined bound is IN the model now: `_4` is `(-1i32) as u32` and
        // `_11` is `-lim`. Before the widening both were free and the solver
        // named `_4 = 1`.
        if model.assignments.iter().any(|(_, v)| {
            matches!(v, CounterexampleValue::Int(4_294_967_295 | -4_294_967_295))
                || matches!(v, CounterexampleValue::Uint(4_294_967_295))
        }) {
            bound_in_model += 1;
        }
        let WitnessGrounding::Ungrounded { reasons } = ground_counterexample(&func, model) else {
            panic!("the reported shape must still be ungrounded: the BV/Int halves decorrelate");
        };
        for reason in &reasons {
            if reason.contains("`lim`") {
                named_lim += 1;
            }
            if reason.contains("__trust_ovf_bv_") {
                named_operand += 1;
            }
        }
    }
    assert_eq!(
        named_lim, 0,
        "the `lim` contradiction must be GONE, not merely caught: the bound is mined, so \
         the solver can no longer choose a value the program's own definition refutes"
    );
    assert!(
        bound_in_model > 0,
        "and the mined bound must be VISIBLE in the model — with zero occurrences the \
         assertion above would pass vacuously on a model that simply stopped naming `lim`"
    );
    assert!(
        named_operand > 0,
        "the fresh bitvector operand's disagreement with its source name is what is left, \
         and it must still be named"
    );
}

// ---------------------------------------------------------------------------
// THE DELIVERY — what a user is shown after grounding.
// ---------------------------------------------------------------------------

/// THE CONTRACT. Whatever a refuted row delivers, it is one of exactly two
/// things: an assignment that REPLAYS to a failing assert, or the explicit
/// `UNGROUNDED` label. Never a concrete assignment the function's own
/// definitions refute — which is what all four of these rows delivered before.
#[test]
fn every_delivered_witness_either_replays_to_the_panic_or_says_it_cannot() {
    for shape in SHAPES {
        let func = load(shape);
        for model in &raw_refutations(shape) {
            let delivered = deliver_counterexample(&func, model);
            let labelled =
                delivered.assignments.len() == 1 && delivered.assignments[0].0 == UNGROUNDED_LABEL;
            if labelled {
                continue;
            }
            assert!(
                matches!(
                    ground_counterexample(&func, &delivered),
                    WitnessGrounding::Replays { .. }
                ),
                "{shape}: a delivered ASSIGNMENT must replay to the panicking state — \
                 anything else is the impossible execution this file exists to stop: \
                 {delivered:?}"
            );
        }
    }
}

/// The REPAIR half, which must not be vacuous: where the fresh bitvector operand
/// vars carry values the guards admit, pushing them back onto the parameters
/// yields a REAL execution, and that is delivered instead of the label.
///
/// `unguarded` (`a * b`, no guard at all) and `shift62_minable` (`|a|,|b| < 2^62`,
/// a bound that folds) are both recovered this way: the raw models named
/// `a = 0, b = 0` — a product that cannot overflow — and the delivered ones
/// really do overflow.
///
/// AMENDED 2026-09-21: `castu_unminable` joins them. Its bound `(-1i32) as u32
/// as i64` is now mined (`const_expr::v2_const_expr_cast_int`), so the guards
/// the repair has to satisfy are the program's real ones and the repair finds
/// `a = 2468347912, b = -4264918149` — a product past `i64::MIN` with both
/// operands inside `|x| < 4294967295`. THIS is what the widening bought: a row
/// that could only be labelled now carries a witness a user can run.
#[test]
fn the_repair_recovers_a_real_witness_where_the_guards_admit_one() {
    for shape in ["unguarded", "shift62_minable", "castu_unminable"] {
        let func = load(shape);
        let models = raw_refutations(shape);
        assert!(!models.is_empty(), "{shape}: nothing to repair");
        let mut repaired = 0usize;
        for model in &models {
            let delivered = deliver_counterexample(&func, model);
            if delivered.assignments.iter().any(|(name, _)| name == UNGROUNDED_LABEL) {
                continue;
            }
            // The delivered witness is the function's own parameters, and the
            // product of the two really is outside `i64`.
            let a = witness_int(&delivered, "a").expect("`a` must be named");
            let b = witness_int(&delivered, "b").expect("`b` must be named");
            assert!(
                a.checked_mul(b).is_none_or(|p| i64::try_from(p).is_err()),
                "{shape}: the delivered witness must actually overflow: {a} * {b}"
            );
            if shape == "castu_unminable" {
                // And it must be inside the MINED bound, which is the whole
                // point: a witness outside `|x| < 4294967295` would mean the
                // guards were not constraining the repair at all.
                assert!(
                    a.abs() < 4_294_967_295 && b.abs() < 4_294_967_295,
                    "castu_unminable: the repair must respect the mined bound: {a}, {b}"
                );
            }
            assert_eq!(
                ground_counterexample(&func, &delivered),
                ground_counterexample(&func, &delivered),
                "grounding is deterministic"
            );
            assert!(
                matches!(
                    ground_counterexample(&func, &delivered),
                    WitnessGrounding::Replays { .. }
                ),
                "{shape}: and it must replay to the panic: {delivered:?}"
            );
            repaired += 1;
        }
        assert!(
            repaired > 0,
            "{shape}: a real witness exists for this row and the repair must find it — \
             with zero repairs the assertions above are vacuous"
        );
    }
}

fn witness_int(cex: &Counterexample, name: &str) -> Option<i128> {
    cex.assignments.iter().find(|(n, _)| n == name).and_then(|(_, v)| match v {
        CounterexampleValue::Int(i) => Some(*i),
        CounterexampleValue::Uint(u) => i128::try_from(*u).ok(),
        _ => None,
    })
}

/// And the shape where NO repair exists — the body leaves the replay's fragment
/// (`mutescape_unminable` calls `bump`) — delivers the LABEL, with the reason
/// and the fix, and no assignment at all.
///
/// AMENDED 2026-09-21: `castu_unminable` used to be listed here too, and it was
/// listed for the RIGHT reason at the time (with `lim` unminable the guards
/// excluded every value the bitvector half offered). Its bound is mined now and
/// it delivers a real witness, so it has moved to
/// `the_repair_recovers_a_real_witness_where_the_guards_admit_one`.
///
/// `mutescape_unminable` stays, and stays for a reason no fold may widen away:
/// `bump(&mut lim)` puts the bound's address on the escape channel, so
/// `local_defs::unique_value_def` refuses it and must keep refusing it — the one
/// `Assign` the scan saw is not the local's value once an alias can write it.
#[test]
fn the_shapes_with_no_recoverable_witness_deliver_the_label_and_its_fix() {
    for shape in ["mutescape_unminable"] {
        let func = load(shape);
        let models = raw_refutations(shape);
        assert!(!models.is_empty());
        for model in &models {
            let delivered = deliver_counterexample(&func, model);
            assert_eq!(
                delivered.assignments.len(),
                1,
                "{shape}: the label is the whole delivery: {delivered:?}"
            );
            assert_eq!(delivered.assignments[0].0, UNGROUNDED_LABEL);
            let rendered = delivered.to_string();
            // `lim`'s address escapes, so its bound is left UNMINED: that is the one
            // case the respelling advice is for (2026-10-01: it is given only then).
            for needle in ["not an execution", "REFUTATION stands", "FIX:", "spell the bound"] {
                assert!(rendered.contains(needle), "{shape}: the label must say `{needle}`");
            }
            // And no value the program refutes survives as something a reader
            // could take for an input.
            assert!(
                !delivered.assignments.iter().any(|(name, _)| name == "lim" || name == "a"),
                "{shape}: an impossible assignment must not be delivered: {delivered:?}"
            );
        }
    }
}

/// The cast fix's effect on the ROW, with no solve (see the WALL-CLOCK note in the
/// header): the mined bound `|x| < 4294967295` is rendered onto BOTH fresh bitvector
/// operand vars of `castu_unminable`'s multiply. Before cf9ce551b45 the cast did not
/// fold and the operands carried no bound at all.
#[test]
fn the_castu_row_carries_the_mined_bound_without_solving() {
    use trust_types::Formula;
    fn bounded_operands(f: &Formula, out: &mut Vec<(String, i128)>) {
        match f {
            Formula::BvSLt(a, b, _) | Formula::BvSLe(a, b, _) => {
                if let (Formula::Var(name, _), Formula::BitVec { value, .. })
                | (Formula::BitVec { value, .. }, Formula::Var(name, _)) =
                    (a.as_ref(), b.as_ref())
                    && name.starts_with("__trust_ovf_bv_")
                {
                    out.push((name.clone(), *value));
                }
            }
            _ => f.children().into_iter().for_each(|c| bounded_operands(c, out)),
        }
    }
    let rows = mul_rows("castu_unminable");
    assert!(!rows.is_empty(), "the multiply must still raise its overflow row");
    for vc in &rows {
        let mut bounds = Vec::new();
        bounded_operands(&vc.formula, &mut bounds);
        for role in ["lhs", "rhs"] {
            for bound in [4_294_967_295i128, -4_294_967_295] {
                assert!(
                    bounds.iter().any(|(name, value)| {
                        name.starts_with(&format!("__trust_ovf_bv_{role}_")) && *value == bound
                    }),
                    "the mined bound {bound} must reach the {role} operand: {bounds:?}"
                );
            }
        }
    }
}

/// The REPAIR, with no solve: a model built by hand in the shape the deployed pair
/// returns for `castu_unminable` (the Int half naming `a = b = 0`, the BV half naming an
/// overflowing pair inside the mined bound) is delivered as the repaired parameters, and
/// they replay to the panic.
#[test]
fn the_castu_repair_replays_a_hand_built_model_without_solving() {
    let func = load("castu_unminable");
    let rows = mul_rows("castu_unminable");
    let operand = |role: &str| -> String {
        let mut names = Vec::new();
        fn vars(f: &trust_types::Formula, out: &mut Vec<String>) {
            if let trust_types::Formula::Var(name, _) = f {
                out.push(name.clone());
            }
            f.children().into_iter().for_each(|c| vars(c, out));
        }
        vars(&rows[0].formula, &mut names);
        names
            .into_iter()
            .find(|n| n.starts_with(&format!("__trust_ovf_bv_{role}_")))
            .unwrap_or_else(|| panic!("the row names a fresh {role} operand var"))
    };
    let (a, b): (i64, i64) = (2_468_347_912, -4_264_918_149);
    assert!(a.checked_mul(b).is_none(), "the hand-built pair really overflows");
    let model = Counterexample::new(vec![
        ("a".to_string(), CounterexampleValue::Int(0)),
        ("b".to_string(), CounterexampleValue::Int(0)),
        (operand("lhs"), CounterexampleValue::Uint(u128::from(a as u64))),
        (operand("rhs"), CounterexampleValue::Uint(u128::from(b as u64))),
    ]);
    let delivered = deliver_counterexample(&func, &model);
    assert_eq!(witness_int(&delivered, "a"), Some(i128::from(a)), "{delivered:?}");
    assert_eq!(witness_int(&delivered, "b"), Some(i128::from(b)), "{delivered:?}");
    assert!(
        matches!(ground_counterexample(&func, &delivered), WitnessGrounding::Replays { .. }),
        "the repaired parameters must replay to the panic: {delivered:?}"
    );
}

/// THE SOUNDNESS BOUNDARY, pinned: grounding rewrites the WITNESS and never the
/// VERDICT. Turning a row `Unknown` to avoid an awkward witness would trade a
/// sound refutation for a lost verdict, and this asserts it cannot happen.
#[test]
fn grounding_never_costs_a_refutation() {
    for shape in SHAPES {
        let func = load(shape);
        let mut results: Vec<(VerificationCondition, VerificationResult)> =
            solved_rows(shape).to_vec();
        let before: Vec<String> = results.iter().map(|(_, r)| kind_of(r).to_string()).collect();
        trust_vcgen::counterexample_grounding::ground_delivered_counterexamples(
            &func,
            &mut results,
        );
        let after: Vec<String> = results.iter().map(|(_, r)| kind_of(r).to_string()).collect();
        assert_eq!(before, after, "{shape}: grounding moved a verdict");
        for (_, result) in &results {
            if let VerificationResult::Failed { counterexample, .. } = result {
                assert!(
                    counterexample.is_some(),
                    "{shape}: a refutation must still carry something actionable"
                );
            }
        }
    }
}

fn kind_of(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Proved { .. } => "proved",
        VerificationResult::Failed { .. } => "failed",
        VerificationResult::Unknown { .. } => "unknown",
        VerificationResult::Timeout { .. } => "timeout",
        _ => "other",
    }
}
