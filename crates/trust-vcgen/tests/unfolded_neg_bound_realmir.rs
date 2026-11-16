// Real-MIR cover for a false refutation of valid Rust whose only defect was how
// the negated CONSTANT was SPELLED — the NEGATION lane's half of the defect the
// guard-fact miner's half of fixed on 2026-09-18.
//
//   pub fn f(a: i64, mut b: i64) -> i64 {
//       let lim = (1u64 << 20) as i64;
//       if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//       b
//   }
//
// `lim` is `1048576`. Nothing here can overflow a negation, and the strict
// DEFAULT lane REFUTED it — exit 1 with
// `[negation] FAILED (ay-in-process); counterexample: ... lim = -9223372036854775808`,
// a witness naming `i64::MIN` for a local whose value is a literal power of two.
// Written `let lim = 1048576i64` or `let lim = 1i64 << 20` the identical function
// exits 0. At 128 bits it was worse: `if a > -(1i128 << 62) && …` produced FOUR
// failed `[negation]` rows, each with `__trust_ovf_bv_neg = 2^127`.
//
// PRE-EXISTING: the sealed 2026-09-17 toolchain gives identical verdicts, so
// neither the constant-fold fix nor the signed-multiply work caused it.
//
// MEASURED ROOT CAUSE — two lanes, one missing resolution.
//
// (1) Int lane (< 128 bits). Un-optimized rustc lowers the bound into its own
//     temporaries and the `as` cast keeps them apart:
//
//       bb1: _4 = Shl(const 1u64, const 20i32);  _3 = Cast(move _4, i64)
//            _9 = Eq(copy _3, const -9223372036854775808)
//            assert(!move _9, "attempt to negate with overflow") -> bb2
//
//     `guards::cast_definition_formula`'s value-preserving int->int arm admitted
//     only a LITERAL operand, so the `Cast` contributed no definition at all:
//     `_4 == 1048576` was mined and then PRUNED as disconnected, `lim` stayed a
//     free `i64`, and `lim == i64::MIN` was satisfiable. `1i64 << 20` compiles
//     clean because there is no cast between the shift and the negated local.
//
// (2) BV lane (>= 128 bits). `-(1i128 << 62)` lowers to `_5 = Shl(const 1i128,
//     const 62i32)` — a shift by a CONSTANT amount — and
//     `overflow_vc::v2_collect_bv_shl_blockdef` renders only a shift whose amount
//     is a bare LOCAL (it needs a BV var to name). It declined, the fresh
//     `__trust_ovf_bv_neg__5` stayed completely free, and every row refuted at
//     `2^127`.
//
// THE FIX is the 2026-09-18 closed-constant-expression resolver, moved to
// `crate::const_expr` and reused (never re-implemented) at both sites, plus the
// same resolution as an ordinary block DEFINITION so a 128-bit constant shift
// stops reaching the solver as the opaque `BvToInt(BvShl(IntToBv(..)))` round trip
// that made in-process ay reject the whole query. It is exact-or-nothing: every
// step range-checked against its own destination type, nothing with a variable
// inside it, `local_defs::unique_value_def` for the walk.
//
// Fixtures are the stage1 compiler's OWN extraction, both lanes:
//
//   rustc --edition 2021 --crate-type lib     -Ztrust-dump=mir:<dir> unfolded_neg_safe.rs
//   rustc --edition 2021 --crate-type lib -O  -Ztrust-dump=mir:<dir> unfolded_neg_safe.rs
//   (and the same two for unfolded_neg_unsafe.rs)
//
// unfolded_neg_safe.rs:
//   pub fn cast_safe(a: i64, mut b: i64) -> i64 {
//       let lim = (1u64 << 20) as i64;
//       if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//       b
//   }
//   pub fn widen_safe(..)     { let lim = (1i32 << 20) as i64;      .. }
//   pub fn addconst_safe(..)  { let lim = (1048575u64 + 1) as i64;  .. }
//   pub fn bits128_safe(a: i128, mut b: i128) -> i128 {
//       if a > -(1i128 << 62) && a < (1i128 << 62)
//           && b > -(1i128 << 62) && b < (1i128 << 62) { b = a * b; }
//       b
//   }
//   pub fn foldbound_safe(a: i64) -> i64 {
//       let lim = -(1i64 << 62) * 2 + 1;   // exactly i64::MIN + 1
//       if a >= lim { -a } else { 0 }
//   }
//
// unfolded_neg_unsafe.rs — the twins whose negation really CAN overflow:
//   pub fn foldbound_unsafe(a: i64) -> i64 {
//       let lim = -(1i64 << 62) * 2;       // exactly i64::MIN
//       if a >= lim { -a } else { 0 }      // `a >= i64::MIN` admits i64::MIN
//   }
//   pub fn foldbound128_unsafe(a: i128) -> i128 {
//       let lim = -(1i128 << 126) * 2;     // exactly i128::MIN
//       if a >= lim { -a } else { 0 }
//   }
//   pub fn castmin_unsafe(a: i64) -> i64 {
//       let lim = (1u64 << 63) as i64;     // IS i64::MIN — the fold must DECLINE
//       if a >= lim { -a } else { 0 }
//   }
//
// `foldbound_safe` / `foldbound_unsafe` are the pair that makes the fold's
// ARITHMETIC load-bearing rather than its mere presence: the two differ by a
// single `+ 1` inside the folded bound, and a fold that dropped the `* 2`, or
// went one off, would swap their verdicts. `castmin_unsafe` pins the other half
// of the contract — `1u64 << 63` is `2^63`, which does NOT fit `i64`, so the
// resolver must hand back NOTHING rather than a wrapped `i64::MIN`.
//
// WHAT THIS FILE DELIBERATELY DOES NOT CLAIM. A negation of a PARAMETER at 128
// bits (`fn f(a: i128) { if a >= i128::MIN + 1 { -a } }`) was refuted by the BV
// lane whatever the bound was spelled as — measured with a plain
// `-170141183460469231731687303715884105727i128` literal when this file landed:
// still FAILED. That is a separate, spelling-INDEPENDENT gap (the Int dominating
// guard is not rendered into the BV neg core), so its safe fixture is not carried
// here; pinning it would pin a different bug.
//
// Trust: 2026-09-21 — that different bug is now FIXED and pinned in its own file,
// `tests/neg128_dominating_guard_realmir.rs`. The paragraph above stays as the
// record of what this file measures and what it does not; read it as history, not
// as the current verdict for a guarded 128-bit parameter.
use trust_types::{
    Counterexample, CounterexampleValue, Operand, Rvalue, Statement, Ty, UnOp, VcKind,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

/// The safe spellings, and whether the `Neg` survives `-O`.
///
/// For the four bound spellings `-O` const-folds the bound into a literal, so the
/// release MIR has no `Neg` and therefore NO negation obligation at all. That is
/// recorded here rather than left implicit, because "not refuted in either lane"
/// is a vacuous claim about a lane with no rows and the file must say which lane
/// actually measures something.
const SAFE: [(&str, bool); 5] = [
    ("cast", false),
    ("widen", false),
    ("addconst", false),
    ("bits128", false),
    ("foldbound", true),
];

const UNSAFE: [&str; 3] = ["foldbound", "foldbound128", "castmin"];

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/unfolded_neg_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every `NegationOverflow` row of the fixture.
fn neg_rows(name: &str) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(&load(name))
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        .collect()
}

/// The DEPLOYED backend set, in the compiler's own order: the cheap in-process
/// interval/range backend first, then in-process ay. Mirrors
/// `rustc_mir_transform::trust_verify::discover_router_backends`. The interval
/// lane is the one that decides a guarded negation, and it is also the lane whose
/// goal binding this commit tightened — so a harness without it would measure
/// neither the fix nor its guard.
fn router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(test_router::test_ay_backend()),
    ])
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY — the fixtures must still be the shapes this file is about.
// ---------------------------------------------------------------------------

fn binops(func: &VerifiableFunction) -> Vec<(String, &Operand, &Operand)> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            match rvalue {
                Rvalue::BinaryOp(op, l, r) => out.push((format!("{op:?}"), l, r)),
                Rvalue::CheckedBinaryOp(op, l, r) => out.push((format!("Checked{op:?}"), l, r)),
                _ => {}
            }
        }
    }
    out
}

/// THE ANTI-VACUITY TEST FOR THE WHOLE FILE. Every DEBUG fixture must still carry
/// its bound as an UNFOLDED operator over CONSTANTS. If a future rustc (or a
/// future extractor) const-folds these at `mir_built`, the bound arrives as a
/// literal, the pre-existing literal path mines it with no help from the
/// resolver, and every safe pin below would pass while measuring nothing.
#[test]
fn the_debug_fixtures_still_carry_an_unfolded_constant_bound() {
    let expected: [(&str, &str); 8] = [
        ("cast_safe", "Shl"),
        ("widen_safe", "Shl"),
        ("addconst_safe", "CheckedAdd"),
        ("bits128_safe", "Shl"),
        ("foldbound_safe", "Shl"),
        ("foldbound_unsafe", "Shl"),
        ("foldbound128_unsafe", "Shl"),
        ("castmin_unsafe", "Shl"),
    ];
    for (shape, op) in expected {
        let name = format!("{shape}_default");
        let func = load(&name);
        let unfolded = binops(&func)
            .into_iter()
            .filter(|(spelling, l, r)| {
                spelling == op
                    && matches!(l, Operand::Constant(_))
                    && matches!(r, Operand::Constant(_))
            })
            .count();
        assert!(
            unfolded > 0,
            "{name}: the debug MIR must still leave the bound as an unfolded `{op}` over \
             literals — with it folded, this file measures nothing"
        );
    }
}

/// The `as`-CAST spelling is the report itself, and the cast must still stand
/// BETWEEN the unfolded constant and the negated local — that separation is the
/// entire Int-lane defect. A `Cast` of a literal would be the old, already-working
/// path.
#[test]
fn the_cast_fixtures_still_cast_a_computed_temporary_not_a_literal() {
    for shape in ["cast_safe", "widen_safe", "addconst_safe", "castmin_unsafe"] {
        let name = format!("{shape}_default");
        let func = load(&name);
        let mut computed_casts = 0usize;
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { rvalue: Rvalue::Cast(src, Ty::Int { width, .. }), .. } =
                    stmt
                else {
                    continue;
                };
                // The shift-amount temporary `_t = (const 20i32 as u32)` is a cast of
                // a LITERAL and is not what this asks about; require a cast of a
                // computed place, at the negated value's own 64-bit width.
                if *width == 64 && matches!(src, Operand::Copy(_) | Operand::Move(_)) {
                    computed_casts += 1;
                }
            }
        }
        assert!(
            computed_casts > 0,
            "{name}: the bound must still reach the negated local THROUGH an `as` cast of a \
             computed temporary — that separation is the defect this file covers"
        );
    }
}

/// The negation must still be a real MIR `Neg` under a real `OverflowNeg` assert:
/// with either gone there is no negation obligation to prove or refute.
#[test]
fn the_debug_fixtures_still_negate_a_value_in_mir() {
    for (shape, _) in SAFE {
        for name in [format!("{shape}_safe_default")] {
            let func = load(&name);
            let negs = func
                .body
                .blocks
                .iter()
                .flat_map(|b| b.stmts.iter())
                .filter(|s| {
                    matches!(s, Statement::Assign { rvalue: Rvalue::UnaryOp(UnOp::Neg, _), .. })
                })
                .count();
            assert!(negs > 0, "{name}: the value must still be negated by a MIR `Neg`");
            assert!(
                !neg_rows(&name).is_empty(),
                "{name}: and that `Neg` must still raise a NegationOverflow obligation"
            );
        }
    }
}

/// The arithmetic the safe/unsafe split rests on, stated in the file rather than
/// asserted by naming. Each line is the exact value the resolver must compute for
/// the corresponding fixture's bound.
#[test]
fn the_safe_unsafe_split_is_arithmetic() {
    assert_eq!((1u64 << 20) as i64, 1_048_576, "cast_safe's bound is a small power of two");
    assert_eq!((1i32 << 20) as i64, 1_048_576, "widen_safe's is the same value, widened");
    assert_eq!((1_048_575u64 + 1) as i64, 1_048_576, "addconst_safe's is the same value again");
    assert_eq!(-(1i64 << 62) * 2 + 1, i64::MIN + 1, "foldbound_safe's bound EXCLUDES i64::MIN");
    assert_eq!(-(1i64 << 62) * 2, i64::MIN, "foldbound_unsafe's bound ADMITS i64::MIN");
    assert_eq!(-(1i128 << 126) * 2, i128::MIN, "and foldbound128_unsafe's admits i128::MIN");
    // `castmin_unsafe`'s bound is `(1u64 << 63) as i64`. `1u64 << 63` is `2^63`,
    // which does NOT fit `i64`, so the resolver must DECLINE it — the machine's
    // `as` reinterprets it to `i64::MIN`, and a resolver that folded the shift and
    // then let the cast wrap would hand back a bound that excludes nothing while
    // claiming to be exact.
    assert_eq!((1u64 << 63) as i64, i64::MIN);
    assert!(i128::from(1u64 << 63) > i128::from(i64::MAX), "2^63 is past i64::MAX");
}

// ---------------------------------------------------------------------------
// SAFE — the false refutation.
// ---------------------------------------------------------------------------

/// THE REPORT, and its four sibling spellings. Every negation row of every safe
/// fixture is PROVED by the deployed backend set in the DEFAULT lane — the lane
/// that refuted them.
#[test]
fn every_safe_unfolded_bound_spelling_is_proved_in_the_default_lane() {
    for (shape, _) in SAFE {
        let name = format!("{shape}_safe_default");
        let rows = neg_rows(&name);
        assert!(!rows.is_empty(), "{name}: the fixture's whole value is its negation rows");
        for vc in rows {
            let result = verdict(&vc);
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "{name}: this negation cannot overflow — the value being negated is a constant \
                 nowhere near INT_MIN, or is bounded away from it by a dominating guard whose \
                 own bound is an unfolded constant expression; got {result:?}"
            );
        }
    }
}

/// And the stronger, separate statement the strict lane actually cares about, in
/// BOTH lanes: a refutation of any of these is a BUILD ERROR on valid Rust.
/// Pinned apart from the proof pin so a future precision loss reads as a precision
/// loss and not as this bug returning.
#[test]
fn no_safe_unfolded_bound_spelling_is_refuted_in_either_lane() {
    for (shape, _) in SAFE {
        for lane in ["default", "release"] {
            let name = format!("{shape}_safe_{lane}");
            for vc in neg_rows(&name) {
                let result = verdict(&vc);
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{name}: this function is safe; a refutation fails the strict compile of \
                     valid Rust: {result:?}"
                );
            }
        }
    }
}

/// Which lane measures what, pinned rather than assumed. `-O` const-folds the
/// four bound spellings into literals, so their release MIR carries no `Neg` and
/// no negation row — the release half of the test above is vacuous for them BY
/// CONSTRUCTION, and that is exactly why the debug lane is where the defect lived.
/// `foldbound` keeps its `-a` in both lanes and so measures both.
#[test]
fn the_release_lane_folds_the_bound_spellings_away() {
    for (shape, survives_opt) in SAFE {
        let name = format!("{shape}_safe_release");
        let rows = neg_rows(&name);
        assert_eq!(
            !rows.is_empty(),
            survives_opt,
            "{name}: release-lane negation rows present = {}, expected {survives_opt} — if this \
             flips, the claim about which lane measures the defect is stale",
            !rows.is_empty()
        );
    }
}

// ---------------------------------------------------------------------------
// UNSAFE twins — the refutations the resolution must not remove.
// ---------------------------------------------------------------------------

/// The negated operand's value in the model, read as the `i128` the machine reads.
///
/// Two spellings, because the two lanes name the operand differently: the Int lane
/// names the local itself (`a`), and the `>= 128`-bit BV lane names the fresh
/// `__trust_ovf_bv_neg_a`. A model names a bitvector by its UNSIGNED bit pattern,
/// so `2^127` IS `i128::MIN` and taking it at face value would turn the witness
/// into a huge positive number.
fn witness_negates_int_min(cex: &Counterexample, width: u32) -> bool {
    let min: i128 = if width >= 128 { i128::MIN } else { -(1i128 << (width - 1)) };
    let min_pattern: u128 = 1u128 << (width - 1);
    cex.assignments.iter().any(|(name, value)| {
        let names_operand = name == "a" || name.starts_with("__trust_ovf_bv_neg_");
        names_operand
            && match value {
                CounterexampleValue::Int(i) => *i == min,
                CounterexampleValue::Uint(u) => *u == min_pattern,
                _ => false,
            }
    })
}

/// THE REGRESSION GUARD. Each twin negates a value that really can be `INT_MIN`,
/// so each must STAY refuted in both lanes, WITH a counterexample.
#[test]
fn every_unsafe_twin_is_still_refuted_with_a_witness() {
    for shape in UNSAFE {
        for lane in ["default", "release"] {
            let name = format!("{shape}_unsafe_{lane}");
            let rows = neg_rows(&name);
            assert!(!rows.is_empty(), "{name}: the twin must still raise negation rows");
            // The twin's subject is the `-a` row. The `foldbound` shapes also negate
            // the bound's own constant (`-(1i64 << 62)`), which is SAFE and correctly
            // proved; select the refutable row by requiring at least one failure and
            // checking every failure's witness below.
            let failures: Vec<VerificationResult> = rows
                .iter()
                .map(verdict)
                .filter(|r| matches!(r, VerificationResult::Failed { .. }))
                .collect();
            assert!(
                !failures.is_empty(),
                "{name}: `-a` really overflows when `a == INT_MIN` and the guard admits it — \
                 this row must stay refuted; verdicts were {:?}",
                rows.iter().map(verdict).collect::<Vec<_>>()
            );
            for f in &failures {
                let VerificationResult::Failed { counterexample, .. } = f else { unreachable!() };
                assert!(
                    counterexample.is_some(),
                    "{name}: and it must still name the values — a refutation without a witness \
                     is not actionable"
                );
            }
        }
    }
}

/// The witnesses must be REAL EXECUTIONS, not artifacts of a dropped fact: the
/// model has to put the NEGATED OPERAND at `INT_MIN`, which is the one input on
/// which the negation actually panics. This is also the check a WRONG fold would
/// fail — resolve `-(1i64 << 62) * 2` to anything but `i64::MIN` and the guard
/// `a >= lim` excludes `i64::MIN`, so no such model exists any more and the row
/// would flip to proved.
#[test]
fn every_unsafe_twin_witness_is_an_execution_that_really_overflows() {
    for shape in UNSAFE {
        let width: u32 = if shape.contains("128") { 128 } else { 64 };
        for lane in ["default", "release"] {
            let name = format!("{shape}_unsafe_{lane}");
            let func = load(&name);
            let mut checked = 0usize;
            for vc in neg_rows(&name) {
                let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc)
                else {
                    continue;
                };
                // THE WITNESS AS DELIVERED, not as the solver returned it
                // (reviewer's second-order finding, 2026-09-19). Measured here:
                // `foldbound128_unsafe`'s raw model names `a = 0` beside
                // `__trust_ovf_bv_neg_a = 2^127` — a fresh bitvector var
                // decoupled from the source name it stands for. The
                // `witness_negates_int_min` check below is satisfied by that
                // FREE var whatever the fold did, so on a declining row it
                // measured nothing. `deliver_counterexample` grounds the model
                // against the function's own definitions first — repairing it
                // from those operand vars where the repair really replays to the
                // panic — so the two assertions below are now about a witness
                // that has been checked. See
                // `tests/counterexample_grounding_realmir.rs`.
                let delivered =
                    trust_vcgen::counterexample_grounding::deliver_counterexample(&func, &cex);
                assert!(
                    trust_vcgen::counterexample_grounding::ground_counterexample(&func, &delivered)
                        .is_grounded(),
                    "{name}: the DELIVERED witness must not contradict the function's own \
                     definitions: {delivered:?}"
                );
                assert!(
                    witness_negates_int_min(&delivered, width),
                    "{name}: the model must negate INT_MIN — that is the only input on which \
                     this negation panics: {delivered:?}"
                );
                checked += 1;
            }
            assert!(checked > 0, "{name}: at least one refutation must carry a witness");
        }
    }
}
