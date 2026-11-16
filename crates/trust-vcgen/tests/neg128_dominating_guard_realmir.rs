// Real-MIR cover for a SPELLING-INDEPENDENT false refutation of valid Rust: the
// 128-bit NEGATION obligation ignored the dominating guard that bounds the
// negated PARAMETER away from `i128::MIN`.
//
//   pub fn litbound_safe(a: i128) -> i128 {
//       if a >= -170141183460469231731687303715884105727i128 { -a } else { 0 }
//   }
//
// The bound is `i128::MIN + 1` written as a PLAIN LITERAL — nothing to fold,
// nothing to resolve — and it EXCLUDES `i128::MIN`, so `-a` cannot overflow on
// the guarded edge. The strict default lane refuted it: `[negation] FAILED
// (ay-in-process); counterexample: __trust_ovf_bv_neg_a = 2^127`. The identical
// shape at `i64` with the identical plain-literal spelling reports `1 proved,
// 0 failed`.
//
// So this is NOT the spelling dependence 5d400f920cf fixed (that one was about
// a bound rustc left UNFOLDED, and it is pinned by
// `tests/unfolded_neg_bound_realmir.rs`). That commit's own `NOT CLAIMED`
// section names this one and its cause: "the Int dominating guard is not
// rendered into the BV neg core".
//
// MEASURED ROOT CAUSE. For a signed width >= 128 the negation VC is emitted in
// pure QF_BV (`checked_vcs::v2_build_assert_negation_vc`,
// `checked_vcs::v2_build_negation_raw_vc` and the hardened twin
// `overflow_vc::v2_hardened_signed_bv_overflow_formula`), because the Int lane's
// `INT_MIN = -2^127` literal does not survive the native `parse_i64` lowering.
// The BV core names the operand with a FRESH var, `__trust_ovf_bv_neg_{base}`,
// deliberately disjoint from the Int-sorted `a` the guard/precondition lanes
// emit — so the dominating `a >= i128::MIN + 1` conjoined around the VC could
// never bind it. The only facts the BV neg core carried were
// `v2_collect_bv_shl_blockdef`'s, which speak about a local DEFINED IN THE BLOCK
// (a defining `Shl`, or a closed constant expression). A PARAMETER has no such
// definition, so the fresh var stayed completely free and `= 2^127` was always a
// model. Every bound spelling failed identically, which is exactly why the
// failure is spelling-INDEPENDENT.
//
// THE FIX. `overflow_vc::v2_bv_neg_dominating_guard_constraints` mines the same
// dominating `operand CMP constant` facts the MULTIPLY lane already mines
// (`v2_dominating_operand_facts`, shared verbatim so the two lanes can never
// drift about WHICH facts hold) and renders them in signed BV on the neg core's
// own fresh var, through the already-sound `v2_bv_guard_constraint` channel.
//
// SOUNDNESS, unchanged from the multiply lane: a fact is used only if it holds
// on EVERY path `v2_build_path_guard_map` records into the assert's block (a
// saturated block records an unguarded path, which empties the intersection),
// it is version-token-checked against the value the negation actually reads, and
// a constant outside the type's range is skipped. A genuinely overflowing
// execution satisfies every conjoined fact and is still refuted — which is what
// the UNSAFE twins below measure.
//
// FIXTURES are a real compiler's own extraction, not hand-written MIR, taken on
// this tree's own stage1 with this change applied (MIR extraction is not
// touched by it):
//
//   rustc --edition 2021 --crate-type lib     -Ztrust-verify=on -Ztrust-policy=advisory \
//         -Ztrust-dump=mir:<dir> neg128_guard_safe.rs
//   rustc --edition 2021 --crate-type lib -O  -Ztrust-verify=on -Ztrust-policy=advisory \
//         -Ztrust-dump=mir:<dir> neg128_guard_safe.rs
//   (and the same two for neg128_guard_unsafe.rs)
//
// HISTORY (2026-09-30 salvage). The first cut of these fixtures was taken on the
// SEALED 2026-09-17 `trust` toolchain, because no stage1 existed in that
// session. Re-extracted here: seven of the eight are the same MIR (four byte for
// byte, three differing only in `span` lines), but `foldbound_safe_release` is
// NOT — the sealed `-O` pipeline folded `lim` to the literal, while this tree's
// `-O` MIR keeps the `Shl`, `Neg` and checked `Mul`/`Add` chain. The fixtures are
// this tree's, so the release lane now exercises the unfolded-bound resolver too.
//
// neg128_guard_safe.rs:
//   pub fn litbound_safe(a: i128) -> i128 {
//       if a >= -170141183460469231731687303715884105727i128 { -a } else { 0 }
//   }
//   pub fn foldbound_safe(a: i128) -> i128 {
//       let lim = -(1i128 << 126) * 2 + 1; // exactly i128::MIN + 1
//       if a >= lim { -a } else { 0 }
//   }
//
// neg128_guard_unsafe.rs — the twins whose negation really CAN overflow
// (`litbound_unsafe`'s bound IS i128::MIN, so it admits it; `unbounded_unsafe`
// has no guard at all):
//   pub fn litbound_unsafe(a: i128) -> i128 {
//       if a >= -170141183460469231731687303715884105728i128 { -a } else { 0 }
//   }
//   pub fn unbounded_unsafe(a: i128) -> i128 { -a }
//
// `litbound_safe` / `litbound_unsafe` differ by ONE in the bound's last digit,
// which is what makes the rendered constant load-bearing rather than the mere
// presence of a fact: a renderer that was off by one, or that wrapped the
// 128-bit bound, would swap their verdicts. `unbounded_unsafe` is the
// adversarial guardrail for the other half — with NO dominating fact to mine the
// operand must stay free and the row must stay refuted.
//
// `foldbound_safe` is carried too because it is the shape where BOTH resolutions
// have to land at once: the closed-constant-expression resolver of 5d400f920cf
// has to turn `-(1i128 << 126) * 2 + 1` into `i128::MIN + 1`, and this commit's
// renderer has to carry that bound onto the parameter's fresh BV var.
use trust_types::{
    ConstValue, Counterexample, CounterexampleValue, Operand, Rvalue, Statement, Ty, UnOp, VcKind,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const SAFE: [&str; 2] = ["litbound", "foldbound"];
const UNSAFE: [&str; 2] = ["litbound", "unbounded"];
const LANES: [&str; 2] = ["default", "release"];

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/neg128_guard_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
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

/// The DEPLOYED backend set, in the compiler's own order — the cheap in-process
/// interval/range backend first, then in-process ay. Mirrors
/// `rustc_mir_transform::trust_verify::discover_router_backends`, and is the same
/// pair `tests/unfolded_neg_bound_realmir.rs` measures on, so the two files'
/// verdicts are comparable.
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

/// Every fixture must still negate a 128-bit SIGNED value under a real
/// `OverflowNeg` assert, and that `Neg` must still raise a negation obligation.
/// With any of the three gone there is nothing here to prove or refute.
#[test]
fn every_fixture_still_negates_a_128_bit_value_in_mir() {
    for (shape, group) in
        SAFE.iter().map(|s| (*s, "safe")).chain(UNSAFE.iter().map(|s| (*s, "unsafe")))
    {
        for lane in LANES {
            let name = format!("{shape}_{group}_{lane}");
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
            let rows = neg_rows(&name);
            assert!(!rows.is_empty(), "{name}: and that `Neg` must still raise negation rows");
            for vc in &rows {
                let VcKind::NegationOverflow { ty } = &vc.kind else { unreachable!() };
                assert_eq!(
                    ty,
                    &Ty::Int { width: 128, signed: true },
                    "{name}: this file is about the 128-bit lane specifically — at <= 64 bits \
                     the negation VC is Int-sorted and the guard already binds it"
                );
            }
        }
    }
}

/// THE SPELLING-INDEPENDENCE CLAIM, stated as a property of the fixtures rather
/// than asserted in prose. The `litbound` pair's bound is a PLAIN LITERAL: there
/// is no `Shl`, no cast and no arithmetic anywhere in its MIR for a
/// constant-expression resolver to fold. So a `litbound_safe` that proves cannot
/// be proving because of 5d400f920cf's resolver — it can only be the dominating
/// guard reaching the BV core, which is what this file adds.
#[test]
fn the_litbound_fixtures_carry_the_bound_as_a_plain_literal() {
    for group in ["safe", "unsafe"] {
        for lane in LANES {
            let name = format!("litbound_{group}_{lane}");
            let func = load(&name);
            let literal_bounds = func
                .body
                .blocks
                .iter()
                .flat_map(|b| b.stmts.iter())
                .filter(|s| {
                    matches!(
                        s,
                        Statement::Assign {
                            rvalue: Rvalue::BinaryOp(_, _, Operand::Constant(ConstValue::Int(_)),),
                            ..
                        }
                    )
                })
                .count();
            assert!(literal_bounds > 0, "{name}: the bound must still be a bare integer literal");
            let computed = func
                .body
                .blocks
                .iter()
                .flat_map(|b| b.stmts.iter())
                .filter(|s| {
                    matches!(
                        s,
                        Statement::Assign {
                            rvalue: Rvalue::BinaryOp(trust_types::BinOp::Shl, ..)
                                | Rvalue::Cast(..),
                            ..
                        }
                    )
                })
                .count();
            assert_eq!(
                computed, 0,
                "{name}: no shift and no cast may appear — with one present this fixture would \
                 be measuring the UNFOLDED-bound defect, which a different file already pins"
            );
        }
    }
}

/// The arithmetic the safe/unsafe split rests on, stated rather than implied by
/// naming. One digit separates the two literals, and it is the digit that decides
/// whether `i128::MIN` is an admitted input.
#[test]
fn the_safe_unsafe_split_is_arithmetic() {
    assert_eq!(
        -170141183460469231731687303715884105727i128,
        i128::MIN + 1,
        "litbound_safe's bound EXCLUDES i128::MIN, so `-a` cannot overflow"
    );
    assert_eq!(
        -170141183460469231731687303715884105728i128,
        i128::MIN,
        "litbound_unsafe's bound ADMITS i128::MIN, so `-a` really panics"
    );
    assert_eq!(-(1i128 << 126) * 2 + 1, i128::MIN + 1, "foldbound_safe's is the same bound");
}

// ---------------------------------------------------------------------------
// SAFE — the false refutation.
// ---------------------------------------------------------------------------

/// THE REPORT. A refutation of any of these rows is a strict BUILD ERROR on valid
/// Rust, in either lane.
///
/// This is deliberately pinned as NOT-REFUTED rather than as PROVED. The deployed
/// pair decides these rows on the INTERVAL backend, which evaluates the
/// obligation's Int-sorted SUBJECT `{base}` in place of its bit-vector alias
/// `__trust_ovf_bv_neg_{base}` (`prove_neg_no_overflow` in
/// `trust-router/src/interval_backend.rs`; until 2026-11-09 `bound_of` gave the
/// alias `{base}`'s recorded bound instead, and WRAPPING-SUB-AND-INTERVAL-NEG-1
/// removed that because the alias's own bit-vector definitions are read unsigned,
/// which proved `-(1i128 << amt)` for `amt < 128`); in-process ay declines them (it rejects
/// its own UNSAT proof of a mixed Int + BV query — `incomplete
/// self-check-rejected`). (Corrected 2026-10-01: the 2026-09-21 text said ay
/// decided them and the interval backend declined a `BvSLe`; the commit's own
/// mutation measurement — remove the alias and this file's router-level `Proved` pin
/// turns Unknown — says the opposite.) A future precision loss in either should read
/// as a precision loss — not as this bug returning.
#[test]
fn no_safe_128_bit_guarded_negation_is_refuted_in_either_lane() {
    for shape in SAFE {
        for lane in LANES {
            let name = format!("{shape}_safe_{lane}");
            let rows = neg_rows(&name);
            assert!(!rows.is_empty(), "{name}: the fixture's whole value is its negation rows");
            for vc in rows {
                let result = verdict(&vc);
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{name}: the dominating guard bounds this parameter away from i128::MIN, so \
                     the negation cannot overflow; a refutation fails the strict compile of \
                     valid Rust: {result:?}"
                );
            }
        }
    }
}

/// And the stronger statement, kept separate so the two can move independently:
/// every safe row is PROVED BY THE ROUTER today — a crate-level verdict. It carries no
/// proof authority in the compiler: the interval backend's `Proved` is not a kernel
/// or native proof, so the compiler reports these rows `runtime-checked` ("solver
/// interval reported Proved without exact kernel/native proof authority") where the
/// row has a runtime check, exactly as it would an Unknown. (Renamed 2026-10-01 from
/// `every_safe_128_bit_guarded_negation_is_proved_today`, whose name read as a
/// compiler verdict.) Measured, not assumed — if a future change makes one of these
/// merely Unknown at the router the pin above still holds and this one reports the
/// change precisely.
#[test]
fn every_safe_128_bit_guarded_negation_is_router_proved_without_authority() {
    for shape in SAFE {
        for lane in LANES {
            let name = format!("{shape}_safe_{lane}");
            for vc in neg_rows(&name) {
                let result = verdict(&vc);
                assert!(
                    matches!(result, VerificationResult::Proved { .. }),
                    "{name}: expected the guarded 128-bit negation to be proved; got {result:?}"
                );
            }
        }
    }
}

/// THE OTHER HALF, pinned on its own lane. The two arms of this fix are
/// independent and BOTH are load-bearing, so each is measured where it is the
/// only one that can act.
///
/// This one is the vcgen arm: the SMT lane alone, with the interval backend
/// removed. Without the BV-rendered guard the formula is genuinely SATISFIABLE —
/// the neg core's fresh var is free — and ay REFUTES it (measured: `Failed`, with
/// `__trust_ovf_bv_neg_a = 2^127`). With the guard rendered it is UNSAT, and ay
/// stops refuting.
///
/// It is pinned as NOT-REFUTED rather than as proved because the row that reaches
/// ay is a MIXED Int + BV query by construction (the BV violation core plus the
/// row's Int-sorted path facts), and in-process ay's strict self-certification
/// rejects an UNSAT proof of any mixed query — `incomplete self-check-rejected`,
/// measured, and the same reason the signed-128 MULTIPLY lane routes its rows to
/// the interval backend. A refutation and an undecided row are not the same
/// defect: the first accuses valid Rust, the second declines to decide it.
#[test]
fn no_safe_128_bit_guarded_negation_is_refuted_by_the_smt_lane_alone() {
    let ay_only =
        || trust_router::Router::with_backends(vec![Box::new(test_router::test_ay_backend())]);
    for shape in SAFE {
        for lane in LANES {
            let name = format!("{shape}_safe_{lane}");
            for vc in neg_rows(&name) {
                let result = ay_only()
                    .verify_all(std::slice::from_ref(&vc))
                    .into_iter()
                    .next()
                    .expect("one verdict")
                    .1;
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{name}: with the dominating guard rendered into the BV neg core the \
                     violation formula is UNSAT, so the SMT lane must not refute it: {result:?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// UNSAFE twins — the refutations the new facts must not remove.
// ---------------------------------------------------------------------------

/// The negated operand's value in the model, read as the `i128` the machine
/// reads. The `>= 128`-bit lane names the operand with its fresh
/// `__trust_ovf_bv_neg_a` alias; a model names a bitvector by its UNSIGNED bit
/// pattern, so `2^127` IS `i128::MIN` and taking it at face value would turn the
/// witness into a huge positive number.
fn witness_negates_int_min(cex: &Counterexample) -> bool {
    let min_pattern: u128 = 1u128 << 127;
    cex.assignments.iter().any(|(name, value)| {
        let names_operand = name == "a" || name.starts_with("__trust_ovf_bv_neg_");
        names_operand
            && match value {
                CounterexampleValue::Int(i) => *i == i128::MIN,
                CounterexampleValue::Uint(u) => *u == min_pattern,
                _ => false,
            }
    })
}

/// THE REGRESSION GUARD. `litbound_unsafe`'s guard admits `i128::MIN` and
/// `unbounded_unsafe` has no guard at all, so both must STAY refuted, in both
/// lanes, WITH a counterexample.
#[test]
fn every_unsafe_twin_is_still_refuted_with_a_witness() {
    for shape in UNSAFE {
        for lane in LANES {
            let name = format!("{shape}_unsafe_{lane}");
            let rows = neg_rows(&name);
            assert!(!rows.is_empty(), "{name}: the twin must still raise negation rows");
            let failures: Vec<VerificationResult> = rows
                .iter()
                .map(verdict)
                .filter(|r| matches!(r, VerificationResult::Failed { .. }))
                .collect();
            assert!(
                !failures.is_empty(),
                "{name}: `-a` really overflows at `a == i128::MIN` and nothing here excludes it — \
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
/// model has to put the NEGATED OPERAND at `i128::MIN`, the one input on which
/// this negation panics. This is also the check an OFF-BY-ONE rendering would
/// fail — render `litbound_unsafe`'s bound as `i128::MIN + 1` and no such model
/// exists any more, so the row would flip to proved.
#[test]
fn every_unsafe_twin_witness_is_an_execution_that_really_overflows() {
    for shape in UNSAFE {
        for lane in LANES {
            let name = format!("{shape}_unsafe_{lane}");
            let func = load(&name);
            let mut checked = 0usize;
            for vc in neg_rows(&name) {
                let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc)
                else {
                    continue;
                };
                // The witness AS DELIVERED, not as the solver returned it: the
                // fresh BV operand var is decoupled from the source name it
                // stands for, so a raw model can name `a = 0` beside
                // `__trust_ovf_bv_neg_a = 2^127`. `deliver_counterexample`
                // grounds the model against the function's own definitions
                // first.
                let delivered =
                    trust_vcgen::counterexample_grounding::deliver_counterexample(&func, &cex);
                assert!(
                    trust_vcgen::counterexample_grounding::ground_counterexample(&func, &delivered)
                        .is_grounded(),
                    "{name}: the DELIVERED witness must not contradict the function's own \
                     definitions: {delivered:?}"
                );
                assert!(
                    witness_negates_int_min(&delivered),
                    "{name}: the model must negate i128::MIN — that is the only input on which \
                     this negation panics: {delivered:?}"
                );
                checked += 1;
            }
            assert!(checked > 0, "{name}: at least one refutation must carry a witness");
        }
    }
}

// ---------------------------------------------------------------------------
// 2026-10-01 — the shapes the lane's SOUNDNESS argument rests on, and the two the
// retired miner could not reach.
//
// The dominating-guard facts of this lane come from `generate::dominating_facts`
// (edge dominance + SSA value identity; it replaced the per-row path miner, which
// compared reaching-def SETS — see `tests/dominating_guard_value_identity_realmir.rs`
// for the false proof that comparison allowed). Review of 526791345b6 asked for the
// gates that argument rests on to be pinned on THIS lane, not only on the multiply
// lane's fixtures. Each STALE twin below has a guard that really bounds SOME value away
// from `i128::MIN` — but not the value the negation reads — so each `-a` really
// overflows:
//
// neg128_guard_stale.rs:
//   pub fn stale_reassign(mut a: i128, b: i128) -> i128 {         // a = b after the guard
//       if a >= -170141183460469231731687303715884105727i128 { a = b; -a } else { 0 }
//   }
//   pub fn copy_stale(mut a: i128, b: i128) -> i128 {             // the guard tests a copy
//       let g = a; a = b;                                         // taken before the write
//       if g >= -170141183460469231731687303715884105727i128 { -a } else { 0 }
//   }
//   pub fn loop_stale(mut a: i128, n: u32) -> i128 {              // written after the guard,
//       let mut r = 0; let mut i = 0;                             // in the same iteration
//       while i < n { if a > -5 { a = a.wrapping_sub(i128::MAX); r = -a; } i += 1; }
//       r
//   }
//   pub fn loop_kill(mut a: i128, c: bool, c2: bool) -> i128 {    // equal reaching SETS at
//       loop {                                                    // the guard and the use,
//           if a >= -5 {                                          // different VALUES
//               if c { a = i128::MIN; if c2 { continue; } }
//               return -a;
//           } else { return 0; }
//       }
//   }
//   pub fn or_join(a: i128, c: bool) -> i128 { if c || a >= -5 { -a } else { 0 } }
//   pub fn false_edge(a: i128) -> i128 { if !(a > -5) { -a } else { 0 } }
//   pub fn switch_otherwise(a: i128) -> i128 { match a { 0 => 1, 1 => 2, _ => -a } }
//
// and two SAFE shapes the retired miner refuted or could not reach:
//
// neg128_guard_shapes_safe.rs:
//   pub fn diamonds_7(a: i128, c0: bool, .., c6: bool) -> (i128, u8) {
//       let mut z: u8 = 0;
//       if a >= -170141183460469231731687303715884105727i128 {
//           if c0 { z = 1; } else { z = 100; }
//           /* six more two-way diamonds on c1..c6 */
//           (-a, z)                                // 2^7 = 128 paths into the negation
//       } else { (0, z) }
//   }
//   pub fn loop_fresh(mut a: i128, n: u32) -> i128 {   // the guard tests the value each
//       let mut r = 0; let mut i = 0;                  // iteration negates
//       while i < n { if a > -5 { r = -a; } a = a.wrapping_sub(3); i += 1; }
//       r
//   }
//
// `diamonds_7` is the cap's shape: past `MAX_PATHS_PER_BLOCK` (64) the retired miner's
// block recorded one unguarded path, its intersection emptied, and valid Rust was a
// strict BUILD ERROR at 7 diamonds (not at 6). Edge dominance enumerates no path.
//
// Fixtures: this tree's stage1, both lanes, as for the files above.
// ---------------------------------------------------------------------------

const STALE: [&str; 7] = [
    "stale_reassign",
    "copy_stale",
    "loop_stale",
    "loop_kill",
    "or_join",
    "false_edge",
    "switch_otherwise",
];
const SHAPES_SAFE: [&str; 2] = ["diamonds_7", "loop_fresh"];

/// The BV fact atoms on the negated operand's fresh var — every
/// `__trust_ovf_bv_neg_* CMP constant` comparison but the violation goal itself — as
/// `(comparison, constant, operand on the left)`.
fn neg_operand_facts(vc: &VerificationCondition) -> Vec<(String, i128, bool)> {
    use trust_types::Formula;
    fn walk(f: &Formula, out: &mut Vec<(String, i128, bool)>) {
        let operand = |f: &Formula| matches!(f, Formula::Var(name, _) if name.starts_with("__trust_ovf_bv_neg_"));
        let constant = |f: &Formula| match f {
            Formula::BitVec { value, .. } => Some(*value),
            _ => None,
        };
        let mut atom = |kind: &str, a: &Formula, b: &Formula| -> bool {
            match (operand(a), constant(b), constant(a), operand(b)) {
                (true, Some(c), _, _) => {
                    out.push((kind.to_string(), c, true));
                    true
                }
                (_, _, Some(c), true) => {
                    out.push((kind.to_string(), c, false));
                    true
                }
                _ => false,
            }
        };
        let handled = match f {
            Formula::BvSLt(a, b, _) => atom("slt", a, b),
            Formula::BvSLe(a, b, _) => atom("sle", a, b),
            _ => false,
        };
        if !handled {
            for child in f.children() {
                walk(child, out);
            }
        }
    }
    let mut out = Vec::new();
    walk(&vc.formula, &mut out);
    out
}

/// Does every fact atom ADMIT the operand value `i128::MIN`? (The violation goal is an
/// `Eq`, not collected; every collected atom is a mined bound.)
fn facts_admit_int_min(facts: &[(String, i128, bool)]) -> bool {
    let x = i128::MIN;
    facts.iter().all(|(kind, c, operand_left)| match (kind.as_str(), operand_left) {
        ("slt", true) => x < *c,
        ("sle", true) => x <= *c,
        ("slt", false) => *c < x,
        ("sle", false) => *c <= x,
        _ => true,
    })
}

/// Anti-vacuity for the new fixtures: each still negates a 128-bit signed value.
#[test]
fn every_new_fixture_still_raises_128_bit_negation_rows() {
    for name in
        STALE.iter().map(|s| format!("{s}")).chain(SHAPES_SAFE.iter().map(|s| format!("{s}")))
    {
        for lane in LANES {
            let rows = neg_rows(&format!("{name}_{lane}"));
            assert!(!rows.is_empty(), "{name} {lane}: the fixture's value is its negation rows");
        }
    }
}

/// THE SOUNDNESS PIN, independent of any solver: on every stale twin, in both lanes,
/// no mined fact excludes `i128::MIN` from the negated operand — the value on which each
/// of these negations really panics. A stale fact here is a false hypothesis, and with
/// it the row is UNSAT on a program that overflows.
#[test]
fn no_stale_guard_fact_reaches_a_negation_that_really_overflows() {
    for name in STALE {
        for lane in LANES {
            for vc in neg_rows(&format!("{name}_{lane}")) {
                let facts = neg_operand_facts(&vc);
                assert!(
                    facts_admit_int_min(&facts),
                    "{name} {lane}: a guard fact about a value this negation does not read \
                     excludes i128::MIN, on which `-a` really overflows: {facts:?}"
                );
            }
        }
    }
}

/// And the deployed pair never PROVES one of them.
#[test]
fn no_stale_twin_is_proved() {
    for name in STALE {
        for lane in LANES {
            for vc in neg_rows(&format!("{name}_{lane}")) {
                let result = verdict(&vc);
                assert!(
                    !matches!(result, VerificationResult::Proved { .. }),
                    "{name} {lane}: `-a` really overflows at i128::MIN: {result:?}"
                );
            }
        }
    }
}

/// THE CAP AND THE LOOP, closed for safe code: the guard's bound reaches the negated
/// operand through 2^7 paths and across a loop, and no row is refuted.
#[test]
fn the_guard_reaches_the_negation_past_the_retired_path_cap_and_across_a_loop() {
    for name in SHAPES_SAFE {
        for lane in LANES {
            let rows = neg_rows(&format!("{name}_{lane}"));
            for vc in &rows {
                let facts = neg_operand_facts(vc);
                assert!(
                    !facts_admit_int_min(&facts),
                    "{name} {lane}: the dominating guard excludes i128::MIN and must reach the \
                     negation's BV core: {facts:?}"
                );
                let result = verdict(vc);
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{name} {lane}: the guard bounds this operand away from i128::MIN; a \
                     refutation is a strict build error on valid Rust: {result:?}"
                );
            }
        }
    }
}

/// The refutations of the stale twins stand, and what they DELIVER is honest: a
/// replayable witness, or the `UNGROUNDED` label — and the label must not send the
/// reader after a bound to respell, because every bound here is a plain literal that
/// folds (review of cf9ce551b45: `stale_reassign` used to be told to "spell the bound
/// so it folds exactly").
#[test]
fn a_stale_twins_label_does_not_advise_respelling_a_bound_that_folds() {
    for name in ["stale_reassign", "copy_stale", "loop_stale"] {
        for lane in LANES {
            let func = load(&format!("{name}_{lane}"));
            let mut refuted = 0usize;
            for vc in neg_rows(&format!("{name}_{lane}")) {
                let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc)
                else {
                    continue;
                };
                refuted += 1;
                let delivered =
                    trust_vcgen::counterexample_grounding::deliver_counterexample(&func, &cex);
                let rendered = delivered.to_string();
                assert!(
                    !rendered.contains("spell the bound"),
                    "{name} {lane}: every bound folds; the label must not advise respelling \
                     one: {rendered}"
                );
                if rendered.contains(trust_vcgen::counterexample_grounding::UNGROUNDED_LABEL) {
                    for needle in ["REFUTATION stands", "stands on its own", "FIX:"] {
                        assert!(rendered.contains(needle), "{name} {lane}: `{needle}`: {rendered}");
                    }
                }
            }
            assert!(refuted > 0, "{name} {lane}: the overflow must be refuted with a model");
        }
    }
}
