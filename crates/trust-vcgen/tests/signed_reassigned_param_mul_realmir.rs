// Real-MIR cover for the SIGNED twin of the `g7` false refutation: valid Rust
// rejected by a strict build because a SIGNED multiply's operands carried no
// bound at all.
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
//   pub fn sgn_mut(a: i64, mut b: i64) -> i64 {
//       if a > -1000 && a < 1000 && b > -1000 && b < 1000 { b = a * b; }
//       b
//   }
//
// `|a * b| < 10^6`, so the multiply cannot overflow an `i64`. It was REFUTED in
// the `-O` lane. 5445c64d21b fixed the UNSIGNED `var * var` arm; its own
// still_open named this file's subject.
//
// THREE causes, one per shape, all in the operand-fact miner:
//
//  1. TARGET SELECTION (`-O`, every shape here). The `-O` lowering multiplies the
//     REASSIGNED PARAMETER ITSELF —
//
//       bb2: _6 = copy _2; _5 = Gt(move _6, -1000); switch ..
//       bb3: _8 = copy _2; _7 = Lt(move _8, 1000);  switch ..
//       bb4: _9 = CheckedBinaryOp(Mul, copy _1, copy _2)
//
//     — and `v2_mul_dominating_operand_facts` skipped any operand local that
//     `guards::value_local_is_unstable` flagged. A `mut` parameter is flagged by
//     that predicate's definition, so `b` was never a TARGET: it got no bound of
//     any kind, its fresh BV var stayed free, and ay refuted the row at
//     `b = i64::MIN`. `v2_local_unstable_only_by_plain_stores` is the split that
//     keeps the alias-escape half of that gate and drops the
//     reassignment-only half — the half whose staleness this caller already
//     re-checks, exactly, with the version-token oracle.
//
//  2. THE CROSS-BLOCK COPY (`sgn_mut_via_local`, BOTH lanes). The guard's copy of
//     the parameter can be made once, in an earlier block —
//
//       bb0: _3 = copy _2                     <- `let g = b;`
//       bb2: _6 = Gt(copy _3, -1000); ..      <- the guards read `g`
//       bb4: _8 = copy _2; _9 = CheckedBinaryOp(Mul, copy _1, copy _8)
//
//     — which `v2_live_copy_source_name` could not see, because it only scanned
//     the reading block's own statements. `v2_live_copy_source_name_reaching`
//     resolves it through the version oracle: the use point's token must be the
//     one that copy statement mints, which is a reaching-definition check, and
//     the copied-from value must still be live.
//
//  3. THE INT RENDERING OF THE FACTS (`sgn_mut`, DEBUG lane). Even with the facts
//     mined, the signed row was left at `Unknown`: the deployed interval backend
//     decides a signed multiply in `prove_bv_smul_no_overflow`, by INTERVAL
//     ARITHMETIC over the four corners of the two operand boxes, and it builds
//     those boxes by looking the operand's NUMERIC bounds up in its INT
//     environment — it never reads a `BvSlt` atom as a bound. The signed arm
//     rendered the dominating facts in BV only.
//
// The four-corner product is the TWO-SIDED reasoning a signed multiply needs, and
// it is why the one-sided twin is not proved by accident: bound only the upper
// side and the operand's box is still infinite below, the product interval is
// unbounded, and the backend declines.
//
// Fixtures are the stage1 compiler's OWN extraction, both lanes:
//
//   rustc --edition 2021 --crate-type lib     -Ztrust-dump=mir:<dir> sgn.rs
//   rustc --edition 2021 --crate-type lib -O  -Ztrust-dump=mir:<dir> sgn.rs
//
// SAFE (must never be refuted; all six are PROVED by the deployed backend set in
// both lanes):
//   * `sgn_mut`           the report.
//   * `sgn_nomut`         control: same arithmetic, parameter NOT reassigned.
//                         Was `runtime_checked`, never refuted — kept so a
//                         regression in the shape that always worked is visible.
//   * `sgn_mut_via_local` the cross-block copy; refuted in BOTH lanes before.
//   * `sgn_mut_lhs`       the LHS is the reassigned parameter.
//   * `sgn_mut_neg`       both operands strictly NEGATIVE (`-1000 <= x <= -1`):
//                         the product is POSITIVE and neither operand's bound
//                         alone bounds it. The genuinely two-sided shape.
//   * `sgn_mut_pow31`     `|a| <= 2^31` and `|b| <= 2^31` give `|a*b| <= 2^62`,
//                         which fits `i64`. See `the_pow31_pow32_split_is_arithmetic`:
//                         for a SIGNED 64-bit product 2^31 is the SAFE side of the
//                         corner and 2^32 the unsafe one (the unsigned file's
//                         `g7_pow32` twin is at 2^32 because `2^32 * 2^32 = 2^64`
//                         is one bit past `u64::MAX`; `2^31 * 2^31 = 2^62` is a
//                         whole bit inside `i64::MAX`).
//
// UNSAFE twins (must STAY refuted, each with a model that is a real execution):
//   * `sgn_onesided`    `if a < 1000 && b < 1000` — nothing bounds either operand
//                       from BELOW, and two large negatives overflow.
//   * `sgn_wrongvar`    the guard bounds `c`, not the multiplied `b`.
//   * `sgn_writebefore` `b` is overwritten AFTER the guard read it and BEFORE the
//                       multiply.
//   * `sgn_pow32`       `|a|,|b| <= 2^32` does not bound an `i64` product.
//   * `sgn_loop`        the guard holds on ENTRY and the loop rewrites `b` past
//                       it — the shape a reaching-definition check must refuse,
//                       because the use inside the body is reached by the
//                       pre-loop value AND by the loop's own `b = a * b`.
//
// The last two are the cross-block hop's OWN twins — the two ways the reaching
// resolution above could be wrong, one per version check it makes:
//   * `sgn_via_local_stale`     `let g = b; b = c;` before the guard. `g == b` WAS
//                               true and is not any more, so the guard on `g` says
//                               nothing about the multiplied value. Refused by the
//                               SRC check (`b`'s token moved between the copy and
//                               the multiply).
//   * `sgn_via_local_two_defs`  `let mut g = b; if t { g = c; }`. On one path `g`
//                               is `c`, so no copy of `b` is the sole definition
//                               reaching the guard. MEASURED: the reaching-def
//                               check is NOT what refuses this one — `g`'s reaching
//                               set at the guard is the two-element join
//                               `{s0_0, s1_0}`, so the version renamer spells the
//                               guard's subject `g#s0_0_s1_0` and the resolver,
//                               which matches on the BARE place name, finds no
//                               candidate at all. It is pinned because the verdict
//                               is the one that matters, and stated here because a
//                               twin whose mechanism you have not measured is not
//                               evidence for the mechanism you assumed.
//   * `sgn_via_local_restated`  `let mut g = b; g = c;` — the live definition
//                               reaching the guard is `g = c` and the FIRST one in
//                               the body is `g = b`. Written to isolate the
//                               reaching-def check, and MEASURED not to: `g` is
//                               spelled `g#s0_1` here too, so the renamer severs
//                               this one as well.
//
// SO, MEASURED AND STATED PLAINLY, because it is the kind of thing a later reader
// would otherwise assume the other way: of the two version conditions in
// `v2_live_copy_source_name_reaching`, only the SRC one is discriminated by a twin
// in this file. Removing it makes `sgn_via_local_stale` PROVED — a kernel-eligible
// proof of a program that really overflows. Removing the REACHING-DEF condition
// changes no verdict in this file, in either lane, because the version RENAMER
// reaches the same hazard first: a local with more than one reaching definition is
// spelled `g#<join>` in the guard formula, and the resolver matches on the bare
// place name, so it finds no candidate at all. The condition is kept anyway — it is
// the resolver's own contract, and making it depend instead on which names another
// pass chose to decorate is a coupling no document states.
use trust_types::{
    Counterexample, CounterexampleValue, Operand, Rvalue, Statement, VcKind, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const SAFE: [&str; 6] = ["mut", "nomut", "via_local", "lhs", "neg", "pow31"];
const UNSAFE: [&str; 8] = [
    "onesided",
    "wrongvar",
    "writebefore",
    "pow32",
    "loop",
    "via_local_stale",
    "via_local_two_defs",
    "via_local_restated",
];

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/signed_param_mul_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn mul_rows(name: &str) -> Vec<VerificationCondition> {
    let rows: Vec<VerificationCondition> = trust_vcgen::generate_vcs(&load(name))
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if format!("{op:?}") == "Mul")
        })
        .collect();
    assert!(!rows.is_empty(), "{name}: the fixture's whole value is its `Mul` overflow row");
    rows
}

/// The DEPLOYED backend set, in the compiler's own order: the cheap in-process
/// interval/range backend first, then in-process ay. Mirrors
/// `rustc_mir_transform::trust_verify::discover_router_backends`; the bare
/// `deterministic_in_process_ay` router used elsewhere in this directory omits
/// the interval lane, which is the ONLY lane that decides a guard-bounded signed
/// multiply (`prove_bv_smul_no_overflow`), so it would report `Unknown` for every
/// row this file pins as proved.
fn router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(test_router::test_ay_backend()),
    ])
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// The model's value for the multiply's `role` operand, read as the `i64` the
/// machine reads. The overflow row's operands are the fresh
/// `__trust_ovf_bv_{role}_{base}` bitvector vars, and a model names a bitvector by
/// its UNSIGNED bit pattern — so `9223372036854775808` IS `i64::MIN`, and taking
/// it at face value would silently turn every negative witness into a huge
/// positive one. `{base}` differs between the lanes (`_9` in debug, `b` under
/// `-O`), which is why this matches on the role PREFIX.
fn bv_operand_i64(cex: &Counterexample, role: &str) -> Option<i64> {
    let prefix = format!("__trust_ovf_bv_{role}_");
    cex.assignments.iter().find(|(n, _)| n.starts_with(&prefix)).and_then(|(_, v)| match v {
        CounterexampleValue::Uint(u) => Some(*u as i64),
        CounterexampleValue::Int(i) => i64::try_from(*i).ok(),
        _ => None,
    })
}

/// The witnessed operand pair, or a panic naming the model that failed to carry
/// one.
fn witness_operands(name: &str, cex: &Counterexample) -> (i64, i64) {
    let lhs = bv_operand_i64(cex, "lhs")
        .unwrap_or_else(|| panic!("{name}: the model must name the lhs operand: {cex:?}"));
    let rhs = bv_operand_i64(cex, "rhs")
        .unwrap_or_else(|| panic!("{name}: the model must name the rhs operand: {cex:?}"));
    (lhs, rhs)
}

/// Does this pair really overflow an `i64` multiply? `i64::checked_mul` is the
/// exact machine question the `Assert(Overflow(Mul))` asks, so this is the
/// property, not a proxy for it.
fn really_overflows_i64(a: i64, b: i64) -> bool {
    a.checked_mul(b).is_none()
}

fn blocks_defining(func: &VerifiableFunction, local: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for b in &func.body.blocks {
        for (k, stmt) in b.stmts.iter().enumerate() {
            if let Statement::Assign { place, .. } = stmt
                && place.local == local
                && place.projections.is_empty()
            {
                out.push((b.id.0, k));
            }
        }
    }
    out
}

/// The `(block, operand locals)` of the fixture's `CheckedBinaryOp(Mul, ..)`.
fn mul_site(func: &VerifiableFunction) -> (usize, Vec<usize>) {
    for b in &func.body.blocks {
        for stmt in &b.stmts {
            if let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(op, l, r), .. } = stmt
                && format!("{op:?}") == "Mul"
            {
                let locals = [l, r]
                    .into_iter()
                    .filter_map(|o| match o {
                        Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                        _ => None,
                    })
                    .collect();
                return (b.id.0, locals);
            }
        }
    }
    panic!("fixture must contain a CheckedBinaryOp(Mul, ..)");
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY — the fixtures must still be the shapes this file is about.
// ---------------------------------------------------------------------------

/// The `-O` fixture of the report must still multiply the REASSIGNED PARAMETER
/// ITSELF. That is the whole subject of cause 1: were rustc's `-O` lowering to
/// drift and introduce a copy, every `_release` row below would pass through the
/// same-block hop that already existed and would say nothing about the target
/// gate.
#[test]
fn the_release_fixtures_still_multiply_the_reassigned_parameter_directly() {
    for shape in ["mut", "lhs", "neg", "pow31", "via_local"] {
        let name = format!("{shape}_safe_release");
        let func = load(&name);
        let (mul_block, operands) = mul_site(&func);
        let reassigned: Vec<usize> =
            (1..=func.body.arg_count).filter(|&l| blocks_defining(&func, l).len() >= 1).collect();
        assert!(
            !reassigned.is_empty(),
            "{name}: the shape is a REASSIGNED parameter; the fixture must store to one"
        );
        assert!(
            operands.iter().any(|l| reassigned.contains(l)),
            "{name}: the multiply must read the reassigned parameter's own local \
             (operands {operands:?}, reassigned params {reassigned:?}) — a copy here \
             would make this row a test of the same-block hop instead"
        );
        assert!(
            !blocks_defining(&func, operands[operands.len() - 1])
                .iter()
                .any(|&(b, _)| b == mul_block),
            "{name}: and nothing may redefine that operand inside the multiply's own block"
        );
    }
}

/// The DEBUG fixture of the report must still carry the per-guard COPY: it is the
/// same-block hop's own shape, and it is what makes the debug and `-O` rows
/// genuinely different measurements rather than one measurement twice.
#[test]
fn the_debug_fixtures_still_carry_a_per_guard_copy_of_the_parameter() {
    for shape in ["mut", "lhs", "neg", "pow31"] {
        let name = format!("{shape}_safe_default");
        let func = load(&name);
        let copies = func
            .body
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .filter(|stmt| {
                matches!(
                    stmt,
                    Statement::Assign {
                        rvalue: Rvalue::Use(Operand::Copy(_) | Operand::Move(_)),
                        ..
                    }
                )
            })
            .count();
        assert!(
            copies >= 2,
            "{name}: the debug lowering must still keep a per-guard copy AND the \
             multiply's own copy of the reassigned parameter; found {copies}"
        );
    }
}

/// `sgn_mut_via_local`'s guard subject `g` must still be defined in a block that
/// contains NO guard reading it — cause 2's whole shape. If rustc were to sink
/// `let g = b;` into the guard blocks, the same-block resolver would already
/// answer and the cross-block hop would never be exercised.
#[test]
fn via_local_still_establishes_its_guard_subject_in_an_earlier_block() {
    for lane in ["default", "release"] {
        let name = format!("via_local_safe_{lane}");
        let func = load(&name);
        // `g` is the only non-parameter local defined by a pure copy of a parameter.
        let g = func
            .body
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter().map(move |s| (b.id.0, s)))
            .find_map(|(bid, stmt)| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                    ..
                } if place.projections.is_empty()
                    && place.local > func.body.arg_count
                    && src.projections.is_empty()
                    && src.local <= func.body.arg_count =>
                {
                    Some((place.local, bid))
                }
                _ => None,
            });
        let (g_local, g_block) =
            g.unwrap_or_else(|| panic!("{name}: the `let g = b;` copy must still be in the MIR"));
        let guard_blocks: Vec<usize> = func
            .body
            .blocks
            .iter()
            .filter(|b| {
                b.stmts.iter().any(|stmt| {
                    matches!(stmt, Statement::Assign { rvalue: Rvalue::BinaryOp(_, l, r), .. }
                        if [l, r].into_iter().any(|o| matches!(o,
                            Operand::Copy(p) | Operand::Move(p) if p.local == g_local)))
                })
            })
            .map(|b| b.id.0)
            .collect();
        assert!(
            guard_blocks.len() >= 2,
            "{name}: `g` must still be the subject of both of its guards, found {guard_blocks:?}"
        );
        assert!(
            !guard_blocks.contains(&g_block),
            "{name}: `g` is established in bb{g_block} and read by guards in {guard_blocks:?} — \
             they must stay DIFFERENT blocks, or this fixture stops testing the cross-block hop"
        );
    }
}

/// The `pow31` / `pow32` split is an ARITHMETIC fact about a signed 64-bit
/// product, not a labelling choice — and it does NOT sit where the unsigned
/// file's `g7_pow32` twin sits. Stated here so that if either fixture is ever
/// retuned, the claim it rests on is in the file.
#[test]
fn the_pow31_pow32_split_is_arithmetic() {
    let pow31: i128 = 1 << 31;
    let pow32: i128 = 1 << 32;
    let imax = i64::MAX as i128;
    let imin = i64::MIN as i128;
    assert!(pow31 * pow31 <= imax, "|a|,|b| <= 2^31 keeps the product inside i64::MAX");
    assert!(-(pow31 * pow31) >= imin, "and inside i64::MIN");
    assert!(pow32 * pow32 > imax, "|a|,|b| <= 2^32 does NOT: 2^64 is past i64::MAX");
}

/// The one-sided twin must still be one-sided: its guards must bound the operands
/// only from ABOVE. A guard drift that added a lower bound would make it safe and
/// the refutation below would be wrong to demand.
#[test]
fn the_onesided_twin_still_has_no_lower_bound() {
    for lane in ["default", "release"] {
        let name = format!("onesided_unsafe_{lane}");
        let func = load(&name);
        let mut ops = Vec::new();
        for b in &func.body.blocks {
            for stmt in &b.stmts {
                if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), .. } = stmt {
                    ops.push(format!("{op:?}"));
                }
            }
        }
        assert!(ops.iter().any(|o| o == "Lt"), "{name}: must still carry its `< 1000` guards");
        assert!(
            !ops.iter().any(|o| o == "Gt" || o == "Ge"),
            "{name}: a lower bound would make this function SAFE; found {ops:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// SAFE — the false refutation, in both lanes.
// ---------------------------------------------------------------------------

/// THE REPORT, and the five shapes around it. Every safe signed
/// reassigned-parameter multiply here is PROVED by the deployed backend set, in
/// BOTH lanes — not merely left un-refuted.
#[test]
fn every_safe_signed_shape_is_proved_in_both_lanes() {
    for shape in SAFE {
        for lane in ["default", "release"] {
            let name = format!("{shape}_safe_{lane}");
            for vc in mul_rows(&name) {
                let result = verdict(&vc);
                assert!(
                    matches!(result, VerificationResult::Proved { .. }),
                    "{name}: this signed multiply is bounded on BOTH sides by dominating \
                     guards, so its four-corner product fits i64; got {result:?}"
                );
            }
        }
    }
}

/// And the stronger, separate statement the strict lane actually cares about: a
/// refutation of any of them is a BUILD ERROR on valid Rust. Pinned apart from
/// the proof pin so that a future precision loss reads as a precision loss and
/// not as this bug returning.
#[test]
fn no_safe_signed_shape_is_refuted_in_either_lane() {
    for shape in SAFE {
        for lane in ["default", "release"] {
            let name = format!("{shape}_safe_{lane}");
            for vc in mul_rows(&name) {
                let result = verdict(&vc);
                assert!(
                    !matches!(result, VerificationResult::Failed { .. }),
                    "{name}: this function is safe; a refutation fails the strict compile \
                     of valid Rust: {result:?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// UNSAFE twins — the refutations the relaxation must not remove.
// ---------------------------------------------------------------------------

/// THE REGRESSION GUARD for the target-gate relaxation and both copy hops. Each
/// twin is a genuine `i64` multiply overflow and must still be REFUTED, in both
/// lanes, WITH a counterexample.
#[test]
fn every_unsafe_signed_twin_is_still_refuted_with_a_witness() {
    for shape in UNSAFE {
        for lane in ["default", "release"] {
            let name = format!("{shape}_unsafe_{lane}");
            for vc in mul_rows(&name) {
                let result = verdict(&vc);
                let VerificationResult::Failed { counterexample, .. } = &result else {
                    panic!(
                        "{name}: this multiply really overflows and must stay refuted: {result:?}"
                    );
                };
                assert!(
                    counterexample.is_some(),
                    "{name}: and it must still name the values — a refutation without a \
                     witness is not actionable"
                );
            }
        }
    }
}

/// The witnesses must be REAL EXECUTIONS, not artifacts of a dropped fact: the
/// model's operand pair has to satisfy the guard that execution actually passes
/// AND overflow `i64::checked_mul`. Without this, a refutation could be right by
/// accident — which is exactly how the false refutations this commit removes
/// looked from the outside.
#[test]
fn every_unsafe_signed_witness_is_an_execution_that_really_overflows() {
    for lane in ["default", "release"] {
        // `sgn_onesided`: the guard is `a < 1000 && b < 1000` and bounds NOTHING
        // from below, so both operands may be hugely negative.
        let name = format!("onesided_unsafe_{lane}");
        for vc in mul_rows(&name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let (a, b) = witness_operands(&name, &cex);
            assert!(a < 1000 && b < 1000, "{name}: the model must take the guarded path: {cex:?}");
            assert!(really_overflows_i64(a, b), "{name}: and `a * b` must overflow: a={a} b={b}");
        }

        // `sgn_wrongvar`: the guard bounds `a` and `c`; `b` is unbounded.
        let name = format!("wrongvar_unsafe_{lane}");
        for vc in mul_rows(&name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let (a, b) = witness_operands(&name, &cex);
            assert!(
                a > -1000 && a < 1000,
                "{name}: the model must respect the guard on `a`, the one variable it \
                 really does bound: {cex:?}"
            );
            assert!(really_overflows_i64(a, b), "{name}: and `a * b` must overflow: a={a} b={b}");
        }

        // `sgn_writebefore`: the guard read the ENTRY `b`; the multiply reads the
        // POST-write value, which is `c` and carries no bound. `a` stays guarded.
        let name = format!("writebefore_unsafe_{lane}");
        for vc in mul_rows(&name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let (a, b) = witness_operands(&name, &cex);
            assert!(
                a > -1000 && a < 1000,
                "{name}: the ENTRY guard on `a` still holds on the path taken: {cex:?}"
            );
            assert!(
                really_overflows_i64(a, b),
                "{name}: and the multiply reads the POST-write `b`, which is the \
                 unbounded `c`: a={a} b={b}"
            );
        }

        // `sgn_pow32`: both operands are guarded `|x| <= 2^32`, and `2^32 * 2^32`
        // is `2^64` — past `i64::MAX` by a bit. The model must sit at that corner.
        let name = format!("pow32_unsafe_{lane}");
        for vc in mul_rows(&name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let (a, b) = witness_operands(&name, &cex);
            let pow32: i64 = 1 << 32;
            assert!(
                (-pow32..=pow32).contains(&a) && (-pow32..=pow32).contains(&b),
                "{name}: the model must take the guarded path: {cex:?}"
            );
            assert!(
                really_overflows_i64(a, b),
                "{name}: and the product must really overflow i64: a={a} b={b}"
            );
        }

        // `sgn_via_local_stale` / `sgn_via_local_two_defs`: `a` is guarded on the
        // path taken and the multiplied `b` is not — in the first because the
        // cross-block tie `g == b` is stale by the multiply, in the second because
        // `g` is `c` on one of its two reaching paths. Either way the model must
        // respect the ONE guard that really binds and still overflow.
        for shape in ["via_local_stale", "via_local_two_defs", "via_local_restated"] {
            let name = format!("{shape}_unsafe_{lane}");
            for vc in mul_rows(&name) {
                let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc)
                else {
                    panic!("{name} must be refuted");
                };
                let (a, b) = witness_operands(&name, &cex);
                assert!(
                    a > -1000 && a < 1000,
                    "{name}: the guard on `a` binds on every path and must hold: {cex:?}"
                );
                assert!(
                    really_overflows_i64(a, b),
                    "{name}: and the multiplied `b` carries no bound, so the product \
                     really overflows: a={a} b={b}"
                );
            }
        }

        // `sgn_loop`: the guard on `b` holds on ENTRY only; the loop body's own
        // `b = a * b` reaches the use too, so no dominating bound may land on the
        // multiplied operand. `a` is never rewritten and stays guarded.
        let name = format!("loop_unsafe_{lane}");
        for vc in mul_rows(&name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let (a, b) = witness_operands(&name, &cex);
            assert!(
                a > -1000 && a < 1000,
                "{name}: `a` is never rewritten, so its guard must hold in the model: {cex:?}"
            );
            assert!(
                really_overflows_i64(a, b),
                "{name}: and the loop-carried `b` must reach a value whose product with \
                 `a` overflows: a={a} b={b}"
            );
        }
    }
}
