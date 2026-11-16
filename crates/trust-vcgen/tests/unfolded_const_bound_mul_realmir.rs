// Real-MIR cover for a false refutation of valid Rust that depended on how the
// GUARD'S BOUND WAS SPELLED.
//
//   pub fn shift_safe(a: i64, mut b: i64) -> i64 {
//       if a > -(1i64 << 31) && a < (1i64 << 31) && b > -(1i64 << 31) && b < (1i64 << 31) {
//           b = a * b;
//       }
//       b
//   }
//
// `|a * b| <= 2^62`, a whole bit inside `i64::MAX`, so the multiply cannot
// overflow. The strict DEFAULT lane REFUTED it with a counterexample — exit 1 on
// a program that is safe. Under `-O` the identical function was PROVED, and so
// was the identical function written with the literal bounds
// `-2147483648`/`2147483648` in BOTH lanes. The verdict depended on the
// SPELLING of a constant, which is the defect.
//
// MEASURED ROOT CAUSE. Un-optimized rustc does not const-fold the bound; it
// lowers it into its own temporaries:
//
//   bb0: _6 = cast const 31 -> u32; _7 = Lt(move _6, const 64u32)
//        assert(move _7, "attempt to shift left with overflow") -> bb1
//   bb1: _5 = Shl(const 1i64, const 31i32)
//   bb2: _4 = Neg(move _5);  _3 = Gt(copy _1, move _4)
//
// so `v2_comparison_formula` rendered the guard as `Gt(Var(a), Var(_4))`,
// `v2_linear_var_const_fact` found no constant on either side, and NO
// var-vs-const fact was mined at all. The multiply's fresh BV operand var
// (`__trust_ovf_bv_{role}_{base}`) therefore stayed completely free and ay
// refuted the row at the type corner. `-O` folds the shift into a literal and
// the very same source proves.
//
// The fix is in the fact miner: `v2_const_expr_operand_int` resolves a guard
// operand that is a CLOSED CONSTANT EXPRESSION — a shift, an arithmetic binop, a
// negation, a value-preserving cast, and the `.0` value half of a
// `CheckedBinaryOp` tuple, over literals only — to the exact integer the machine
// computes, and `v2_comparison_formula` renders that side as the constant. Every
// step is range-checked against its own destination type, so a fold the machine
// would wrap or truncate (`1i64 << 63` is `2^63`) declines instead of inventing a
// bound, and a shift amount at or past the width (`1i64 << 64`) is refused
// outright. Nothing with a VARIABLE anywhere inside it folds.
//
// PRE-EXISTING, not caused by the signed-multiply work that landed the same day:
// the sealed 2026-09-17 toolchain refutes `shift_safe` too.
//
// Fixtures are the stage1 compiler's OWN extraction, both lanes:
//
//   rustc --edition 2021 --crate-type lib     -Ztrust-dump=mir:<dir> unf.rs
//   rustc --edition 2021 --crate-type lib -O  -Ztrust-dump=mir:<dir> unf.rs
//
// SAFE (must be PROVED in both lanes) — four spellings of the same `2^31` bound,
// one per MIR shape an unfolded constant expression takes:
//   * `shift`     the report: `-(1i64 << 31)` / `(1i64 << 31)`, a `Shl` under a
//                 `Neg`.
//   * `mulconst`  `65536i64 * 32768i64`: a `CheckedMul` of two literals read back
//                 through its `.0` tuple field.
//   * `addconst`  `2147483647i64 + 1`: the `CheckedAdd` shape, which also pins
//                 that the fold is not shift-specific.

// The fold's RECURSIVE case — an unfolded operand of an unfolded operator, such
// as `-((1i64 << 15) << 16)` — is pinned in
// `src/generate/const_expr_bound_tests.rs` rather than here. It was carried as a
// fifth real-MIR shape and REMOVED: its `2^32` unsafe twin is refutable but ay
// does not find the model inside the strict lane's per-obligation budget (60 s,
// measured), so the twin reported `Unknown`. `Unknown` is fail-closed and
// therefore not a regression — but a twin that cannot show its refutation is not
// evidence, and pinning it as `Unknown` would pin a solver budget rather than a
// verdict. `shift` (`Neg` over `Shl`) and `mulconst` (`Neg` over `.0` over
// `CheckedMul`) both exercise the recursion two levels deep, on real MIR.
//
// UNSAFE twins (must STAY refuted, with a model that is a real execution) — the
// identical four spellings of a `2^32` bound, which genuinely does NOT bound an
// `i64` product (`2^32 * 2^32 = 2^64`, one bit past `i64::MAX`). They are what
// makes the fold's ARITHMETIC load-bearing rather than its mere presence: a fold
// that returned the wrong constant, or that ignored the operator and took the
// first literal it saw, would prove one of these.
use trust_types::{
    BinOp, Counterexample, CounterexampleValue, Operand, Rvalue, SourceSpan, Statement, UnOp,
    VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const SHAPES: [&str; 3] = ["shift", "mulconst", "addconst"];

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/unfolded_const_bound_{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// The span of the fixture's SUBJECT multiply — the `a * b` whose operands are
/// both LOCAL reads.
///
/// The `mulconst` fixture also multiplies two CONSTANTS inside the
/// bound itself, and those rows are separate obligations with their own (correct)
/// verdicts. Selecting the subject by "both operands are local reads" keeps the
/// safe/unsafe pins pointed at the one row this file is about, instead of
/// silently demanding that a constant multiply of `65536 * 65536` be refuted.
fn subject_mul_span(func: &VerifiableFunction) -> SourceSpan {
    let mut found: Option<SourceSpan> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Mul, l, r), span, ..
            } = stmt
            else {
                continue;
            };
            let local_read = |o: &Operand| matches!(o, Operand::Copy(_) | Operand::Move(_));
            if local_read(l) && local_read(r) {
                assert!(
                    found.is_none(),
                    "the fixture must contain exactly one variable*variable multiply"
                );
                found = Some(span.clone());
            }
        }
    }
    found.expect("fixture must contain a `a * b` CheckedBinaryOp(Mul, local, local)")
}

/// Every `Mul` overflow row of the fixture.
fn mul_rows(name: &str) -> Vec<VerificationCondition> {
    let rows: Vec<VerificationCondition> = trust_vcgen::generate_vcs(&load(name))
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if format!("{op:?}") == "Mul")
        })
        .collect();
    assert!(!rows.is_empty(), "{name}: the fixture's whole value is its `Mul` overflow rows");
    rows
}

/// The `Mul` overflow rows of the SUBJECT multiply alone.
fn subject_mul_rows(name: &str) -> Vec<VerificationCondition> {
    let func = load(name);
    let span = subject_mul_span(&func);
    let rows: Vec<VerificationCondition> =
        mul_rows(name).into_iter().filter(|vc| vc.location == span).collect();
    assert!(!rows.is_empty(), "{name}: the `a * b` row must be among the fixture's `Mul` rows");
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
/// positive one. `{base}` differs between the lanes, which is why this matches on
/// the role PREFIX.
fn bv_operand_i64(cex: &Counterexample, role: &str) -> Option<i64> {
    let prefix = format!("__trust_ovf_bv_{role}_");
    cex.assignments.iter().find(|(n, _)| n.starts_with(&prefix)).and_then(|(_, v)| match v {
        CounterexampleValue::Uint(u) => Some(*u as i64),
        CounterexampleValue::Int(i) => i64::try_from(*i).ok(),
        _ => None,
    })
}

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

// ---------------------------------------------------------------------------
// ANTI-VACUITY — the fixtures must still be the shapes this file is about.
// ---------------------------------------------------------------------------

/// THE ANTI-VACUITY TEST FOR THIS WHOLE FILE. Every DEBUG fixture must still
/// carry its bound as an UNFOLDED operator over constants: a `Shl` for the shift
/// spellings, a `CheckedMul`/`CheckedAdd` of two literals for the others. If a
/// future rustc (or a future extractor) const-folds these at `mir_built`, the
/// bound arrives as a literal, `v2_linear_var_const_fact` mines it with no help
/// from the fold, and every SAFE pin below would pass while measuring nothing.
#[test]
fn the_debug_fixtures_still_carry_an_unfolded_constant_bound() {
    let expected: [(&str, &str); 3] =
        [("shift", "Shl"), ("mulconst", "CheckedMul"), ("addconst", "CheckedAdd")];
    for (shape, op) in expected {
        for safety in ["safe", "unsafe"] {
            let name = format!("{shape}_{safety}_default");
            let func = load(&name);
            let mut unfolded = 0usize;
            for block in &func.body.blocks {
                for stmt in &block.stmts {
                    let Statement::Assign { rvalue, .. } = stmt else { continue };
                    let (spelling, l, r) = match rvalue {
                        Rvalue::BinaryOp(b, l, r) => (format!("{b:?}"), l, r),
                        Rvalue::CheckedBinaryOp(b, l, r) => (format!("Checked{b:?}"), l, r),
                        _ => continue,
                    };
                    // Constant OPERANDS only.
                    if spelling == op
                        && matches!(l, Operand::Constant(_))
                        && matches!(r, Operand::Constant(_))
                    {
                        unfolded += 1;
                    }
                }
            }
            assert!(
                unfolded > 0,
                "{name}: the debug MIR must still leave the bound as an unfolded `{op}` over \
                 literals — with it folded, this file measures nothing"
            );
        }
    }
}

/// The negated half of each bound must still be a real `Neg` over the unfolded
/// constant: `-(1i64 << 31)` is what makes the LOWER bound depend on the fold,
/// and a two-sided bound is what a signed multiply needs (bound one side only and
/// the operand's box is still infinite below, so the product interval is
/// unbounded and the backend declines).
#[test]
fn the_debug_fixtures_still_negate_their_lower_bound_in_mir() {
    for shape in SHAPES {
        for safety in ["safe", "unsafe"] {
            let name = format!("{shape}_{safety}_default");
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
            assert!(
                negs > 0,
                "{name}: the lower bound must still be spelled as a MIR `Neg` of the unfolded \
                 constant"
            );
        }
    }
}

/// The `2^31` / `2^32` split is an ARITHMETIC fact about a signed 64-bit product,
/// not a labelling choice: the SAFE fixtures bound at `2^31` and the UNSAFE twins
/// at `2^32`. Stated here so the claim the whole file rests on is in the file.
#[test]
fn the_safe_unsafe_split_is_arithmetic() {
    let pow31: i128 = 1 << 31;
    let pow32: i128 = 1 << 32;
    assert!(pow31 * pow31 <= i64::MAX as i128, "|a|,|b| < 2^31 keeps the product inside i64::MAX");
    assert!(-(pow31 * pow31) >= i64::MIN as i128, "and inside i64::MIN — the bound is two-sided");
    assert!(pow32 * pow32 > i64::MAX as i128, "|a|,|b| <= 2^32 does NOT: 2^64 is past i64::MAX");
}

// ---------------------------------------------------------------------------
// SAFE — the false refutation, in both lanes.
// ---------------------------------------------------------------------------

/// THE REPORT, and the three sibling spellings. Every `Mul` overflow row of every
/// safe fixture — the guarded `a * b` AND the constant multiplies inside the
/// bounds themselves — is PROVED by the deployed backend set in BOTH lanes.
#[test]
fn every_safe_unfolded_bound_spelling_is_proved_in_both_lanes() {
    for shape in SHAPES {
        for lane in ["default", "release"] {
            let name = format!("{shape}_safe_{lane}");
            for vc in mul_rows(&name) {
                let result = verdict(&vc);
                assert!(
                    matches!(result, VerificationResult::Proved { .. }),
                    "{name}: this multiply is bounded on BOTH sides by dominating guards whose \
                     constant is spelled as an unfolded expression, so its four-corner product \
                     fits i64; got {result:?}"
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
fn no_safe_unfolded_bound_spelling_is_refuted_in_either_lane() {
    for shape in SHAPES {
        for lane in ["default", "release"] {
            let name = format!("{shape}_safe_{lane}");
            for vc in mul_rows(&name) {
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

// ---------------------------------------------------------------------------
// UNSAFE twins — the refutations the fold must not remove.
// ---------------------------------------------------------------------------

/// THE REGRESSION GUARD. The identical four spellings at a `2^32` bound really do
/// overflow an `i64` product, and each must STAY refuted in both lanes, WITH a
/// counterexample.
#[test]
fn every_unsafe_unfolded_bound_twin_is_still_refuted_with_a_witness() {
    for shape in SHAPES {
        for lane in ["default", "release"] {
            let name = format!("{shape}_unsafe_{lane}");
            for vc in subject_mul_rows(&name) {
                let result = verdict(&vc);
                let VerificationResult::Failed { counterexample, .. } = &result else {
                    panic!(
                        "{name}: this multiply really overflows and must stay refuted: {result:?}"
                    );
                };
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
/// model's operand pair has to satisfy the guard that execution actually passes
/// AND overflow `i64::checked_mul`. Without this a refutation could be right by
/// accident — which is exactly how the false refutation this commit removes
/// looked from the outside. It is also the check that a WRONG constant fold would
/// fail: mine `2^31` where the source says `2^32` and no model can sit outside
/// `[-2^31, 2^31]` any more.
#[test]
fn every_unsafe_unfolded_bound_witness_is_an_execution_that_really_overflows() {
    let pow32: i64 = 1 << 32;
    for shape in SHAPES {
        for lane in ["default", "release"] {
            let name = format!("{shape}_unsafe_{lane}");
            for vc in subject_mul_rows(&name) {
                let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc)
                else {
                    panic!("{name} must be refuted");
                };
                let (a, b) = witness_operands(&name, &cex);
                assert!(
                    (-pow32..=pow32).contains(&a) && (-pow32..=pow32).contains(&b),
                    "{name}: the model must take the guarded path, i.e. respect the 2^32 bound \
                     the source really wrote: {cex:?}"
                );
                assert!(
                    really_overflows_i64(a, b),
                    "{name}: and the product must really overflow i64: a={a} b={b}"
                );
            }
        }
    }
}
