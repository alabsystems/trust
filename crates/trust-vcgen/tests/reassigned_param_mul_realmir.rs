// Real-MIR cover for a REASSIGNED PARAMETER whose per-guard COPY lost its tie to
// the parameter (a false refutation of valid Rust).
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
//   pub fn g7(a: u64, mut b: u64) -> u64 {
//       if a < 1000 && b < 1000 { b = a * b; }
//       b
//   }
//
// Both operands are guarded `< 1000`, so `a * b < 10^6` and the multiply cannot
// overflow a `u64`. It was REFUTED. In the DEBUG MIR rustc gives the
// short-circuit `&&` its own copy of the reassigned parameter, and the multiply
// its own copy again:
//
//   bb1: _5 = copy _2; _4 = Lt(move _5, 1000); switch _4 -> [0: bb4, else: bb2]
//   bb2: _6 = copy _2; _7 = CheckedMul(copy _1, copy _6); assert(!_7.1) -> bb3
//
// `_5 == b` and `_5 < 1000` arrive as path facts; nothing ever said `_6 == b`,
// and no dominating fact was keyed on `_6` either. So both renderings of the row
// read the multiplied operand as FREE — the Int core as `a * _6`, the BV half as
// an unconstrained `__trust_ovf_bv_rhs__6` — and ay refuted valid Rust at
// `_6 = 2^63`. The `-O` MIR multiplies `_2` directly, which is why the same
// function compiled in release and failed in debug.
//
// Root fix, both halves of the one lost tie:
//   * `block_defs::v2_formula_with_copy_ties_at_point_recorded` conjoins the
//     same-block COPY TIES (`_6 == b`) onto the Int core — copies only, never the
//     block's other computations, so the mixed BV + Int query stays in the
//     fragment the disjoint-component refutation lane decides.
//   * `v2_mul_dominating_operand_facts` resolves one live copy hop on BOTH sides
//     — the operand down to `b` and the guard's subject `_5` down to `b` — so the
//     dominating `< 1000` lands on the operand, rendered in BV (as before) AND in
//     Int (`v2_int_mul_dominating_guard_constraints`, which is what the deployed
//     interval backend actually reads).
//
// Fixtures are the stage1 compiler's OWN extraction, both lanes:
//
//   rustc --edition 2021 --crate-type lib     -Ztrust-dump=mir:<dir> src.rs
//   rustc --edition 2021 --crate-type lib -O  -Ztrust-dump=mir:<dir> src.rs
//
// SAFE (must never be refuted; the three that the deployed backend set decides
// must be PROVED):
//   * `g7`                      the report, rhs reassigned.
//   * `g7_lhs`    `if a < 1000 && b < 1000 { a = a * b; }`  — lhs reassigned.
//   * `g7_nested` `if a < 1000 { if b < 1000 { b = a * b; } }` — no guard copy;
//     the shape that always proved, kept so a regression here is visible.
//   * `g7_chain`  `if a < 1000 && b < 1000 { b = a + b; b = a * b; }` (u32) — the
//     operand is a copy of a parameter the SAME guarded region already rewrote.
//     Refuted before the fix in BOTH lanes; the copy ties are what clear it.
//
// UNSAFE twins (must STAY refuted, each with a model of a real execution):
//   * `g7_wrongvar`    the guard bounds `c`, not the multiplied `b`.
//   * `g7_writebefore` `b` is overwritten AFTER the guard read it and BEFORE the
//     multiply — the exact shape a copy tie must NOT bridge.
//   * `g7_pow32`       a `<= 2^32` bound on each operand does not bound a u64
//     product (`2^32 * 2^32 = 2^64`).
use trust_types::{
    Counterexample, CounterexampleValue, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/reassigned_param_mul_{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
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
/// interval/range backend first, then in-process ay. This mirrors
/// `rustc_mir_transform::trust_verify::discover_router_backends`; the bare
/// `deterministic_in_process_ay` router used elsewhere in this directory omits
/// the interval lane, which is the lane that actually discharges a guarded
/// unsigned multiply, so it would report `Unknown` for a row the compiler proves.
fn router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(test_router::test_ay_backend()),
    ])
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// Does the product of two model values really exceed `u64::MAX`? Both operands
/// are `u64` values a model named, so they are non-negative and at most `2^64`;
/// the product reaches `2^128`, which `u128` cannot hold either — an arithmetic
/// OVERFLOW of the check itself is therefore a product far past `u64::MAX`, so
/// `checked_mul`'s `None` is `true`, never a silent wrap.
fn product_exceeds_u64(a: i128, b: i128) -> bool {
    let (Ok(a), Ok(b)) = (u128::try_from(a), u128::try_from(b)) else {
        panic!("a model value for a u64 operand must be non-negative: a={a} b={b}");
    };
    a.checked_mul(b).is_none_or(|p| p > u128::from(u64::MAX))
}

fn int_of(cex: &Counterexample, name: &str) -> Option<i128> {
    cex.assignments.iter().find(|(n, _)| n == name).and_then(|(_, v)| match v {
        CounterexampleValue::Int(i) => Some(*i as i128),
        CounterexampleValue::Uint(u) => Some(*u as i128),
        _ => None,
    })
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY — the fixtures must still be the shapes this file is about.
// ---------------------------------------------------------------------------

/// The debug fixtures must still carry the PER-GUARD COPY that the bug is about.
/// If rustc's lowering drifts and stops emitting `_5 = copy _2`, every test below
/// would pass for a reason unrelated to what it guards.
#[test]
fn the_debug_fixtures_still_carry_a_per_guard_copy_of_the_parameter() {
    for name in ["g7_safe_default", "lhs_safe_default", "chain_safe_default"] {
        let func = load(name);
        let copies = func
            .body
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .filter(|stmt| {
                matches!(
                    stmt,
                    trust_types::Statement::Assign {
                        rvalue: trust_types::Rvalue::Use(
                            trust_types::Operand::Copy(_) | trust_types::Operand::Move(_)
                        ),
                        ..
                    }
                )
            })
            .count();
        assert!(
            copies >= 2,
            "{name}: the debug lowering must still keep a per-guard copy AND the \
             multiply's own copy of the reassigned parameter; found {copies} copy \
             statements"
        );
    }
    // And the release fixture of `g7` must NOT: its multiply reads the parameter
    // directly, with no copy statement before it in that block. That asymmetry is
    // the whole reason the bug was invisible under `-O`.
    let release = load("g7_safe_release");
    let mul_block = release
        .body
        .blocks
        .iter()
        .find(|b| {
            b.stmts.iter().any(|s| {
                matches!(
                    s,
                    trust_types::Statement::Assign {
                        rvalue: trust_types::Rvalue::CheckedBinaryOp(trust_types::BinOp::Mul, ..),
                        ..
                    }
                )
            })
        })
        .expect("the release fixture multiplies");
    let copies_before_mul = mul_block
        .stmts
        .iter()
        .take_while(|s| {
            !matches!(
                s,
                trust_types::Statement::Assign {
                    rvalue: trust_types::Rvalue::CheckedBinaryOp(trust_types::BinOp::Mul, ..),
                    ..
                }
            )
        })
        .filter(|s| {
            matches!(
                s,
                trust_types::Statement::Assign {
                    rvalue: trust_types::Rvalue::Use(
                        trust_types::Operand::Copy(_) | trust_types::Operand::Move(_)
                    ),
                    ..
                }
            )
        })
        .count();
    assert_eq!(
        copies_before_mul, 0,
        "the release lowering multiplies the parameter directly — no copy statement \
         precedes it in the multiply's block"
    );
}

// ---------------------------------------------------------------------------
// SAFE — the false refutation, both directions.
// ---------------------------------------------------------------------------

/// THE REPORT. `g7` is safe and the deployed backend set must PROVE it, not
/// merely decline to refute it.
#[test]
fn the_reassigned_parameter_multiply_is_proved() {
    for name in ["g7_safe_default", "lhs_safe_default", "nested_safe_default"] {
        for vc in mul_rows(name) {
            let result = verdict(&vc);
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "{name}: both operands are guarded below 1000, so the u64 product is \
                 below 10^6 and the multiply cannot overflow; got {result:?}"
            );
        }
    }
}

/// Every SAFE shape, in BOTH lanes, must at minimum never be REFUTED — a
/// refutation here is a build error on valid Rust. `g7_chain` is the shape whose
/// operand is a copy of a parameter the same guarded region already rewrote; it
/// was refuted in both the debug and the `-O` extraction before the fix and is
/// not yet proved by the deployed set, so it is pinned at the level the fix
/// actually reaches.
#[test]
fn no_safe_shape_is_refuted_in_either_lane() {
    for name in [
        "g7_safe_default",
        "g7_safe_release",
        "lhs_safe_default",
        "lhs_safe_release",
        "nested_safe_default",
        "nested_safe_release",
        "chain_safe_default",
        "chain_safe_release",
    ] {
        for vc in mul_rows(name) {
            let result = verdict(&vc);
            assert!(
                !matches!(result, VerificationResult::Failed { .. }),
                "{name}: this function is safe; a refutation of it fails the strict \
                 compile of valid Rust: {result:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// UNSAFE twins — the refutations the fix must not remove.
// ---------------------------------------------------------------------------

/// THE REGRESSION GUARD. Each twin is a genuine `u64` multiply overflow and must
/// still be REFUTED, in both lanes, WITH a counterexample — a refutation with no
/// witness is not actionable, and a decline here would ship the bug.
#[test]
fn every_unsafe_twin_is_still_refuted_with_a_witness() {
    for name in [
        "wrongvar_unsafe_default",
        "wrongvar_unsafe_release",
        "writebefore_unsafe_default",
        "writebefore_unsafe_release",
        "pow32_unsafe_default",
        "pow32_unsafe_release",
    ] {
        for vc in mul_rows(name) {
            let result = verdict(&vc);
            let VerificationResult::Failed { counterexample, .. } = &result else {
                panic!("{name}: this multiply really overflows and must stay refuted: {result:?}");
            };
            assert!(
                counterexample.is_some(),
                "{name}: and it must still name the values — a refutation without a \
                 witness is not actionable"
            );
        }
    }
}

/// The witnesses must be REAL EXECUTIONS, not artifacts of a dropped fact. Each
/// twin's model has to satisfy the guard it actually passes AND make the product
/// exceed the type, otherwise the refutation is right by accident.
#[test]
fn every_unsafe_witness_is_an_execution_that_really_overflows() {
    // `wrongvar`: the guard is `a < 1000 && c < 1000`; `b` is unbounded.
    for name in ["wrongvar_unsafe_default", "wrongvar_unsafe_release"] {
        for vc in mul_rows(name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let a = int_of(&cex, "a").unwrap_or_else(|| panic!("{name}: model must name `a`"));
            let b = int_of(&cex, "b").unwrap_or_else(|| panic!("{name}: model must name `b`"));
            let c = int_of(&cex, "c").unwrap_or_else(|| panic!("{name}: model must name `c`"));
            assert!(a < 1000 && c < 1000, "{name}: the model must take the guarded path: {cex:?}");
            assert!(
                product_exceeds_u64(a, b),
                "{name}: and `a * b` must really exceed u64::MAX: a={a} b={b}"
            );
        }
    }

    // `writebefore`: the guard reads the ENTRY `b` (`b < 1000`) and the multiply
    // reads the POST-write value, which is `c`. A model that is a real execution
    // therefore has `b < 1000` and an overflowing `a * c`. Before the fix this
    // row was refuted with a nonzero divisor-style model that no execution has;
    // the establish-point versioning is what keeps the two `b` values apart.
    for name in ["writebefore_unsafe_default", "writebefore_unsafe_release"] {
        for vc in mul_rows(name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let a = int_of(&cex, "a").unwrap_or_else(|| panic!("{name}: model must name `a`"));
            let b = int_of(&cex, "b").unwrap_or_else(|| panic!("{name}: model must name `b`"));
            let c = int_of(&cex, "c").unwrap_or_else(|| panic!("{name}: model must name `c`"));
            assert!(
                a < 1000 && b < 1000,
                "{name}: the ENTRY values must satisfy the guard the execution passed: {cex:?}"
            );
            assert!(
                product_exceeds_u64(a, c),
                "{name}: and the multiply reads the POST-write `b`, which is `c`: a={a} c={c}"
            );
        }
    }

    // `pow32`: both operands are guarded `<= 2^32`, and `2^32 * 2^32 = 2^64`
    // overflows by exactly one bit. The model must sit at that corner.
    for name in ["pow32_unsafe_default", "pow32_unsafe_release"] {
        for vc in mul_rows(name) {
            let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&vc) else {
                panic!("{name} must be refuted");
            };
            let a = int_of(&cex, "a").unwrap_or_else(|| panic!("{name}: model must name `a`"));
            let b = int_of(&cex, "b").unwrap_or_else(|| panic!("{name}: model must name `b`"));
            assert!(
                a <= 4294967296 && b <= 4294967296,
                "{name}: the model must take the guarded path: {cex:?}"
            );
            assert!(
                product_exceeds_u64(a, b),
                "{name}: and the product must really exceed u64::MAX: a={a} b={b}"
            );
        }
    }
}
