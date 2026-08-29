//! REAL-ARTIFACT regression guard for the NEGATION-overflow obligation that was
//! being CERTIFIED — the `OverflowNeg` member of the family whose zero-divisor,
//! `Overflow(Div|Rem)` and shift members are guarded by
//! `divzero_canary_real_mir.rs` and `shift_canary_real_mir.rs`.
//!
//! Every fixture under `tests/data/` is the compiler's OWN extracted verification
//! input, captured verbatim with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -C debug-assertions=on \
//!        -Ztrust-dump=mir:<dir> crates/trust-vcgen/tests/data/neg_arms.rs
//! ```
//!
//! so these are not hand-built approximations of the MIR — they are the MIR, and
//! `neg_arms.rs` is committed beside them so every row can be re-derived. Read
//! the fixtures from the EXTRACTED bundle, never from `--emit=mir`: the
//! pretty-printer keeps copy temporaries the extraction folds away, which makes
//! projected-operand shapes look covered when they are not.
//!
//! # What went wrong
//!
//! rustc lowers `-x` to
//!
//! ```text
//! bb0: _2 = Eq(x, i32::MIN); assert(!move _2, expected: false, OverflowNeg) -> bb1
//! bb1: _0 = Neg(x)
//! ```
//!
//! so the Neg STATEMENT always sits in the assert's success target. Both the
//! assert arm (`safety.rs`'s `AssertMessage::OverflowNeg`) and the statement arm
//! (`v2_build_negation_raw_vc`) emitted a `VcKind::NegationOverflow` at the same
//! span — same kind, same span, distinguishable only by a producer-local ordinal.
//! The statement one inherits the assert-passed guard through its block defs, so
//! on the real canary MIR its violation formula was
//!
//! ```text
//! (and (= _3 …) (= m …) (= _4 (= m (- 2147483648)))
//!      (and (not _4) … (= _4 (= m (- 2147483648))) … (= m (- 2147483648))))
//! ```
//!
//! — it binds `_4 = (m == INT_MIN)`, then asserts `NOT _4` AND `m == INT_MIN`,
//! i.e. `_4 AND NOT _4`, UNSAT **by construction for every program**. It can never
//! fail and discharges nothing, but it shipped in the structured transport as a
//! `certified` `negation` row at the exact span of a genuinely-false negation
//! overflow. On `let m = (x & 0) | i32::MIN; -m` — false for EVERY input — the
//! whole census read
//!
//! ```text
//! summary: 0 trusted, 1 certified, 0 failed, 0 unknown, 1 runtime-checked out of 2
//! ```
//!
//! and THE ONLY POSITIVE CLAIM IN IT WAS THE VACUOUS ONE.
//!
//! `v2_negation_assert_exactly_bound` suppresses that duplicate — and only under
//! the assert lane's OWN exact binding plus a sole-entry check, so the tests below
//! pin both directions: the duplicate is gone, and every obligation that was doing
//! real work is still there.
//!
//! # Polarity — this is the div/rem shape, not the shift one
//!
//! `OverflowNeg`'s MIR assert expects `false`: the cond is the FAILURE condition
//! (`x == INT_MIN`), exactly like `DivisionByZero`, and unlike `Overflow(Shl|Shr)`
//! whose cond IS the guard. `vacuous_flags` below therefore looks for the div/rem
//! shape: a flag asserted FALSE alongside its own defining condition asserted
//! TRUE.

use std::collections::HashMap;

use trust_types::{Formula, VcKind, VerifiableFunction};

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn load_json(name: &str) -> serde_json::Value {
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must parse as JSON: {e}"))
}

fn from_value(name: &str, value: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(value)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

fn load(name: &str) -> VerifiableFunction {
    // STRAIGHT FROM TEXT, never through `serde_json::Value`. `Value`'s number
    // type is `PosInt(u64) | NegInt(i64) | Float(f64)`, so a 128-bit constant
    // cannot survive the hop: `negation_i128` carries `Int: i128::MIN`
    // (-170141183460469231731687303715884105728), which does not fit i64 and is
    // silently widened to `f64`, after which the derive rejects it with
    // "invalid type: floating point `-1.7014118346046923e+38`, expected i128".
    // The streaming deserializer implements `deserialize_i128` and parses the
    // literal exactly. Only the MUTATING helper needs a `Value` to edit, and no
    // mutated fixture carries a 128-bit constant.
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

fn negation_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        .collect()
}

/// Walk the VC's conjunctive skeleton, recording
///   * `defs` — flag definitions `flag = <condition>` (the MIR bool temps);
///   * `neg`  — flags asserted NEGATIVELY (`(not flag)`, i.e. a passed assert);
///   * `pos`  — everything asserted POSITIVELY, rendered.
fn collect(
    f: &Formula,
    defs: &mut HashMap<String, String>,
    neg: &mut Vec<String>,
    pos: &mut Vec<String>,
) {
    match f {
        Formula::And(parts) => {
            for p in parts {
                collect(p, defs, neg, pos);
            }
        }
        Formula::Not(inner) => {
            if let Formula::Var(name, _) = inner.as_ref() {
                neg.push(name.clone());
            }
        }
        Formula::Var(name, _) => pos.push(format!("VAR:{name}")),
        Formula::Eq(a, b) => {
            // `flag = <condition>` is a DEFINITION, not an assertion of `flag`.
            if let Formula::Var(name, _) = a.as_ref() {
                defs.insert(name.clone(), b.to_smtlib());
            } else if let Formula::Var(name, _) = b.as_ref() {
                defs.insert(name.clone(), a.to_smtlib());
            }
            pos.push(f.to_smtlib());
        }
        other => pos.push(other.to_smtlib()),
    }
}

/// The flags this VC asserts FALSE while also asserting their defining condition
/// TRUE — `flag && !flag` at once. Such a VC is UNSAT by construction: it can only
/// ever come back `proved`, and it proves nothing. That is precisely the shape
/// that was shipping as a `certified` `negation` row at the span of a
/// genuinely-false negation overflow.
///
/// One level of definition is resolved on purpose. A raw literal/complement scan
/// is NOT good enough: a second, unrelated negation legitimately carries the
/// FIRST negation's passed-assert `(not _4)` as a path guard while its own
/// violation is about a different value, and a crude scan would flag that honest
/// obligation as vacuous. The contradiction only counts when the negated flag's
/// OWN defining condition is what the VC asserts positively.
fn vacuous_flags(vc: &trust_types::VerificationCondition) -> Vec<String> {
    let mut defs = HashMap::new();
    let (mut neg, mut pos) = (Vec::new(), Vec::new());
    collect(&vc.formula, &mut defs, &mut neg, &mut pos);
    let mut bad: Vec<String> = neg
        .iter()
        .filter(|flag| defs.get(*flag).is_some_and(|d| pos.contains(d)))
        .cloned()
        .collect();
    bad.sort();
    bad.dedup();
    bad
}

fn assert_no_vacuous_obligation(name: &str, func: &VerifiableFunction) {
    for vc in negation_vcs(func) {
        let bad = vacuous_flags(&vc);
        assert!(
            bad.is_empty(),
            "{name}: a surviving negation obligation asserts {bad:?} false while asserting \
             its defining condition true — UNSAT by construction, so it can only ever be \
             `proved`: {}",
            vc.formula.to_smtlib()
        );
    }
}

// ---------------------------------------------------------------------------
// The canary that was being certified.
// ---------------------------------------------------------------------------

#[test]
fn negation_overflow_canary_keeps_exactly_one_non_vacuous_obligation() {
    // `let m = (x & 0) | i32::MIN; -m` overflows on EVERY input. Pre-fix this
    // emitted TWO rows and the vacuous one was the census's only positive claim.
    let name = "sentinel_negation_overflow_must_not_prove";
    let func = load(name);
    assert_eq!(
        negation_vcs(&func).len(),
        1,
        "`-((x & 0) | i32::MIN)` must carry exactly one negation-overflow obligation, \
         not a self-guarded duplicate that can only ever be `proved`"
    );
    assert_no_vacuous_obligation(name, &func);
}

// ---------------------------------------------------------------------------
// MUTATION ARMS — the suppression must not become a blanket. Every obligation
// that does real work must survive, and the surface must still DISCHARGE the
// genuinely-true ones.
// ---------------------------------------------------------------------------

#[test]
fn provably_safe_negation_keeps_its_honest_obligation() {
    // THE SAFE CASE. `if x > i32::MIN { -x }` emitted proved+proved pre-fix, and
    // exactly ONE of those two was HONEST: the assert-lane row is UNSAT because
    // the program's OWN `x > i32::MIN` guard contradicts `x == i32::MIN`, which is
    // a real discharge. The other was UNSAT because it asserted `(not _3)`
    // alongside `_3`'s own definition, which discharges nothing. A fix that
    // deleted the honest row would be a lost recovery, so this pins that the
    // survivor is the honest one — non-vacuous, and still carrying the real
    // `x == INT_MIN` violation for the solver to refute.
    let name = "provably_safe_negation";
    let func = load(name);
    let vcs = negation_vcs(&func);
    assert_eq!(vcs.len(), 1, "a provably-safe negation keeps exactly one real obligation");
    assert_no_vacuous_obligation(name, &func);
    assert!(
        vcs[0].formula.to_smtlib().contains("(= x (- 2147483648))"),
        "the surviving obligation must still state the real overflow condition: {}",
        vcs[0].formula.to_smtlib()
    );
}

#[test]
fn unguarded_negation_keeps_its_refutable_obligation() {
    // `-x` with a wholly unconstrained operand: neither provable nor refutable by
    // construction, and the obligation must survive with its violation intact.
    // Pre-fix this too shipped a `certified` vacuous row beside the real one.
    let name = "unguarded_negation";
    let func = load(name);
    let vcs = negation_vcs(&func);
    assert_eq!(vcs.len(), 1, "an unconstrained negation keeps its obligation");
    assert_no_vacuous_obligation(name, &func);
    assert!(
        vcs[0].formula.to_smtlib().contains("(= x (- 2147483648))"),
        "the surviving obligation must still state the real UB condition: {}",
        vcs[0].formula.to_smtlib()
    );
}

#[test]
fn two_distinct_negations_each_keep_their_own_obligation() {
    // `(-a).wrapping_add(-b)`: two negated values, two asserts, in CHAINED blocks
    // (bb1 both negates `a` and computes bb2's guard). A skip keyed on the BLOCK
    // rather than on the negated VALUE silently drops one of these two real
    // obligations. Pre-fix this emitted FOUR rows (two honest, two vacuous).
    let name = "two_distinct_negations";
    let func = load(name);
    assert_eq!(negation_vcs(&func).len(), 2, "each distinct negated value keeps one obligation");
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn projected_source_negation_keeps_exactly_one_obligation() {
    // `-(a - b)`. Under overflow checks the negated value is the `.0` field of the
    // `CheckedSub` tuple, re-materialized as `_3 = move (_4.0)` — the shape where
    // measuring from `--emit=mir` instead of the extracted bundle misleads. The
    // assert compares `copy _3` while the Neg reads `move _3`, so the binding must
    // hold across the Copy/Move spelling difference, exactly as the assert lane's
    // own `same_runtime_operand` does.
    let name = "negation_of_projected_value";
    let func = load(name);
    assert_eq!(negation_vcs(&func).len(), 1, "a projected-source negation keeps one obligation");
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn i128_negation_is_left_alone() {
    // MEASURED SCOPE BOUNDARY. At width 128 both lanes take BV constructors over
    // DIFFERENT block-def sets, so "the same proposition" would be an argument
    // rather than an identity — and there is nothing to fix: `-x: i128` reports
    // BOTH rows `failed`, so it over-reports and never false-proves. Suppressing
    // there could only lose a refutable row.
    let func = load("negation_i128");
    assert_eq!(
        negation_vcs(&func).len(),
        2,
        "i128 negation is outside the suppression's measured scope and must keep both rows"
    );
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED STRUCTURAL MUTATIONS — one field of a real artifact is changed at
// a time. Each takes the shape OUT of the canonical rustc chain, and the
// suppression must switch off, so the per-STATEMENT row survives every one.
//
// The counts below are EXACT rather than merely non-zero, and that is what makes
// each arm a planted violation: loosening the one rule it targets drops the total
// by exactly the statement row, so the arm goes red. Note the assert lane's own
// contribution is not a constant — when its builder declines it emits an
// `UnsupportedMir` proof gap instead of a `NegationOverflow`, which is why some
// arms total 1 and others 2:
//
// ```text
// arm                                     strict  rule loosened
// a_second_entry_into_the_negation_block        2  1
// a_second_negation_in_the_target_block         2  0   (BOTH rows lost)
// inverted_assert_polarity                      1  0
// mismatched_assert_message                     1  0
// guard_over_a_different_value                  1  0
// guard_against_a_lookalike_constant            1  0
// non_equality_guard                            1  0
// a_negation_in_the_entry_block                 2  1
// ```
// ---------------------------------------------------------------------------

/// The real canary MIR with one field replaced, then run through the generator.
fn canary_mutated(tag: &str, mutate: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = load_json("sentinel_negation_overflow_must_not_prove");
    mutate(&mut value);
    from_value(tag, value)
}

/// The canary's `_4 = Eq(copy _2, const i32::MIN)` cond definition.
fn canary_cond(v: &mut serde_json::Value) -> &mut serde_json::Value {
    &mut v["body"]["blocks"][0]["stmts"][2]["Assign"]["rvalue"]["BinaryOp"]
}

#[test]
fn a_second_entry_into_the_negation_block_does_not_suppress() {
    // THE SOLE-ENTRY ARM. A forged body must not launder the obligation through an
    // assert its executions can bypass: bb2 jumps straight into the Neg block, so
    // the surviving assert row would not cover every execution of the Neg.
    let func = canary_mutated("bypassed", |v| {
        let blocks = v["body"]["blocks"].as_array_mut().expect("blocks array");
        blocks.push(serde_json::json!({ "id": 2, "stmts": [], "terminator": { "Goto": 1 } }));
    });
    assert_eq!(
        negation_vcs(&func).len(),
        2,
        "a negation block with a second way in keeps BOTH rows — duplicates over-report, \
         they never under-report"
    );
}

#[test]
fn a_second_negation_in_the_target_block_does_not_suppress() {
    // THE UNIQUENESS ARM, and the reason block identity alone is not statement
    // identity. With two Negs in the target, one assert cannot be authority for
    // both; a rule that only asked "does an `OverflowNeg` assert target this
    // block?" would drop BOTH statement rows at once.
    let func = canary_mutated("two_negs", |v| {
        let span = v["body"]["blocks"][1]["stmts"][0]["Assign"]["span"].clone();
        let stmts = v["body"]["blocks"][1]["stmts"].as_array_mut().expect("bb1 stmts");
        stmts.push(serde_json::json!({
            "Assign": {
                "place": { "local": 3, "projections": [] },
                "rvalue": { "UnaryOp": ["Neg", { "Copy": { "local": 1, "projections": [] } }] },
                "span": span
            }
        }));
    });
    assert_eq!(
        negation_vcs(&func).len(),
        2,
        "an ambiguous target block keeps EVERY statement row (the assert lane itself \
         declines here, so both of these are statement rows)"
    );
}

#[test]
fn inverted_assert_polarity_does_not_suppress() {
    // rustc's `OverflowNeg` assert expects `false` — the cond is the FAILURE
    // condition. An `expected: true` lookalike inverts the semantics and is not
    // this negation's UB guard.
    let func = canary_mutated("inverted_polarity", |v| {
        v["body"]["blocks"][0]["terminator"]["Assert"]["expected"] = serde_json::json!(true);
    });
    assert_eq!(
        negation_vcs(&func).len(),
        1,
        "a non-canonical assert polarity must not take the statement's obligation away"
    );
}

#[test]
fn mismatched_assert_message_does_not_suppress() {
    // An `Overflow(Sub)` assert is a different obligation and does not guard a Neg.
    let func = canary_mutated("wrong_msg", |v| {
        v["body"]["blocks"][0]["terminator"]["Assert"]["msg"] =
            serde_json::json!({ "Overflow": "Sub" });
    });
    assert_eq!(
        negation_vcs(&func).len(),
        1,
        "an assert for a different operation must not take this negation's obligation away"
    );
}

#[test]
fn guard_over_a_different_value_does_not_suppress() {
    // THE OPERAND-EXACTNESS ARM. The cond is re-pointed from `_2` (the value bb1
    // negates) to `_1`. A block-keyed skip still suppresses bb1's statement row
    // because "an `OverflowNeg` assert targets bb1" — and drops the only
    // obligation of a negation nothing actually guards. Bare target identity must
    // NEVER be suppression authority.
    let func = canary_mutated("crossed_cond", |v| {
        let cond = &mut canary_cond(v)[1];
        assert_eq!(cond["Copy"]["local"], 2, "fixture drifted: bb0 must compare `_2`");
        cond["Copy"]["local"] = serde_json::json!(1);
    });
    assert_eq!(
        negation_vcs(&func).len(),
        1,
        "a guard over a DIFFERENT value is not this negation's UB check"
    );
}

#[test]
fn guard_against_a_lookalike_constant_does_not_suppress() {
    // `Eq(_2, -2147483647)` is not the i32 negation's `x == INT_MIN` UB check.
    let func = canary_mutated("wrong_constant", |v| {
        let bound = &mut canary_cond(v)[2];
        assert_eq!(bound["Constant"]["Int"], -2147483648i64, "fixture drifted: bound must be MIN");
        bound["Constant"]["Int"] = serde_json::json!(-2147483647i64);
    });
    assert_eq!(
        negation_vcs(&func).len(),
        1,
        "a guard against the wrong bound must not take the negation's obligation away"
    );
}

#[test]
fn non_equality_guard_does_not_suppress() {
    // `Ne(_2, INT_MIN)` under `expected: false` asserts the operand IS `INT_MIN`.
    // That is not the UB guard, and it must not be read as one.
    let func = canary_mutated("wrong_cond_op", |v| {
        canary_cond(v)[0] = serde_json::json!("Ne");
    });
    assert_eq!(
        negation_vcs(&func).len(),
        1,
        "a non-equality guard must not take the negation's obligation away"
    );
}

#[test]
fn a_negation_in_the_entry_block_does_not_suppress() {
    // THE ENTRY-BLOCK ARM. `unguarded_negation` turned inside out: the Neg moves
    // to bb0 and the assert to bb1, which targets bb0. Nothing ELSE reaches bb0,
    // so the sole-entry check is satisfied and every operand/cond criterion still
    // binds — but bb0 is where execution STARTS, so its Neg runs without ever
    // passing that assert. Only the entry-block rule refuses this laundering.
    let mut value = load_json("unguarded_negation");
    let neg = value["body"]["blocks"][1]["stmts"].clone();
    let eq = value["body"]["blocks"][0]["stmts"].clone();
    let mut assert_t = value["body"]["blocks"][0]["terminator"].clone();
    assert_t["Assert"]["target"] = serde_json::json!(0);
    value["body"]["blocks"] = serde_json::json!([
        { "id": 0, "stmts": neg, "terminator": "Return" },
        { "id": 1, "stmts": eq, "terminator": assert_t },
    ]);
    let func = from_value("neg_in_entry", value);
    assert_eq!(
        negation_vcs(&func).len(),
        2,
        "the ENTRY block's executions never pass a later assert; it is not authority"
    );
}
