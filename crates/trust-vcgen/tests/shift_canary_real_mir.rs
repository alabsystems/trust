//! REAL-ARTIFACT regression guard for the SHIFT-overflow obligation that was
//! being CERTIFIED — the shift member of the family whose zero-divisor and
//! `Overflow(Div|Rem)` members are guarded by `divzero_canary_real_mir.rs`.
//!
//! Every fixture under `tests/data/` is the compiler's OWN extracted
//! verification input, captured verbatim with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> \
//!        crates/trust-vcgen/tests/data/shift_arms.rs
//! ```
//!
//! so these are not hand-built approximations of the MIR — they are the MIR, and
//! `shift_arms.rs` is committed beside them so every row can be re-derived.
//!
//! # What went wrong
//!
//! rustc lowers `1u32 << s` to
//!
//! ```text
//! bb0: _3 = Lt(s, 32); assert(move _3, expected: true, Overflow(Shl)) -> bb1
//! bb1: _0 = Shl(const 1u32, s)
//! ```
//!
//! so the shift STATEMENT always sits in the assert's success target. Both the
//! assert arm and the statement arm emitted a `VcKind::ShiftOverflow` at the same
//! span — same kind, same span, distinguishable only by a producer-local ordinal.
//! The statement one inherits the assert-passed guard through its block defs, so
//! on the real canary MIR its violation formula was
//!
//! ```text
//! (and (= _2 (bv2nat (bvor x 64))) (= _3 (< _2 32))
//!      (and _3 ... (>= _2 32)))
//! ```
//!
//! — it binds `_3 = (_2 < 32)`, then asserts `_3` AND `_2 >= 32`, i.e. `_3 AND
//! NOT _3`, UNSAT **by construction for every program**. It can never fail and
//! discharges nothing, but it shipped in the structured transport as a `proved`
//! `shift:left` row at the exact span of a genuinely-false shift overflow, which
//! is how `clean/tests/trust_verify/vacuity_sentinel.rs`'s
//! `sentinel_shift_overflow_must_not_prove` came to be reported CERTIFIED.
//!
//! `v2_shift_assert_exactly_bound` suppresses that duplicate — and only under the
//! assert lane's OWN exact binding plus a sole-entry check, so the tests below pin
//! both directions: the duplicate is gone, and every obligation that was doing
//! real work is still there.
//!
//! # Polarity — why this is not the div/rem rule with a flag
//!
//! `Overflow(Shl|Shr)`'s canonical MIR assert expects `true` (the cond IS the
//! guard, `Lt(amount, BITS)`). `DivisionByZero` and `Overflow(Div|Rem)` expect
//! `false` (the cond is the failure condition). `vacuous_flags` below therefore
//! detects BOTH shapes: a flag asserted false alongside its own defining
//! condition asserted true (the div/rem shape), and a flag asserted true
//! alongside the COMPLEMENT of its defining condition (this one).

use std::collections::HashMap;

use trust_types::{Formula, VcKind, VerifiableFunction};

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn load_json(name: &str) -> serde_json::Value {
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must parse as JSON: {e}"))
}

fn load(name: &str) -> VerifiableFunction {
    // STRAIGHT FROM TEXT, never through `serde_json::Value`: its number type is
    // `PosInt(u64) | NegInt(i64) | Float(f64)`, so a 128-bit constant is
    // silently widened to `f64` on the hop and the derive then rejects it
    // ("invalid type: floating point ..., expected i128"). This bit
    // `negation_canary_real_mir`'s `negation_i128` arm for real; these fixtures
    // carry no 128-bit constant today, and now cannot start failing that way.
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

fn from_value(name: &str, value: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(value)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

fn shift_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .collect()
}

/// Walk the VC's conjunctive skeleton, recording
///   * `defs` — flag definitions `flag = <condition>` (the MIR bool temps);
///   * `pos` / `neg` — flags asserted positively / negatively;
///   * `atoms` — every non-definition atom asserted positively.
fn collect(
    f: &Formula,
    defs: &mut HashMap<String, Formula>,
    pos: &mut Vec<String>,
    neg: &mut Vec<String>,
    atoms: &mut Vec<Formula>,
) {
    match f {
        Formula::And(parts) => {
            for p in parts {
                collect(p, defs, pos, neg, atoms);
            }
        }
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Var(name, _) => neg.push(name.clone()),
            other => atoms.push(Formula::Not(Box::new(other.clone()))),
        },
        Formula::Var(name, _) => pos.push(name.clone()),
        Formula::Eq(a, b) => {
            // `flag = <condition>` is a DEFINITION, not an assertion of `flag`.
            if let Formula::Var(name, _) = a.as_ref() {
                defs.insert(name.clone(), b.as_ref().clone());
            } else if let Formula::Var(name, _) = b.as_ref() {
                defs.insert(name.clone(), a.as_ref().clone());
            } else {
                atoms.push(f.clone());
            }
        }
        other => atoms.push(other.clone()),
    }
}

fn same(a: &Formula, b: &Formula) -> bool {
    a.to_smtlib() == b.to_smtlib()
}

/// Whether `a` is the exact logical complement of `b` over identical operands.
fn complementary(a: &Formula, b: &Formula) -> bool {
    match (a, b) {
        (Formula::Lt(x, y), Formula::Ge(p, q))
        | (Formula::Ge(x, y), Formula::Lt(p, q))
        | (Formula::Le(x, y), Formula::Gt(p, q))
        | (Formula::Gt(x, y), Formula::Le(p, q)) => same(x, p) && same(y, q),
        (Formula::Not(inner), other) | (other, Formula::Not(inner)) => same(inner, other),
        _ => false,
    }
}

/// The flags this VC asserts while ALSO asserting the negation of their own
/// defining condition — `flag AND NOT flag`. Such a VC is UNSAT by construction:
/// it can only ever come back `proved`, and it proves nothing. That is precisely
/// the shape that was shipping as a `proved` `shift:left` row at the span of a
/// genuinely-false shift overflow.
///
/// One level of definition is resolved on purpose. A raw literal/complement scan
/// is NOT good enough: a second, unrelated shift legitimately carries the FIRST
/// shift's passed-assert `_4` as a path guard while its own violation is about a
/// different amount (`two_distinct_shift_amounts` below is exactly that), and a
/// crude scan flags that honest obligation as vacuous. The contradiction only
/// counts when the asserted flag's OWN defining condition is what the VC negates.
fn vacuous_flags(vc: &trust_types::VerificationCondition) -> Vec<String> {
    let mut defs = HashMap::new();
    let (mut pos, mut neg, mut atoms) = (Vec::new(), Vec::new(), Vec::new());
    collect(&vc.formula, &mut defs, &mut pos, &mut neg, &mut atoms);
    let mut bad: Vec<String> = Vec::new();
    // Shift polarity: `flag` true, `NOT def(flag)` also asserted.
    for flag in &pos {
        if let Some(def) = defs.get(flag)
            && atoms.iter().any(|a| complementary(a, def))
        {
            bad.push(flag.clone());
        }
    }
    // Div/rem polarity, kept so this detector covers the whole family: `flag`
    // false, `def(flag)` asserted true.
    for flag in &neg {
        if let Some(def) = defs.get(flag)
            && atoms.iter().any(|a| same(a, def))
        {
            bad.push(flag.clone());
        }
    }
    bad.sort();
    bad.dedup();
    bad
}

fn assert_no_vacuous_obligation(name: &str, func: &VerifiableFunction) {
    for vc in shift_vcs(func) {
        let bad = vacuous_flags(&vc);
        assert!(
            bad.is_empty(),
            "{name}: a surviving shift obligation asserts {bad:?} while also asserting \
             the negation of its defining condition — UNSAT by construction, so it can \
             only ever be `proved`: {}",
            vc.formula.to_smtlib()
        );
    }
}

// ---------------------------------------------------------------------------
// The canary that was being certified, and its `Shr` twin.
// ---------------------------------------------------------------------------

#[test]
fn shift_overflow_canary_keeps_exactly_one_non_vacuous_obligation() {
    let name = "sentinel_shift_overflow_must_not_prove";
    let func = load(name);
    assert_eq!(
        shift_vcs(&func).len(),
        1,
        "`1u32 << (x | 64)` must carry exactly one shift-overflow obligation, not a \
         self-guarded duplicate that can only ever be `proved`"
    );
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn shr_overflow_canary_keeps_exactly_one_non_vacuous_obligation() {
    // The suppression is per-opcode: `Overflow(Shr)` must bind `Shr`, and the
    // right-shift member of the family must be deduplicated too.
    let name = "sentinel_shr_overflow_must_not_prove";
    let func = load(name);
    assert_eq!(
        shift_vcs(&func).len(),
        1,
        "`x >> (x | 64)` must carry exactly one shift-overflow obligation"
    );
    assert_no_vacuous_obligation(name, &func);
}

// ---------------------------------------------------------------------------
// MUTATION ARMS — the suppression must not become a blanket. Every obligation
// that does real work must survive, and the surface must still DISCHARGE the
// genuinely-true ones.
// ---------------------------------------------------------------------------

#[test]
fn two_distinct_shift_amounts_each_keep_their_own_obligation() {
    // `(x << s) ^ (x << t)`: two amounts, two asserts. A skip keyed on the BLOCK
    // rather than on the AMOUNT silently drops one of these two real obligations.
    // Pre-fix this emitted FOUR rows (two honest, two vacuous).
    let name = "two_distinct_shift_amounts";
    let func = load(name);
    assert_eq!(shift_vcs(&func).len(), 2, "each distinct shift amount keeps one obligation");
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn crossed_guard_keeps_the_unguarded_shifts_obligation() {
    // THE OPERAND-EXACTNESS ARM. One field of the real `two_distinct_shift_amounts`
    // artifact is changed: bb0's guard is re-pointed from `s` (the amount bb1
    // shifts by) to `t`. A block-keyed skip still suppresses bb1's statement row
    // because "an `Overflow(Shl)` assert targets bb1" — and drops a genuinely
    // unguarded shift's only obligation. The operand-exact binding refuses, so
    // that row survives and the count stays at 2.
    let mut value = load_json("two_distinct_shift_amounts");
    let cond = &mut value["body"]["blocks"][0]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"][1];
    assert_eq!(cond["Copy"]["local"], 2, "fixture drifted: bb0 must guard `s` (_2)");
    cond["Copy"]["local"] = serde_json::json!(3); // guard `t` instead
    let func = from_value("crossed_guard", value);
    assert_eq!(
        shift_vcs(&func).len(),
        2,
        "a guard over a DIFFERENT amount is not this shift's UB check; bare target \
         identity must never be suppression authority"
    );
}

#[test]
fn provably_safe_shift_keeps_a_dischargeable_obligation() {
    // `x << (s & 31)` is genuinely safe. The surface must still carry a real,
    // non-vacuous obligation for it — a suppression that DELETED the safe case's
    // obligation instead of proving it would not be a fix. The surviving row's
    // violation `_3 >= 32` is contradicted by the interval fact `_3 <= 31`
    // recovered from `s & 31`, not by a self-guard, so it discharges honestly.
    let name = "provably_safe_shift";
    let func = load(name);
    let vcs = shift_vcs(&func);
    assert_eq!(vcs.len(), 1, "a provably-safe shift keeps exactly one real obligation");
    assert_no_vacuous_obligation(name, &func);
    assert!(
        vcs[0].formula.to_smtlib().contains("(<= _3 31)"),
        "the surviving obligation must carry the real `s & 31` range fact that \
         discharges it: {}",
        vcs[0].formula.to_smtlib()
    );
}

#[test]
fn unguarded_shift_keeps_its_refutable_obligation() {
    // `x << s` with a wholly unconstrained amount: neither provable nor refutable
    // by construction, and the obligation must survive with its violation intact.
    let name = "unguarded_shift";
    let func = load(name);
    let vcs = shift_vcs(&func);
    assert_eq!(vcs.len(), 1, "an unconstrained shift keeps its obligation");
    assert_no_vacuous_obligation(name, &func);
    assert!(
        vcs[0].formula.to_smtlib().contains("(>= s 32)"),
        "the surviving obligation must still state the real UB condition: {}",
        vcs[0].formula.to_smtlib()
    );
}

#[test]
fn constant_amount_shift_keeps_its_obligation() {
    // `x << 8`. rustc still emits an assert, but over a cast TEMPORARY
    // (`_2 = 8 as u32; _3 = Lt(_2, 32)`) while the shift statement reads the
    // constant directly — so no exact binding exists. The per-statement row must
    // survive untouched, and it discharges on constant arithmetic.
    let name = "constant_amount_shift";
    let func = load(name);
    assert_eq!(
        shift_vcs(&func).len(),
        1,
        "a shift whose assert guards a different operand keeps its own obligation"
    );
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED STRUCTURAL MUTATIONS — one field of the real canary artifact is
// changed at a time. Each takes the shape OUT of the canonical rustc chain, and
// the suppression must switch off: the obligation count must never fall to 0.
// ---------------------------------------------------------------------------

/// The real canary MIR with one field replaced, then run through the generator.
fn canary_mutated(tag: &str, mutate: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = load_json("sentinel_shift_overflow_must_not_prove");
    mutate(&mut value);
    from_value(tag, value)
}

#[test]
fn inverted_assert_polarity_does_not_suppress() {
    // rustc's shift assert expects `true`. An `expected: false` lookalike has
    // different semantics and is not this shift's UB guard.
    let func = canary_mutated("inverted_polarity", |v| {
        v["body"]["blocks"][0]["terminator"]["Assert"]["expected"] = serde_json::json!(false);
    });
    assert!(
        !shift_vcs(&func).is_empty(),
        "a non-canonical assert polarity must not take the statement's obligation away"
    );
}

#[test]
fn guard_over_a_different_value_does_not_suppress() {
    // The cond guards `_1` (x) while the shift's amount is `_2`.
    let func = canary_mutated("crossed_cond", |v| {
        let cond = &mut v["body"]["blocks"][0]["stmts"][1]["Assign"]["rvalue"]["BinaryOp"][1];
        assert_eq!(cond["Copy"]["local"], 2, "fixture drifted: bb0 must guard `_2`");
        cond["Copy"]["local"] = serde_json::json!(1);
    });
    assert!(
        !shift_vcs(&func).is_empty(),
        "a guard over a different value must not take the shift's obligation away"
    );
}

#[test]
fn lookalike_bits_constant_does_not_suppress() {
    // `Lt(_2, 64)` is not the u32 shift's `amount < 32` UB check.
    let func = canary_mutated("wrong_bits", |v| {
        let bits = &mut v["body"]["blocks"][0]["stmts"][1]["Assign"]["rvalue"]["BinaryOp"][2];
        assert_eq!(bits["Constant"]["Uint"][0], 32, "fixture drifted: BITS must be 32");
        bits["Constant"]["Uint"][0] = serde_json::json!(64);
    });
    assert!(
        !shift_vcs(&func).is_empty(),
        "a guard against the wrong width must not take the shift's obligation away"
    );
}

#[test]
fn mismatched_opcode_does_not_suppress() {
    // An `Overflow(Shr)` assert does not guard a `Shl`.
    let func = canary_mutated("wrong_opcode", |v| {
        v["body"]["blocks"][0]["terminator"]["Assert"]["msg"] =
            serde_json::json!({ "Overflow": "Shr" });
    });
    assert!(
        !shift_vcs(&func).is_empty(),
        "an assert for the other shift opcode must not take this shift's obligation away"
    );
}

#[test]
fn a_second_entry_into_the_shift_block_does_not_suppress() {
    // THE SOLE-ENTRY ARM. A forged body must not launder the obligation through
    // an assert its executions can bypass: bb2 jumps straight into the shift
    // block, so the surviving assert row would not cover every execution.
    let func = canary_mutated("bypassed", |v| {
        let blocks = v["body"]["blocks"].as_array_mut().expect("blocks array");
        blocks.push(serde_json::json!({
            "id": 2,
            "stmts": [],
            "terminator": { "Goto": 1 }
        }));
    });
    assert_eq!(
        shift_vcs(&func).len(),
        2,
        "a shift block with a second way in keeps BOTH rows — duplicates over-report, \
         they never under-report"
    );
}
