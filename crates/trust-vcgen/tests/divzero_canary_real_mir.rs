//! REAL-ARTIFACT regression guard for the zero-divisor obligation that was being
//! CERTIFIED.
//!
//! Every fixture under `tests/data/` is the compiler's OWN extracted verification
//! input, captured verbatim with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> <file>.rs
//! ```
//!
//! so these are not hand-built approximations of the MIR — they are the MIR.
//!
//! # What went wrong
//!
//! rustc lowers `x / n` to `bb0: _c = Eq(n, 0); assert(!_c) -> bb1` /
//! `bb1: _ = Div(x, n)`, so the Div STATEMENT always sits in the assert's success
//! target. Both the assert arm and the statement arm emitted a
//! `VcKind::DivisionByZero` obligation at the same span. The statement one
//! inherits the assert-passed guard through its block defs, so on the real canary
//! MIR its violation formula is
//!
//! ```text
//! (and ... (= _4 (= _3.0 0)) (and (not _4) ... (= _3.0 0)))
//! ```
//!
//! — `_3.0 != 0 AND _3.0 == 0`, UNSAT **by construction for every program**. It can
//! never fail and discharges nothing, but it shipped in the structured transport as
//! a `proved` `divzero` row at the exact span of a genuinely-false division by
//! zero, which is how `clean/tests/trust_verify/vacuity_sentinel.rs`'s
//! `sentinel_div_by_zero_must_not_prove` came to be reported CERTIFIED.
//!
//! `v2_divzero_assert_exactly_bound` suppresses that duplicate — and only under an
//! exact operand/cond binding with a sole-entry check, so the tests below pin both
//! directions: the duplicate is gone, and every obligation that was doing real work
//! is still there.

use trust_types::{Formula, VcKind, VerifiableFunction};

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

fn zero_divisor_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
        .collect()
}

/// Walk the VC's top-level conjunction, recording
///   * `defs`   — flag definitions `flag = <condition>` (the MIR bool temps);
///   * `neg`    — flags asserted NEGATIVELY (`(not flag)`, i.e. a passed assert);
///   * `pos`    — everything asserted POSITIVELY, rendered.
fn collect(
    f: &Formula,
    defs: &mut std::collections::HashMap<String, String>,
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

/// The flags this VC asserts to be FALSE while also asserting their defining
/// condition to be TRUE — i.e. `flag != 0` and `flag == 0` at once. Such a VC is
/// UNSAT by construction: it can only ever come back `proved`, and it proves
/// nothing. That is precisely the shape that was shipping as a `proved` `divzero`
/// row at the span of a genuinely-false division by zero.
///
/// This resolves one level of definition on purpose. A raw literal/complement
/// scan is NOT good enough here: a second, unrelated division legitimately
/// carries the FIRST division's passed-assert `(not _4)` as a path guard while
/// its own violation is about a different divisor, and a crude scan flags that
/// honest obligation as vacuous. The contradiction only counts when the negated
/// flag's OWN defining condition is what the VC asserts positively.
fn vacuous_flags(vc: &trust_types::VerificationCondition) -> Vec<String> {
    let mut defs = std::collections::HashMap::new();
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
    for vc in zero_divisor_vcs(func) {
        let bad = vacuous_flags(&vc);
        assert!(
            bad.is_empty(),
            "{name}: a surviving zero-divisor obligation asserts {bad:?} false while \
             asserting its defining condition true — UNSAT by construction, so it can \
             only ever be `proved`: {}",
            vc.formula.to_smtlib()
        );
    }
}

// ---------------------------------------------------------------------------
// The canaries that were being certified.
// ---------------------------------------------------------------------------

#[test]
fn div_by_zero_canary_keeps_exactly_one_non_vacuous_obligation() {
    let func = load("sentinel_div_by_zero_must_not_prove");
    let vcs = zero_divisor_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "`x / (n - n)` must carry exactly one zero-divisor obligation, not a \
         self-guarded duplicate that can only ever be `proved`"
    );
    assert_no_vacuous_obligation("sentinel_div_by_zero_must_not_prove", &func);
}

#[test]
fn remainder_by_zero_canary_keeps_exactly_one_non_vacuous_obligation() {
    let func = load("sentinel_remainder_by_zero_must_not_prove");
    let vcs = zero_divisor_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "`x % (n - n)` must carry exactly one zero-divisor obligation, not a \
         self-guarded duplicate that can only ever be `proved`"
    );
    assert_no_vacuous_obligation("sentinel_remainder_by_zero_must_not_prove", &func);
}

// ---------------------------------------------------------------------------
// MUTATION ARMS — the suppression must not become a blanket. Each of these
// FAILED against a block-keyed skip; they are why the binding is operand-exact.
// ---------------------------------------------------------------------------

#[test]
fn two_distinct_divisors_each_keep_their_own_obligation() {
    // `(x / n) ^ (x / m)`: two divisors, two asserts. A skip keyed on the BLOCK
    // rather than on the DIVISOR silently drops one of these two real
    // obligations. Pre-fix this emitted FOUR rows (two honest, two vacuous).
    let func = load("two_distinct_divisors");
    let vcs = zero_divisor_vcs(&func);
    assert_eq!(vcs.len(), 2, "each distinct divisor keeps exactly one obligation of its own");
    assert_no_vacuous_obligation("two_distinct_divisors", &func);
}

#[test]
fn unguarded_library_call_division_keeps_its_obligation() {
    // `a.div_euclid(b)` lowers to a Call with NO MIR zero-check assert — the
    // shape the per-statement arm exists to cover. There is nothing to bind to,
    // so the obligation must survive untouched.
    let func = load("unguarded_call_division");
    assert_eq!(
        zero_divisor_vcs(&func).len(),
        1,
        "an unguarded library-call division must keep its zero-divisor obligation"
    );
}

#[test]
fn provably_safe_division_keeps_a_dischargeable_obligation() {
    // `x / (n | 1)` is genuinely safe. The surface must still carry a real,
    // non-vacuous obligation for it and be able to discharge it — a canary that
    // refuses everything, or a suppression that deletes the safe case's
    // obligation instead of proving it, is not a fix.
    let func = load("provably_safe_division");
    let vcs = zero_divisor_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "a provably-safe division keeps exactly one real obligation to discharge"
    );
    assert_no_vacuous_obligation("provably_safe_division", &func);
}
