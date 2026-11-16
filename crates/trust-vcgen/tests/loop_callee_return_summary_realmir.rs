//! REAL-MIR pin for a same-crate callee's RETURN SUMMARY reaching a LOOP BODY.
//!
//! # What was wrong
//!
//! bit-vec 0.9.1 (`src/lib.rs:206`) has
//!
//! ```text
//! fn reverse_bits(byte: u8) -> u8 {
//!     let mut result = 0;
//!     for i in 0..u8::bits() {
//!         result |= ((byte >> i) & 1) << (u8::bits() - 1 - i);
//!     }
//!     result
//! }
//! ```
//!
//! where `<u8 as BitBlock>::bits()` is `fn bits() -> usize { 8 }` in the same
//! crate. Compiled with `-Ztrust-policy=advisory` it reported
//!
//! ```text
//! [overflow:sub] FAILED (ay-in-process); counterexample: … _17 = 0, … byte = 1, i = 0
//! [shift:left]   FAILED (trust-bitmask-refute)
//! [shift:right]  FAILED (ay-in-process); counterexample: … _5 = 9, … byte = 0, i = 8
//! ```
//!
//! Neither counterexample is an execution: `_5` and `_17` are the two
//! `u8::bits()` results, which are 8 on every call. Replayed concretely over all
//! 256 inputs, `reverse_bits` never panics. The callee's const-set summary `{8}`
//! WAS recorded, but it was consumed only as a PATH fact at the call site, and a
//! path fact is weakened away at the loop-header join, so the loop body saw the
//! call results as free variables. `build_callee_return_summary_facts` now states
//! the summary as a GLOBAL fact about a local whose one value is that call.
//!
//! # The matrix
//!
//! | fixture | expectation |
//! |---|---|
//! | `reverse_bits` (bit-vec verbatim, trait-impl callee) | no row REFUTED |
//! | `lsb_fold` (`for i in 0..eight() { byte >> i }`) | shift row not REFUTED |
//! | `lsb_fold_set` (callee returns `4` or `8`: a const SET) | shift row not REFUTED |
//! | `lsb_fold_real` (`nine()` is 9: `byte >> 8` is reachable) | shift row REFUTED |
//! | `lsb_fold_reassigned` (`n = eight()`, then `n = 100` on one path) | shift row REFUTED |
//!
//! The last two are the load-bearing half: a real bug reached through a summarised
//! callee, and a local with a second definition, must both keep their refutation.
//!
//! # Fixtures
//!
//! `tests/fixtures/loop_ret_summary_*_mir.json` are the compiler's own extraction of
//! the source below, captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> loop_ret_summary.rs
//! ```
//!
//! ```text
//! pub trait Bits { fn bits() -> usize; }
//! impl Bits for u8 { #[inline] fn bits() -> usize { 8 } }
//! fn eight() -> usize { 8 }
//! fn nine() -> usize { 9 }
//! fn pick(c: bool) -> usize { if c { return 4; } 8 }
//! pub fn reverse_bits(byte: u8) -> u8 { /* bit-vec, above */ }
//! pub fn lsb_fold(byte: u8) -> u8 {
//!     let mut r = 0; for i in 0..eight() { r |= (byte >> i) & 1; } r
//! }
//! pub fn lsb_fold_set(byte: u8, c: bool) -> u8 {
//!     let mut r = 0; for i in 0..pick(c) { r |= (byte >> i) & 1; } r
//! }
//! pub fn lsb_fold_real(byte: u8) -> u8 {
//!     let mut r = 0; for i in 0..nine() { r |= (byte >> i) & 1; } r
//! }
//! pub fn lsb_fold_reassigned(byte: u8, c: bool) -> u8 {
//!     let mut n = eight(); if c { n = 100; }
//!     let mut r = 0; for i in 0..n { r |= (byte >> i) & 1; } r
//! }
//! ```
//!
//! `pick` is spelled with an early `return` on purpose. In the verification
//! extraction both `if c { 4 } else { 8 }` and `match c { true => 4, false => 8 }`
//! lower to `_2 = 4 | _2 = 8; _0 = copy _2`, whose non-constant `_0` write makes
//! every return summary fail closed (measured), so either spelling would test
//! nothing here; the early return writes `_0 = const` on both paths.
//!
//! The summaries are computed over the whole extraction exactly as
//! `rustc_mir_transform::trust_verify::trust_init_backing_certificates` computes
//! them, and installed through the same `CalleeSummaryContext`.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

const ALL: &[&str] = &[
    "u8_bits",
    "eight",
    "nine",
    "pick",
    "reverse_bits",
    "lsb_fold",
    "lsb_fold_set",
    "lsb_fold_real",
    "lsb_fold_reassigned",
];

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/loop_ret_summary_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The whole-crate summary context, built the way the compiler builds it.
fn summaries() -> trust_vcgen::CalleeSummaryContext {
    let funcs: Vec<VerifiableFunction> = ALL.iter().map(|n| load(n)).collect();
    trust_vcgen::CalleeSummaryContext::default()
        .with_return_bounds(trust_vcgen::compute_return_bound_summaries(&funcs))
        .with_return_lower_bounds(trust_vcgen::compute_return_lower_bound_summaries(&funcs))
        .with_return_const_sets(trust_vcgen::compute_return_const_set_summaries(&funcs))
}

/// `(kind_tag, verdict_tag)` for every shift / arithmetic-overflow row of `name`,
/// each dispatched to the deterministic in-process ay the bridge uses.
fn machine_rows(name: &str) -> Vec<(String, String)> {
    let func = load(name);
    let summaries = summaries();
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone())
                .with_callee_summaries(summaries);
            let vcs = trust_vcgen::generate_vcs_with_context(&func, &context);
            let router = test_router::deterministic_test_router();
            let mut rows = Vec::new();
            for vc in &vcs {
                let tag = match &vc.kind {
                    VcKind::ShiftOverflow { .. } => "shift",
                    VcKind::ArithmeticOverflow { .. } => "overflow",
                    _ => continue,
                };
                let verdict = match router
                    .verify_all(std::slice::from_ref(vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC")
                    .1
                {
                    VerificationResult::Proved { .. } => "PROVED".to_string(),
                    VerificationResult::Failed { .. } => "REFUTED".to_string(),
                    other => format!("{other:?}").chars().take(24).collect(),
                };
                rows.push((tag.to_string(), verdict));
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn assert_has_rows(name: &str, rows: &[(String, String)], kind: &str) {
    assert!(
        rows.iter().any(|(k, _)| k == kind),
        "{name}: the fixture must actually produce a `{kind}` row or this test proves nothing; \
         got {rows:?}"
    );
}

#[test]
fn the_callee_summaries_this_file_relies_on_are_recorded() {
    let funcs: Vec<VerifiableFunction> = ALL.iter().map(|n| load(n)).collect();
    let sets = trust_vcgen::compute_return_const_set_summaries(&funcs);
    let key = |n: &str| load(n).def_path;
    assert_eq!(sets.get(&key("u8_bits")), Some(&vec![8]));
    assert_eq!(sets.get(&key("eight")), Some(&vec![8]));
    assert_eq!(sets.get(&key("nine")), Some(&vec![9]));
    assert_eq!(sets.get(&key("pick")), Some(&vec![4, 8]));
}

/// bit-vec 0.9.1's `reverse_bits`, verbatim: every shift and subtraction is in
/// range because `u8::bits()` is 8. No row may be refuted.
#[test]
fn bit_vec_reverse_bits_is_not_refuted() {
    let rows = machine_rows("reverse_bits");
    assert_has_rows("reverse_bits", &rows, "shift");
    assert_has_rows("reverse_bits", &rows, "overflow");
    assert!(
        rows.iter().all(|(_, v)| v != "REFUTED"),
        "reverse_bits never panics (all 256 inputs replayed); a refutation is a \
         counterexample over a havocked `u8::bits()`: {rows:?}"
    );
}

#[test]
fn a_constant_returning_loop_bound_is_not_refuted() {
    let rows = machine_rows("lsb_fold");
    assert_has_rows("lsb_fold", &rows, "shift");
    assert!(rows.iter().all(|(_, v)| v != "REFUTED"), "lsb_fold: {rows:?}");
}

#[test]
fn a_const_set_returning_loop_bound_is_not_refuted() {
    let rows = machine_rows("lsb_fold_set");
    assert_has_rows("lsb_fold_set", &rows, "shift");
    assert!(rows.iter().all(|(_, v)| v != "REFUTED"), "lsb_fold_set: {rows:?}");
}

/// `nine()` is 9, so `i` reaches 8 and `byte >> 8` overflows: the summary is a
/// TRUE fact and must leave this real bug refuted.
#[test]
fn a_real_overflow_through_a_summarised_callee_stays_refuted() {
    let rows = machine_rows("lsb_fold_real");
    assert!(
        rows.iter().any(|(k, v)| k == "shift" && v == "REFUTED"),
        "lsb_fold_real overflows at i = 8 and must stay refuted: {rows:?}"
    );
}

/// `n` is `eight()` on one path and 100 on the other: the call is not `n`'s only
/// value, so no summary fact may attach to it and the real overflow stays refuted.
#[test]
fn a_local_with_a_second_definition_gets_no_summary_fact() {
    let rows = machine_rows("lsb_fold_reassigned");
    assert!(
        rows.iter().any(|(k, v)| k == "shift" && v == "REFUTED"),
        "lsb_fold_reassigned overflows at i = 8 when c is true and must stay refuted: {rows:?}"
    );
}
