//! REAL-MIR pin: a lossless std scalar conversion carries its SOURCE range at
//! every read, including inside a loop (cap from-range, 2026-10-03).
//!
//! # What was wrong
//!
//! `semantic_guard` states `dest == arg` for `<u64 as From<u32>>::from(x)` (the
//! TRUST-09 arm, `tests/int_from_into_realmir.rs`), but that is a PATH fact: the
//! guard walk weakens every block it revisits with different guards to `true`, so
//! inside a loop the destination was a free `u64` again. tla-model-ir's
//! `u64::from(e.len) + 1` (`model.rs:1081/1083`) was REFUTED by the ay lane at
//! `u64::MAX`, a value no `u32` widens to (stage 1, measured 2026-10-03), and
//! `u32::from(c)` for a `char` had no model at all. The local's every value is now
//! bounded by its source type (`call_facts::lossless_conversion_source_range`),
//! which needs no path.
//!
//! # The matrix
//!
//! Each positive is paired with a control of the same shape whose overflow is
//! REAL and must stay REFUTED.
//!
//! | fixture | row | expectation |
//! |---|---|---|
//! | `sum_two_u32_from` (`u64::from(x) + u64::from(y)`) | `+` | PROVED |
//! | `sum_u32_from_and_u64` (`u64::from(x) + z`, `z: u64`) | `+` | REFUTED |
//! | `bool_from_in_loop` (`usize::from(b) + (usize::MAX - 1)`) | `+` | PROVED |
//! | `bool_from_in_loop_over` (`usize::from(b) + usize::MAX`) | `+` | REFUTED |
//! | `char_from_in_loop` (`u32::from(c) + 0xFFEF_0000`) | `+` | PROVED |
//! | `char_from_in_loop_over` (`u32::from(c) + 0xFFEF_0001`) | `+` | REFUTED |
//! | `into_two_u16_in_loop` (`a.into() * b.into()`, `u16 → u32`) | `*` | not REFUTED |
//! | `into_u16_times_u32_in_loop` (`a.into() * b`, `b: u32`) | `*` | REFUTED |
//! | `product_three_u32_from` (`u64::from(x) * u64::from(y) * u64::from(x)`) | `*` | not all PROVED |
//! | `signed_from_in_loop` (`i64::from(x) + (i64::MAX - 2^31 + 1)`, `x: i32`) | `+` | PROVED |
//! | `signed_from_in_loop_over` (`i64::from(x) + (i64::MAX - 2^31 + 2)`) | `+` | REFUTED |
//! | `char_into_in_loop` (`c.into(): u32` `+ 0xFFEF_0000`) | `+` | PROVED |
//! | `char_into_in_loop_over` (`c.into(): u32` `+ 0xFFEF_0001`) | `+` | REFUTED |
//!
//! # Fixtures
//!
//! `tests/fixtures/from_range_*_mir.json` are the compiler's own extraction,
//! captured on a Trust stage 1 with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> from_range.rs
//! ```
//!
//! ```text
//! pub struct P { pub x: u32, pub y: u32, pub z: u64 }
//! pub fn sum_two_u32_from(ps: &[P]) -> bool {
//!     for p in ps { if u64::from(p.x) + u64::from(p.y) > 7 { return true; } }
//!     false
//! }
//! pub fn sum_u32_from_and_u64(ps: &[P]) -> bool {
//!     for p in ps { if u64::from(p.x) + p.z > 7 { return true; } }
//!     false
//! }
//! pub fn product_three_u32_from(ps: &[P]) -> bool {
//!     for p in ps { if u64::from(p.x) * u64::from(p.y) * u64::from(p.x) > 7 { return true; } }
//!     false
//! }
//! pub fn bool_from_in_loop(bs: &[bool]) -> bool {
//!     for b in bs { if usize::from(*b) + (usize::MAX - 1) > 7 { return true; } }
//!     false
//! }
//! pub fn bool_from_in_loop_over(bs: &[bool]) -> bool {
//!     for b in bs { if usize::from(*b) + usize::MAX > 7 { return true; } }
//!     false
//! }
//! pub fn char_from_in_loop(cs: &[char]) -> bool {
//!     for c in cs { if u32::from(*c) + 0xFFEF_0000 > 7 { return true; } }
//!     false
//! }
//! pub fn char_from_in_loop_over(cs: &[char]) -> bool {
//!     for c in cs { if u32::from(*c) + 0xFFEF_0001 > 7 { return true; } }
//!     false
//! }
//! pub fn into_two_u16_in_loop(ps: &[(u16, u16)]) -> bool {
//!     for &(a, b) in ps { let a: u32 = a.into(); let b: u32 = b.into(); if a * b > 7 { return true; } }
//!     false
//! }
//! pub fn into_u16_times_u32_in_loop(ps: &[(u16, u32)]) -> bool {
//!     for &(a, b) in ps { let a: u32 = a.into(); if a * b > 7 { return true; } }
//!     false
//! }
//! // second capture (same command, review round): a signed source and the `Into`
//! // spelling of `char`.
//! pub fn signed_from_in_loop(xs: &[i32]) -> bool {
//!     for x in xs { if i64::from(*x) + (i64::MAX - 2_147_483_647) > 7 { return true; } }
//!     false
//! }
//! pub fn signed_from_in_loop_over(xs: &[i32]) -> bool {
//!     for x in xs { if i64::from(*x) + (i64::MAX - 2_147_483_646) > 7 { return true; } }
//!     false
//! }
//! pub fn char_into_in_loop(cs: &[char]) -> bool {
//!     for &c in cs { let v: u32 = c.into(); if v + 0xFFEF_0000 > 7 { return true; } }
//!     false
//! }
//! pub fn char_into_in_loop_over(cs: &[char]) -> bool {
//!     for &c in cs { let v: u32 = c.into(); if v + 0xFFEF_0001 > 7 { return true; } }
//!     false
//! }
//! ```
use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/from_range_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The verdict of every `ArithmeticOverflow { op }` row of `name`, each
/// dispatched to the deterministic in-process ay the bridge uses.
fn overflow_rows(name: &str, op: BinOp) -> Vec<String> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            let mut rows = Vec::new();
            for vc in &vcs {
                if !matches!(&vc.kind, VcKind::ArithmeticOverflow { op: o, .. } if *o == op) {
                    continue;
                }
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
                rows.push(verdict);
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn assert_all_proved(name: &str, op: BinOp, why: &str) {
    let rows = overflow_rows(name, op);
    assert!(!rows.is_empty(), "`{name}` must produce a `{op:?}` overflow row");
    assert!(rows.iter().all(|v| v == "PROVED"), "{why}: {rows:?}");
}

fn assert_some_refuted(name: &str, op: BinOp, why: &str) {
    let rows = overflow_rows(name, op);
    assert!(rows.iter().any(|v| v == "REFUTED"), "{why}: {rows:?}");
}

#[test]
fn two_u32_widenings_summed_in_a_loop_prove() {
    assert_all_proved(
        "sum_two_u32_from",
        BinOp::Add,
        "`u64::from(x) + u64::from(y)` is at most 2^33 - 2; a refutation is a counterexample \
         over a lossless conversion that lost its source range in the loop",
    );
}

#[test]
fn a_u32_widening_plus_a_full_u64_stays_refuted() {
    assert_some_refuted(
        "sum_u32_from_and_u64",
        BinOp::Add,
        "`u64::from(x) + z` with `z: u64` overflows at `z = u64::MAX`; this must stay refuted",
    );
}

#[test]
fn bool_widening_in_a_loop_proves() {
    assert_all_proved(
        "bool_from_in_loop",
        BinOp::Add,
        "`usize::from(b)` is 0 or 1, so `+ (usize::MAX - 1)` cannot overflow",
    );
}

#[test]
fn bool_widening_plus_usize_max_stays_refuted() {
    assert_some_refuted(
        "bool_from_in_loop_over",
        BinOp::Add,
        "`usize::from(true) + usize::MAX` overflows; this must stay refuted",
    );
}

#[test]
fn char_widening_in_a_loop_proves() {
    assert_all_proved(
        "char_from_in_loop",
        BinOp::Add,
        "`u32::from(c)` is at most `char::MAX` = 0x10FFFF, and 0x10FFFF + 0xFFEF0000 = u32::MAX",
    );
}

#[test]
fn char_widening_one_past_the_edge_stays_refuted() {
    assert_some_refuted(
        "char_from_in_loop_over",
        BinOp::Add,
        "`u32::from(char::MAX) + 0xFFEF0001` overflows; this must stay refuted",
    );
}

#[test]
fn signed_widening_in_a_loop_proves() {
    assert_all_proved(
        "signed_from_in_loop",
        BinOp::Add,
        "`i64::from(x)` with `x: i32` is at most 2^31 - 1, and (2^31 - 1) + (i64::MAX - (2^31 - 1)) \
         = i64::MAX",
    );
}

#[test]
fn signed_widening_one_past_the_edge_stays_refuted() {
    assert_some_refuted(
        "signed_from_in_loop_over",
        BinOp::Add,
        "`i64::from(i32::MAX) + (i64::MAX - 2^31 + 2)` overflows; this must stay refuted",
    );
}

#[test]
fn char_into_in_a_loop_proves() {
    assert_all_proved(
        "char_into_in_loop",
        BinOp::Add,
        "`<char as Into<u32>>::into(c)` is at most 0x10FFFF, and 0x10FFFF + 0xFFEF0000 = u32::MAX",
    );
}

#[test]
fn char_into_one_past_the_edge_stays_refuted() {
    assert_some_refuted(
        "char_into_in_loop_over",
        BinOp::Add,
        "`char::MAX.into() + 0xFFEF0001` overflows; this must stay refuted",
    );
}

#[test]
fn two_u16_into_u32_multiplied_in_a_loop_is_not_refuted() {
    let rows = overflow_rows("into_two_u16_in_loop", BinOp::Mul);
    assert!(!rows.is_empty(), "the fixture must produce a `Mul` overflow row");
    assert!(
        rows.iter().all(|v| v != "REFUTED"),
        "`a * b` over two `u16 → u32` widenings is at most (2^16 - 1)^2 < 2^32: {rows:?}"
    );
}

#[test]
fn a_u16_into_times_a_full_u32_stays_refuted() {
    assert_some_refuted(
        "into_u16_times_u32_in_loop",
        BinOp::Mul,
        "`u32::from(a) * b` with `b: u32` overflows; this must stay refuted",
    );
}

/// The nonlinear control: the in-process solver answers Unknown on this product
/// (measured 2026-10-03), so the pin is the weaker "never PROVED" — a source
/// range must not make a real `2^96` overflow look discharged.
#[test]
fn three_u32_widenings_multiplied_are_never_proved() {
    let rows = overflow_rows("product_three_u32_from", BinOp::Mul);
    assert!(!rows.is_empty(), "the fixture must produce a `Mul` overflow row");
    assert!(
        rows.iter().any(|v| v != "PROVED"),
        "`x * y * x` over `u32 → u64` widenings reaches 2^96; the outer product must not prove: {rows:?}"
    );
}

/// The verdicts of `name`'s `op` rows after `mutate` rewrote the fixture.
fn overflow_rows_mutated(
    name: &str,
    op: BinOp,
    mutate: impl FnOnce(&mut VerifiableFunction),
) -> Vec<String> {
    let mut func = load(name);
    mutate(&mut func);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            vcs.iter()
                .filter(
                    |vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op: o, .. } if *o == op),
                )
                .map(|vc| {
                    match router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1
                    {
                        VerificationResult::Proved { .. } => "PROVED".to_string(),
                        VerificationResult::Failed { .. } => "REFUTED".to_string(),
                        other => format!("{other:?}").chars().take(24).collect(),
                    }
                })
                .collect()
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

/// Rewrite every `From<u32>` conversion call of the fixture with `edit(callee,
/// arg_local, func)`.
fn edit_conversion_calls(
    func: &mut VerifiableFunction,
    edit: impl Fn(&mut String, usize, &mut Vec<trust_types::LocalDecl>),
) {
    let locals = &mut func.body.locals;
    for block in &mut func.body.blocks {
        if let trust_types::Terminator::Call { func: callee, args, .. } = &mut block.terminator
            && callee.contains("From<u32>")
            && let Some(trust_types::Operand::Copy(p) | trust_types::Operand::Move(p)) =
                args.first()
        {
            let local = p.local;
            edit(callee, local, locals);
        }
    }
}

/// MUTATION: the same fixture with the conversion's trait moved to a user crate.
/// The range is a fact about `core`'s impl only, so the row must go back to its
/// pre-fix verdict.
#[test]
fn a_user_trait_spelling_gets_no_source_range() {
    let rows = overflow_rows_mutated("sum_two_u32_from", BinOp::Add, |func| {
        edit_conversion_calls(func, |callee, _, _| {
            *callee = callee.replace("core::convert::From", "mycrate::convert::From");
        });
    });
    assert!(
        rows.iter().all(|v| v != "PROVED"),
        "a `mycrate::convert::From` callee is not std's lossless conversion: {rows:?}"
    );
}

/// MUTATION: the std spelling, but the ARGUMENT's declared type is not the `u32`
/// the spelling names (as for a generic parameter NAMED `u32`, which renders the
/// same path). The declared types are the authentication; the row must not prove.
#[test]
fn a_spelling_whose_argument_is_not_the_named_primitive_gets_no_source_range() {
    let rows = overflow_rows_mutated("sum_two_u32_from", BinOp::Add, |func| {
        edit_conversion_calls(func, |_, arg, locals| {
            for decl in locals.iter_mut().filter(|d| d.index == arg) {
                decl.ty = trust_types::Ty::Int { width: 64, signed: false };
            }
        });
    });
    assert!(
        rows.iter().all(|v| v != "PROVED"),
        "an argument declared `u64` is not a `u32` source, whatever the path says: {rows:?}"
    );
}
