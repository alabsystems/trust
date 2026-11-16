//! THE E6 DIFFERENTIAL HARNESS — increment P of the E6 admission expansion
//! (`docs/design-notes/2026-09-28-e6-admission-expansion.md` §6, review H14).
//!
//! # What it checks
//!
//! An E6 import turns a Rust body into a kernel DEFINITION, and every E9
//! discharge then closes by definitional equality against it. The kernel checks
//! that the definition is well-typed; it CANNOT check that the definition means
//! what the Rust body computes. That reading — extractor, reader, mint — is in
//! the trusted base (`docs/TCB.md`, `EnsuresCitationDischarge`), and a wrong
//! reading is a false `Certified` with nothing downstream to catch it (review
//! H1: `a < b` on `bool` certified against an `==` image).
//!
//! So this harness executes both sides and compares them, for EVERY input:
//!
//! * the Rust side is `fixtures/e6_differential/shapes.rs`, `include!`d below
//!   and run natively;
//! * the Lean side is the SAME source's MIR, as a Trust compiler extracted it
//!   (`-Ztrust-dump=mir:`, checked in as `shapes.{unopt,opt}.json` by
//!   `regen.py`), imported through the production entry point
//!   [`admit_function_into`], and EVALUATED by the Clean kernel: `whnf` of the
//!   minted constant applied to literal arguments, decoded back to a value.
//!
//! Inputs are EXHAUSTIVE over `u8`, `i8` and `bool` parameters (65 536 pairs
//! for a binary `u8` shape, every tuple of up to three `bool`s) and over the
//! one-parameter `u16`/`i16` rows, and SAMPLED — every boundary plus a fixed
//! pseudo-random spread ([`domain_values`] lists each) — for `u32`, `i32`,
//! `u64`, `i64` and `i128`, which every carrier the E6 tree reader and
//! producer admit has a row over (review P1-2). A `char` row
//! ([`CHAR_SHAPES`]) is fed valid scalar values only. Any disagreement fails,
//! naming the shape, the opt level and the input; so does a minted image of
//! a body that PANICS on an input.
//!
//! The `v_*` shapes take `&Flags` and are imported the way the compiler
//! imports a `&self` / `&T` function: as their borrow-erased PARAMETER VIEW
//! (`trust_types::e6_param_view`, over the frozen-field table the compiler
//! records), through `admit_view_function_into`, and evaluated on the view's
//! by-value field parameters. That view puts single-assignment temporaries
//! (the field reads) in front of the E6-only reader; since I3′ the
//! short-circuit shapes do too, as the temporaries rustc joins `&&`/`||` in.
//!
//! Each function also carries an EXPECTATION — admitted or refused — so the
//! harness is a ratchet as well: an increment that widens the fragment flips
//! the expectation in the same diff, and every newly admitted shape is then
//! differentially checked on its first run. A shape nobody expected to mint
//! that starts minting fails here before any UI fixture is written.
//!
//! # What it does not check
//!
//! * The FACET gate. Every body is offered with all four facets certified, so
//!   the harness exercises the reader and the mint on shapes the real facet
//!   gate might refuse. That only widens what is checked.
//! * Widths above 16 bits exhaustively. The images are width-parametric in the
//!   mint, but a slip at `u32`..`i128` that the boundary-plus-spread sample
//!   misses would be seen only by the UI fixtures.
//! * Every BODY. A row per carrier and construct is checked; a shape no row
//!   spells rests on the kernel's typing of its image alone.
//! * Spellings of the ISLAND side. Whether an author's `a == b` elaborates to
//!   a term defeq to the image is the kernel's question, and the UI fixtures
//!   ask it; this harness asks whether the image is the RUST function.
//!
//! Runnable with no compiler build:
//! `targo --unverified test --manifest-path crates/Cargo.toml -p trust-certify --test e6_differential`

use std::collections::BTreeMap;
use std::ffi::OsStr;

use clean_kernel::{Environment, Expr, ExprKind, Literal, TypeChecker};
use trust_certify::clean_island::{admit_function_into, admit_view_function_into};
use trust_spec_elab::FacetTable;
use trust_types::e6_param_view::{
    E6ParamView, FrozenPointee, FrozenRow, FrozenSharedParams, e6_param_view,
};
use trust_types::{Ty, VerifiableFunction};

#[allow(
    dead_code,
    clippy::bool_comparison,
    clippy::eq_op,
    clippy::nonminimal_bool,
    clippy::bool_to_int_with_if,
    clippy::manual_range_contains,
    clippy::match_bool,
    clippy::match_like_matches_macro,
    clippy::needless_bool,
    clippy::if_not_else,
    clippy::precedence
)]
mod shapes {
    include!("fixtures/e6_differential/shapes.rs");
}

/// Inputs evaluated per fresh kernel checker (see the harness loop).
const CHECKER_BATCH: usize = 4096;

const SHAPES_SRC: &str = include_str!("fixtures/e6_differential/shapes.rs");
const UNOPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.unopt.json");
const OPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.opt.json");

/// Respect the machine-wide admission without changing the unmanaged harness's
/// existing host-sized (at most six) pool. Keep this policy local to the test:
/// it changes scheduling, never the image/input population or kernel budgets.
fn evaluation_workers(
    available: usize,
    build_slot_held: Option<&OsStr>,
    cargo_build_jobs: Option<&OsStr>,
) -> Result<usize, &'static str> {
    let host_limit = available.max(1).min(6);
    if build_slot_held != Some(OsStr::new("1")) {
        return Ok(host_limit);
    }
    let share = cargo_build_jobs
        .and_then(OsStr::to_str)
        .filter(|value| !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|value| value.parse::<u32>().ok())
        .filter(|value| *value > 0)
        .ok_or("BUILD_SLOT_HELD=1 requires a positive u32 CARGO_BUILD_JOBS share")?;
    Ok(host_limit.min(share as usize))
}

#[test]
fn evaluation_workers_respect_the_admitted_share_and_existing_host_limit() {
    let held = Some(OsStr::new("1"));
    assert_eq!(evaluation_workers(28, held, Some(OsStr::new("2"))), Ok(2));
    assert_eq!(evaluation_workers(28, held, Some(OsStr::new("1"))), Ok(1));
    assert_eq!(evaluation_workers(28, held, Some(OsStr::new("16"))), Ok(6));
    assert_eq!(evaluation_workers(1, held, Some(OsStr::new("2"))), Ok(1));
}

#[test]
fn evaluation_workers_preserve_unmanaged_behavior() {
    for held in [None, Some(OsStr::new("0")), Some(OsStr::new(""))] {
        for share in [None, Some(OsStr::new("2")), Some(OsStr::new("invalid"))] {
            assert_eq!(evaluation_workers(28, held, share), Ok(6));
            assert_eq!(evaluation_workers(1, held, share), Ok(1));
        }
    }
}

#[test]
fn evaluation_workers_refuse_missing_or_malformed_admitted_shares() {
    let held = Some(OsStr::new("1"));
    assert!(evaluation_workers(28, held, None).is_err());
    for share in ["", "0", "-1", "+2", " 2", "2 ", "2.0", "4294967296"] {
        assert!(evaluation_workers(28, held, Some(OsStr::new(share))).is_err(), "{share:?}");
    }
}

#[cfg(unix)]
#[test]
fn evaluation_workers_refuse_non_unicode_admitted_shares() {
    use std::os::unix::ffi::OsStrExt;

    let share = Some(OsStr::from_bytes(b"2\xff"));
    assert!(evaluation_workers(28, Some(OsStr::new("1")), share).is_err());
    assert_eq!(evaluation_workers(28, None, share), Ok(6));
}

/// Whether the E6 importer is EXPECTED to mint a function today. Moving an
/// entry from `Refused` to `Admitted` is the ratchet an increment turns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    Admitted,
    Refused,
}
use Expect::{Admitted, Refused};

/// The expectation table: `(function, unoptimized, -O)`. Both opt levels are
/// listed because the readers see the optimizer's MIR, and the two are not
/// always read alike.
const EXPECTATIONS: &[(&str, Expect, Expect)] = &[
    ("k_const", Admitted, Admitted),
    ("k_const_param", Admitted, Admitted),
    ("k_neg_i8", Admitted, Admitted),
    ("p_second", Admitted, Admitted),
    ("p_bool", Admitted, Admitted),
    ("p_i8", Admitted, Admitted),
    ("s_lt", Admitted, Admitted),
    ("s_le", Admitted, Admitted),
    ("s_eq", Admitted, Admitted),
    ("s_lt_i8", Admitted, Admitted),
    ("sl_lt", Admitted, Admitted),
    ("sl_eq", Admitted, Admitted),
    ("c_lt", Admitted, Admitted),
    ("c_le", Admitted, Admitted),
    ("c_eq", Admitted, Admitted),
    ("c_gt", Admitted, Admitted),
    ("c_ge", Admitted, Admitted),
    ("c_ne", Admitted, Admitted),
    ("c_lit", Admitted, Admitted),
    ("c_lit_left", Admitted, Admitted),
    ("c_lt_i8", Admitted, Admitted),
    ("c_ge_neg_i8", Admitted, Admitted),
    ("b_and", Admitted, Admitted),
    ("b_or", Admitted, Admitted),
    ("b_and_i8", Admitted, Admitted),
    ("w_add", Admitted, Admitted),
    ("w_sub", Admitted, Admitted),
    ("w_mul", Admitted, Admitted),
    ("w_add_lit", Admitted, Admitted),
    ("w_chain", Admitted, Admitted),
    ("ck_add_i8", Admitted, Admitted),
    ("ck_sub_i8", Admitted, Admitted),
    ("ck_mul_i8", Admitted, Admitted),
    // Refused at this HEAD by the FACET gate: rustc leaves the guard's
    // `i64::MIN as i128` literal casts in the MIR at both opt levels, and the
    // firewall declines a cast of a constant (MEASURED on the dump). The
    // image is checked here the day a fold makes the shape reachable.
    ("gn_narrow", Refused, Refused),
    ("we_eq", Admitted, Admitted),
    ("bb_eq", Admitted, Admitted),
    ("bb_ne", Admitted, Admitted),
    ("bb_lt", Refused, Refused),
    ("bb_le", Refused, Refused),
    ("bb_gt", Refused, Refused),
    ("bb_eq_true", Admitted, Admitted),
    ("bb_ne_false", Admitted, Admitted),
    // I3′: rustc's `InstSimplify` rewrites `a == false` to `!a` (MEASURED on
    // the dump), which the tree reader reads as a negation.
    ("bb_eq_false", Admitted, Admitted),
    ("bb_eq_mixed", Refused, Refused),
    ("bb_eq_of_cmps", Admitted, Admitted),
    // E6 expansion I3′ and I4′ TARGET shapes (`shapes.rs`), added EXPECTED
    // REFUSED before either reader change lands, so the harness first proves
    // the fragment does not read them today; each increment flips its own
    // rows in the diff that widens the reader.
    ("t_and", Admitted, Admitted),
    ("t_or", Admitted, Admitted),
    ("t_not", Admitted, Admitted),
    ("t_or3", Admitted, Admitted),
    ("t_and3", Admitted, Admitted),
    ("ay_gate_keeps_sat", Admitted, Admitted),
    ("ay_lemma_admitted_inductive", Admitted, Admitted),
    ("ay_xor_accumulate_parity", Admitted, Admitted),
    ("t_bor", Admitted, Admitted),
    ("t_not_and", Admitted, Admitted),
    ("t_not_or", Admitted, Admitted),
    ("t_and_not", Admitted, Admitted),
    ("t_nested", Admitted, Admitted),
    ("t_and_or_mix", Admitted, Admitted),
    ("t_let", Admitted, Admitted),
    ("t_eq_tree", Admitted, Admitted),
    ("t_ne_tree", Admitted, Admitted),
    ("t_xor_eq", Admitted, Admitted),
    ("t_cmp3", Admitted, Admitted),
    ("t_cmp6", Admitted, Admitted),
    ("t_ne_lit", Admitted, Admitted),
    // Already the frozen `BoolBinary` (an `&&`/`||` of exactly two comparison
    // leaves), so the chain reads it before any E6-only reader is asked.
    ("t_digit", Admitted, Admitted),
    ("t_mixed", Admitted, Admitted),
    // The frozen `BoolBinary` again (`a < b || a == -1`).
    ("t_i8", Admitted, Admitted),
    ("t_not_cmp", Admitted, Admitted),
    ("t_cmp3_u32", Admitted, Admitted),
    ("t_bool_lt_tree", Refused, Refused),
    ("t_bit_u8", Refused, Refused),
    ("t_cmp_of_select", Refused, Refused),
    ("d_if_bool", Admitted, Admitted),
    ("d_if_u8", Admitted, Admitted),
    ("d_if_const", Admitted, Admitted),
    ("d_sel_const", Admitted, Admitted),
    ("d_match_u8", Admitted, Admitted),
    ("d_match_bool", Admitted, Admitted),
    ("d_matches", Admitted, Admitted),
    ("d_match_i8", Admitted, Admitted),
    ("d_matches_i8", Admitted, Admitted),
    ("d_chain", Admitted, Admitted),
    ("d_max", Admitted, Admitted),
    ("d_ge_sel", Admitted, Admitted),
    ("d_ne_sel", Admitted, Admitted),
    ("d_if_not", Admitted, Admitted),
    ("d_range", Admitted, Admitted),
    ("d_match_u8_bool", Admitted, Admitted),
    ("d_if_cmp_bool", Admitted, Admitted),
    ("d_match_param_arms", Admitted, Admitted),
    ("d_if_i8", Admitted, Admitted),
    ("d_if_nested", Admitted, Admitted),
    // A guard is not visible as such in the extracted MIR: unoptimized, `n if
    // n > 5` is exactly `if x > 5` (read, and executed below); `-O` keeps the
    // guard's borrow of its binding, which no reader reads.
    ("d_guard", Admitted, Refused),
    ("d_bind", Admitted, Admitted),
    ("d_match_u64", Admitted, Admitted),
    ("d_sel_i32", Admitted, Admitted),
    ("d_range_exh", Refused, Refused),
    // Review P1-2: a row per carrier the tree reader and producer admit.
    ("d_match_i128", Admitted, Admitted),
    ("d_sel_i128", Admitted, Admitted),
    ("d_sel_i64", Admitted, Admitted),
    ("d_match_i64", Admitted, Admitted),
    ("t_i8_ord", Admitted, Admitted),
    ("d_sel_i8_ord", Admitted, Admitted),
    ("d_match_u16", Admitted, Admitted),
    ("d_match_i16", Admitted, Admitted),
    ("t_u16", Admitted, Admitted),
    ("t_i16", Admitted, Admitted),
    ("d_match_u32", Admitted, Admitted),
    ("d_match_i32", Admitted, Admitted),
    // Read, but the producer has no image at `U128`.
    ("d_match_u128", Refused, Refused),
    // Refused by the reader: the label `u128::MAX` has no `i128` spelling.
    ("d_match_u128_max", Refused, Refused),
    ("d_match_char", Admitted, Admitted),
    ("d_if_bool_eq", Admitted, Admitted),
    ("d_if_not_lt", Admitted, Admitted),
    ("d_if_not_lt_let", Admitted, Admitted),
    // Review P1-3: an effect or a partial operation in an ARM position. A
    // mint of any of these but the last is a soundness incident, not an
    // expectation to flip (the Rust side of several is partial: `check_image`
    // reports a native panic under a minted image as a failure of its own).
    // The last, `i_if_wrapping`, is total and admitted since TG14
    // (E6-TG14-PANIC-EDGE-1); it keeps its place because
    // `every_shape_has_an_expectation_and_a_native_arm` pins this list to the
    // declaration order of `shapes.rs`, whose own P1-3 comment cannot change
    // without regenerating both dumps.
    ("i_or_call", Refused, Refused),
    ("i_and_add", Refused, Refused),
    ("i_or_div", Refused, Refused),
    ("i_and_index", Refused, Refused),
    ("i_and_const_index", Refused, Refused),
    ("i_match_call", Refused, Refused),
    // TG14 (design note I2′/I4′), NOT a P1-3 partial operation: the marked
    // `wrapping_add` is a compiler-authenticated total primitive, read as its
    // exact modular image and executed against the Rust body on every input
    // below. The panicking `+` beside it (`i_and_add`) stays refused.
    ("i_if_wrapping", Admitted, Admitted),
];

/// The shapes whose `u32` parameters are `char`s in the source (the
/// extraction the E6 lane reads lowers `char` to its `u32` scalar value). Their
/// inputs are VALID scalar values only ([`char_samples`]): a `char` holds
/// nothing else, so an image is checked on exactly the values it can meet.
const CHAR_SHAPES: &[&str] = &["d_match_char"];

/// The PARAMETER-VIEW shapes (`&Flags` parameters), `(function, unoptimized,
/// -O)`. Each is imported as its borrow-erased view ([`view_of`]) through
/// `admit_view_function_into`, the entry the compiler uses for a `&self` /
/// `&T` function, and evaluated on the VIEW's by-value parameters. The view
/// puts single-assignment temporaries in front of the E6-only reader
/// (`view_fields_reach_the_readers_temporaries`).
const VIEW_EXPECTATIONS: &[(&str, Expect, Expect)] = &[
    ("v_ne", Admitted, Admitted),
    ("v_eq", Admitted, Admitted),
    ("v_ne_other", Admitted, Admitted),
    ("v_ne_two", Admitted, Admitted),
    ("v_lt", Refused, Refused),
    // E6 expansion I3′/I4′ targets through the view, expected REFUSED first.
    ("v_and", Admitted, Admitted),
    ("v_tree", Admitted, Admitted),
    ("v_sel", Admitted, Admitted),
    ("v_match", Admitted, Admitted),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    U8(u8),
    I8(i8),
    Bool(bool),
    I64(i64),
    I128(i128),
    U32(u32),
    U64(u64),
    I32(i32),
    U16(u16),
    I16(i16),
    U128(u128),
    /// A `[bool; 4]` argument: only ever an argument of a REFUSED row (no
    /// kernel literal exists for it; see [`kernel_arg`]).
    Bools4([bool; 4]),
    OptI8(Option<i8>),
    OptI64(Option<i64>),
}

fn u8_of(v: Val) -> u8 {
    match v {
        Val::U8(x) => x,
        other => panic!("expected a u8 argument, got {other:?}"),
    }
}
fn i8_of(v: Val) -> i8 {
    match v {
        Val::I8(x) => x,
        other => panic!("expected an i8 argument, got {other:?}"),
    }
}
fn bool_of(v: Val) -> bool {
    match v {
        Val::Bool(x) => x,
        other => panic!("expected a bool argument, got {other:?}"),
    }
}
fn i64_of(v: Val) -> i64 {
    match v {
        Val::I64(x) => x,
        other => panic!("expected an i64 argument, got {other:?}"),
    }
}
fn i128_of(v: Val) -> i128 {
    match v {
        Val::I128(x) => x,
        other => panic!("expected an i128 argument, got {other:?}"),
    }
}
fn u32_of(v: Val) -> u32 {
    match v {
        Val::U32(x) => x,
        other => panic!("expected a u32 argument, got {other:?}"),
    }
}
fn u64_of(v: Val) -> u64 {
    match v {
        Val::U64(x) => x,
        other => panic!("expected a u64 argument, got {other:?}"),
    }
}
fn i32_of(v: Val) -> i32 {
    match v {
        Val::I32(x) => x,
        other => panic!("expected an i32 argument, got {other:?}"),
    }
}
fn u16_of(v: Val) -> u16 {
    match v {
        Val::U16(x) => x,
        other => panic!("expected a u16 argument, got {other:?}"),
    }
}
fn i16_of(v: Val) -> i16 {
    match v {
        Val::I16(x) => x,
        other => panic!("expected an i16 argument, got {other:?}"),
    }
}
fn u128_of(v: Val) -> u128 {
    match v {
        Val::U128(x) => x,
        other => panic!("expected a u128 argument, got {other:?}"),
    }
}
fn bools4_of(v: Val) -> [bool; 4] {
    match v {
        Val::Bools4(x) => x,
        other => panic!("expected a [bool; 4] argument, got {other:?}"),
    }
}
/// A `char` argument, carried as the `u32` scalar value the extraction reads.
fn char_of(v: Val) -> char {
    let x = u32_of(v);
    char::from_u32(x)
        .unwrap_or_else(|| panic!("{x:#x} is not a char; CHAR_SHAPES feeds scalar values"))
}

/// Run `name` natively on `args`. Every `shapes.rs` function has exactly one
/// arm, and [`every_shape_has_an_expectation_and_a_native_arm`] holds the
/// three lists (source, expectations, this match) together.
fn native(name: &str, a: &[Val]) -> Val {
    use shapes::*;
    match name {
        "k_const" => Val::U8(k_const()),
        "k_const_param" => Val::U8(k_const_param(u8_of(a[0]))),
        "k_neg_i8" => Val::I8(k_neg_i8()),
        "p_second" => Val::U8(p_second(u8_of(a[0]), u8_of(a[1]))),
        "p_bool" => Val::Bool(p_bool(bool_of(a[0]))),
        "p_i8" => Val::I8(p_i8(i8_of(a[0]))),
        "s_lt" => Val::U8(s_lt(u8_of(a[0]), u8_of(a[1]))),
        "s_le" => Val::U8(s_le(u8_of(a[0]), u8_of(a[1]))),
        "s_eq" => Val::U8(s_eq(u8_of(a[0]), u8_of(a[1]))),
        "s_lt_i8" => Val::I8(s_lt_i8(i8_of(a[0]), i8_of(a[1]))),
        "sl_lt" => Val::U8(sl_lt(u8_of(a[0]), u8_of(a[1]))),
        "sl_eq" => Val::U8(sl_eq(u8_of(a[0]), u8_of(a[1]))),
        "c_lt" => Val::Bool(c_lt(u8_of(a[0]), u8_of(a[1]))),
        "c_le" => Val::Bool(c_le(u8_of(a[0]), u8_of(a[1]))),
        "c_eq" => Val::Bool(c_eq(u8_of(a[0]), u8_of(a[1]))),
        "c_gt" => Val::Bool(c_gt(u8_of(a[0]), u8_of(a[1]))),
        "c_ge" => Val::Bool(c_ge(u8_of(a[0]), u8_of(a[1]))),
        "c_ne" => Val::Bool(c_ne(u8_of(a[0]), u8_of(a[1]))),
        "c_lit" => Val::Bool(c_lit(u8_of(a[0]))),
        "c_lit_left" => Val::Bool(c_lit_left(u8_of(a[0]))),
        "c_lt_i8" => Val::Bool(c_lt_i8(i8_of(a[0]), i8_of(a[1]))),
        "c_ge_neg_i8" => Val::Bool(c_ge_neg_i8(i8_of(a[0]))),
        "b_and" => Val::Bool(b_and(u8_of(a[0]), u8_of(a[1]))),
        "b_or" => Val::Bool(b_or(u8_of(a[0]), u8_of(a[1]))),
        "b_and_i8" => Val::Bool(b_and_i8(i8_of(a[0]), i8_of(a[1]))),
        "w_add" => Val::U8(w_add(u8_of(a[0]), u8_of(a[1]))),
        "w_sub" => Val::U8(w_sub(u8_of(a[0]), u8_of(a[1]))),
        "w_mul" => Val::U8(w_mul(u8_of(a[0]), u8_of(a[1]))),
        "w_add_lit" => Val::U8(w_add_lit(u8_of(a[0]))),
        "w_chain" => Val::U8(w_chain(u8_of(a[0]), u8_of(a[1]))),
        "ck_add_i8" => Val::OptI8(ck_add_i8(i8_of(a[0]), i8_of(a[1]))),
        "ck_sub_i8" => Val::OptI8(ck_sub_i8(i8_of(a[0]), i8_of(a[1]))),
        "ck_mul_i8" => Val::OptI8(ck_mul_i8(i8_of(a[0]), i8_of(a[1]))),
        "gn_narrow" => Val::OptI64(gn_narrow(i128_of(a[0]))),
        "we_eq" => Val::Bool(we_eq(i64_of(a[0]), i128_of(a[1]))),
        "bb_eq" => Val::Bool(bb_eq(bool_of(a[0]), bool_of(a[1]))),
        "bb_ne" => Val::Bool(bb_ne(bool_of(a[0]), bool_of(a[1]))),
        "bb_lt" => Val::Bool(bb_lt(bool_of(a[0]), bool_of(a[1]))),
        "bb_le" => Val::Bool(bb_le(bool_of(a[0]), bool_of(a[1]))),
        "bb_gt" => Val::Bool(bb_gt(bool_of(a[0]), bool_of(a[1]))),
        "bb_eq_true" => Val::Bool(bb_eq_true(bool_of(a[0]))),
        "bb_ne_false" => Val::Bool(bb_ne_false(bool_of(a[0]), bool_of(a[1]))),
        "bb_eq_false" => Val::Bool(bb_eq_false(bool_of(a[0]), bool_of(a[1]))),
        "bb_eq_mixed" => Val::Bool(bb_eq_mixed(bool_of(a[0]), u8_of(a[1]))),
        "bb_eq_of_cmps" => Val::Bool(bb_eq_of_cmps(u8_of(a[0]), u8_of(a[1]), bool_of(a[2]))),
        "t_and" => Val::Bool(t_and(bool_of(a[0]), bool_of(a[1]))),
        "t_or" => Val::Bool(t_or(bool_of(a[0]), bool_of(a[1]))),
        "t_not" => Val::Bool(t_not(bool_of(a[0]))),
        "t_or3" => Val::Bool(t_or3(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_and3" => Val::Bool(t_and3(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "ay_gate_keeps_sat" => {
            Val::Bool(ay_gate_keeps_sat(bool_of(a[0]), bool_of(a[1]), bool_of(a[2])))
        }
        "ay_lemma_admitted_inductive" => {
            Val::Bool(ay_lemma_admitted_inductive(bool_of(a[0]), bool_of(a[1]), bool_of(a[2])))
        }
        "ay_xor_accumulate_parity" => {
            Val::Bool(ay_xor_accumulate_parity(bool_of(a[0]), bool_of(a[1])))
        }
        "t_bor" => Val::Bool(t_bor(bool_of(a[0]), bool_of(a[1]))),
        "t_not_and" => Val::Bool(t_not_and(bool_of(a[0]), bool_of(a[1]))),
        "t_not_or" => Val::Bool(t_not_or(bool_of(a[0]), bool_of(a[1]))),
        "t_and_not" => Val::Bool(t_and_not(bool_of(a[0]), bool_of(a[1]))),
        "t_nested" => Val::Bool(t_nested(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_and_or_mix" => Val::Bool(t_and_or_mix(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_let" => Val::Bool(t_let(bool_of(a[0]), bool_of(a[1]))),
        "t_eq_tree" => Val::Bool(t_eq_tree(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_ne_tree" => Val::Bool(t_ne_tree(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_xor_eq" => Val::Bool(t_xor_eq(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_cmp3" => Val::Bool(t_cmp3(u8_of(a[0]), u8_of(a[1]))),
        "t_cmp6" => Val::Bool(t_cmp6(u8_of(a[0]))),
        "t_ne_lit" => Val::Bool(t_ne_lit(u8_of(a[0]))),
        "t_digit" => Val::Bool(t_digit(u8_of(a[0]))),
        "t_mixed" => Val::Bool(t_mixed(u8_of(a[0]), u8_of(a[1]), bool_of(a[2]))),
        "t_i8" => Val::Bool(t_i8(i8_of(a[0]), i8_of(a[1]))),
        "t_not_cmp" => Val::Bool(t_not_cmp(u8_of(a[0]), u8_of(a[1]))),
        "t_cmp3_u32" => Val::Bool(t_cmp3_u32(u32_of(a[0]), u32_of(a[1]))),
        "t_bool_lt_tree" => Val::Bool(t_bool_lt_tree(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "t_bit_u8" => Val::Bool(t_bit_u8(u8_of(a[0]), u8_of(a[1]))),
        "t_cmp_of_select" => Val::Bool(t_cmp_of_select(bool_of(a[0]), bool_of(a[1]), u8_of(a[2]))),
        "d_if_bool" => Val::Bool(d_if_bool(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "d_if_u8" => Val::U8(d_if_u8(bool_of(a[0]), u8_of(a[1]), u8_of(a[2]))),
        "d_if_const" => Val::U8(d_if_const(bool_of(a[0]))),
        "d_sel_const" => Val::U8(d_sel_const(u8_of(a[0]))),
        "d_match_u8" => Val::U8(d_match_u8(u8_of(a[0]))),
        "d_match_bool" => Val::U8(d_match_bool(bool_of(a[0]))),
        "d_matches" => Val::Bool(d_matches(u8_of(a[0]))),
        "d_match_i8" => Val::I8(d_match_i8(i8_of(a[0]))),
        "d_matches_i8" => Val::Bool(d_matches_i8(i8_of(a[0]))),
        "d_chain" => Val::U8(d_chain(u8_of(a[0]))),
        "d_max" => Val::U8(d_max(u8_of(a[0]), u8_of(a[1]))),
        "d_ge_sel" => Val::U8(d_ge_sel(u8_of(a[0]), u8_of(a[1]))),
        "d_ne_sel" => Val::U8(d_ne_sel(u8_of(a[0]), u8_of(a[1]))),
        "d_if_not" => Val::U8(d_if_not(bool_of(a[0]), u8_of(a[1]))),
        "d_range" => Val::U8(d_range(u8_of(a[0]))),
        "d_match_u8_bool" => Val::Bool(d_match_u8_bool(u8_of(a[0]))),
        "d_if_cmp_bool" => Val::Bool(d_if_cmp_bool(u8_of(a[0]), bool_of(a[1]))),
        "d_match_param_arms" => Val::U8(d_match_param_arms(u8_of(a[0]), u8_of(a[1]))),
        "d_if_i8" => Val::I8(d_if_i8(bool_of(a[0]), i8_of(a[1]))),
        "d_if_nested" => Val::U8(d_if_nested(bool_of(a[0]), bool_of(a[1]))),
        "d_guard" => Val::U8(d_guard(u8_of(a[0]))),
        "d_bind" => Val::U8(d_bind(u8_of(a[0]))),
        "d_match_u64" => Val::U64(d_match_u64(u64_of(a[0]))),
        "d_sel_i32" => Val::I32(d_sel_i32(i32_of(a[0]))),
        "d_range_exh" => Val::U8(d_range_exh(u8_of(a[0]))),
        "d_match_i128" => Val::I128(d_match_i128(i128_of(a[0]))),
        "d_sel_i128" => Val::I128(d_sel_i128(i128_of(a[0]))),
        "d_sel_i64" => Val::I64(d_sel_i64(i64_of(a[0]))),
        "d_match_i64" => Val::I64(d_match_i64(i64_of(a[0]))),
        "t_i8_ord" => Val::Bool(t_i8_ord(i8_of(a[0]), i8_of(a[1]))),
        "d_sel_i8_ord" => Val::I8(d_sel_i8_ord(i8_of(a[0]), i8_of(a[1]))),
        "d_match_u16" => Val::U16(d_match_u16(u16_of(a[0]))),
        "d_match_i16" => Val::I16(d_match_i16(i16_of(a[0]))),
        "t_u16" => Val::Bool(t_u16(u16_of(a[0]))),
        "t_i16" => Val::Bool(t_i16(i16_of(a[0]))),
        "d_match_u32" => Val::U32(d_match_u32(u32_of(a[0]))),
        "d_match_i32" => Val::I32(d_match_i32(i32_of(a[0]))),
        "d_match_u128" => Val::U128(d_match_u128(u128_of(a[0]))),
        "d_match_u128_max" => Val::U128(d_match_u128_max(u128_of(a[0]))),
        "d_match_char" => Val::U8(d_match_char(char_of(a[0]))),
        "d_if_bool_eq" => Val::Bool(d_if_bool_eq(bool_of(a[0]), bool_of(a[1]), bool_of(a[2]))),
        "d_if_not_lt" => Val::U8(d_if_not_lt(u8_of(a[0]), u8_of(a[1]))),
        "d_if_not_lt_let" => Val::U8(d_if_not_lt_let(u8_of(a[0]), u8_of(a[1]))),
        "i_or_call" => Val::Bool(i_or_call(bool_of(a[0]), u8_of(a[1]))),
        "i_and_add" => Val::Bool(i_and_add(bool_of(a[0]), u8_of(a[1]))),
        "i_or_div" => Val::Bool(i_or_div(bool_of(a[0]), u8_of(a[1]), u8_of(a[2]))),
        "i_and_index" => Val::Bool(i_and_index(
            bool_of(a[0]),
            bools4_of(a[1]),
            usize::try_from(u64_of(a[2])).expect("a 64-bit host"),
        )),
        "i_and_const_index" => Val::Bool(i_and_const_index(bool_of(a[0]), bools4_of(a[1]))),
        "i_match_call" => Val::U8(i_match_call(u8_of(a[0]))),
        "i_if_wrapping" => Val::U8(i_if_wrapping(bool_of(a[0]), u8_of(a[1]))),
        // The view shapes take their arguments in VIEW order: each `&Flags`
        // parameter contributes `p` then `q`, in parameter order.
        "v_ne" => Val::Bool(v_ne(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) })),
        "v_eq" => Val::Bool(v_eq(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) })),
        "v_ne_other" => {
            Val::Bool(v_ne_other(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) }, bool_of(a[2])))
        }
        "v_ne_two" => Val::Bool(v_ne_two(
            &Flags { p: bool_of(a[0]), q: bool_of(a[1]) },
            &Flags { p: bool_of(a[2]), q: bool_of(a[3]) },
        )),
        "v_lt" => Val::Bool(v_lt(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) })),
        "v_and" => Val::Bool(v_and(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) })),
        "v_tree" => Val::Bool(v_tree(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) }, bool_of(a[2]))),
        "v_sel" => {
            Val::U8(v_sel(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) }, u8_of(a[2]), u8_of(a[3])))
        }
        "v_match" => Val::U8(v_match(&Flags { p: bool_of(a[0]), q: bool_of(a[1]) })),
        other => panic!("no native arm for `{other}` — add one beside its shapes.rs function"),
    }
}

// ---------------------------------------------------------------------------
// The parameter view
// ---------------------------------------------------------------------------

/// The frozen pointee the compiler records for a `&Flags` parameter named
/// `param_name` (`trust_frozen_shared_param_table`: both fields are `bool`
/// scalars of a `Freeze` struct, in declared order, under the IR name the
/// extraction gives the ADT).
fn flags_pointee(param_name: &str) -> FrozenPointee {
    let row = |field_index: usize, field_name: &str| FrozenRow {
        field_index,
        field_name: field_name.to_owned(),
        carrier: "bool".to_owned(),
    };
    FrozenPointee {
        param_name: param_name.to_owned(),
        adt_name: "e6_shapes::Flags".to_owned(),
        rows: vec![row(0, "p"), row(1, "q")],
    }
}

/// The borrow-erased view of a view shape: every `&Flags` parameter frozen
/// with both fields, exactly the table the compiler would hand
/// `e6_param_view`. Panics (naming the shape) when the builder refuses, which
/// is itself a finding: every view shape is a plain field read.
fn view_of(name: &str, tag: &str, func: &VerifiableFunction) -> E6ParamView {
    let frozen: FrozenSharedParams = (1..=func.body.arg_count)
        .filter_map(|i| {
            let local = func.body.locals.iter().find(|l| l.index == i)?;
            let name = local.name.as_deref()?;
            matches!(local.ty, Ty::Ref { .. }).then(|| (i - 1, flags_pointee(name)))
        })
        .collect();
    e6_param_view(func, &frozen)
        .unwrap_or_else(|refusal| panic!("{name} [{tag}]: the view builder refused: {refusal:?}"))
        .unwrap_or_else(|| panic!("{name} [{tag}]: the view builder found no borrow to erase"))
}

// ---------------------------------------------------------------------------
// Inputs
// ---------------------------------------------------------------------------

/// The sampled values for a wide signed parameter: every boundary the two cast
/// shapes care about, then a fixed xorshift spread (deterministic, so a
/// failure reproduces).
fn wide_samples(bits: u32) -> Vec<i128> {
    let (min, max) = if bits == 64 {
        (i128::from(i64::MIN), i128::from(i64::MAX))
    } else {
        (i128::MIN, i128::MAX)
    };
    let mut out = vec![
        0,
        1,
        -1,
        2,
        -2,
        // the `-3` thresholds of `d_sel_i64`/`d_sel_i128`, both sides
        3,
        -3,
        -4,
        min,
        min + 1,
        max,
        max - 1,
        i128::from(i64::MIN),
        i128::from(i64::MIN) - 1,
        i128::from(i64::MIN) + 1,
        i128::from(i64::MAX),
        i128::from(i64::MAX) + 1,
        i128::from(i64::MAX) - 1,
        i128::from(u64::MAX),
        i128::from(i32::MIN),
        i128::from(i32::MAX),
    ];
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..48 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        let wide = (i128::from(s) << 64) | i128::from(s.rotate_left(29));
        out.push(if bits == 64 { i128::from(s as i64) } else { wide });
    }
    out.retain(|v| *v >= min && *v <= max);
    out.sort_unstable();
    out.dedup();
    out
}

/// The sampled values for a WIDE UNSIGNED parameter of `bits` bits (32 or
/// 64): the boundaries a comparison or a `switchInt` against a small literal
/// cares about, the top of the range, and a fixed xorshift spread truncated to
/// the width (deterministic, so a failure reproduces). Wide carriers are
/// SAMPLED, never exhaustive: the images are width-parametric in the renderer,
/// and these rows exist so a width-specific slip is seen at all.
fn wide_unsigned_samples(bits: u32) -> Vec<u128> {
    let max = if bits == 64 { u128::from(u64::MAX) } else { u128::from(u32::MAX) };
    let mut out = vec![0, 1, 2, 5, 9, 10, 11, 199, 200, 201, 255, 256, max, max - 1, max / 2];
    out.extend([3_999_999_999u128, 4_000_000_000, 4_000_000_001]);
    let mut s: u64 = 0xD1B5_4A32_D192_ED03;
    for _ in 0..48 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        out.push(u128::from(s) & max);
    }
    out.retain(|v| *v <= max);
    out.sort_unstable();
    out.dedup();
    out
}

/// Every value one parameter of type `ty` takes in the harness.
fn domain_values(ty: &Ty) -> Vec<Val> {
    match ty {
        Ty::Bool => vec![Val::Bool(false), Val::Bool(true)],
        Ty::Int { width: 8, signed: false } => (0..=u8::MAX).map(Val::U8).collect(),
        Ty::Int { width: 8, signed: true } => (i8::MIN..=i8::MAX).map(Val::I8).collect(),
        Ty::Int { width: 64, signed: true } => {
            wide_samples(64).into_iter().map(|v| Val::I64(v as i64)).collect()
        }
        Ty::Int { width: 128, signed: true } => {
            wide_samples(128).into_iter().map(Val::I128).collect()
        }
        Ty::Int { width: 32, signed: false } => {
            wide_unsigned_samples(32).into_iter().map(|v| Val::U32(v as u32)).collect()
        }
        Ty::Int { width: 64, signed: false } => {
            wide_unsigned_samples(64).into_iter().map(|v| Val::U64(v as u64)).collect()
        }
        Ty::Int { width: 32, signed: true } => {
            let mut v: Vec<i32> = vec![0, 1, -1, -4, -5, -6, i32::MIN, i32::MIN + 1, i32::MAX];
            v.extend(wide_samples(64).into_iter().map(|x| x as i32));
            v.sort_unstable();
            v.dedup();
            v.into_iter().map(Val::I32).collect()
        }
        // `u16`/`i16` are EXHAUSTIVE: every row over them has one parameter.
        Ty::Int { width: 16, signed: false } => (0..=u16::MAX).map(Val::U16).collect(),
        Ty::Int { width: 16, signed: true } => (i16::MIN..=i16::MAX).map(Val::I16).collect(),
        Ty::Int { width: 128, signed: false } => {
            let mut v: Vec<u128> = vec![0, 1, 2, u128::MAX, u128::MAX - 1, u128::MAX / 2];
            v.extend(wide_samples(128).into_iter().map(|x| x as u128));
            v.sort_unstable();
            v.dedup();
            v.into_iter().map(Val::U128).collect()
        }
        // Every `[bool; 4]`; only refused rows take one.
        Ty::Array { elem, len: 4 } if **elem == Ty::Bool => {
            (0u8..16).map(|bits| Val::Bools4(std::array::from_fn(|i| bits >> i & 1 == 1))).collect()
        }
        other => panic!("the harness has no input domain for a `{other:?}` parameter"),
    }
}

/// The VALID `char` scalar values a [`CHAR_SHAPES`] row is evaluated on: all
/// of ASCII and Latin-1, the edges of the surrogate gap and of the plane
/// range, and a fixed xorshift spread folded into the valid ranges.
fn char_samples() -> Vec<Val> {
    let mut v: Vec<u32> = (0..=0xFF).collect();
    v.extend([0x100, 0xD7FF, 0xE000, 0xFFFF, 0x1_0000, 0x10_FFFE, 0x10_FFFF]);
    let mut s: u64 = 0x2545_F491_4F6C_DD1D;
    for _ in 0..48 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        v.push((s % 0x11_0000) as u32);
    }
    v.retain(|x| char::from_u32(*x).is_some());
    v.sort_unstable();
    v.dedup();
    v.into_iter().map(Val::U32).collect()
}

fn param_tys(func: &VerifiableFunction) -> Vec<Ty> {
    (1..=func.body.arg_count)
        .map(|i| {
            func.body
                .locals
                .iter()
                .find(|l| l.index == i)
                .unwrap_or_else(|| panic!("{}: no local for parameter {i}", func.def_path))
                .ty
                .clone()
        })
        .collect()
}

/// The cartesian product of every parameter's values (a [`CHAR_SHAPES`]
/// row's `u32` parameters take [`char_samples`]).
fn all_inputs(name: &str, func: &VerifiableFunction) -> Vec<Vec<Val>> {
    let mut rows: Vec<Vec<Val>> = vec![Vec::new()];
    for ty in param_tys(func) {
        let values = if CHAR_SHAPES.contains(&name) && ty == (Ty::Int { width: 32, signed: false })
        {
            char_samples()
        } else {
            domain_values(&ty)
        };
        rows = rows
            .into_iter()
            .flat_map(|row| {
                values.iter().map(move |v| {
                    let mut r = row.clone();
                    r.push(*v);
                    r
                })
            })
            .collect();
    }
    rows
}

// ---------------------------------------------------------------------------
// The kernel side: literals in, whnf, a value out
// ---------------------------------------------------------------------------

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}

fn bitvec_lit(bits: u32, pattern: u128) -> Expr {
    Expr::apps(c("BitVec.ofNat"), [Expr::nat_lit(u64::from(bits)), Expr::nat_lit_u128(pattern)])
}

/// The kernel literal for one argument. Built here, independently of the
/// elaborator's own `Domain::numeral`, so a wrong literal spelling in the
/// producer cannot cancel against the same spelling in the harness.
fn kernel_arg(v: Val) -> Expr {
    match v {
        Val::U8(x) => Expr::app(c("UInt8.ofNat"), Expr::nat_lit(u64::from(x))),
        Val::I8(x) => bitvec_lit(8, u128::from(x as u8)),
        Val::I64(x) => bitvec_lit(64, u128::from(x as u64)),
        Val::I128(x) => bitvec_lit(128, x as u128),
        Val::U32(x) => Expr::app(c("UInt32.ofNat"), Expr::nat_lit(u64::from(x))),
        Val::U64(x) => Expr::app(c("UInt64.ofNat"), Expr::nat_lit(x)),
        Val::I32(x) => bitvec_lit(32, u128::from(x as u32)),
        Val::U16(x) => Expr::app(c("UInt16.ofNat"), Expr::nat_lit(u64::from(x))),
        Val::I16(x) => bitvec_lit(16, u128::from(x as u16)),
        Val::Bool(true) => c("Bool.true"),
        Val::Bool(false) => c("Bool.false"),
        Val::U128(_) | Val::Bools4(_) => {
            panic!("{v:?}: only a REFUSED row takes this argument, and none is ever evaluated")
        }
        Val::OptI8(_) | Val::OptI64(_) => panic!("an Option is never an argument here"),
    }
}

fn nat_value(e: &Expr) -> Option<u128> {
    let ExprKind::Lit(Literal::Nat(n)) = e.kind() else { return None };
    match n.limbs() {
        [] => Some(0),
        [lo] => Some(u128::from(*lo)),
        [lo, hi] => Some(u128::from(*lo) | (u128::from(*hi) << 64)),
        _ => None,
    }
}

fn const_name(e: &Expr) -> Option<String> {
    match e.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Evaluate `term` to a harness value of the same KIND as `like` (the native
/// result, whose kind is fixed by the function's signature), or explain why
/// the kernel's normal form is not one.
fn kernel_value(tc: &TypeChecker<'_>, like: Val, term: Expr) -> Result<Val, String> {
    let nat_of = |wrapped: Expr| -> Result<u128, String> {
        let nf = tc.whnf(&wrapped);
        nat_value(&nf).ok_or_else(|| format!("normal form is not a Nat literal: {nf:?}"))
    };
    let bitvec_nat = |bits: u32, e: Expr| {
        nat_of(Expr::apps(c("BitVec.toNat"), [Expr::nat_lit(u64::from(bits)), e]))
    };
    let option_payload = |e: Expr| -> Result<Option<Expr>, String> {
        let nf = tc.whnf(&e);
        let head = const_name(nf.get_app_fn());
        let args: Vec<Expr> = nf.get_app_args().into_iter().cloned().collect();
        match head.as_deref() {
            Some("Option.none") if args.len() == 1 => Ok(None),
            Some("Option.some") if args.len() == 2 => Ok(Some(args[1].clone())),
            _ => Err(format!("normal form is not an Option constructor: {nf:?}")),
        }
    };
    Ok(match like {
        Val::Bool(_) => {
            let nf = tc.whnf(&term);
            match const_name(&nf).as_deref() {
                Some("Bool.true") => Val::Bool(true),
                Some("Bool.false") => Val::Bool(false),
                _ => return Err(format!("normal form is not a Bool constructor: {nf:?}")),
            }
        }
        Val::U8(_) => {
            let n = nat_of(Expr::app(c("UInt8.toNat"), term))?;
            Val::U8(u8::try_from(n).map_err(|_| format!("UInt8.toNat gave {n}, above 255"))?)
        }
        Val::I8(_) => Val::I8(bitvec_nat(8, term)? as u8 as i8),
        Val::I64(_) => Val::I64(bitvec_nat(64, term)? as u64 as i64),
        Val::I128(_) => Val::I128(bitvec_nat(128, term)? as i128),
        Val::U32(_) => {
            let n = nat_of(Expr::app(c("UInt32.toNat"), term))?;
            Val::U32(u32::try_from(n).map_err(|_| format!("UInt32.toNat gave {n}, above u32"))?)
        }
        Val::U64(_) => {
            let n = nat_of(Expr::app(c("UInt64.toNat"), term))?;
            Val::U64(u64::try_from(n).map_err(|_| format!("UInt64.toNat gave {n}, above u64"))?)
        }
        Val::I32(_) => Val::I32(bitvec_nat(32, term)? as u32 as i32),
        Val::U16(_) => {
            let n = nat_of(Expr::app(c("UInt16.toNat"), term))?;
            Val::U16(u16::try_from(n).map_err(|_| format!("UInt16.toNat gave {n}, above u16"))?)
        }
        Val::I16(_) => Val::I16(bitvec_nat(16, term)? as u16 as i16),
        Val::U128(_) | Val::Bools4(_) => {
            return Err(format!("no kernel read-back for a {like:?} result"));
        }
        Val::OptI8(_) => Val::OptI8(match option_payload(term)? {
            None => None,
            Some(p) => Some(bitvec_nat(8, p)? as u8 as i8),
        }),
        Val::OptI64(_) => Val::OptI64(match option_payload(term)? {
            None => None,
            Some(p) => Some(bitvec_nat(64, p)? as u64 as i64),
        }),
    })
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn fnv1a64(bytes: &[u8]) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    format!("{h:016x}")
}

struct Fixture {
    tag: &'static str,
    functions: BTreeMap<String, VerifiableFunction>,
}

/// A dump as `regen.py` writes it. Deserialized DIRECTLY, never through
/// `serde_json::Value`: a `switchInt` label above `u64::MAX` (an `i128`/`u128`
/// `match`, e.g. `d_match_i128`'s `-1` as the pattern `2^128 - 1`) goes
/// through `Value` as an `f64` and no longer deserializes as the `u128` it is.
#[derive(serde::Deserialize)]
struct Dump {
    source_fnv1a64: String,
    functions: BTreeMap<String, VerifiableFunction>,
}

fn load(tag: &'static str, json: &str) -> Fixture {
    let dump: Dump = serde_json::from_str(json)
        .unwrap_or_else(|e| panic!("shapes.{tag}.json does not deserialize: {e}"));
    let recorded = dump.source_fnv1a64.as_str();
    let actual = fnv1a64(SHAPES_SRC.as_bytes());
    assert_eq!(
        recorded, actual,
        "shapes.{tag}.json was generated from a different shapes.rs (recorded {recorded}, \
         source is {actual}). Re-run \
         `python3 crates/trust-certify/tests/fixtures/e6_differential/regen.py <trustc>`."
    );
    let functions = dump
        .functions
        .into_iter()
        .map(|(path, func)| {
            let short = path.rsplit("::").next().unwrap_or(&path).to_string();
            (short, func)
        })
        .collect();
    Fixture { tag, functions }
}

fn fixtures() -> [Fixture; 2] {
    [load("unopt", UNOPT_JSON), load("opt", OPT_JSON)]
}

/// Every source function has an expectation, a native arm, and a dumped body
/// at both opt levels — and nothing else does.
#[test]
fn every_shape_has_an_expectation_and_a_native_arm() {
    let declared: Vec<&str> = SHAPES_SRC
        .lines()
        .filter_map(|l| l.strip_prefix("pub fn "))
        .map(|rest| rest.split('(').next().unwrap_or_default())
        .collect();
    let expected: Vec<&str> =
        EXPECTATIONS.iter().chain(VIEW_EXPECTATIONS).map(|(n, ..)| *n).collect();
    assert_eq!(
        declared, expected,
        "shapes.rs and EXPECTATIONS ++ VIEW_EXPECTATIONS list different functions"
    );
    for fixture in fixtures() {
        let dumped: Vec<&str> = fixture.functions.keys().map(String::as_str).collect();
        let mut want = expected.clone();
        want.sort_unstable();
        assert_eq!(dumped, want, "shapes.{}.json dumps a different function set", fixture.tag);
        for (name, func) in &fixture.functions {
            let is_view = VIEW_EXPECTATIONS.iter().any(|(n, ..)| n == name);
            let view;
            let func = if is_view {
                view = view_of(name, fixture.tag, func);
                &view.func
            } else {
                func
            };
            let args: Vec<Val> = param_tys(func).iter().map(|ty| domain_values(ty)[0]).collect();
            // The Rust side of a REFUSED row may be partial on the probe input
            // (`i_or_div` divides by zero there); that is a panic of the
            // function, not a missing arm, which is the one panic this checks.
            if let Err(payload) = std::panic::catch_unwind(|| native(name, &args)) {
                let message = payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|m| (*m).to_owned()))
                    .unwrap_or_default();
                assert!(!message.contains("no native arm"), "{message}");
            }
        }
    }
}

/// The view shapes are not vacuous for the READER: at the unoptimized level
/// the view of `v_ne` reaches `read_e6_body` (the frozen chain does not read
/// `!=`) through single-assignment temporaries — the field reads — so the
/// reader's temporary resolution is what the harness evaluates there.
#[test]
fn view_fields_reach_the_readers_temporaries() {
    use trust_types::admissible_body::recognize_admissible_body;
    use trust_types::e6_expr::{BoolEqOp, BoolLeaf, E6Expr, read_e6_body};
    let fixture = load("unopt", UNOPT_JSON);
    let view = view_of("v_ne", "unopt", &fixture.functions["v_ne"]);
    assert_eq!(view.param_names, ["f.p", "f.q"]);
    assert_eq!(recognize_admissible_body(&view.func), None, "the frozen chain does not read `!=`");
    assert_eq!(
        read_e6_body(&view.func),
        Some(E6Expr::BoolCmp {
            op: BoolEqOp::Ne,
            left: BoolLeaf::Param(0),
            right: BoolLeaf::Param(1)
        })
    );
    let [block] = view.func.body.blocks.as_slice() else { panic!("one block") };
    let temps = block
        .stmts
        .iter()
        .filter(|stmt| {
            matches!(stmt, trust_types::Statement::Assign { place, rvalue: trust_types::Rvalue::Use(_), .. }
                if place.local > view.func.body.arg_count)
        })
        .count();
    assert!(temps >= 1, "the view body reads its fields through temporaries: {:?}", block.stmts);
}

/// The review-P1-2 rows are not vacuous for the TREE producer: at both opt
/// levels each one is refused by the frozen chain and read by the E6-only
/// tree reader, so its image is the tree producer's at that carrier — and
/// the two `condition()` rows put the condition shape they are named for
/// under the decision (a `bool` `==`; a `!` over a comparison).
#[test]
fn the_carrier_rows_reach_the_tree_reader() {
    use trust_types::admissible_body::recognize_admissible_body;
    use trust_types::e6_expr::{E6Carrier, E6Cmp, E6Expr, E6Term, read_e6_body};
    const TREE_ROWS: &[&str] = &[
        "d_match_i128",
        "d_sel_i128",
        "d_sel_i64",
        "d_match_i64",
        "t_i8_ord",
        "d_sel_i8_ord",
        "d_match_u16",
        "d_match_i16",
        "t_u16",
        "t_i16",
        "d_match_u32",
        "d_match_i32",
        "d_match_u128",
        "d_match_char",
        "d_if_bool_eq",
        // NOT `d_if_not_lt`: rustc folds `if !(a < b)` into the branch
        // targets, and the frozen `Select` reads the result (MEASURED); the
        // `let` form is the one that puts a `!` under the decision.
        "d_if_not_lt_let",
    ];
    for fixture in fixtures() {
        for name in TREE_ROWS {
            let func = &fixture.functions[*name];
            assert_eq!(
                recognize_admissible_body(func),
                None,
                "{name} [{}]: the frozen chain reads it, so the row does not reach the tree",
                fixture.tag
            );
            assert!(
                matches!(read_e6_body(func), Some(E6Expr::Tree(_))),
                "{name} [{}]: the tree reader does not read it: {:?}",
                fixture.tag,
                trust_types::e6_expr::read_e6_tree(func)
            );
        }
        let max = trust_types::e6_expr::read_e6_tree(&fixture.functions["d_match_u128_max"]);
        assert!(
            matches!(&max, Err(why) if why.contains("outside `u128`")),
            "d_match_u128_max [{}]: the reader must fail closed on the label: {max:?}",
            fixture.tag
        );
        let cond_of = |name: &str| match read_e6_body(&fixture.functions[name]) {
            Some(E6Expr::Tree(E6Term::Ite { cond, .. })) => *cond,
            other => panic!("{name} [{}]: not a decision: {other:?}", fixture.tag),
        };
        assert!(
            matches!(
                cond_of("d_if_bool_eq"),
                E6Term::Cmp { op: E6Cmp::Eq, carrier: E6Carrier::Bool, .. }
            ),
            "d_if_bool_eq [{}]: the condition is not a `bool` `==`",
            fixture.tag
        );
        assert!(
            matches!(cond_of("d_if_not_lt_let"), E6Term::Not(ref c) if matches!(**c, E6Term::Cmp { op: E6Cmp::Lt, .. })),
            "d_if_not_lt_let [{}]: the condition is not `!(a < b)`",
            fixture.tag
        );
    }
}

/// E6-TG14-PANIC-EDGE-1: `i_and_add`'s `x + 1` is rustc's `CheckedBinaryOp`
/// pair, its overflow `Assert` and `.0` at BOTH opt levels (MEASURED on the
/// fixtures). The tree reader refuses at the `Assert`: the body panics at
/// `(true, 255)`, so no total image of it is faithful.
#[test]
fn the_overflow_assert_of_a_checked_add_refuses_the_tree() {
    for fixture in fixtures() {
        let read = trust_types::e6_expr::read_e6_tree(&fixture.functions["i_and_add"]);
        let why = read.as_ref().err().map(String::as_str).unwrap_or_default();
        assert!(
            why.contains("an `Assert`") && why.contains("a panic path"),
            "i_and_add [{}]: the overflow Assert must refuse the tree: {read:?}",
            fixture.tag
        );
    }
}

/// THE HARNESS. For every function at both opt levels: the import mints
/// exactly when expected, and every minted image agrees with the native
/// function on every input.
#[test]
fn every_minted_image_agrees_with_the_rust_body_on_every_input() {
    // Refuse broken admission metadata before minting or starting any workers.
    let threads = evaluation_workers(
        std::thread::available_parallelism().map_or(1, |n| n.get()),
        std::env::var_os("BUILD_SLOT_HELD").as_deref(),
        std::env::var_os("CARGO_BUILD_JOBS").as_deref(),
    )
    .unwrap_or_else(|error| panic!("E6 differential harness: {error}"));
    eprintln!("E6 differential harness: {threads} evaluation worker(s)");
    let mut failures: Vec<String> = Vec::new();
    // Phase 1 — mint, sequentially (minting extends the environment).
    let mut jobs: Vec<(&'static str, &'static str, VerifiableFunction, String)> = Vec::new();
    let mut envs: Vec<(&'static str, Environment)> = Vec::new();
    let mut view_images = 0usize;
    for fixture in fixtures() {
        let mut env = Environment::with_prelude();
        for (name, u, o) in EXPECTATIONS {
            let expect = if fixture.tag == "opt" { *o } else { *u };
            let func = &fixture.functions[*name];
            let table = FacetTable::from_structural_facets([(
                func.def_path.clone(),
                true,
                true,
                true,
                true,
            )]);
            match (expect, admit_function_into(&mut env, func, &table)) {
                (Refused, None) => {}
                (Admitted, None) => {
                    failures
                        .push(format!("{name} [{}]: REFUSED but expected Admitted", fixture.tag));
                }
                (expect, Some((_, admission))) => {
                    if expect == Refused {
                        failures.push(format!(
                            "{name} [{}]: MINTED but expected Refused — a widening must move \
                             the expectation (the image is still checked below)",
                            fixture.tag
                        ));
                    }
                    jobs.push((fixture.tag, name, func.clone(), admission.kernel_const));
                }
            }
        }
        // The view shapes: minted as their borrow-erased VIEW, through the
        // compiler's own entry, and evaluated on the view's parameters. The
        // view's isolated facet gate (V4) runs inside the entry, so no facet
        // record is offered.
        for (name, u, o) in VIEW_EXPECTATIONS {
            let expect = if fixture.tag == "opt" { *o } else { *u };
            let view = view_of(name, fixture.tag, &fixture.functions[*name]);
            match (expect, admit_view_function_into(&mut env, &view, &FacetTable::new())) {
                (Refused, None) => {}
                (Admitted, None) => failures.push(format!(
                    "{name} [{}] (view): REFUSED but expected Admitted",
                    fixture.tag
                )),
                (expect, Some((_, admission))) => {
                    if expect == Refused {
                        failures.push(format!(
                            "{name} [{}] (view): MINTED but expected Refused",
                            fixture.tag
                        ));
                    }
                    view_images += 1;
                    jobs.push((fixture.tag, name, view.func.clone(), admission.kernel_const));
                }
            }
        }
        envs.push((fixture.tag, env));
    }
    // Phase 2 — evaluate every image on every input, in parallel over images.
    let env_of = |tag: &str| &envs.iter().find(|(t, _)| *t == tag).expect("env").1;
    let results: Vec<(usize, Vec<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|worker| {
                let jobs = &jobs;
                scope.spawn(move || {
                    let mut checked = 0usize;
                    let mut found = Vec::new();
                    for (tag, name, func, kernel_const) in jobs.iter().skip(worker).step_by(threads)
                    {
                        let (n, f) = check_image(env_of(tag), tag, name, func, kernel_const);
                        checked += n;
                        found.extend(f);
                    }
                    (checked, found)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("worker")).collect()
    });
    let checked_inputs: usize = results.iter().map(|(n, _)| n).sum();
    failures.extend(results.into_iter().flat_map(|(_, f)| f));
    eprintln!(
        "E6 differential harness: {} image(s) ({view_images} through the parameter view), \
         {checked_inputs} input(s) evaluated",
        jobs.len()
    );
    assert!(
        failures.is_empty(),
        "E6 differential harness: {} failure(s) over {checked_inputs} evaluated input(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    // Not vacuous: the harness must have evaluated images, at scale.
    assert!(jobs.len() >= 60, "only {} images were checked", jobs.len());
    assert!(view_images >= 8, "only {view_images} parameter-view images were checked");
    assert!(checked_inputs >= 1_000_000, "only {checked_inputs} inputs were evaluated");
}

/// Evaluate one minted image on every input of `func` and compare it with the
/// native function: `(inputs evaluated, failure lines)`.
fn check_image(
    env: &Environment,
    tag: &str,
    name: &str,
    func: &VerifiableFunction,
    kernel_const: &str,
) -> (usize, Vec<String>) {
    let head = c(kernel_const);
    let mut failures = Vec::new();
    let mut disagreements = 0usize;
    let inputs = all_inputs(name, func);
    // Only a REFUSED row takes an argument with no kernel literal, so an image
    // minted for one is already a failure; say so instead of panicking a
    // worker inside `kernel_arg`.
    if let Some(first) = inputs.first()
        && first.iter().any(|v| matches!(v, Val::U128(_) | Val::Bools4(_)))
    {
        return (
            0,
            vec![format!(
                "{name} [{tag}]: an image was minted for a row whose arguments have no kernel \
             literal in this harness ({first:?})"
            )],
        );
    }
    // A FRESH checker per batch: a checker carries a reduction budget across
    // calls, and one shared over 65 536 inputs runs dry part-way (MEASURED:
    // `w_chain` stopped reducing at input 49 924), which reads as a
    // non-evaluation, never as a value. A checker per INPUT is also correct
    // but far slower (MEASURED: over 10 minutes for the whole harness).
    for batch in inputs.chunks(CHECKER_BATCH) {
        let tc = TypeChecker::new(env);
        for input in batch {
            let term = Expr::apps(head.clone(), input.iter().map(|v| kernel_arg(*v)));
            // A minted image of a PARTIAL function is a failure of its own:
            // no image may stand for a body that panics on an input it admits.
            let Ok(rust) = std::panic::catch_unwind(|| native(name, input)) else {
                disagreements += 1;
                if disagreements <= 3 {
                    failures.push(format!(
                        "{name} [{tag}] at {input:?}: the Rust body PANICS, yet an image was minted"
                    ));
                }
                continue;
            };
            let line = match kernel_value(&tc, rust, term) {
                Ok(lean) if lean == rust => continue,
                Ok(lean) => {
                    format!("{name} [{tag}] at {input:?}: Rust {rust:?}, Lean image {lean:?}")
                }
                Err(why) => {
                    format!("{name} [{tag}] at {input:?}: the image did not evaluate: {why}")
                }
            };
            disagreements += 1;
            if disagreements <= 3 {
                failures.push(line);
            }
        }
    }
    if disagreements > 3 {
        failures.push(format!("{name} [{tag}]: {disagreements} disagreement(s) in all"));
    }
    (inputs.len(), failures)
}

/// The harness can see a wrong image. A mint of `<` for the body `a <= b` is
/// built by hand and must disagree — at exactly the 256 diagonal inputs — so a
/// green run above is not the product of a decoder that agrees with anything.
#[test]
fn the_harness_sees_a_wrong_image() {
    let fixture = load("unopt", UNOPT_JSON);
    let mut env = Environment::with_prelude();
    // Mint the body of `c_lt` under the name of `c_le`'s import.
    let mut wrong = fixture.functions["c_lt"].clone();
    wrong.def_path = "e6_shapes::c_le_forged".into();
    let table =
        FacetTable::from_structural_facets([(wrong.def_path.clone(), true, true, true, true)]);
    let (_, admission) = admit_function_into(&mut env, &wrong, &table).expect("c_lt mints");
    let head = c(&admission.kernel_const);
    let mut disagree = 0;
    for input in all_inputs("c_le", &fixture.functions["c_le"]) {
        let tc = TypeChecker::new(&env);
        let term = Expr::apps(head.clone(), input.iter().map(|v| kernel_arg(*v)));
        let rust = native("c_le", &input);
        let lean = kernel_value(&tc, rust, term).expect("evaluates");
        if lean != rust {
            disagree += 1;
        }
    }
    assert_eq!(disagree, 256, "`<` against `<=` differs exactly on the diagonal");
}
