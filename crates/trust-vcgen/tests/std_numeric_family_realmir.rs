// Trust (2026-09-25, std-numeric-family): the vcgen half of the std numeric
// value-panic fixes, pinned on REAL extracted MIR (`-Ztrust-dump=mir-only`,
// `fixtures/std_numeric_family/*.json`, one function per file, named by the
// file). Every UNGUARDED shape here built rc=0 on the default lane (stage-1 of
// origin/main `8d6aadf7e9`) and panicked at runtime on the caller's argument;
// the end-to-end pins are the revisions of
// `tests/ui/trust/policy_b/std_numeric_value_panics_charged.rs`. These tests
// pin the row the call-site recognizer (`generate::numeric_panic`) now MINTS
// and — through the in-process solver — that each precise row REFUTES the
// unguarded call and PROVES its guarded twin. Dumps are optimized MIR, so they
// do not claim the compiler path on their own.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/std_numeric_family/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The kinds of `UnsupportedMir` row this family mints.
const FAMILY_UNMODELED: &[&str] = &[
    "float-clamp-bounds-unmodeled",
    "ord-clamp-bounds-unmodeled",
    "duration-from-float-unmodeled",
    "duration-float-scale-unmodeled",
    "duration-arith-overflow-unmodeled",
    "duration-sum-overflow",
    "time-point-duration-overflow",
    "nonzero-negation-overflow-unmodeled",
    "int-assign-op-overflow-unmodeled",
    "range-from-step-overflow-unmodeled",
    "range-count-overflow-unmodeled",
    // NUM-NIGHTLY-UNCHARGED-1 (2026-10-06): `strict_cast::<T>` to a non-primitive
    // (generic) target.
    "strict-cast-target-unmodeled",
    // STEP-TRAIT-DIRECT-UNCHARGED-1 (2026-10-11): a direct `Step::forward` /
    // `Step::backward` on one of core's own `Step` types.
    "step-forward-overflow-unmodeled",
    "step-backward-overflow-unmodeled",
];

/// The `Assertion` messages / `DivisionByZero` rows this family mints — a row is
/// the family's iff its message starts with one of these method prefixes.
const FAMILY_MESSAGE_PREFIXES: &[&str] = &[
    "Ord::clamp",
    "float clamp",
    "ilog",
    "isqrt",
    "next_power_of_two",
    "next_multiple_of",
    "div_euclid",
    "rem_euclid",
    "char::to_digit",
    "char::from_digit",
    "from_str_radix",
    "from_ascii_radix",
    "strict_",
    "Add::add",
    "Sub::sub",
    "Mul::mul",
    "Neg::neg",
    "Shl::shl",
    "Shr::shr",
    "ShlAssign::shl_assign",
    "ShrAssign::shr_assign",
    "Duration",
    // The decided row of `Instant/SystemTime::now() +/- <small literal Duration>`
    // (minted since 2026-10-02; it minted nothing before).
    "time point",
    "Iterator::count",
    // NUM-NIGHTLY-UNCHARGED-1 (2026-10-06): the nightly `funnel_shl`/`funnel_shr`.
    "funnel_",
];

enum Want {
    /// A precise family row the solver REFUTES (the call panics for some input).
    Refuted,
    /// A fail-closed row of this kind (refused under the default policy).
    Unmodeled(&'static str),
    /// Every family row PROVES and none is fail-closed. Since 2026-10-02 this is also
    /// the expectation for a literal argument the recognizer DECIDES cannot panic: it
    /// mints its row with a `false` violation instead of nothing (a `NoRow`
    /// expectation was retired with that change; KNOWN_HAZARDS "`certify` exits 0 on a
    /// literal `clamp`").
    Proved,
}

fn family_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| match &vc.kind {
            VcKind::Assertion { message } => {
                FAMILY_MESSAGE_PREFIXES.iter().any(|p| message.starts_with(p))
            }
            // `Duration / k`'s zero-divisor row, and the overflow-call lane's
            // `strict_add`/`Add::add` row (these fixtures carry no other division,
            // and every other overflow row in them is provable).
            VcKind::DivisionByZero | VcKind::ArithmeticOverflow { .. } => true,
            _ => false,
        })
        .collect()
}

fn family_unmodeled(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } if FAMILY_UNMODELED.contains(&kind.as_str()) => {
                Some(kind.clone())
            }
            _ => None,
        })
        .collect()
}

fn check(name: &str, want: Want) {
    let func = load(name);
    let vcs = generate_vcs(&func);
    let rows = family_rows(&vcs);
    let unmodeled = family_unmodeled(&vcs);
    let router = router();
    let verdicts: Vec<VerificationResult> = rows
        .iter()
        .map(|vc| router.verify_all(std::slice::from_ref(*vc)).into_iter().next().unwrap().1)
        .collect();
    let dbg = || {
        rows.iter()
            .zip(&verdicts)
            .map(|(vc, r)| format!("{:?}\n{}\n  => {r:?}", vc.kind, vc.formula.to_smtlib()))
            .collect::<Vec<_>>()
            .join("\n")
    };
    match want {
        Want::Refuted => assert!(
            verdicts.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
            "{name}: the unguarded call must carry a REFUTED family row; unmodeled={unmodeled:?}\n{}",
            dbg()
        ),
        Want::Unmodeled(kind) => assert!(
            unmodeled.iter().any(|k| k == kind),
            "{name}: expected the fail-closed `{kind}` row; got {unmodeled:?}\n{}",
            dbg()
        ),
        Want::Proved => {
            assert!(!rows.is_empty(), "{name}: the guarded call must still carry its family row");
            assert!(
                verdicts.iter().all(|r| matches!(r, VerificationResult::Proved { .. })),
                "{name}: the guarded family row must PROVE\n{}",
                dbg()
            );
            assert!(unmodeled.is_empty(), "{name}: no fail-closed row expected; got {unmodeled:?}");
        }
    }
}

// ---- Ord::clamp ----

#[test]
fn ord_clamp_on_an_integer_is_charged_precisely() {
    check("clamp_i32", Want::Refuted);
    check("clamp_i32_g", Want::Proved);
    check("clamp_i32_lit", Want::Proved);
    check("clamp_char", Want::Refuted);
}

#[test]
fn ord_clamp_on_a_non_primitive_is_refused() {
    check("clamp_tuple", Want::Unmodeled("ord-clamp-bounds-unmodeled"));
}

#[test]
fn float_clamp_decides_literal_bounds_and_refuses_the_rest() {
    check("clamp_f64", Want::Unmodeled("float-clamp-bounds-unmodeled"));
    check("clamp_f64_lit", Want::Proved);
}

// ---- integer domains ----

#[test]
fn integer_logarithm_domains_are_charged() {
    check("ilog2_u32", Want::Refuted);
    check("ilog2_u32_g", Want::Proved);
    check("ilog10_i64", Want::Refuted);
    check("ilog10_i64_g", Want::Proved);
    check("ilog_base", Want::Refuted);
    check("ilog_base_g", Want::Proved);
}

#[test]
fn a_signed_isqrt_of_a_negative_is_charged() {
    check("isqrt_i32", Want::Refuted);
    check("isqrt_i32_g", Want::Proved);
}

#[test]
fn next_power_of_two_and_next_multiple_of_overflow_is_charged() {
    check("next_pow2", Want::Refuted);
    check("next_pow2_g", Want::Proved);
    check("next_mult", Want::Refuted);
    check("next_mult_g", Want::Proved);
}

// ---- the nightly surface (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06) ----
//
// The 2026-09-25 audit covered stable methods only. Every UNGUARDED shape below
// built rc=0 on the default lane of the stage 1 of `9e11546767` (the bundled
// member's or the absent `unchecked_funnel_*` intrinsic's `runtime_checked` row
// only) and a verify-off driver passing the value exited 101; the end-to-end pins
// are `tests/ui/trust/policy_b/std_numeric_value_panics_charged_nightly{,_run}.rs`.
// Dumped with that stage 1 (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`).

#[test]
fn signed_next_multiple_of_is_charged() {
    check("next_mult_i32", Want::Refuted);
    // `b > 0` alone leaves `i32::MAX.next_multiple_of(2)`, and a literal divisor
    // still overflows near `MAX` (`121i8.next_multiple_of(8)` is 128).
    check("next_mult_i32_pos_only", Want::Refuted);
    check("next_mult_i8_lit", Want::Refuted);
    check("next_mult_i32_g", Want::Proved);
    check("next_mult_i32_neg_g", Want::Proved);
    // core returns `self` at once on `rhs == -1`.
    check("next_mult_i32_minus_one", Want::Proved);
}

#[test]
fn a_funnel_shift_by_the_width_or_more_is_charged() {
    check("funnel_shl_u32", Want::Refuted);
    check("funnel_shr_u64", Want::Refuted);
    check("funnel_shl_lit_bad", Want::Refuted);
    // A guard on the wrong operand, and an off-by-one guard (`n <= 32`).
    check("funnel_shl_wrong_var", Want::Refuted);
    check("funnel_shl_off_by_one", Want::Refuted);
    check("funnel_shl_u32_g", Want::Proved);
    check("funnel_shr_u64_g", Want::Proved);
    check("funnel_shl_lit", Want::Proved);
}

#[test]
fn a_strict_cast_outside_the_target_range_is_charged() {
    check("strict_cast_u32_u8", Want::Refuted);
    check("strict_cast_i64_i8", Want::Refuted);
    // A negative never fits an unsigned target, however wide.
    check("strict_cast_i32_u64", Want::Refuted);
    check("strict_cast_signed_u32", Want::Refuted);
    check("strict_cast_unsigned_i32", Want::Refuted);
    check("strict_cast_u32_u8_g", Want::Proved);
    check("strict_cast_i64_i8_g", Want::Proved);
    // A widening cast always fits.
    check("strict_cast_u8_u32", Want::Proved);
    check("strict_cast_signed_u32_g", Want::Proved);
    check("strict_cast_unsigned_i32_g", Want::Proved);
    // The target is read off the destination, never the rendered turbofish; a
    // generic `T` has no range, so the call is refused.
    check("strict_cast_generic", Want::Unmodeled("strict-cast-target-unmodeled"));
}

/// Trust (wave-19 review, 2026-10-09): the TRAIT spelling `strict_cast` delegates to,
/// `<Dst as core::convert::num::CheckedCastFromInt<Src>>::strict_cast_from(v)` (also
/// what `u8::strict_cast_from(v)` renders), panics on the same values. The inherent
/// `strict_cast*` arms never matched it: on the stage 1 of `46e9afaf95` each unguarded
/// shape below built rc=0 on the default lane with one `runtime_checked` panic-freedom
/// row, and a verify-off driver exited 101 "attempt to cast integer with overflow" on
/// 300. Dumps (`-Ztrust-dump=mir-only`, that stage 1) of `scf.rs`, one function each.
/// Before the fix every `Refuted` and `Proved` line here fails (no family row), and so
/// does the `Unmodeled` one.
#[test]
fn the_checked_cast_trait_strict_cast_from_is_charged_like_strict_cast() {
    check("strict_cast_from_u32_u8", Want::Refuted);
    check("strict_cast_from_i64_i8", Want::Refuted);
    check("strict_cast_from_i32_u64", Want::Refuted);
    // `a <= 256` leaves 256.
    check("strict_cast_from_off_by_one", Want::Refuted);
    check("strict_cast_from_u32_u8_g", Want::Proved);
    check("strict_cast_from_i64_i8_g", Want::Proved);
    // A widening cast always fits.
    check("strict_cast_from_u8_u32", Want::Proved);
    // `<T as CheckedCastFromInt<u32>>::strict_cast_from`: no range for `T`, refused.
    check("strict_cast_from_generic", Want::Unmodeled("strict-cast-target-unmodeled"));
}

#[test]
fn the_nightly_day_and_week_duration_constructors_are_charged() {
    check("dur_from_days", Want::Refuted);
    check("dur_from_weeks", Want::Refuted);
    check("dur_from_days_g", Want::Proved);
    check("dur_from_weeks_lit", Want::Proved);
}

#[test]
fn signed_euclid_min_by_minus_one_is_charged_beside_the_zero_divisor() {
    // `b != 0` discharges `divzero_call`'s row but not `MIN.rem_euclid(-1)`.
    check("rem_euclid_min", Want::Refuted);
    check("rem_euclid_min_g", Want::Proved);
}

// ---- radix ----

#[test]
fn a_radix_outside_its_range_is_charged() {
    check("to_digit", Want::Refuted);
    check("to_digit_g", Want::Proved);
    check("to_digit_lit", Want::Proved);
    // `from_digit` panics on `radix > 36` ONLY; `if r <= 36` proves it.
    check("from_digit", Want::Refuted);
    check("from_digit_g", Want::Proved);
    check("from_str_radix", Want::Refuted);
    check("from_str_radix_lit", Want::Proved);
    // Trust (ASCII-FROM-ASCII-RADIX-1, 2026-10-05): the nightly `from_ascii_radix`
    // (`int_from_ascii`) runs the same radix check and was never charged: these
    // built rc=0 on the default lane and panicked on radix 37 (`NonZero`'s on
    // radix 1). Dumped with the stage 1 of `ec03f72395`
    // (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`).
    check("from_ascii_radix_u32", Want::Refuted);
    check("from_ascii_radix_nonzero", Want::Refuted);
    check("from_ascii_radix_g", Want::Proved);
    check("from_ascii_radix_lit", Want::Proved);
}

// ---- strict_* and by-value operator calls ----

#[test]
fn strict_arithmetic_and_explicit_operator_calls_are_charged() {
    check("strict_add", Want::Refuted);
    check("strict_add_g", Want::Proved);
    check("strict_neg_u", Want::Refuted);
    check("ufcs_add", Want::Refuted);
}

// ---- Duration / Instant ----

#[test]
fn duration_constructors_and_division_are_charged_precisely() {
    check("dur_new", Want::Refuted);
    check("dur_new_g", Want::Proved);
    check("dur_div", Want::Refuted);
    check("dur_div_g", Want::Proved);
}

#[test]
fn duration_arithmetic_is_decided_on_literals_and_refused_otherwise() {
    check("dur_add", Want::Unmodeled("duration-arith-overflow-unmodeled"));
    check("dur_lit_add", Want::Proved);
    check("dur_from_f64", Want::Unmodeled("duration-from-float-unmodeled"));
    check("inst_plus_lit", Want::Proved);
    check("inst_plus_param", Want::Unmodeled("time-point-duration-overflow"));
}

#[test]
fn a_literal_duration_is_free_only_on_a_fresh_clock_reading() {
    // Review of `ff3a28cc92` (2026-09-28): the literal carve-out ignored the
    // receiver, so a CALLER's time point built at the representable edge
    // (`checked_add` to the largest value that fits) plus one literal second
    // built rc=0 and panicked at -O0 and -O. It now needs `now()` itself.
    check("inst_param_plus_lit", Want::Unmodeled("time-point-duration-overflow"));
    check("sys_param_sub_lit", Want::Unmodeled("time-point-duration-overflow"));
    // `let t = Instant::now(); t + lit` traces through the copy.
    check("inst_now_let_plus_lit", Want::Proved);
    // An assign form's receiver is `&mut` (loop-carried) state: charged.
    check("inst_now_addassign_lit", Want::Unmodeled("time-point-duration-overflow"));
    // An opaque constant time point may be the unstable `SystemTime::MAX`:
    // `UNIX_EPOCH + lit` is refused (a recorded over-refusal).
    check("sys_epoch_plus_lit", Want::Unmodeled("time-point-duration-overflow"));
}

#[test]
fn an_option_or_result_duration_sum_is_charged_like_a_duration_sum() {
    // `sum::<Option<Duration>>()` / `sum::<Result<Duration, E>>()` run
    // `Duration`'s own `Sum` inside core's `try_process` adaptor; review of
    // `ff3a28cc92` measured both rc=0 and panicking at -O0 and -O.
    check("sum_opt_duration", Want::Unmodeled("duration-sum-overflow"));
    check("sum_res_duration", Want::Unmodeled("duration-sum-overflow"));
}

// ---- range iteration ----

#[test]
fn range_iteration_overflow_is_charged() {
    check("range_incl_count", Want::Refuted);
    check("range_incl_count_g", Want::Proved);
    check("range_from_next", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    // Every consumer that advances a `RangeFrom` (not only `next`/`nth`), and
    // the explicit `<&mut RangeFrom<u8> as Iterator>::next` (review of
    // `ff3a28cc92`: both rc=0, panicking at -O0).
    check("range_from_find", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    check("range_from_ufcs_mut", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    // Trust (NEW-RANGE-ITER-UNCHARGED-1, 2026-10-11): the by-value iterators of the
    // stable `core::range` types. Each body below built rc=0 on the default lane of the
    // stage 1 of `1213387e6d` with one `runtime_checked` row and panicked ("overflow in
    // `Step::forward`" at `char::MAX`, "attempt to add with overflow" at `u8::MAX`,
    // "count overflowed usize" on `0..=u64::MAX` and `0..u128::MAX`); the end-to-end
    // pins are `tests/ui/trust/new_range_iter_step_charged{,_run}.rs`. Dumped with that
    // stage 1 (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`). Before the fix none of
    // these minted a family row, so every line fails.
    check("new_range_from_next", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    check("new_range_from_find", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    check("new_range_from_u8", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    // The `count` receiver is an `into_iter` call result, whose bounds are not traced:
    // the too-wide count is refused, never proved.
    check("new_range_incl_count_u64", Want::Unmodeled("range-count-overflow-unmodeled"));
    check("new_range_excl_count_u128", Want::Unmodeled("range-count-overflow-unmodeled"));
    // Trust (NEW-RANGE-REMAINDER-UNCHARGED-1, wave-24 review, 2026-10-12): the nightly
    // inherent `RangeFromIter::remainder` steps an EXHAUSTED iterator with
    // `Step::forward(start, 1)`. Dumped (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`,
    // -O0) by the stage 1 of `51eac007f3` from
    //   #![feature(new_range_remainder)]
    //   use core::range::{RangeFrom, RangeFromIter};
    //   pub fn new_range_from_remainder_param(it: RangeFromIter<char>) -> RangeFrom<char>
    //       { it.remainder() }
    //   pub fn new_range_from_remainder_char(c: char) -> RangeFrom<char> { let mut it =
    //       RangeFrom::from(c..).into_iter(); it.by_ref().take(1).for_each(drop);
    //       it.remainder() }
    //   (and `new_range_from_remainder_u8`, the same body over `u8`).
    // On that stage 1 each built rc=0 on the default lane with one `runtime_checked`
    // row, and a verify-off driver exited 101 at `char::MAX` and `u8::MAX`. Before the
    // fix none minted a family row, so these three lines fail.
    check("new_range_from_remainder_param", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    check("new_range_from_remainder_char", Want::Unmodeled("range-from-step-overflow-unmodeled"));
    check("new_range_from_remainder_u8", Want::Unmodeled("range-from-step-overflow-unmodeled"));
}

/// Trust (NEW-RANGE-ITER-UNCHARGED-1, 2026-10-11): the controls of the fix above. A
/// `RangeInclusiveIter<u32>` count cannot overflow the 64-bit `usize` these captures were
/// dumped for, and a lazy `take` advances nothing at its own call: neither mints a family
/// row or a fail-closed row.
#[test]
fn new_range_controls_mint_no_family_row() {
    for name in ["new_range_incl_count_u32", "new_range_from_take"] {
        let vcs = generate_vcs(&load(name));
        assert!(family_rows(&vcs).is_empty(), "{name}: no family row expected");
        assert!(family_unmodeled(&vcs).is_empty(), "{name}: no fail-closed row expected");
    }
}

/// Trust (STEP-TRAIT-DIRECT-UNCHARGED-1, 2026-10-11): a direct `Step::forward` /
/// `Step::backward` (nightly `step_trait`). On the stage 1 of `1213387e6d` each body
/// built rc=0 on the default lane with one `runtime_checked` row, and a verify-off driver
/// exited 101 ("overflow in `Step::forward`" at `char::MAX`, "overflow in
/// `Step::backward`" at `'\0'`, "attempt to add with overflow" at `u8::MAX`); the
/// end-to-end pins are `tests/ui/trust/policy_b/std_step_trait_value_panics_charged{,_run}.rs`.
/// Dumped with that stage 1 (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`). Before
/// the fix none minted a family row, so the three `Unmodeled` lines fail. The total
/// `forward_checked` mints none.
#[test]
fn step_trait_direct_calls_are_charged() {
    check("step_fwd_char", Want::Unmodeled("step-forward-overflow-unmodeled"));
    check("step_bwd_char", Want::Unmodeled("step-backward-overflow-unmodeled"));
    check("step_fwd_u8", Want::Unmodeled("step-forward-overflow-unmodeled"));
    let vcs = generate_vcs(&load("step_fwd_checked_char"));
    assert!(family_unmodeled(&vcs).is_empty(), "step_fwd_checked_char: total, no row expected");
}

/// Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): an open `x..` range over a NON-integer
/// core `Step` type. Dumped (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`, -O0) by
/// `scratchpad/stage1-w25f` (the wave-25 stage 1, tree of `a971311ee2`) from
///   pub fn step_elem_ipv4_next2(x: Ipv4Addr) -> Option<Ipv4Addr>
///       { let mut it = x..; it.next(); it.next() }
///   (and `step_elem_nonzero_next2` over `NonZero<u8>`, `step_elem_ipv6_next2` over
///   `Ipv6Addr`), `step_elem_ipv4_find` (`(x..).find(|a| a.octets()[3] == 7)`),
///   `step_elem_newrange_v4_next2` (`core::range::RangeFrom::from(x..).into_iter()`, then
///   `next(); next()`), `step_elem_ipv6_count` (`(a..b).count()` over `Ipv6Addr`) and the
///   control `step_elem_ipv4_bounded` (`x..=Ipv4Addr::BROADCAST`, `next(); next()`).
/// On that stage 1 the `x..` bodies built rc=0 on the default lane with one
/// `runtime_checked` row each, and a verify-off driver exited 101 ("overflow in
/// `Step::forward`" at `Ipv4Addr::BROADCAST` and `u128::MAX`, "attempt to add with
/// overflow" at `NonZero::<u8>::MAX`); the end-to-end pins are
/// `tests/ui/trust/policy_b/range_from_step_types_charged{,_run}.rs`. The `RangeFrom` arms
/// read `int | char` only, and `range_count_can_overflow` answered `false` for any other
/// element, so before the fix none of these minted a family row and every `Unmodeled`
/// line fails.
#[test]
fn core_step_elem_range_iteration_is_charged() {
    for name in [
        "step_elem_ipv4_next2",
        "step_elem_nonzero_next2",
        "step_elem_ipv4_find",
        "step_elem_ipv6_next2",
        "step_elem_newrange_v4_next2",
    ] {
        check(name, Want::Unmodeled("range-from-step-overflow-unmodeled"));
    }
    // `Range<Ipv6Addr>::count` can exceed a 64-bit `usize` (128-bit span); its step
    // count is not modeled, so it is refused, never proved.
    check("step_elem_ipv6_count", Want::Unmodeled("range-count-overflow-unmodeled"));
    // A bounded `x..=MAX` range never steps past `MAX`: no family row.
    let vcs = generate_vcs(&load("step_elem_ipv4_bounded"));
    assert!(family_rows(&vcs).is_empty(), "step_elem_ipv4_bounded: no family row expected");
    assert!(
        family_unmodeled(&vcs).is_empty(),
        "step_elem_ipv4_bounded: no fail-closed row expected"
    );
}

#[test]
fn explicit_compound_assign_calls_on_integers_are_charged() {
    // `a.add_assign(b)` and siblings carry core's overflow check on `*self`
    // (`#[rustc_inherit_overflow_checks]`); review of `ff3a28cc92` measured
    // add/sub/mul/shl_assign rc=0 with NO row and panicking at -O0. They now
    // get the `*a op b` row the operator spelling `*a += b` owes.
    check("add_assign_i32", Want::Refuted);
    check("sub_assign_u32_ref", Want::Refuted);
    check("mul_assign_i64", Want::Refuted);
    check("shl_assign_u32", Want::Refuted);
    check("shl_assign_u32_g", Want::Proved);
    check("add_assign_i32_g", Want::Proved);
    // A guard on the pointee (`b <= *a`) is a fact about the SAME place the row
    // reads, so the guarded `&mut` receiver is never refuted.
    let vcs = generate_vcs(&load("sub_assign_u32_ref_g"));
    let router = router();
    let rows = family_rows(&vcs);
    assert!(!rows.is_empty(), "sub_assign_u32_ref_g: the guarded call must still carry its row");
    for vc in rows {
        let r = router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1;
        assert!(
            !matches!(r, VerificationResult::Failed { .. }),
            "sub_assign_u32_ref_g: a guarded `*a - b` must not be refuted: {r:?}"
        );
    }
    assert!(family_unmodeled(&vcs).is_empty(), "sub_assign_u32_ref_g: no fail-closed row expected");
}

#[test]
fn a_product_of_two_variables_is_refuted_like_a_star_b() {
    // The same-type `strict_mul` and a by-value `Mul::mul` get the row the
    // `BinaryOp` arm builds for `a * b` (its bit-vector route). An `Assertion`
    // over the LIA product (the first cut) was answered `Unknown` and reported
    // runtime-checked, so `i32::strict_mul` built rc=0.
    check("strict_mul_i32", Want::Refuted);
    check("ufcs_mul_i32", Want::Refuted);
    // ...and a dominating range guard on both operands is never REFUTED: the
    // in-process solver answers the guarded product `Unknown`, which the default
    // policy reports runtime-checked for an `ArithmeticOverflow` row (it keeps
    // its overflow check) — exactly what it answers for the guarded `a * b`.
    let vcs = generate_vcs(&load("ufcs_mul_i32_g"));
    let router = router();
    for vc in
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
    {
        let r = router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1;
        assert!(
            !matches!(r, VerificationResult::Failed { .. }),
            "ufcs_mul_i32_g: a guarded product must not be refuted: {r:?}"
        );
    }
}

#[test]
fn strict_pow_is_charged_like_pow() {
    // `strict_pow` takes the overflow-call lane's `pow` row (an
    // `ArithmeticOverflow` row): a symbolic exponent is refuted, a constant
    // exponent is unrolled, and a guard on the base proves it.
    check("strict_pow_u32", Want::Refuted);
    check("strict_pow_u32_sq", Want::Refuted);
    check("strict_pow_u32_sq_g", Want::Proved);
    // Trust (2026-10-05, POW-SYMEXP-1): the symbolic-exponent body was
    // `base >= 2 AND exp >= W`, so a guard bounding the exponent below the width
    // (`if e < 32 { a.strict_pow(e) }`, which panics at `3u32.strict_pow(21)`)
    // and a negative base (`(-2i32).strict_pow(e)`, which panics at `e == 32`)
    // both PROVED. Dumped with the stage 1 of `ec03f72395`
    // (`-Ztrust-policy=advisory -Ztrust-dump=mir-only`).
    check("strict_pow_u32_eg", Want::Refuted);
    check("strict_pow_i32_neg", Want::Refuted);
    // ...and a guard that excludes every overflow still proves (`2^31` fits u32).
    check("strict_pow_2_eg", Want::Proved);
}
