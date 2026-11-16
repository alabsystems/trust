// ADVERSARIAL FIXTURES FOR THE DOMAIN-CONVERSION RULE TABLE.
//
// Every test below is built the same way: take the predicate a WRONG
// implementation would make true, evaluate it CONCRETELY at the witness value
// with a real two's-complement bit-vector evaluator, and show that the machine
// says the opposite. A rule table that only asserts on the shape of the emitted
// `Formula` cannot catch a rule that emits a well-shaped but wrong node; these
// evaluate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Sort;

use super::*;

// ---------------------------------------------------------------------------
// A concrete two's-complement evaluator over the bit-vector fragment this
// module emits. Values are (pattern, width) with the pattern always reduced to
// the low `width` bits, exactly the SMT-LIB reading.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Bits {
    pattern: u128,
    width: u32,
}

fn mask(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1_u128 << width) - 1 }
}

impl Bits {
    fn new(pattern: u128, width: u32) -> Self {
        Bits { pattern: pattern & mask(width), width }
    }

    /// The mathematical integer this pattern denotes in the given domain.
    fn value(self, signed: bool) -> i128 {
        if signed && self.width < 128 && (self.pattern >> (self.width - 1)) & 1 == 1 {
            (self.pattern as i128) - (1_i128 << self.width)
        } else if signed && self.width == 128 {
            self.pattern as i128
        } else {
            self.pattern as i128
        }
    }
}

/// Evaluate a formula from this module's fragment. `env` binds `Var` names to
/// their patterns. Panics on any node outside the fragment — a deliberate
/// tripwire: if the rule table ever emits something else, the fixture stops
/// silently passing.
fn eval(formula: &Formula, env: &[(&str, Bits)]) -> Bits {
    match formula {
        Formula::BitVec { value, width } => Bits::new(*value as u128, *width),
        Formula::Var(name, Sort::BitVec(width)) => {
            let bits = env
                .iter()
                .find(|(bound, _)| bound == name)
                .unwrap_or_else(|| panic!("unbound {name}"))
                .1;
            assert_eq!(bits.width, *width, "{name} bound at the wrong width");
            bits
        }
        Formula::BvZeroExt(inner, extra) => {
            let inner = eval(inner, env);
            Bits::new(inner.pattern, inner.width + extra)
        }
        Formula::BvSignExt(inner, extra) => {
            let inner = eval(inner, env);
            let target = inner.width + extra;
            let negative = (inner.pattern >> (inner.width - 1)) & 1 == 1;
            let filled = if negative {
                inner.pattern | (mask(target) & !mask(inner.width))
            } else {
                inner.pattern
            };
            Bits::new(filled, target)
        }
        Formula::BvExtract { inner, high, low } => {
            let inner = eval(inner, env);
            Bits::new(inner.pattern >> low, high - low + 1)
        }
        Formula::BvAnd(a, b, width) => {
            let (a, b) = (eval(a, env), eval(b, env));
            assert_eq!((a.width, b.width), (*width, *width));
            Bits::new(a.pattern & b.pattern, *width)
        }
        Formula::BvShl(a, b, width) => {
            let (a, b) = (eval(a, env), eval(b, env));
            assert_eq!((a.width, b.width), (*width, *width));
            // SMT-LIB bvshl: a shift of `width` or more yields zero.
            let shifted = if b.pattern >= u128::from(*width) { 0 } else { a.pattern << b.pattern };
            Bits::new(shifted, *width)
        }
        other => panic!("outside the evaluated fragment: {other:?}"),
    }
}

fn dom(width: u32, signed: bool) -> MachineDomain {
    MachineDomain::new(width, signed).expect("a supported Rust width")
}

fn var(name: &str, width: u32) -> Formula {
    Formula::Var(name.to_string(), Sort::BitVec(width))
}

const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

/// The witness patterns every exhaustive check runs: zero, one, the unsigned
/// maximum, the value with only the sign bit set (the smallest signed value),
/// and the largest signed value.
fn witnesses(width: u32) -> Vec<u128> {
    let top = 1_u128 << (width - 1);
    vec![0, 1, mask(width), top, top - 1, top | 1]
}

// ---------------------------------------------------------------------------
// THE RULE TABLE, checked by evaluation rather than by shape.
// ---------------------------------------------------------------------------

/// EVERY conversion the table admits preserves the mathematical value, at every
/// witness pattern, for every pair of Rust widths and signednesses. This is the
/// exactness claim itself, discharged by evaluation.
#[test]
fn every_admitted_conversion_preserves_the_mathematical_value() {
    let mut admitted = 0;
    for src_width in WIDTHS {
        for src_signed in [false, true] {
            for dst_width in WIDTHS {
                for dst_signed in [false, true] {
                    let src = dom(src_width, src_signed);
                    let dst = dom(dst_width, dst_signed);
                    let Some(conversion) = value_preserving_conversion(src, dst) else {
                        continue;
                    };
                    admitted += 1;
                    for pattern in witnesses(src_width) {
                        let before = Bits::new(pattern, src_width);
                        let after = eval(&conversion.apply(var("x", src_width)), &[("x", before)]);
                        assert_eq!(
                            after.width, dst_width,
                            "{src:?} -> {dst:?} must land at the target width",
                        );
                        assert_eq!(
                            before.value(src_signed),
                            after.value(dst_signed),
                            "{src:?} -> {dst:?} changed the value of {pattern:#x} \
                             ({conversion:?})",
                        );
                    }
                }
            }
        }
    }
    // 10 identities + the strict widenings; a table that admitted nothing would
    // pass the loop above vacuously.
    assert_eq!(admitted, 40, "the admitted set is the rule table, not the empty set");
}

/// (i) A SIGN-EXTENDED NEGATIVE TREATED AS ZERO-EXTENDED. `-1i32` is
/// `0xffff_ffff`. The predicate a zero-extending implementation makes true is
/// `widened > 0`; the machine says `-1 > 0` is false.
#[test]
fn sign_extension_is_not_zero_extension_at_a_negative_source() {
    let src = dom(32, true);
    let dst = dom(64, true);
    let conversion = value_preserving_conversion(src, dst).expect("i32 -> i64 is value-preserving");
    assert_eq!(conversion, ValueConversion::SignExtend(32));

    let negative_one = Bits::new(0xffff_ffff, 32);
    assert_eq!(negative_one.value(true), -1);

    let emitted = eval(&conversion.apply(var("x", 32)), &[("x", negative_one)]);
    assert_eq!(emitted.pattern, 0xffff_ffff_ffff_ffff);
    assert_eq!(emitted.value(true), -1, "the machine keeps -1");

    let wrong = eval(&ValueConversion::ZeroExtend(32).apply(var("x", 32)), &[("x", negative_one)]);
    assert_eq!(wrong.pattern, 0x0000_0000_ffff_ffff);
    assert_eq!(wrong.value(true), 4_294_967_295, "zero extension invents a positive value");
    assert!(
        wrong.value(true) > 0 && emitted.value(true) < 0,
        "`widened > 0` is exactly the predicate a zero-extending i32 -> i64 would mint",
    );
}

/// (ii) A NARROWING TREATED AS IDENTITY. `u64 as u32` at `2^32` is `0`, so
/// `(a as u32) == 0` is true there while `a == 0` is false. The table refuses to
/// mint any conversion at all, in EITHER signedness, so no term exists to be
/// lowered as the identity.
#[test]
fn no_narrowing_is_admitted_in_any_signedness() {
    for src_width in WIDTHS {
        for dst_width in WIDTHS {
            if dst_width >= src_width {
                continue;
            }
            for src_signed in [false, true] {
                for dst_signed in [false, true] {
                    assert_eq!(
                        value_preserving_conversion(
                            dom(src_width, src_signed),
                            dom(dst_width, dst_signed),
                        ),
                        None,
                        "u{src_width}/i -> u{dst_width}/i narrowing must be refused",
                    );
                }
            }
        }
    }
    // The witness the sibling lane's `contract_truncating_cast_stays_refused.rs`
    // fixture uses: 2^32 is a u64 whose low 32 bits are zero.
    let two_to_the_32 = Bits::new(1_u128 << 32, 64);
    assert_eq!(two_to_the_32.value(false), 4_294_967_296);
    assert_eq!(
        Bits::new(two_to_the_32.pattern, 32).value(false),
        0,
        "the machine's u64 -> u32 is the low 32 bits, and it is not the identity",
    );
}

/// (iii) `i32 as u32` AT A NEGATIVE VALUE. `-1i32 as u32` is `4294967295`, so
/// `(a as u32) > 0` is true where `a > 0` is false. Signed -> unsigned is
/// refused at every width pair, including widening ones.
#[test]
fn signed_to_unsigned_is_refused_at_every_width_pair() {
    for src_width in WIDTHS {
        for dst_width in WIDTHS {
            assert_eq!(
                value_preserving_conversion(dom(src_width, true), dom(dst_width, false)),
                None,
                "i{src_width} -> u{dst_width} must be refused",
            );
        }
    }
    let negative_one = Bits::new(0xffff_ffff, 32);
    assert_eq!(negative_one.value(true), -1);
    assert_eq!(
        negative_one.value(false),
        4_294_967_295,
        "the same pattern read unsigned is positive — that is the whole defect",
    );
}

/// (iv) AN EQUAL-WIDTH `u8 as i8` AT 255. The pattern is unchanged, the value is
/// not: `255u8` becomes `-1i8`.
#[test]
fn equal_width_signedness_reinterpretation_is_refused_both_ways() {
    for width in WIDTHS {
        assert_eq!(value_preserving_conversion(dom(width, false), dom(width, true)), None);
        assert_eq!(value_preserving_conversion(dom(width, true), dom(width, false)), None);
    }
    let all_ones = Bits::new(0xff, 8);
    assert_eq!(all_ones.value(false), 255);
    assert_eq!(all_ones.value(true), -1);
    assert!(
        all_ones.value(false) > 0 && all_ones.value(true) < 0,
        "`(a as i8) > 0` is exactly the predicate an identity `u8 -> i8` would mint",
    );
    // …but unsigned into a STRICTLY wider signed target IS exact, and 255 is
    // where a wrong rule would show it.
    let widened = value_preserving_conversion(dom(8, false), dom(16, true))
        .expect("u8 -> i16 has the spare sign bit");
    assert_eq!(widened, ValueConversion::ZeroExtend(8));
    assert_eq!(eval(&widened.apply(var("x", 8)), &[("x", all_ones)]).value(true), 255);
}

/// (v) A SHIFT AMOUNT AT OR BEYOND THE WIDTH. `1u8 << 8` is `1` on the machine
/// (rustc masks the count by `width - 1`), while a raw `bvshl` by 8 on an 8-bit
/// vector is `0`. The mask is therefore load-bearing, and this fixture fails if
/// it is ever dropped.
#[test]
fn a_shift_amount_at_the_width_is_masked_exactly_as_rustc_masks_it() {
    let masked = shift_amount_resize_and_mask(var("k", 8), 8, 8).expect("u8 count, u8 value");
    let count = eval(&masked, &[("k", Bits::new(8, 8))]);
    assert_eq!(count.pattern, 0, "8 & 7 == 0");

    let shifted = Formula::BvShl(Box::new(var("x", 8)), Box::new(masked.clone()), 8);
    let with_mask = eval(&shifted, &[("x", Bits::new(1, 8)), ("k", Bits::new(8, 8))]);
    assert_eq!(with_mask.pattern, 1, "`1u8 << 8` is 1 on the machine");

    let unmasked = Formula::BvShl(Box::new(var("x", 8)), Box::new(var("k", 8)), 8);
    let without_mask = eval(&unmasked, &[("x", Bits::new(1, 8)), ("k", Bits::new(8, 8))]);
    assert_eq!(
        without_mask.pattern, 0,
        "an unmasked bvshl by the width is zero — the wrong answer"
    );
    assert_ne!(with_mask, without_mask, "the mask is what makes this exact");

    // Beyond the width, and from a WIDER count than the shifted value: rustc
    // truncates the count, so `(x: u8) << (0x1_0000_0003u64)` shifts by 3.
    let wide = shift_amount_resize_and_mask(var("k", 64), 64, 8).expect("u64 count, u8 value");
    let count = eval(&wide, &[("k", Bits::new((1 << 32) + 3, 64))]);
    assert_eq!(count.pattern, 3, "truncate to 8 bits, then mask by 7");
}

/// The shift-count resize agrees with rustc for EVERY (count width, count
/// signedness, value width) triple, checked against a direct model of
/// `build_shift_expr_rhs`: mask in the count's own type FIRST, then truncate or
/// zero-extend. The two orders must select the same count.
#[test]
fn the_shift_count_resize_matches_rustcs_mask_then_resize_order() {
    for count_width in WIDTHS {
        for value_width in WIDTHS {
            let ours =
                shift_amount_resize_and_mask(var("k", count_width), count_width, value_width)
                    .expect("supported widths");
            for pattern in witnesses(count_width) {
                let bound = Bits::new(pattern, count_width);
                let ours_count = eval(&ours, &[("k", bound)]);

                // rustc: `and` with `value_width - 1` typed at the COUNT's width,
                // then trunc/zext to the value width. Signedness never enters:
                // the extension is unconditionally zero.
                let rustc_masked = bound.pattern & u128::from(value_width - 1);
                let rustc_count = Bits::new(rustc_masked, value_width);

                assert_eq!(
                    ours_count, rustc_count,
                    "u{count_width} count {pattern:#x} into a {value_width}-bit shift",
                );
                assert!(
                    ours_count.pattern < u128::from(value_width),
                    "a masked count is always in range",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// THE JOIN.
// ---------------------------------------------------------------------------

#[test]
fn the_join_widens_exactly_and_refuses_every_inexact_meeting() {
    let (joined, from_left, from_right) = join(dom(32, false), dom(64, false)).expect("u32, u64");
    assert_eq!(
        (joined, from_left, from_right),
        (dom(64, false), ValueConversion::ZeroExtend(32), ValueConversion::Identity,)
    );

    let (joined, from_left, from_right) = join(dom(32, true), dom(64, true)).expect("i32, i64");
    assert_eq!(
        (joined, from_left, from_right),
        (dom(64, true), ValueConversion::SignExtend(32), ValueConversion::Identity,)
    );

    let (joined, from_left, _) = join(dom(32, false), dom(64, true)).expect("u32, i64");
    assert_eq!((joined, from_left), (dom(64, true), ValueConversion::ZeroExtend(32)));

    // No exact join exists in the Rust width set for these, and inventing a
    // wider one is not this function's business.
    assert_eq!(join(dom(8, false), dom(8, true)), None, "u8 and i8");
    assert_eq!(join(dom(32, false), dom(32, true)), None, "u32 and i32");
    assert_eq!(join(dom(64, false), dom(32, true)), None, "u64 does not fit i32");
    assert_eq!(join(dom(128, false), dom(64, true)), None, "u128 has no signed home");
}

/// A join is only ever correct under an operator that means the MATHEMATICAL
/// relation. Under wrapping arithmetic it is a false-proof generator, and this
/// records the witness: `x + 1 > x` is FALSE for a `u32` `x` at `u32::MAX`
/// (the sum wraps to 0) and TRUE if the same expression is evaluated in the
/// joined 64-bit domain.
#[test]
fn widening_under_wrapping_arithmetic_would_flip_the_answer() {
    let at_u32_max = Bits::new(mask(32), 32);
    let wrapped = Bits::new(at_u32_max.pattern + 1, 32);
    assert_eq!(wrapped.value(false), 0);
    assert!(
        wrapped.value(false) < at_u32_max.value(false),
        "on the machine `x + 1 > x` is false at u32::MAX",
    );

    let widened = eval(&ValueConversion::ZeroExtend(32).apply(var("x", 32)), &[("x", at_u32_max)]);
    let sum_at_64 = Bits::new(widened.pattern + 1, 64);
    assert!(
        sum_at_64.value(false) > widened.value(false),
        "in the joined domain the same expression is TRUE — which is why \
         `join` must never be applied to an arithmetic operand",
    );
}

// ---------------------------------------------------------------------------
// THE SCAN.
// ---------------------------------------------------------------------------

#[test]
fn the_scan_separates_the_three_reasons_a_domain_can_be_absent() {
    let mut empty = DomainScan::default();
    assert_eq!(empty.uniform(), None);
    assert_eq!(empty.refusal_detail(), "no leaf declares a machine domain");

    empty.observe(dom(32, false));
    assert_eq!(empty.uniform(), Some(dom(32, false)));

    let mut disagreeing = DomainScan::default();
    disagreeing.observe(dom(32, false));
    disagreeing.observe(dom(64, false));
    disagreeing.observe(dom(32, false));
    assert_eq!(disagreeing.uniform(), None);
    assert_eq!(
        disagreeing.refusal_detail(),
        "declared domains disagree: u32, u64 (exact widening join at u64)",
    );

    let mut inexact = DomainScan::default();
    inexact.observe(dom(8, false));
    inexact.observe(dom(8, true));
    assert_eq!(inexact.exact_join(), None);
    assert_eq!(
        inexact.refusal_detail(),
        "declared domains disagree: i8, u8 (no exact widening join exists)",
    );

    let mut carrier = DomainScan::default();
    carrier.observe(dom(64, false));
    carrier.observe_non_machine("data");
    assert_eq!(carrier.uniform(), None, "one machine domain is not enough if a leaf has none");
    assert_eq!(carrier.refusal_detail(), "leaves with no machine domain: data");

    let mut both = DomainScan::default();
    both.observe(dom(32, false));
    both.observe(dom(64, false));
    both.observe_non_machine("data");
    assert_eq!(
        both.refusal_detail(),
        "declared domains disagree: u32, u64 (exact widening join at u64); \
         leaves with no machine domain: data",
    );
}

#[test]
fn unsupported_widths_convert_to_nothing() {
    assert_eq!(MachineDomain::new(7, false), None);
    assert_eq!(MachineDomain::new(0, false), None);
    assert!(!width_supported(1));
    assert!(WIDTHS.iter().all(|width| width_supported(*width)));
    assert_eq!(shift_amount_resize_and_mask(var("k", 8), 7, 8), None);
    assert_eq!(shift_amount_resize_and_mask(var("k", 8), 8, 7), None);
}

/// THE CLOSED-ATOM WRAP CHANNEL, as a plain arithmetic fact. An atom that lost
/// its variables to substitution has no domain of its own, so it borrows one —
/// and if that borrowed domain is narrow enough, a literal SUM that Rust
/// evaluates in `i32` wraps instead. `255 + 1 == 0` is FALSE in Rust and TRUE at
/// a borrowed `u8`.
///
/// The translator's answer is not to pick a better width but to admit no
/// arithmetic at all in a closed atom (see
/// `contracts::machine_faithful_translate_joined`'s `meet`); this records the
/// witness that makes that restriction load-bearing.
#[test]
fn a_borrowed_narrow_domain_makes_a_closed_sum_read_the_wrong_way() {
    let wrapped = Bits::new(255 + 1, 8);
    assert_eq!(wrapped.value(false), 0, "at u8 the sum wraps to 0 and `== 0` reads TRUE");
    let honest = Bits::new(255 + 1, 32);
    assert_eq!(honest.value(false), 256, "in Rust's i32 the same sum is 256 and `== 0` is FALSE");
    let at_the_join = Bits::new(65535 + 1, 16);
    assert_eq!(
        at_the_join.value(false),
        0,
        "and widening to the JOIN does not fix it — u8 joined with u16 is u16, \
         where `65535 + 1 == 0` reads TRUE just the same",
    );
}
