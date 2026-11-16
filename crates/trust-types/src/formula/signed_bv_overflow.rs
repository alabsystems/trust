// trust-types/formula/signed_bv_overflow: the signed add/sub overflow predicate
// over bitvectors, single-sourced for its producer and its consumers.
//
// trust-vcgen emits this predicate as the violation of a signed `w`-bit add/sub
// overflow obligation. trust-certify's signed-BV lane and trust-router's
// structural-UNSAT twin recognize it and discharge it from the operands' signed
// bounds. A consumer may only discharge a row by this argument when the row
// ASSERTS the predicate, so the recognizer rebuilds it with the producer's own
// constructor and compares structurally — a row that merely mentions a bounded
// `BvAdd`/`BvSub` somewhere is not an overflow row.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{Formula, Sort};

/// The SIGNED add/sub overflow (failure) condition via the SIGN-BIT test, in pure
/// QF_BV using ONLY `BvULt` + `BvAdd`/`BvSub` at the operand width + `And`/`Or`/`Not`
/// + `BitVec`.
///
/// A `width`-bit value `v` is SIGNED-NEGATIVE iff its UNSIGNED value has the sign bit
/// set, i.e. `NOT (v <u 2^(width-1))`. With `r = a OP b` taken at width `width`
/// (two's-complement wraparound), signed overflow is the classic sign-relation test:
///   * `a + b` overflows iff `a`,`b` have the SAME sign and `r`'s sign differs from `a`'s;
///   * `a - b` overflows iff `a`,`b` have DIFFERENT signs and `r`'s sign differs from `a`'s.
///
/// The result is `And([sign_relation, result_sign_flips])`; consumers match its TWO
/// conjuncts. Neither conjunct alone is the overflow predicate: `a = 5, b = -10`
/// flips `r`'s sign with no overflow.
///
/// SOUNDNESS: this is the EXACT two's-complement overflow predicate (it agrees with the
/// `w+1`-bit sign-extension form on every input — see trust-vcgen's exhaustive `w=8`
/// cross-check test). An unconstrained operand keeps it satisfiable, so a real
/// `i128::MAX - (-1)` / `1<<127` overflow stays SAT/refutable.
///
/// `None` unless `1 <= width <= 128` (the sign-bit literal is undefined outside it).
#[must_use]
pub fn signed_bv_addsub_overflow_sign_test(
    a: Formula,
    b: Formula,
    is_add: bool,
    width: u32,
) -> Option<Formula> {
    if width == 0 || width > 128 {
        return None;
    }
    // The sign-bit mask `2^(width-1)`. For `width == 128` this is `i128::MIN`'s bit
    // pattern (the `BitVec` value field is two's-complement; the SMT layer masks to
    // `width`) — the SAME representation the neg `INT_MIN` check uses.
    let msb = Formula::BitVec {
        value: if width == 128 { i128::MIN } else { 1i128 << (width - 1) },
        width,
    };
    let nonneg = |v: &Formula| Formula::BvULt(Box::new(v.clone()), Box::new(msb.clone()), width);
    let result = if is_add {
        Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), width)
    } else {
        Formula::BvSub(Box::new(a.clone()), Box::new(b.clone()), width)
    };
    let nn_a = nonneg(&a);
    let nn_b = nonneg(&b);
    let nn_r = nonneg(&result);
    // Boolean `x != y`, expanded to `And`/`Or`/`Not` so no Bool-sorted `Eq` is emitted.
    let differ = |x: &Formula, y: &Formula| {
        Formula::Or(vec![
            Formula::And(vec![x.clone(), Formula::Not(Box::new(y.clone()))]),
            Formula::And(vec![Formula::Not(Box::new(x.clone())), y.clone()]),
        ])
    };
    let result_sign_flips = differ(&nn_r, &nn_a);
    let sign_relation = if is_add {
        // SAME sign = NOT (signs differ).
        Formula::Not(Box::new(differ(&nn_a, &nn_b)))
    } else {
        differ(&nn_a, &nn_b)
    };
    Some(Formula::And(vec![sign_relation, result_sign_flips]))
}

/// The signed (two's-complement) value of a `width`-bit literal: the literal's
/// `value` field masked to `width` bits — the SMT layer's reading — and read with
/// bit `width-1` as the sign. `BitVec { value: 2^31, width: 32 }` is `i32::MIN`,
/// not `+2^31`.
///
/// `None` unless `f` is a `BitVec` literal of EXACTLY `width` bits and
/// `1 <= width <= 128`: a literal of another width is not a bound at this width.
#[must_use]
pub fn signed_bv_literal_value(f: &Formula, width: u32) -> Option<i128> {
    let Formula::BitVec { value, width: literal_width } = f else { return None };
    if *literal_width != width || width == 0 || width > 128 {
        return None;
    }
    // Two's-complement reinterpretation: keep the low `width` bits, move the sign
    // bit to bit 127, and shift back arithmetically so it extends.
    let shift = 128 - width;
    Some((((*value as u128) << shift) as i128) >> shift)
}

/// A signed `lhs OP rhs` at `width` bits (`OP` = add when `is_add`, else sub)
/// whose COMPLETE overflow predicate a conjunct pool asserts — see
/// [`asserted_signed_bv_addsub_overflows`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SignedBvAddSubOverflow<'a> {
    pub lhs: &'a Formula,
    pub rhs: &'a Formula,
    pub is_add: bool,
    pub width: u32,
}

/// Every signed `BvAdd`/`BvSub(lhs, rhs, w)` whose exact overflow predicate
/// ([`signed_bv_addsub_overflow_sign_test`]) is ASSERTED by `conjuncts`: both of
/// the predicate's conjuncts — rebuilt from the operation's own operands with the
/// producer's constructor — occur, structurally equal, among `conjuncts`.
///
/// `conjuncts` must be TOP-LEVEL conjuncts of the formula being discharged (its
/// `And` flattened, nothing under an `Or`/`Not`/`Implies`). Then the formula
/// implies "`lhs OP rhs` overflows `w` signed bits", and a consumer that refutes
/// that overflow from the operands' bounds refutes the formula. An operation that
/// merely OCCURS in the formula — inside an `ensures` equation, a guard, one
/// disjunct of an `Or` — is not returned: there the formula does not imply its
/// overflow, and refuting the overflow says nothing about the formula.
#[must_use]
pub fn asserted_signed_bv_addsub_overflows<'a>(
    conjuncts: &[&'a Formula],
) -> Vec<SignedBvAddSubOverflow<'a>> {
    let mut found: Vec<SignedBvAddSubOverflow<'a>> = Vec::new();
    for &c in conjuncts {
        // Candidates come from the result-sign-flip conjunct, which carries the
        // operation at a fixed position: `Or([And([BvULt(r, msb), ..]), ..])`.
        // Locating the candidate this way is only a search; the structural
        // comparison against the rebuilt predicate below is the gate.
        let Formula::Or(branches) = c else { continue };
        let [Formula::And(first), _] = branches.as_slice() else { continue };
        let [Formula::BvULt(result, _, _), _] = first.as_slice() else { continue };
        let (lhs, rhs, width, is_add) = match result.as_ref() {
            Formula::BvAdd(a, b, w) => (a.as_ref(), b.as_ref(), *w, true),
            Formula::BvSub(a, b, w) => (a.as_ref(), b.as_ref(), *w, false),
            _ => continue,
        };
        let Some(Formula::And(parts)) =
            signed_bv_addsub_overflow_sign_test(lhs.clone(), rhs.clone(), is_add, width)
        else {
            continue;
        };
        if !parts.iter().all(|part| conjuncts.contains(&part)) {
            continue;
        }
        let candidate = SignedBvAddSubOverflow { lhs, rhs, is_add, width };
        if !found.contains(&candidate) {
            found.push(candidate);
        }
    }
    found
}

/// The closed signed interval `[lo, hi]` that the TOP-LEVEL conjuncts `conjuncts`
/// give a `width`-bit operand of a signed add/sub.
///
/// It starts from the inherent signed range of the operand's innermost
/// sign-extension source (a `sw→w` `BvSignExt` holds a `sw`-bit signed value;
/// a bare operand has the full `w`-bit range) and narrows it by every
/// `BvSLt`/`BvSLe` atom comparing a literal with the operand or with one of its
/// sign-extension sources. Sign extension preserves the signed value, so a bound
/// on any of those layers bounds the operand. An atom is used only when its
/// width, its literal's width and the layer's width all agree, and its literal is
/// read as two's complement at that width ([`signed_bv_literal_value`]).
/// `BvSLt(c, x)` ⟹ `x ≥ c+1`; `BvSLt(x, c)` ⟹ `x ≤ c-1`; non-strict via `BvSLe`.
/// Any other conjunct is ignored, which only widens the interval.
///
/// `None` when the operand is not well-sorted at `width` bits. The interval may
/// be empty (`lo > hi`) when the bounds contradict; callers decline that case.
#[must_use]
pub fn signed_bv_operand_interval(
    conjuncts: &[&Formula],
    operand: &Formula,
    width: u32,
) -> Option<(i128, i128)> {
    if width == 0 || width > 128 {
        return None;
    }
    if crate::smt_logic::check_formula_sort(operand) != Ok(Sort::BitVec(width)) {
        return None;
    }
    // The operand and each sign-extension source under it, with its width.
    let mut layers: Vec<(&Formula, u32)> = vec![(operand, width)];
    let (mut current, mut current_width) = (operand, width);
    while let Formula::BvSignExt(inner, extra) = current {
        let inner_width = current_width.checked_sub(*extra).filter(|w| *w > 0)?;
        current = inner.as_ref();
        current_width = inner_width;
        layers.push((current, current_width));
    }
    let (mut lo, mut hi) = signed_range(current_width);
    for &c in conjuncts {
        let (strict, l, r, atom_width) = match c {
            Formula::BvSLt(l, r, w) => (true, l.as_ref(), r.as_ref(), *w),
            Formula::BvSLe(l, r, w) => (false, l.as_ref(), r.as_ref(), *w),
            _ => continue,
        };
        for &(layer, layer_width) in &layers {
            if atom_width != layer_width {
                continue;
            }
            if l == layer {
                // `layer <(=) c` ⟹ upper bound.
                let Some(v) = signed_bv_literal_value(r, layer_width) else { continue };
                if let Some(bound) = if strict { v.checked_sub(1) } else { Some(v) } {
                    hi = hi.min(bound);
                }
            } else if r == layer {
                // `c <(=) layer` ⟹ lower bound.
                let Some(v) = signed_bv_literal_value(l, layer_width) else { continue };
                if let Some(bound) = if strict { v.checked_add(1) } else { Some(v) } {
                    lo = lo.max(bound);
                }
            }
        }
    }
    Some((lo, hi))
}

/// The signed `[min, max]` of a `w`-bit two's-complement integer (`1 <= w <= 128`).
fn signed_range(w: u32) -> (i128, i128) {
    if w >= 128 { (i128::MIN, i128::MAX) } else { (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bvvar(name: &str, width: u32) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(width))
    }
    fn lit(value: i128, width: u32) -> Formula {
        Formula::BitVec { value, width }
    }
    fn flatten(f: &Formula) -> Vec<&Formula> {
        match f {
            Formula::And(items) => items.iter().flat_map(flatten).collect(),
            other => vec![other],
        }
    }

    #[test]
    fn literal_value_is_twos_complement_at_its_width() {
        // The machine lane's i64/i32 type-range literals.
        assert_eq!(signed_bv_literal_value(&lit(1 << 63, 64), 64), Some(i64::MIN as i128));
        assert_eq!(signed_bv_literal_value(&lit((1 << 63) - 1, 64), 64), Some(i64::MAX as i128));
        assert_eq!(signed_bv_literal_value(&lit(1 << 31, 32), 32), Some(i32::MIN as i128));
        assert_eq!(signed_bv_literal_value(&lit(-1000, 64), 64), Some(-1000));
        assert_eq!(signed_bv_literal_value(&lit(255, 8), 8), Some(-1));
        assert_eq!(signed_bv_literal_value(&lit(10, 128), 128), Some(10));
        assert_eq!(signed_bv_literal_value(&lit(i128::MIN, 128), 128), Some(i128::MIN));
        // Width 127: the sign bit is bit 126.
        assert_eq!(signed_bv_literal_value(&lit(1 << 126, 127), 127), Some(-(1i128 << 126)));
        // A literal of another width, a zero width and a non-literal are not values here.
        assert_eq!(signed_bv_literal_value(&lit(10, 64), 128), None);
        assert_eq!(signed_bv_literal_value(&lit(0, 0), 0), None);
        assert_eq!(signed_bv_literal_value(&Formula::Int(10), 128), None);
    }

    #[test]
    fn sign_test_shape_is_pinned() {
        let a = bvvar("a", 8);
        let b = bvvar("b", 8);
        let msb = lit(128, 8);
        let nn = |v: Formula| Formula::BvULt(Box::new(v), Box::new(msb.clone()), 8);
        let not = |f: Formula| Formula::Not(Box::new(f));
        let differ = |x: Formula, y: Formula| {
            Formula::Or(vec![
                Formula::And(vec![x.clone(), not(y.clone())]),
                Formula::And(vec![not(x), y]),
            ])
        };
        let sum = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 8);
        let expected = Formula::And(vec![
            not(differ(nn(a.clone()), nn(b.clone()))),
            differ(nn(sum), nn(a.clone())),
        ]);
        assert_eq!(
            signed_bv_addsub_overflow_sign_test(a.clone(), b.clone(), true, 8),
            Some(expected)
        );
        assert_eq!(signed_bv_addsub_overflow_sign_test(a.clone(), b.clone(), true, 0), None);
        assert_eq!(signed_bv_addsub_overflow_sign_test(a, b, false, 129), None);
    }

    #[test]
    fn the_asserted_predicate_is_found_and_a_mention_is_not() {
        let a = bvvar("a", 128);
        let b = bvvar("b", 128);
        let pred = signed_bv_addsub_overflow_sign_test(a.clone(), b.clone(), true, 128).unwrap();
        let guards = vec![
            Formula::BvSLe(Box::new(lit(0, 128)), Box::new(a.clone()), 128),
            Formula::BvSLt(Box::new(a.clone()), Box::new(lit(10, 128)), 128),
        ];
        let mut row = guards.clone();
        row.push(pred.clone());
        let row = Formula::And(row);
        let found = asserted_signed_bv_addsub_overflows(&flatten(&row));
        assert_eq!(
            found,
            vec![SignedBvAddSubOverflow { lhs: &a, rhs: &b, is_add: true, width: 128 }]
        );

        // The postcondition row the confirmer dumped: the add sits inside an
        // `ensures` equation. No overflow predicate is asserted.
        let ensures = Formula::Eq(
            Box::new(bvvar("_0", 128)),
            Box::new(Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 128)),
        );
        let mut lie = guards.clone();
        lie.push(ensures);
        assert!(asserted_signed_bv_addsub_overflows(&flatten(&Formula::And(lie))).is_empty());

        // Only the result-sign-flip half: not the overflow predicate.
        let Formula::And(parts) = &pred else { unreachable!() };
        let mut half = guards.clone();
        half.push(parts[1].clone());
        assert!(asserted_signed_bv_addsub_overflows(&flatten(&Formula::And(half))).is_empty());

        // The whole predicate as one disjunct: not asserted.
        let mut disjunct = guards;
        disjunct.push(Formula::Or(vec![pred, Formula::Bool(true)]));
        assert!(asserted_signed_bv_addsub_overflows(&flatten(&Formula::And(disjunct))).is_empty());
    }

    #[test]
    fn operand_interval_decodes_and_matches_widths() {
        let a = bvvar("a", 64);
        // The machine lane's i64 type-range atoms plus a guard `0 <= a < 10`.
        let atoms = [
            Formula::BvSLe(Box::new(lit(1 << 63, 64)), Box::new(a.clone()), 64),
            Formula::BvSLe(Box::new(a.clone()), Box::new(lit((1 << 63) - 1, 64)), 64),
            Formula::BvSLe(Box::new(lit(0, 64)), Box::new(a.clone()), 64),
            Formula::BvSLt(Box::new(a.clone()), Box::new(lit(10, 64)), 64),
        ];
        let refs: Vec<&Formula> = atoms.iter().collect();
        assert_eq!(signed_bv_operand_interval(&refs, &a, 64), Some((0, 9)));
        // Only the type-range atoms: the full i64 range, not an empty one.
        assert_eq!(
            signed_bv_operand_interval(&refs[..2], &a, 64),
            Some((i64::MIN as i128, i64::MAX as i128))
        );

        // A 64→128 sign extension: inherent i64 range, narrowed by a bound on the
        // 64-bit source and by one on the 128-bit extension; an atom whose width
        // does not match its layer is ignored.
        let sx = Formula::BvSignExt(Box::new(a.clone()), 64);
        let atoms = [
            Formula::BvSLe(Box::new(lit(-5, 64)), Box::new(a.clone()), 64),
            Formula::BvSLt(Box::new(sx.clone()), Box::new(lit(7, 128)), 128),
            Formula::BvSLt(Box::new(a.clone()), Box::new(lit(3, 128)), 128),
        ];
        let refs: Vec<&Formula> = atoms.iter().collect();
        assert_eq!(signed_bv_operand_interval(&refs, &sx, 128), Some((-5, 6)));
        assert_eq!(
            signed_bv_operand_interval(&[], &sx, 128),
            Some((i64::MIN as i128, i64::MAX as i128))
        );
        // Ill-sorted at the claimed width.
        assert_eq!(signed_bv_operand_interval(&[], &a, 128), None);
        assert_eq!(signed_bv_operand_interval(&[], &Formula::Var("i".into(), Sort::Int), 64), None);
    }
}
