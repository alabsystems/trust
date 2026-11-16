// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Unit tests of the reconstruction-scale gates (`reconstruction_scale.rs`).

use super::super::{linear_term_to_kernel, linear_term_to_smt};
use super::*;

fn var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn scaled(k: i128, t: Formula) -> Formula {
    Formula::Mul(Box::new(Formula::Int(k)), Box::new(t))
}

fn add(a: Formula, b: Formula) -> Formula {
    Formula::Add(Box::new(a), Box::new(b))
}

fn sub(a: Formula, b: Formula) -> Formula {
    Formula::Sub(Box::new(a), Box::new(b))
}

fn scale_of(t: &Formula) -> u128 {
    atom_scale(&Atom::Le(t, &Formula::Int(0)))
}

#[test]
fn scales_of_the_measured_shapes() {
    let x = var("x");
    assert_eq!(scale_of(&x), 1);
    // A closed atom is neutral in the product.
    assert_eq!(scale_of(&Formula::Int(1 << 63)), 1);
    // a01's capacity atom.
    assert_eq!(scale_of(&scaled(1 << 30, x.clone())), 1 << 30);
    assert_eq!(scale_of(&scaled(-(1 << 13), x.clone())), 1 << 13);
    // A nested scaling multiplies.
    assert_eq!(scale_of(&scaled(64, scaled(128, x.clone()))), 1 << 13);
    // var × var is one product atom, coefficient 1.
    assert_eq!(scale_of(&Formula::Mul(Box::new(x.clone()), Box::new(var("y")))), 1);
    // The guarded-subtraction atom `x - 1` (the shape round 1's first census
    // found declined as `u128::MAX`).
    assert_eq!(scale_of(&sub(x.clone(), Formula::Int(1))), 1);
    // Both sides count: `4093·a ≤ g` is 4093.
    let (a, g) = (var("a"), var("g"));
    let lhs = scaled(4093, a.clone());
    assert_eq!(atom_scale(&Atom::Le(&lhs, &g)), 4093);
    assert_eq!(atom_scale(&Atom::Lt(&g, &lhs)), 4093);
}

/// Every term the pool's renderers accept gets a FINITE scale: the gate's
/// `u128::MAX` fallback must be unreachable from a renderable atom, or it
/// silently withholds `Certified` from rows the ay lane used to certify.
#[test]
fn every_renderable_term_has_a_finite_scale() {
    let leaves = vec![var("x"), var("y"), Formula::Int(3), Formula::UInt(7), Formula::Int(-2)];
    let mut terms = leaves.clone();
    for a in &leaves {
        for b in &leaves {
            let (a, b) = (Box::new(a.clone()), Box::new(b.clone()));
            terms.push(Formula::Add(a.clone(), b.clone()));
            terms.push(Formula::Sub(a.clone(), b.clone()));
            terms.push(Formula::Mul(a.clone(), b.clone()));
            terms.push(Formula::Neg(a.clone()));
        }
    }
    let depth_one = terms.clone();
    for a in &depth_one {
        for b in &depth_one {
            let (a, b) = (Box::new(a.clone()), Box::new(b.clone()));
            terms.push(Formula::Add(a.clone(), b.clone()));
            terms.push(Formula::Sub(a.clone(), b.clone()));
            terms.push(Formula::Mul(a, b));
        }
    }
    let zero = Formula::Int(0);
    let mut renderable = 0;
    for t in &terms {
        if linear_term_to_kernel(t).is_some() && linear_term_to_smt(t).is_some() {
            renderable += 1;
            assert_ne!(atom_scale(&Atom::Le(t, &zero)), u128::MAX, "renderable, no form: {t:?}");
        }
    }
    assert!(renderable > 100, "the enumeration must reach the renderers: {renderable}");
}

#[test]
fn the_pool_scale_is_a_product_and_merges_like_terms() {
    let (a, b, g1, g2) = (var("a"), var("b"), var("g1"), var("g2"));
    let k = Formula::Int(1 << 60);
    // b45's guards: `a·4093 = g1 < K`, `b·4091 = g2 < K` — each at most 2^12,
    // so round 1's maximum (4093) let them through; their product does not.
    let eq1 = scaled(4093, a.clone());
    let eq2 = scaled(4091, b.clone());
    let atoms = [Atom::Le(&eq1, &g1), Atom::Lt(&g1, &k), Atom::Le(&eq2, &g2), Atom::Lt(&g2, &k)];
    assert_eq!(pool_coefficient_scale(&atoms), 4093 * 4091);
    assert!(pool_coefficient_scale(&atoms) > AY_RECONSTRUCTION_MAX_COEFFICIENT);
    // b03's chain `3·5·7·11·13`.
    let chain: Vec<Formula> =
        [3, 5, 7, 11, 13].iter().map(|&c| scaled(c, var(&format!("x{c}")))).collect();
    let chain_atoms: Vec<Atom<'_>> = chain.iter().map(|t| Atom::Le(t, &k)).collect();
    assert_eq!(pool_coefficient_scale(&chain_atoms), 15015);
    // b49's doubling spelling `x₁ = x₀ + x₀` is a coefficient of 2, twenty
    // times over: `x + x` merges, where round 1's per-term reading saw 1.
    let x: Vec<Formula> = (0..=20).map(|i| var(&format!("x{i}"))).collect();
    let doubled: Vec<Formula> = (0..20).map(|i| add(x[i].clone(), x[i].clone())).collect();
    let doubling: Vec<Atom<'_>> = (0..20).map(|i| Atom::Le(&x[i + 1], &doubled[i])).collect();
    assert_eq!(pool_coefficient_scale(&doubling), 1 << 20);
    // Closed atoms and unit rows are neutral.
    let five = Formula::Int(5);
    assert_eq!(pool_coefficient_scale(&[Atom::Le(&five, &k), Atom::Lt(&a, &b)]), 1);
    // `a - a` cancels to a closed atom.
    let cancel = sub(scaled(7, a.clone()), scaled(7, a.clone()));
    assert_eq!(pool_coefficient_scale(&[Atom::Le(&cancel, &k)]), 1);
}

/// ay's refutation of b45's capacity row, VERBATIM (captured from
/// `AyProofResult::Unsat { proof }`, 2026-09-26): its Farkas step carries
/// `4093/4091`, so clean_auto's integer multipliers are `4093·4091`.
const B45_FARKAS_STEP: &str = "(assume t0 (<= a__slice_len _5))
(step t14.n (cl (not (<= 9223372036854775808 (* _17 1))) (<= 9223372036854775808 _17)) :rule la_generic :args (1 1))
(step t15 (cl (not (< _4 _7)) (not (<= a__slice_len _5)) (not (<= _7 1152921504606846976)) (not (<= _14 1152921504606846976)) (not (< _11 _14)) (not (<= v1 _4)) (not (<= b__slice_len _12)) (not (<= v2 _11)) (not (<= 9223372036854775808 _17)) (not (<= v3 (+ _18 _19))) (not (<= (* _5 4093) v1)) (not (<= (* _12 4091) v2)) (not (<= _18 a__slice_len)) (not (<= _17 v3)) (not (<= _19 b__slice_len))) :rule la_generic :args (1 4093 1 (/ 4093.0 4091.0) (/ 4093.0 4091.0) 1 4093 (/ 4093.0 4091.0) 4093 4093 1 (/ 4093.0 4091.0) 4093 4093 4093))
(step t16 (cl) :rule th_resolution :premises (t15 t0))";

#[test]
fn the_b45_certificate_is_read_as_the_multipliers_clean_auto_replays() {
    let estimate = alethe_closeout_estimate(B45_FARKAS_STEP).expect("parses");
    assert_eq!(estimate.farkas_steps, 2);
    assert_eq!(estimate.opaque_steps, 0);
    // LCM 4091: the unit coefficients become 4091, the 4093s 4093·4091, the
    // 4093/4091s 4093; every literal has two leaves, or its symbols plus two.
    assert!(estimate.worst_leaves > 4093 * 4091, "{estimate:?}");
    assert!(estimate.worst_leaves > AY_RECONSTRUCTION_MAX_CLOSEOUT_LEAVES);
}

#[test]
fn a_unit_certificate_is_its_leaves() {
    let unit = "(step t1 (cl (not (<= x 5)) (not (<= 7 x))) :rule la_generic :args (1 1))";
    let estimate = alethe_closeout_estimate(unit).unwrap();
    // Each literal: two printed leaves, one symbol + 2 = 3 by the floor.
    assert_eq!(estimate.worst_leaves, 6);
    // `lia_generic` without `:args` is all-unit, as clean_auto reads it.
    let lia = "(step t1 (cl (not (<= x 5)) (not (<= 7 x))) :rule lia_generic)";
    assert_eq!(alethe_closeout_estimate(lia).unwrap().worst_leaves, 6);
    // A scaled one: `3·(x ≤ 5) + (16 ≤ x+x+x)`.
    let weighted =
        "(step t1 (cl (not (<= x 5)) (not (<= 16 (+ x x x)))) :rule la_generic :args (3 1))";
    assert_eq!(alethe_closeout_estimate(weighted).unwrap().worst_leaves, 3 * 3 + 4);
}

#[test]
fn unreadable_certificates_are_unbounded_not_small() {
    // Coefficient count disagrees with the clause.
    let short = "(step t1 (cl (not (<= x 5)) (not (<= 7 x))) :rule la_generic :args (1))";
    assert_eq!(alethe_closeout_estimate(short).unwrap().worst_leaves, u128::MAX);
    // A coefficient that is not a numeral.
    let odd = "(step t1 (cl (not (<= x 5)) (not (<= 7 x))) :rule la_generic :args (1 k))";
    assert_eq!(alethe_closeout_estimate(odd).unwrap().worst_leaves, u128::MAX);
    // A numeral past u128.
    let huge = format!(
        "(step t1 (cl (not (<= x 5)) (not (<= 7 x))) :rule la_generic :args (1 {}))",
        "9".repeat(60)
    );
    assert_eq!(alethe_closeout_estimate(&huge).unwrap().worst_leaves, u128::MAX);
    // No clause.
    let bare = "(step t1 :rule la_generic :args (1 1))";
    assert_eq!(alethe_closeout_estimate(bare).unwrap().worst_leaves, u128::MAX);
    // Unbalanced text does not parse at all.
    assert_eq!(alethe_closeout_estimate("(step t1 (cl"), None);
    // `hole` steps are counted, not sized.
    let hole = "(step t1 (cl (not (<= x 5)) (not (<= 7 x))) :rule hole)";
    let estimate = alethe_closeout_estimate(hole).unwrap();
    assert_eq!((estimate.opaque_steps, estimate.farkas_steps), (1, 0));
}

#[test]
fn let_and_named_terms_are_sized_by_what_they_stand_for() {
    let with_let = "(step t1 (cl (not (<= (let ((s (+ a b c d))) (+ s s)) 5)) (not (<= 7 a))) \
                    :rule la_generic :args (2 1))";
    // `(+ s s)` is eight leaves, plus the constant: 9, times 2; then 3.
    assert_eq!(alethe_closeout_estimate(with_let).unwrap().worst_leaves, 2 * 9 + 3);
    let named = "(assume a0 (! (+ a b c d e f) :named @p))
(step t1 (cl (not (<= @p 5)) (not (<= 7 a))) :rule la_generic :args (1 1))";
    assert_eq!(alethe_closeout_estimate(named).unwrap().worst_leaves, 7 + 3);
}

#[test]
fn coefficients_parse_in_every_rendered_spelling() {
    let atom = |s: &'static str| Sx::Atom(s);
    assert_eq!(parse_coefficient(&atom("3")), Some((3, 1)));
    assert_eq!(parse_coefficient(&atom("-3")), Some((3, 1)));
    assert_eq!(parse_coefficient(&atom("4093.0")), Some((4093, 1)));
    assert_eq!(parse_coefficient(&atom("1.5")), Some((3, 2)));
    let ratio = Sx::List(vec![atom("/"), atom("4093.0"), atom("4091.0")]);
    assert_eq!(parse_coefficient(&ratio), Some((4093, 4091)));
    let neg = Sx::List(vec![atom("-"), atom("2")]);
    assert_eq!(parse_coefficient(&neg), Some((2, 1)));
    assert_eq!(parse_coefficient(&Sx::List(vec![atom("/"), atom("1"), atom("0")])), None);
    assert_eq!(parse_coefficient(&atom("x")), None);
    assert_eq!(parse_coefficient(&atom(".5")), None);
}
