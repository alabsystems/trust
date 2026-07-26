// trust-strengthen/abstract_domains/tests.rs: Tests for abstract domain hierarchy
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

// ===== IntervalDomain tests =====

#[test]
fn test_interval_new_valid() {
    let i = IntervalDomain::new(0, 10);
    assert_eq!(i.low(), Some(0));
    assert_eq!(i.high(), Some(10));
}

#[test]
fn test_interval_new_empty() {
    let i = IntervalDomain::new(10, 0);
    assert!(i.is_bottom());
}

#[test]
fn test_interval_constant() {
    let i = IntervalDomain::constant(42);
    assert_eq!(i.low(), Some(42));
    assert_eq!(i.high(), Some(42));
    assert!(i.contains(42));
    assert!(!i.contains(43));
}

#[test]
fn test_interval_unbounded() {
    let i = IntervalDomain::at_least(0);
    assert!(i.contains(0));
    assert!(i.contains(1_000_000));
    assert!(!i.contains(-1));

    let j = IntervalDomain::at_most(100);
    assert!(j.contains(100));
    assert!(j.contains(-1000));
    assert!(!j.contains(101));
}

#[test]
fn test_interval_join() {
    let a = IntervalDomain::new(0, 5);
    let b = IntervalDomain::new(3, 10);
    let j = a.join(&b);
    assert_eq!(j.low(), Some(0));
    assert_eq!(j.high(), Some(10));
}

#[test]
fn test_interval_join_with_bottom() {
    let a = IntervalDomain::Bottom;
    let b = IntervalDomain::new(3, 10);
    assert_eq!(a.join(&b), b);
    assert_eq!(b.join(&a), b);
}

#[test]
fn test_interval_join_unbounded() {
    let a = IntervalDomain::at_least(0);
    let b = IntervalDomain::new(3, 10);
    let j = a.join(&b);
    assert_eq!(j.low(), Some(0));
    assert!(j.high().is_none()); // Unbounded
}

#[test]
fn test_interval_meet() {
    let a = IntervalDomain::new(0, 10);
    let b = IntervalDomain::new(5, 15);
    let m = a.meet(&b);
    assert_eq!(m.low(), Some(5));
    assert_eq!(m.high(), Some(10));
}

#[test]
fn test_interval_meet_disjoint() {
    let a = IntervalDomain::new(0, 3);
    let b = IntervalDomain::new(5, 10);
    let m = a.meet(&b);
    assert!(m.is_bottom());
}

#[test]
fn test_interval_widen_default_thresholds() {
    let a = IntervalDomain::new(0, 5);
    let b = IntervalDomain::new(0, 6);
    let w = a.widen(&b);
    // Upper bound grew: should jump to next threshold >= 6
    // DEFAULT_THRESHOLDS includes 127
    assert_eq!(w.low(), Some(0));
    // Should be 127 (next threshold >= 6)
    assert_eq!(w.high(), Some(127));
}

#[test]
fn test_interval_widen_lower_decreases() {
    let a = IntervalDomain::new(5, 10);
    let b = IntervalDomain::new(4, 10);
    let w = a.widen(&b);
    // Lower bound decreased: jump to next threshold <= 4
    assert_eq!(w.high(), Some(10));
    assert_eq!(w.low(), Some(2)); // next threshold <= 4 is 2
}

#[test]
fn test_interval_widen_stable() {
    let a = IntervalDomain::new(0, 10);
    let b = IntervalDomain::new(0, 10);
    let w = a.widen(&b);
    assert_eq!(w, a);
}

#[test]
fn test_interval_narrow() {
    let a = IntervalDomain::Interval { low: Bound::Unbounded, high: Bound::Unbounded };
    let b = IntervalDomain::new(0, 100);
    let n = a.narrow(&b);
    assert_eq!(n.low(), Some(0));
    assert_eq!(n.high(), Some(100));
}

#[test]
fn test_interval_narrow_partial() {
    let a = IntervalDomain::Interval { low: Bound::Finite(0), high: Bound::Unbounded };
    let b = IntervalDomain::new(5, 50);
    let n = a.narrow(&b);
    // Lower bound was finite, keep it; upper was unbounded, narrow to 50
    assert_eq!(n.low(), Some(0));
    assert_eq!(n.high(), Some(50));
}

#[test]
fn test_interval_top_bottom() {
    assert!(IntervalDomain::top().is_top());
    assert!(IntervalDomain::bottom().is_bottom());
    assert!(!IntervalDomain::top().is_bottom());
    assert!(!IntervalDomain::bottom().is_top());
}

#[test]
fn test_interval_subset() {
    let a = IntervalDomain::new(2, 8);
    let b = IntervalDomain::new(0, 10);
    assert!(a.is_subset_of(&b));
    assert!(!b.is_subset_of(&a));
}

#[test]
fn test_interval_add() {
    let a = IntervalDomain::new(1, 5);
    let b = IntervalDomain::new(2, 3);
    let sum = a.add(&b);
    assert_eq!(sum.low(), Some(3));
    assert_eq!(sum.high(), Some(8));
}

#[test]
fn test_interval_sub() {
    let a = IntervalDomain::new(5, 10);
    let b = IntervalDomain::new(1, 3);
    let diff = a.sub(&b);
    assert_eq!(diff.low(), Some(2));
    assert_eq!(diff.high(), Some(9));
}

#[test]
fn test_interval_mul() {
    let a = IntervalDomain::new(-2, 3);
    let b = IntervalDomain::new(1, 4);
    let prod = a.mul(&b);
    assert_eq!(prod.low(), Some(-8));
    assert_eq!(prod.high(), Some(12));
}

#[test]
fn test_interval_display() {
    assert_eq!(format!("{}", IntervalDomain::new(0, 10)), "[0, 10]");
    assert_eq!(format!("{}", IntervalDomain::Bottom), "bottom");
    assert_eq!(format!("{}", IntervalDomain::at_least(0)), "[0, +inf]");
    assert_eq!(format!("{}", IntervalDomain::at_most(10)), "[-inf, 10]");
}

// ===== OctagonDomain tests =====

#[test]
fn test_octagon_new_is_top() {
    let oct = OctagonDomain::new(vec!["x".into(), "y".into()]);
    assert!(!oct.is_bottom());
    // After creation with no constraints, non-diagonal entries are None
    // so it's top
    assert!(oct.is_top());
}

#[test]
fn test_octagon_add_difference_constraint() {
    let mut oct = OctagonDomain::new(vec!["x".into(), "y".into()]);
    oct.add_difference_constraint("x", "y", 5);
    assert!(oct.check_difference("x", "y", 5));
    assert!(oct.check_difference("x", "y", 10)); // x - y <= 5 implies x - y <= 10
    assert!(!oct.check_difference("x", "y", 4)); // Cannot prove x - y <= 4
}

#[test]
fn test_octagon_upper_lower_bounds() {
    let mut oct = OctagonDomain::new(vec!["x".into()]);
    oct.add_upper_bound("x", 10);
    oct.add_lower_bound("x", 2);
    assert!(oct.check_upper_bound("x", 10));
    assert!(oct.check_lower_bound("x", 2));
    assert!(!oct.check_upper_bound("x", 9));
    assert!(!oct.check_lower_bound("x", 3));
}

#[test]
fn test_octagon_get_interval() {
    let mut oct = OctagonDomain::new(vec!["x".into(), "y".into()]);
    oct.add_upper_bound("x", 10);
    oct.add_lower_bound("x", 0);
    let interval = oct.get_interval("x");
    assert_eq!(interval.low(), Some(0));
    assert_eq!(interval.high(), Some(10));
}

#[test]
fn test_octagon_floyd_warshall_transitivity() {
    let mut oct = OctagonDomain::new(vec!["x".into(), "y".into(), "z".into()]);
    // x - y <= 3, y - z <= 4 => x - z <= 7
    oct.add_difference_constraint("x", "y", 3);
    oct.add_difference_constraint("y", "z", 4);
    assert!(oct.check_difference("x", "z", 7));
}

#[test]
fn test_octagon_bottom_from_contradiction() {
    let mut oct = OctagonDomain::new(vec!["x".into()]);
    oct.add_upper_bound("x", 5);
    oct.add_lower_bound("x", 10);
    assert!(oct.is_bottom());
}

#[test]
fn test_octagon_join() {
    let mut a = OctagonDomain::new(vec!["x".into()]);
    a.add_upper_bound("x", 5);
    a.add_lower_bound("x", 0);

    let mut b = OctagonDomain::new(vec!["x".into()]);
    b.add_upper_bound("x", 10);
    b.add_lower_bound("x", 3);

    let j = a.join(&b);
    // Join takes max of bounds: upper = max(5, 10) = 10, lower = max(0, 3) => loosest
    assert!(j.check_upper_bound("x", 10));
    assert!(j.check_lower_bound("x", 0));
}

#[test]
fn test_octagon_join_with_bottom() {
    let a = OctagonDomain::new_bottom(vec!["x".into()]);
    let mut b = OctagonDomain::new(vec!["x".into()]);
    b.add_upper_bound("x", 10);

    let j = a.join(&b);
    assert!(j.check_upper_bound("x", 10));
}

#[test]
fn test_octagon_meet() {
    let mut a = OctagonDomain::new(vec!["x".into()]);
    a.add_upper_bound("x", 10);
    a.add_lower_bound("x", 0);

    let mut b = OctagonDomain::new(vec!["x".into()]);
    b.add_upper_bound("x", 7);
    b.add_lower_bound("x", 3);

    let m = a.meet(&b);
    assert!(m.check_upper_bound("x", 7));
    assert!(m.check_lower_bound("x", 3));
}

#[test]
fn test_octagon_widen() {
    let mut a = OctagonDomain::new(vec!["x".into()]);
    a.add_upper_bound("x", 5);
    a.add_lower_bound("x", 0);

    let mut b = OctagonDomain::new(vec!["x".into()]);
    b.add_upper_bound("x", 6);
    b.add_lower_bound("x", 0);

    let w = a.widen(&b);
    // Upper bound increased (5 -> 6): widen drops it to unconstrained
    // Lower bound stable: keep
    assert!(w.check_lower_bound("x", 0));
    assert!(!w.check_upper_bound("x", 100)); // Upper bound was dropped
}

#[test]
fn test_octagon_subset() {
    let mut a = OctagonDomain::new(vec!["x".into()]);
    a.add_upper_bound("x", 5);
    a.add_lower_bound("x", 2);

    let mut b = OctagonDomain::new(vec!["x".into()]);
    b.add_upper_bound("x", 10);
    b.add_lower_bound("x", 0);

    assert!(a.is_subset_of(&b));
    assert!(!b.is_subset_of(&a));
}

#[test]
fn test_octagon_index_out_of_bounds_vc() {
    // Scenario: i < len, which means i - len <= -1
    let mut oct = OctagonDomain::new(vec!["i".into(), "len".into()]);
    oct.add_difference_constraint("i", "len", -1);
    // This should prove that i - len <= -1, i.e., i < len
    assert!(oct.check_difference("i", "len", -1));
}

// ===== CongruenceDomain tests =====

#[test]
fn test_congruence_constant() {
    let c = CongruenceValue::constant(42);
    assert!(c.contains(42));
    assert!(!c.contains(43));
    assert!(c.is_constant());
}

#[test]
fn test_congruence_modular() {
    let c = CongruenceValue::new(4, 1);
    assert!(c.contains(1));
    assert!(c.contains(5));
    assert!(c.contains(9));
    assert!(!c.contains(2));
    assert!(!c.contains(4));
}

#[test]
fn test_congruence_top() {
    let t = CongruenceValue::top_value();
    assert!(t.is_top());
    assert!(t.contains(0));
    assert!(t.contains(999));
}

#[test]
fn test_congruence_domain_add() {
    let mut d = CongruenceDomain::new();
    d.set_var("a", CongruenceValue::new(4, 0)); // a === 0 (mod 4)
    d.set_var("b", CongruenceValue::new(4, 2)); // b === 2 (mod 4)
    d.transfer_add("c", "a", "b");
    // c === (0+2) (mod gcd(4,4)) = 2 (mod 4)
    let c = d.get_var("c");
    assert!(c.contains(2));
    assert!(c.contains(6));
    assert!(!c.contains(3));
}

#[test]
fn test_congruence_domain_mul_const() {
    let mut d = CongruenceDomain::new();
    d.set_var("x", CongruenceValue::new(3, 1)); // x === 1 (mod 3)
    d.transfer_mul_const("y", "x", 2);
    // y === (1*2) (mod 3*2) = 2 (mod 6)
    let y = d.get_var("y");
    assert!(y.contains(2));
    assert!(y.contains(8));
    assert!(!y.contains(3));
}

#[test]
fn test_congruence_domain_mod_const() {
    let mut d = CongruenceDomain::new();
    d.set_var("x", CongruenceValue::new(6, 4)); // x === 4 (mod 6)
    d.transfer_mod_const("y", "x", 3);
    // gcd(6, 3) = 3, residue = 4 % 3 = 1
    // y === 1 (mod 3)
    let y = d.get_var("y");
    assert!(y.contains(1));
    assert!(y.contains(4));
    assert!(!y.contains(2));
}

#[test]
fn test_congruence_domain_shr_const() {
    let mut d = CongruenceDomain::new();
    d.set_var("x", CongruenceValue::new(8, 0)); // x === 0 (mod 8)
    d.transfer_shr_const("y", "x", 2);
    // 8 / 4 = 2, residue = 0 >> 2 = 0
    // y === 0 (mod 2)
    let y = d.get_var("y");
    assert!(y.contains(0));
    assert!(y.contains(2));
    assert!(!y.contains(1));
}

#[test]
fn test_congruence_shift_amount_vc() {
    // Scenario: shift amount s, need to prove s < 32
    // If we know s === 0 (mod 1) and s is in [0, 31] from interval, can discharge
    let mut d = CongruenceDomain::new();
    d.set_var("s", CongruenceValue::constant(4)); // s is exactly 4
    assert!(d.check_less_than("s", 32)); // 4 < 32
    assert!(!d.check_less_than("s", 4)); // not 4 < 4
}

#[test]
fn test_congruence_join() {
    let a = CongruenceValue::new(4, 0); // x === 0 (mod 4)
    let b = CongruenceValue::new(4, 2); // x === 2 (mod 4)
    let j = congruence_join(a, b);
    // gcd(4, 4, |0-2|) = gcd(4, 2) = 2
    // j should be x === 0 (mod 2)
    assert!(j.contains(0));
    assert!(j.contains(2));
    assert!(j.contains(4));
    assert!(!j.contains(1));
}

#[test]
fn test_congruence_meet() {
    let a = CongruenceValue::new(4, 2); // x === 2 (mod 4)
    let b = CongruenceValue::new(6, 2); // x === 2 (mod 6)
    let m = congruence_meet(a, b);
    // lcm(4, 6) = 12, and residues compatible (both 2)
    // m should be x === 2 (mod 12)
    assert!(m.contains(2));
    assert!(m.contains(14));
    assert!(!m.contains(6));
}

#[test]
fn test_congruence_meet_incompatible() {
    let a = CongruenceValue::new(4, 0); // x === 0 (mod 4)
    let b = CongruenceValue::new(4, 1); // x === 1 (mod 4)
    let m = congruence_meet(a, b);
    assert!(matches!(m, CongruenceValue::Bottom));
}

#[test]
fn test_congruence_domain_join() {
    let mut a = CongruenceDomain::new();
    a.set_var("x", CongruenceValue::new(4, 0));
    let mut b = CongruenceDomain::new();
    b.set_var("x", CongruenceValue::new(4, 2));
    let j = a.join(&b);
    let x = j.get_var("x");
    assert!(x.contains(0));
    assert!(x.contains(2));
}

#[test]
fn test_congruence_domain_meet() {
    let mut a = CongruenceDomain::new();
    a.set_var("x", CongruenceValue::new(4, 2));
    let mut b = CongruenceDomain::new();
    b.set_var("x", CongruenceValue::new(6, 2));
    let m = a.meet(&b);
    let x = m.get_var("x");
    assert!(x.contains(2));
    assert!(x.contains(14));
}

#[test]
fn test_congruence_domain_bottom() {
    let d = CongruenceDomain::new_bottom();
    assert!(d.is_bottom());
    let x = d.get_var("x");
    assert!(matches!(x, CongruenceValue::Bottom));
}

#[test]
fn test_congruence_domain_top() {
    let d = CongruenceDomain::new();
    assert!(d.is_top());
}

#[test]
fn test_congruence_subset() {
    // x === 0 (mod 8) is subset of x === 0 (mod 4)
    let a = CongruenceValue::new(8, 0);
    let b = CongruenceValue::new(4, 0);
    assert!(congruence_subset(a, b));
    assert!(!congruence_subset(b, a));
}

// ===== ReducedProduct tests =====

#[test]
fn test_reduced_product_join() {
    let a = ReducedProduct::new(IntervalDomain::new(0, 5), IntervalDomain::new(10, 20));
    let b = ReducedProduct::new(IntervalDomain::new(3, 8), IntervalDomain::new(15, 25));
    let j = a.join(&b);
    assert_eq!(j.first.low(), Some(0));
    assert_eq!(j.first.high(), Some(8));
    assert_eq!(j.second.low(), Some(10));
    assert_eq!(j.second.high(), Some(25));
}

#[test]
fn test_reduced_product_meet() {
    let a = ReducedProduct::new(IntervalDomain::new(0, 10), IntervalDomain::new(5, 15));
    let b = ReducedProduct::new(IntervalDomain::new(3, 7), IntervalDomain::new(8, 20));
    let m = a.meet(&b);
    assert_eq!(m.first.low(), Some(3));
    assert_eq!(m.first.high(), Some(7));
    assert_eq!(m.second.low(), Some(8));
    assert_eq!(m.second.high(), Some(15));
}

#[test]
fn test_reduced_product_bottom_propagates() {
    let a = ReducedProduct::new(IntervalDomain::Bottom, IntervalDomain::new(0, 10));
    assert!(a.is_bottom());
}

#[test]
fn test_reduced_product_top() {
    let a = ReducedProduct::new(IntervalDomain::top(), IntervalDomain::top());
    assert!(a.is_top());
}

#[test]
fn test_reduced_product_subset() {
    let a = ReducedProduct::new(IntervalDomain::new(2, 5), IntervalDomain::new(3, 7));
    let b = ReducedProduct::new(IntervalDomain::new(0, 10), IntervalDomain::new(0, 10));
    assert!(a.is_subset_of(&b));
    assert!(!b.is_subset_of(&a));
}

// ===== Reduction tests =====

#[test]
fn test_reduce_interval_octagon() {
    let mut interval = IntervalDomain::new(0, 100);
    let mut oct = OctagonDomain::new(vec!["x".into()]);
    oct.add_upper_bound("x", 50);

    reduce_interval_octagon(&mut interval, &mut oct, "x");

    // Interval should be tightened to [0, 50]
    assert_eq!(interval.low(), Some(0));
    assert_eq!(interval.high(), Some(50));
}

#[test]
fn test_reduce_interval_congruence() {
    let mut interval = IntervalDomain::new(3, 10);
    let cong = CongruenceValue::new(4, 0); // x === 0 (mod 4)

    reduce_interval_congruence(&mut interval, &cong);

    // Smallest multiple of 4 >= 3 is 4, largest <= 10 is 8
    assert_eq!(interval.low(), Some(4));
    assert_eq!(interval.high(), Some(8));
}

#[test]
fn test_reduce_interval_congruence_exact() {
    let mut interval = IntervalDomain::new(0, 100);
    let cong = CongruenceValue::constant(42);

    reduce_interval_congruence(&mut interval, &cong);

    // Should be exactly [42, 42]
    assert_eq!(interval.low(), Some(42));
    assert_eq!(interval.high(), Some(42));
}

#[test]
fn test_reduce_interval_congruence_empty() {
    let mut interval = IntervalDomain::new(1, 3);
    let cong = CongruenceValue::new(4, 0); // x === 0 (mod 4)

    reduce_interval_congruence(&mut interval, &cong);

    // No multiple of 4 in [1, 3]
    assert!(interval.is_bottom());
}

#[test]
fn test_triple_product() {
    // Test the triple product: Interval x Octagon x Congruence
    type TripleProduct =
        ReducedProduct<ReducedProduct<IntervalDomain, OctagonDomain>, CongruenceDomain>;

    let a = TripleProduct::new(
        ReducedProduct::new(IntervalDomain::new(0, 10), OctagonDomain::new(vec!["x".into()])),
        CongruenceDomain::new(),
    );
    let b = TripleProduct::new(
        ReducedProduct::new(IntervalDomain::new(5, 15), OctagonDomain::new(vec!["x".into()])),
        CongruenceDomain::new(),
    );

    let j = a.join(&b);
    assert_eq!(j.first.first.low(), Some(0));
    assert_eq!(j.first.first.high(), Some(15));
}

#[test]
fn test_octagon_discharges_vc_interval_cannot() {
    // Scenario: proving i < len when we only know i - len <= -1
    // Interval alone: i in [0, 100], len in [0, 100] -- cannot prove i < len
    // Octagon: has the relational constraint i - len <= -1, PROVES i < len

    let i_interval = IntervalDomain::new(0, 100);
    let len_interval = IntervalDomain::new(0, 100);
    // Interval alone cannot prove i < len
    // (both ranges overlap -- we need relational info)
    assert!(
        !i_interval.is_subset_of(&IntervalDomain::new(0, 99))
            || !len_interval.is_subset_of(&IntervalDomain::at_least(1))
    );

    // Octagon CAN prove it:
    let mut oct = OctagonDomain::new(vec!["i".into(), "len".into()]);
    oct.add_difference_constraint("i", "len", -1); // i - len <= -1 means i < len
    assert!(oct.check_difference("i", "len", -1));
}

#[test]
fn test_congruence_discharges_shift_vc() {
    // Scenario: proving shift amount s < 32
    // If s is computed as (x & 0x1F), we know s === s (mod 32) and s in [0, 31]
    // Congruence tracks that s is a constant or in a known modular class

    let mut cong = CongruenceDomain::new();
    cong.set_var("s", CongruenceValue::constant(7)); // s is known to be 7
    assert!(cong.check_less_than("s", 32)); // 7 < 32, shift is safe

    // More general: if s === 0 (mod 32), we know possible values are 0, 32, 64...
    // Combined with interval [0, 31], only 0 is possible
    let mut interval = IntervalDomain::new(0, 31);
    let shift_cong = CongruenceValue::new(32, 0);
    reduce_interval_congruence(&mut interval, &shift_cong);
    // Only value === 0 (mod 32) in [0, 31] is 0
    assert_eq!(interval.low(), Some(0));
    assert_eq!(interval.high(), Some(0));
}

// ===== Display tests =====

#[test]
fn test_congruence_value_display() {
    assert_eq!(format!("{}", CongruenceValue::Bottom), "bottom");
    assert_eq!(format!("{}", CongruenceValue::constant(42)), "=42");
    assert_eq!(format!("{}", CongruenceValue::top_value()), "top");
    assert_eq!(format!("{}", CongruenceValue::new(4, 1)), "1 (mod 4)");
}

#[test]
fn test_congruence_domain_display() {
    let d = CongruenceDomain::new_bottom();
    assert_eq!(format!("{d}"), "bottom");

    let d = CongruenceDomain::new();
    assert_eq!(format!("{d}"), "top");

    let mut d = CongruenceDomain::new();
    d.set_var("x", CongruenceValue::new(4, 1));
    assert_eq!(format!("{d}"), "cong(x: 1 (mod 4))");
}

// ===== GCD tests =====

#[test]
fn test_gcd() {
    assert_eq!(gcd(12, 8), 4);
    assert_eq!(gcd(7, 13), 1);
    assert_eq!(gcd(0, 5), 5);
    assert_eq!(gcd(5, 0), 5);
    assert_eq!(gcd(0, 0), 0);
}
