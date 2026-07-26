// Trust: regression test for compile-time bug rust-lang#94961
//
// Exponential time in coherence checking with many traits. When a type
// implements many traits and those traits have overlapping blanket impls,
// the coherence checker must verify that no two impls conflict. The number
// of checks grows combinatorially with the number of trait impls. With N
// traits each having M impls, coherence may perform O(N * M^2) or worse
// overlap checks.
//
// The original report showed exponential compile-time growth when adding
// trait implementations to types that already implement many traits. This
// test creates a type with 20+ trait impls and several traits with multiple
// impls to stress the coherence checking machinery.
//
// Upstream: https://github.com/rust-lang/rust/issues/94961
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// Many small traits. The coherence checker must verify impl consistency
// across all of them when they appear together in where-clause bounds.
trait T0 { fn t0(&self) -> usize; }
trait T1 { fn t1(&self) -> usize; }
trait T2 { fn t2(&self) -> usize; }
trait T3 { fn t3(&self) -> usize; }
trait T4 { fn t4(&self) -> usize; }
trait T5 { fn t5(&self) -> usize; }
trait T6 { fn t6(&self) -> usize; }
trait T7 { fn t7(&self) -> usize; }
trait T8 { fn t8(&self) -> usize; }
trait T9 { fn t9(&self) -> usize; }
trait T10 { fn t10(&self) -> usize; }
trait T11 { fn t11(&self) -> usize; }
trait T12 { fn t12(&self) -> usize; }
trait T13 { fn t13(&self) -> usize; }
trait T14 { fn t14(&self) -> usize; }
trait T15 { fn t15(&self) -> usize; }
trait T16 { fn t16(&self) -> usize; }
trait T17 { fn t17(&self) -> usize; }
trait T18 { fn t18(&self) -> usize; }
trait T19 { fn t19(&self) -> usize; }

// A single type implementing all traits.
struct Widget;

impl T0 for Widget { fn t0(&self) -> usize { 0 } }
impl T1 for Widget { fn t1(&self) -> usize { 1 } }
impl T2 for Widget { fn t2(&self) -> usize { 2 } }
impl T3 for Widget { fn t3(&self) -> usize { 3 } }
impl T4 for Widget { fn t4(&self) -> usize { 4 } }
impl T5 for Widget { fn t5(&self) -> usize { 5 } }
impl T6 for Widget { fn t6(&self) -> usize { 6 } }
impl T7 for Widget { fn t7(&self) -> usize { 7 } }
impl T8 for Widget { fn t8(&self) -> usize { 8 } }
impl T9 for Widget { fn t9(&self) -> usize { 9 } }
impl T10 for Widget { fn t10(&self) -> usize { 10 } }
impl T11 for Widget { fn t11(&self) -> usize { 11 } }
impl T12 for Widget { fn t12(&self) -> usize { 12 } }
impl T13 for Widget { fn t13(&self) -> usize { 13 } }
impl T14 for Widget { fn t14(&self) -> usize { 14 } }
impl T15 for Widget { fn t15(&self) -> usize { 15 } }
impl T16 for Widget { fn t16(&self) -> usize { 16 } }
impl T17 for Widget { fn t17(&self) -> usize { 17 } }
impl T18 for Widget { fn t18(&self) -> usize { 18 } }
impl T19 for Widget { fn t19(&self) -> usize { 19 } }

// A composite trait requiring many supertraits. Proving that a type
// satisfies this bound requires the solver to check all supertraits,
// and coherence must verify there are no conflicting impls for any of them.
trait CompositeA: T0 + T1 + T2 + T3 + T4 + T5 + T6 + T7 + T8 + T9 {
    fn composite_a(&self) -> usize;
}

trait CompositeB: T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 {
    fn composite_b(&self) -> usize;
}

impl CompositeA for Widget {
    fn composite_a(&self) -> usize {
        self.t0() + self.t1() + self.t2() + self.t3() + self.t4()
        + self.t5() + self.t6() + self.t7() + self.t8() + self.t9()
    }
}

impl CompositeB for Widget {
    fn composite_b(&self) -> usize {
        self.t10() + self.t11() + self.t12() + self.t13() + self.t14()
        + self.t15() + self.t16() + self.t17() + self.t18() + self.t19()
    }
}

// Functions with where-clause bounds referencing many traits.
// The compiler must verify these bounds are satisfiable.
fn use_composite_a<T: CompositeA>(item: &T) -> usize {
    item.composite_a()
}

fn use_composite_b<T: CompositeB>(item: &T) -> usize {
    item.composite_b()
}

fn use_all<T: CompositeA + CompositeB>(item: &T) -> usize {
    item.composite_a() + item.composite_b()
}

fn main() {
    let w = Widget;
    assert_eq!(use_composite_a(&w), 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9);
    assert_eq!(use_composite_b(&w), 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 19);
    assert_eq!(use_all(&w), (0..20).sum::<usize>());
}
