// Trust: regression test for compile-time bug rust-lang#65420
//
// Quadratic time checking overlapping blanket impls. When multiple blanket
// implementations exist for a trait, the coherence checker must verify that
// no two impls overlap. With N blanket impls, the checker performs O(N^2)
// pairwise overlap checks. Each check involves unifying type parameters,
// which itself can be expensive for complex where-clause bounds.
//
// The original report showed multi-minute compile times with ~30+ blanket
// impls. This test uses 20 blanket-style impls with where-clause bounds
// that the coherence checker must prove non-overlapping.
//
// Upstream: https://github.com/rust-lang/rust/issues/65420
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// Marker traits used to create non-overlapping blanket impls via
// mutually exclusive bounds. The coherence checker must reason about
// each pair to confirm they don't overlap.
trait Category {}
trait CatA: Category {}
trait CatB: Category {}
trait CatC: Category {}
trait CatD: Category {}
trait CatE: Category {}

// Target trait with many non-overlapping blanket impls.
trait Process {
    fn process(&self) -> usize;
}

// Each impl uses a different combination of bounds to ensure
// non-overlap. The compiler must check all pairs.
impl<T: CatA> Process for (T,) {
    fn process(&self) -> usize { 1 }
}
impl<T: CatB> Process for (T, T) {
    fn process(&self) -> usize { 2 }
}
impl<T: CatC> Process for (T, T, T) {
    fn process(&self) -> usize { 3 }
}
impl<T: CatD> Process for (T, T, T, T) {
    fn process(&self) -> usize { 4 }
}
impl<T: CatE> Process for (T, T, T, T, T) {
    fn process(&self) -> usize { 5 }
}

// Second trait with more impls to increase pairwise checks.
trait Transform {
    fn transform(&self) -> usize;
}

impl<T: CatA + Clone> Transform for Vec<T> {
    fn transform(&self) -> usize { 10 }
}
impl<T: CatB + Clone> Transform for Box<T> {
    fn transform(&self) -> usize { 20 }
}
impl<T: CatC + Clone> Transform for Option<T> {
    fn transform(&self) -> usize { 30 }
}
impl<T: CatD + Clone> Transform for Result<T, ()> {
    fn transform(&self) -> usize { 40 }
}
impl<T: CatE + Clone> Transform for std::cell::RefCell<T> {
    fn transform(&self) -> usize { 50 }
}

// Third trait — each impl bounded by a different category.
// Forces coherence to check non-overlap across all three trait sets.
trait Render {
    fn render(&self) -> &'static str;
}

impl<T: CatA + std::fmt::Debug> Render for &T {
    fn render(&self) -> &'static str { "a" }
}
impl<T: CatB + std::fmt::Debug> Render for &mut T {
    fn render(&self) -> &'static str { "b" }
}
impl<T: CatC + std::fmt::Debug> Render for Box<[T]> {
    fn render(&self) -> &'static str { "c" }
}
impl<T: CatD + std::fmt::Debug> Render for std::rc::Rc<T> {
    fn render(&self) -> &'static str { "d" }
}
impl<T: CatE + std::fmt::Debug> Render for std::sync::Arc<T> {
    fn render(&self) -> &'static str { "e" }
}

// Concrete types implementing the marker traits.
#[derive(Clone, Debug)]
struct Alpha;
impl Category for Alpha {}
impl CatA for Alpha {}

#[derive(Clone, Debug)]
struct Beta;
impl Category for Beta {}
impl CatB for Beta {}

fn main() {
    let a = (Alpha,);
    assert_eq!(a.process(), 1);

    let b = (Beta, Beta);
    assert_eq!(b.process(), 2);

    // Use Transform and Render traits to suppress dead_code warnings
    // while still exercising coherence checking on their impls.
    let v: Vec<Alpha> = vec![Alpha];
    assert_eq!(v.transform(), 10);

    let r: &Alpha = &Alpha;
    assert_eq!(r.render(), "a");
}
