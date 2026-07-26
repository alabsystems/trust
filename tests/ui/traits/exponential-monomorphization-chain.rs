// Trust: regression test for compile-time exponential monomorphization
//
// Generic function chains where each level instantiates the next with a
// larger type cause exponential monomorphization blowup. The pattern is:
// `f::<A>` calls `g::<(A, A)>` which calls `h::<((A, A), (A, A))>` —
// the type doubles at each level.
//
// This is a fundamental compiler scalability issue: the monomorphizer
// must instantiate each generic function with its concrete type, and if
// types grow exponentially, so does the work. Modern rustc mitigates this
// with the type-length limit, but the compilation time can still be
// excessive before the limit is reached.
//
// This test uses 10 levels (level9 down to level0) with 9 doublings,
// producing a type tree of O(2^9) = 512 leaves. This should compile
// quickly but exercises the monomorphization deduplication path.
//
// Related to patterns from multiple upstream issues involving type growth.
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

trait Size {
    fn size() -> usize;
}

impl Size for u8 {
    fn size() -> usize { 1 }
}

impl<A: Size, B: Size> Size for (A, B) {
    fn size() -> usize { A::size() + B::size() }
}

// Each function instantiates the next level with a doubled type.
// f0: T -> f1: (T, T) -> f2: ((T, T), (T, T)) -> ...
fn level0<T: Size>() -> usize { T::size() }
fn level1<T: Size>() -> usize { level0::<(T, T)>() }
fn level2<T: Size>() -> usize { level1::<(T, T)>() }
fn level3<T: Size>() -> usize { level2::<(T, T)>() }
fn level4<T: Size>() -> usize { level3::<(T, T)>() }
fn level5<T: Size>() -> usize { level4::<(T, T)>() }
fn level6<T: Size>() -> usize { level5::<(T, T)>() }
fn level7<T: Size>() -> usize { level6::<(T, T)>() }
fn level8<T: Size>() -> usize { level7::<(T, T)>() }
fn level9<T: Size>() -> usize { level8::<(T, T)>() }

pub fn main() {
    // level9 starts with u8, each level doubles:
    // level9<u8> -> level8<(u8,u8)> -> level7<((u8,u8),(u8,u8))> -> ...
    // After 9 doublings, the final type at level0 has 2^9 = 512 leaves.
    let result = level9::<u8>();
    assert_eq!(result, 512);
}
