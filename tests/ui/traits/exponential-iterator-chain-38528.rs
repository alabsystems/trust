// Trust: regression test for compile-time bug rust-lang#38528
//
// Deeply nested iterator chains (e.g., `.chain().chain().chain()...`) produce
// deeply nested generic types like `Chain<Chain<Chain<..., B>, C>, D>`. Each
// additional `.chain()` call roughly doubles the monomorphization work because
// the compiler must instantiate the full type tree for each generic parameter.
//
// The original report showed compile times growing from ~5s to ~45s when
// removing `Box::new()` type erasure. This test uses 8 chained iterators,
// which should compile quickly but exercises the nested-type code path.
//
// Upstream: https://github.com/rust-lang/rust/issues/38528
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass
//@ edition: 2021

fn make_iter_a() -> impl Iterator<Item = u32> {
    [1u32, 2, 3].into_iter()
}

fn make_iter_b() -> impl Iterator<Item = u32> {
    [4u32, 5, 6].into_iter()
}

fn make_iter_c() -> impl Iterator<Item = u32> {
    [7u32, 8, 9].into_iter()
}

pub fn main() {
    // Each .chain() nests the type one level deeper:
    // Chain<Chain<Chain<..., IntoIter<u32>>, IntoIter<u32>>, IntoIter<u32>>
    //
    // At 8 levels, the monomorphized type is already quite complex. Without
    // proper handling, the compiler would spend excessive time in item
    // collection and code generation.
    let iter = make_iter_a()
        .chain(make_iter_b())
        .chain(make_iter_c())
        .chain(make_iter_a())
        .chain(make_iter_b())
        .chain(make_iter_c())
        .chain(make_iter_a())
        .chain(make_iter_b());

    let sum: u32 = iter.sum();
    assert!(sum > 0);
}
