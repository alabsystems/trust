// Trust: Regression test for rust-lang#135103
// Flatten/FlatMap must NOT use InPlaceIterable optimization
// because flattening can produce more elements than the source.
//@ run-pass

fn main() {
    // This used to cause a buffer overflow via in-place collection
    // when Flatten produced more elements than the source Vec
    let v: Vec<Vec<u8>> = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
    let flat: Vec<u8> = v.into_iter().flatten().collect();
    assert_eq!(flat, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

    // FlatMap case
    let v: Vec<u32> = vec![1, 2, 3];
    let expanded: Vec<u32> = v.into_iter().flat_map(|x| vec![x, x * 10, x * 100]).collect();
    assert_eq!(expanded, vec![1, 10, 100, 2, 20, 200, 3, 30, 300]);
}
