// Test that deeply nested const expressions don't cause exponential
// normalization time. This is a regression test for rust-lang#150061.
//
// Before the fix, the normalization folder would visit const subtrees
// multiple times (once via super_fold_with on args, then again on the
// result), causing O(2^N) work for nested const expressions.
//
//@ check-pass

trait ConstProvider {
    const VALUE: u64;
}

struct Layer0;
struct Layer1;
struct Layer2;
struct Layer3;
struct Layer4;
struct Layer5;
struct Layer6;
struct Layer7;
struct Layer8;
struct Layer9;
struct Layer10;
struct Layer11;
struct Layer12;
struct Layer13;
struct Layer14;
struct Layer15;

impl ConstProvider for Layer0 {
    const VALUE: u64 = 1;
}

// Each layer doubles the normalization work without caching
impl ConstProvider for Layer1 {
    const VALUE: u64 = <Layer0 as ConstProvider>::VALUE + <Layer0 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer2 {
    const VALUE: u64 = <Layer1 as ConstProvider>::VALUE + <Layer1 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer3 {
    const VALUE: u64 = <Layer2 as ConstProvider>::VALUE + <Layer2 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer4 {
    const VALUE: u64 = <Layer3 as ConstProvider>::VALUE + <Layer3 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer5 {
    const VALUE: u64 = <Layer4 as ConstProvider>::VALUE + <Layer4 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer6 {
    const VALUE: u64 = <Layer5 as ConstProvider>::VALUE + <Layer5 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer7 {
    const VALUE: u64 = <Layer6 as ConstProvider>::VALUE + <Layer6 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer8 {
    const VALUE: u64 = <Layer7 as ConstProvider>::VALUE + <Layer7 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer9 {
    const VALUE: u64 = <Layer8 as ConstProvider>::VALUE + <Layer8 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer10 {
    const VALUE: u64 = <Layer9 as ConstProvider>::VALUE + <Layer9 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer11 {
    const VALUE: u64 = <Layer10 as ConstProvider>::VALUE + <Layer10 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer12 {
    const VALUE: u64 = <Layer11 as ConstProvider>::VALUE + <Layer11 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer13 {
    const VALUE: u64 = <Layer12 as ConstProvider>::VALUE + <Layer12 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer14 {
    const VALUE: u64 = <Layer13 as ConstProvider>::VALUE + <Layer13 as ConstProvider>::VALUE;
}

impl ConstProvider for Layer15 {
    const VALUE: u64 = <Layer14 as ConstProvider>::VALUE + <Layer14 as ConstProvider>::VALUE;
}

// Without const normalization caching, this would require 2^15 = 32768
// normalization steps. With caching, it's O(15).
fn main() {
    assert_eq!(<Layer15 as ConstProvider>::VALUE, 32768);
}
