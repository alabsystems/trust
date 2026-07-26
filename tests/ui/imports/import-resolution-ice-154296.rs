//@ check-pass
// Regression test for rust-lang#154296
// Inconsistent import resolution ordering should not ICE.
//
// The ICE occurred when the speculative fixed-point iteration resolved an
// import's module path to one module, but by finalization time a conflicting
// glob import had changed the resolution graph so the same path resolved
// differently. The fix ensures the finalize result is accepted as authoritative
// and the cached state is corrected rather than triggering a span_bug!().
//
// This test exercises the scenario where a single import shadows a glob-imported
// name that is used as part of another import's module path, creating potential
// ordering-dependent resolution during the fixed-point iteration.

mod a {
    pub mod inner {
        pub struct Item;
    }
}

mod b {
    pub mod inner {
        pub struct Item;
    }
}

// Glob brings `a::inner` into scope as `inner`
use a::*;

// Single import also defines `inner`, shadowing the glob.
// During the fixed-point iteration, `inner` may resolve to `a::inner` (from
// the glob) before the single import is processed, then change to `b::inner`
// once the single import takes precedence.
use b::inner;

// This import uses the now-shadowed `inner` — exercises the code path where
// the module for the import path may change between speculative and final passes.
use inner::Item;

fn main() {
    let _x = Item;
}
