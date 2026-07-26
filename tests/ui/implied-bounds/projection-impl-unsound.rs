//@ known-bug: #100051
// Trust: regression test for rust-lang#100051 (Part of #859)
// Implied bounds from projections in impl headers must not create unsound
// lifetime relationships.
//
// The core attack: `<&'long &'short () as Forget>::Forgotten` normalizes to
// `()`, but WF of the unnormalized `&'long &'short ()` requires `'short: 'long`.
// If the compiler treats this WF requirement as an implied bound, it unsoundly
// assumes `'short: 'long` for the entire impl body, allowing lifetime extension.
//
// The fix: `compute_implied_outlives_bounds_inner` in
// `compiler/rustc_trait_selection/src/traits/query/type_op/implied_outlives_bounds.rs`
// only uses the *normalized* type's WF obligations, not the unnormalized type's.

// Author: Andrew Yates <andrewyates.name@gmail.com>

trait Forget {
    type Forgotten;
}

impl<T> Forget for T {
    type Forgotten = ();
}

// This impl has a projection in its header that normalizes away lifetime constraints.
// The WF of `&'long &'short ()` requires `'short: 'long`, but since the projection
// normalizes to `()`, that requirement must NOT become an implied bound.
impl<'short, 'long> std::convert::From<&'long &'short ()>
    for <&'long &'short () as Forget>::Forgotten
{
    fn from(_: &'long &'short ()) -> Self {}
}

// Direct test: can we exploit the implied bound to extend lifetimes?
trait LifetimeExtend<'a, 'b> {
    fn extend(self, short: &'a str) -> &'b str;
}

impl<'a, 'b> LifetimeExtend<'a, 'b> for <&'b &'a () as Forget>::Forgotten {
    fn extend(self, short: &'a str) -> &'b str {
        short
    }
}

fn main() {}
