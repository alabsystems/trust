//@ known-bug: #100051
//@ check-pass
// Trust: regression test for rust-lang#100051 (Part of #859)
// Verify that implied bounds from projections in impl headers don't create
// unsound lifetime relationships.
//
// The core issue: when an impl header contains a projection like
// `<&'b &'a () as Trait>::Type` that normalizes away lifetime constraints
// (e.g., normalizes to `()`), the WF requirements of the unnormalized type
// (`'a: 'b`) must NOT leak as implied bounds. Without the fix, the compiler
// would incorrectly assume `'a: 'b` allowing lifetime extension.

trait Forget {
    type Forgotten;
}

impl<T> Forget for T {
    type Forgotten = ();
}

// This trait allows converting between lifetimes — should be impossible
// without the appropriate bound.
trait LifetimeExtend<'short, 'long> {
    fn extend(self, short: &'short str) -> &'long str;
}

// The impl header `<&'long &'short () as Forget>::Forgotten` normalizes to `()`.
// WF of `&'long &'short ()` requires `'short: 'long`, but this MUST NOT be
// assumed as an implied bound — otherwise `extend` could unsoundly convert
// a short-lived reference to a long-lived one.
impl<'short, 'long> LifetimeExtend<'short, 'long>
    for <&'long &'short () as Forget>::Forgotten
{
    fn extend(self, short: &'short str) -> &'long str {
        short // [pending soundness check] ERROR lifetime may not live long enough
    }
}

// If the above compiled without error, this would be a use-after-free:
fn main() {
    let extended;
    {
        let local = String::from("dangling");
        extended = <() as LifetimeExtend>::extend((), &local);
    }
    // `extended` would dangle here if the unsoundness were allowed
    println!("{}", extended);
}
