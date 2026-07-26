// Trust: regression test for rust-lang#130521
// Part of #859
//
// Implied bounds from GAT (Generic Associated Type) projections are unsound.
// When a GAT has lifetime bounds in its definition (e.g., `type Gat<'a>
// where Self: 'a`), the compiler uses these as implied bounds at call sites.
// However, these implied bounds can be exploited to forge lifetime
// relationships that don't actually hold, allowing lifetime extension.
//
// The core issue: `where Self: 'a` on a GAT provides an implied bound
// that `Self: 'a` whenever `<T as Trait>::Gat<'a>` appears. By
// carefully constructing types, this can be used to prove arbitrary
// lifetime outlives relationships.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/130521
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should reject the unsound implied bounds from GATs.

trait LendingIterator {
    type Item<'a> where Self: 'a;
}

// The key: this impl says Item<'a> = &'a &'inner str.
// For this to be well-formed, we need 'inner: 'a.
// The GAT's `where Self: 'a` gives us `StringRef<'inner>: 'a`,
// which should imply 'inner: 'a. But the compiler uses this
// in REVERSE — it uses the GAT projection to PROVE that 'inner: 'a
// even when it shouldn't hold.
struct StringRef<'inner>(&'inner str);

impl<'inner> LendingIterator for StringRef<'inner> {
    type Item<'a> = &'a &'inner str where Self: 'a;
}

fn extend_lifetime_gat<'a, 'b>(s: &'a str) -> &'b str
where
    // This constraint is satisfied by StringRef<'a>: LendingIterator,
    // but the GAT implied bounds leak 'a into 'b.
    for<'x> StringRef<'a>: LendingIterator<Item<'x> = &'x &'a str>,
{
    // The function body just returns the input with a different lifetime.
    // The where-clause's implied bounds should not allow this, but
    // the GAT implied bounds make it possible.
    s //~ ERROR lifetime may not live long enough
}

fn main() {
    let d;
    {
        let x = String::from("use-after-free via GAT implied bounds");
        d = extend_lifetime_gat(&x); //~ ERROR `x` does not live long enough
    }
    // Use-after-free: x is dropped but d still references it.
    println!("{}", d);
}
