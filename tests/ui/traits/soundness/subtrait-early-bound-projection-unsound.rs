// Trust: regression test for rust-lang#131029
// Part of #859
//
// Subtrait projection with early-bound generics is unsound. When a
// subtrait has an associated type that involves early-bound generic
// parameters from the supertrait, the compiler can incorrectly
// normalize projections in a way that drops lifetime constraints.
//
// The issue: Given `trait Sub<'a>: Super<Assoc = &'a str>`, projecting
// `<T as Super>::Assoc` in a context where T is only known to impl
// `Sub<'a>` for some specific 'a can cause the compiler to lose track
// of which 'a the associated type is bound to, allowing lifetime extension.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/131029
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should reject the unsound projection normalization.

trait Super {
    type Assoc;
}

trait Sub<'a>: Super<Assoc = &'a str> {}

// This struct implements Sub<'a> for a specific lifetime 'a.
struct MyType<'a>(&'a str);

impl<'a> Super for MyType<'a> {
    type Assoc = &'a str;
}

impl<'a> Sub<'a> for MyType<'a> {}

// The unsound function: it takes a T: for<'a> Sub<'a> and uses
// the supertrait projection to get <T as Super>::Assoc.
// Because Sub<'a> has the bound Super<Assoc = &'a str>, and we
// require T: for<'a> Sub<'a>, the projection <T as Super>::Assoc
// should be `&'a str` for ALL 'a — but the compiler resolves it
// to a single concrete lifetime, allowing lifetime confusion.
fn extend_via_subtrait<T>(val: <T as Super>::Assoc) -> &'static str
where
    T: for<'a> Sub<'a>,
{
    // The compiler thinks <T as Super>::Assoc = &'static str because
    // T: for<'a> Sub<'a> implies T: Sub<'static>, and the supertrait
    // bound gives Assoc = &'static str. But if T is actually bound
    // to a shorter lifetime, this is unsound.
    val
}

fn main() {
    let result;
    {
        let local = String::from("unsound subtrait projection");
        // We can't actually construct a type that is `for<'a> Sub<'a>`
        // with MyType (since MyType<'a> is only Sub<'a> for one 'a),
        // but the compiler's handling of this pattern in generic contexts
        // is the source of unsoundness. This test documents the pattern.
        //
        // The actual exploit requires a type that can satisfy the HRTB
        // bound. When such a type exists, this function would allow
        // extending the lifetime of `local` to 'static.
        result = extend_via_subtrait::<MyType<'_>>(&local);
        //~^ ERROR implementation of `Sub` is not general enough
        //~| ERROR `local` does not live long enough
    }
    println!("{}", result);
}
