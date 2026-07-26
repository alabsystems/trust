// Trust: regression test for rust-lang#100051 (Part of #859)
// Verify that legitimate implied bounds from impl headers still work correctly.
// Projections that preserve lifetime relationships (rather than erasing them)
// should still provide valid implied bounds.
//@ check-pass

trait HasAssoc {
    type Assoc;
}

impl<'a> HasAssoc for &'a str {
    type Assoc = &'a str;
}

// This is a legitimate use: the projection `<&'a str as HasAssoc>::Assoc`
// normalizes to `&'a str`, which preserves the lifetime. The implied bound
// that `'a` is valid comes from the normalized type itself, not from
// WF of the unnormalized type erasing constraints.
trait Process<'a> {
    fn process(&self, input: &'a str) -> &'a str;
}

impl<'a> Process<'a> for <&'a str as HasAssoc>::Assoc {
    fn process(&self, input: &'a str) -> &'a str {
        input
    }
}

// Another legitimate case: the projection doesn't erase any lifetime
// constraints that weren't already present in the normalized form.
trait Identity {
    type Output;
}

impl<'a, T: 'a> Identity for &'a T {
    type Output = &'a T;
}

trait Use<'a, T: 'a> {
    fn use_ref(&self, r: &'a T) -> &'a T;
}

impl<'a, T: 'a> Use<'a, T> for <&'a T as Identity>::Output {
    fn use_ref(&self, r: &'a T) -> &'a T {
        r
    }
}

fn main() {
    // Verify the legitimate impls work at runtime
    let s = "hello";
    let result = <&str as Process>::process(&s, s);
    assert_eq!(result, "hello");

    let val = 42u32;
    let result = <&u32 as Use<u32>>::use_ref(&&val, &val);
    assert_eq!(*result, 42);
}
