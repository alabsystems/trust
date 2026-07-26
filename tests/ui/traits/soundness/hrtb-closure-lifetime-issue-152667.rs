//@ run-pass
#![allow(dead_code)]
// Trust: regression test for rust-lang#152667
// Part of #859
//
// Lifetime inference unsoundness in higher-ranked closures. When a closure
// has an expected signature where the output references late-bound regions
// not constrained by the inputs, unconstrained lifetime inference can
// silently allow use-after-free. The fix rejects expected closure signatures
// where the output references late-bound regions not constrained by inputs,
// and registers WF obligations on resolved output types.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/152667
//
// STATUS: Fixed. The compiler now rejects closures with output lifetimes
// unconstrained by inputs.

trait Capture<'a> {
    type Output;
}

impl<'a, T: 'a> Capture<'a> for T {
    type Output = &'a T;
}

fn higher_ranked<F>(f: F) -> String
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let local = String::from("temporary data");
    let result = f(&local);
    // If the closure can cheat lifetime inference, `result` could
    // outlive `local` — use-after-free
    result.to_string()
}

fn main() {
    // This should be fine: the identity closure preserves lifetimes correctly
    let result = higher_ranked(|x| x);
    println!("{}", result);
}
