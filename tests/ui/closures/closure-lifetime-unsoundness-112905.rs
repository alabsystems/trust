// Regression test for rust-lang#112905 (tRust #914)
// Validates that closure lifetime soundness is enforced at multiple levels:
// 1. E0582 catches unsound bounds at the definition site
// 2. extract_sig_from_projection validates during closure inference (defense-in-depth)
//
// The unsound pattern: `for<'a, 'b> Fn(&'a T) -> &'b T` where 'b is independent
// of 'a, allowing closures to return references with unrelated lifetimes.

// E0582 catches this at the bound definition site.
fn unsound_explicit<F: for<'a, 'b> Fn(&'a str) -> &'b str>(_f: F) {}
//~^ ERROR binding for associated type `Output` references lifetime `'b`, which does not appear in the trait input types

// The sound pattern: output lifetime constrained by input lifetime.
fn sound_explicit<F: for<'a> Fn(&'a str) -> &'a str>(f: F) -> &'static str {
    let local = String::from("hello");
    f(&local)
    //~^ ERROR cannot return value referencing local variable `local`
}

// Verify closures with properly constrained lifetimes still work.
fn valid_usage() {
    fn identity<F: Fn(&str) -> &str>(f: F, s: &str) -> &str {
        f(s)
    }
    let s = "hello";
    let result = identity(|x| x, s);
    assert_eq!(result, "hello");
}

fn main() {
    valid_usage();
}
