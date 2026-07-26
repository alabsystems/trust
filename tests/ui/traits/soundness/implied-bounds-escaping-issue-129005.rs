// Trust: regression test for rust-lang#129005
// Part of #859
//
// Implied bounds with escaping bound variables allow unsound lifetime
// extension. When computing implied outlives bounds from where-clauses
// containing `for<>` binders, predicates with escaping bound variables
// should be filtered out. Without the fix, the trait solver could use
// these escaped binders to satisfy obligations that should not hold,
// effectively allowing arbitrary lifetime extension.
//
// This is closely related to rust-lang#100051 (implied bounds from projections)
// but exploits a different path through the outlives bounds computation.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/129005
//
// STATUS: Fixed. Predicates with escaping bound variables are now filtered
// from implied outlives bounds computation.

trait Trait<'a> {
    type Assoc;
}

impl<'a, T: 'a> Trait<'a> for T {
    type Assoc = &'a T;
}

trait Extend<'a, 'b> {
    fn extend(self, x: &'a str) -> &'b str;
}

// This impl exploits escaping bound vars in the for<> clause.
// The implied bounds from `for<'c> T: Trait<'c>` should NOT allow
// relating 'a and 'b, but the bug let them leak through.
impl<'a, 'b> Extend<'a, 'b> for ()
where
    for<'c> (): Trait<'c>,
{
    fn extend(self, x: &'a str) -> &'b str {
        // With the bug: compiles, unsound — 'a unrelated to 'b
        // With the fix: rejected
        x //~ ERROR lifetime may not live long enough
    }
}

fn main() {
    let s = String::from("hello");
    let r;
    {
        r = <() as Extend<'_, '_>>::extend((), &s);
    }
    println!("{}", r);
}
