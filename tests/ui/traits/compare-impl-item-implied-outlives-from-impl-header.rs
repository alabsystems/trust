#![allow(refining_impl_trait)]

// tRust HISTORY: this test originally pinned a Trust extension (check-pass)
// where compare_method_predicate_entailment and RPITIT collection seeded the
// impl header's assumed-WF types (`Self = &'a T` implies `T: 'a`) before
// proving impl-method predicates. That extension was REMOVED 2026-07-02: it
// was unmarked/ungated, relocated E0277 spans (min_specialization/issue-79224
// wrong-span + duplicate), and made the region check more permissive than
// upstream — risky next to the open implied-bounds soundness holes
// (rust-lang#100051 family) and a drop-in divergence (code accepted here
// would not build on rustc). Upstream rejects both shapes below; so do we.

trait Ordinary {
    fn method();
}

impl<'a, T> Ordinary for &'a T {
    fn method()
    where
        T: 'a,
    //~^ ERROR impl has stricter requirements than trait
    {
    }
}

trait WithRpitit<'a, T> {
    fn method() -> impl Sized + 'a;
}

impl<'a, T> WithRpitit<'a, T> for &'a T {
    fn method() -> &'a T {
        //~^ ERROR the parameter type `T` may not live long enough
        //~| ERROR the parameter type `T` may not live long enough
        loop {}
    }
}

fn main() {}
