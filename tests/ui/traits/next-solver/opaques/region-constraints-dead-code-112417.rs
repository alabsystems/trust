// Regression test for rust-lang#112417: unchecked region constraints
// for opaque types in dead code.
//
// Previously, `foo` compiled despite the hidden type `Foo<'a, 'b>`
// requiring `'b: 'a` -- a constraint not reflected in the opaque
// type's bounds. The defining use was in dead code (after panic!()),
// so HIR typeck used erased regions and never checked the constraint.
//
// Status: GUARDED -- the next solver's TypingMode::Borrowck path and
// add_item_bounds_for_hidden_type partially mitigate this, but the
// underlying issue (erased regions from dead-code HIR typeck) persists.
// The code below still compiles when it arguably should not.
// This test documents the current behavior and will catch future
// regressions if the fix is completed.
//
// Trust: next-solver regression test for WS1 soundness bug
//@ compile-flags: -Znext-solver=globally
//@ check-pass
// FIXME(rust-lang#112417): this should ideally be compile-fail,
// rejecting foo() because the region constraint 'b: 'a is not
// enforced on the opaque type.

#![allow(dead_code, unused)]

trait CallMeMaybe<'a, 'b> {
    fn mk() -> Self;
    fn subtype<T>(self, x: &'b T) -> &'a T;
}

struct Foo<'a, 'b: 'a>(&'a (), &'b ());
impl<'a, 'b> CallMeMaybe<'a, 'b> for Foo<'a, 'b> {
    fn mk() -> Self {
        Foo(&(), &())
    }
    fn subtype<T>(self, x: &'b T) -> &'a T {
        x
    }
}

// This function is the unsound one: it returns an opaque type
// whose hidden type (Foo<'a, 'b>) requires 'b: 'a, but the
// opaque type `impl CallMeMaybe<'a, 'b>` does not enforce it.
// The defining use is in dead code (after panic!()).
fn foo<'a, 'b>() -> impl CallMeMaybe<'a, 'b> {
    panic!();
    #[allow(unreachable_code)]
    Foo::<'a, 'b>(&(), &())
}

fn main() {}
