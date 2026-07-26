// Trust: regression test for rust-lang#142239
// Part of #859
//
// TAIT (type_alias_impl_trait) opaque type WF check used the defining
// function's param_env instead of the opaque type's own param_env. The
// defining function may have stronger bounds (e.g., T: SomeTrait) that
// the opaque type's context does not guarantee. This allowed hidden types
// that depend on the function's extra bounds to pass WF checking
// incorrectly.
//
// The fix uses the opaque type's own param_env for TAIT while keeping the
// function's param_env for RPIT (where the opaque type lives inside the
// function and the function's bounds are appropriate).
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/142239
//
// STATUS: Fixed. TAIT WF checks now use the opaque type's own param_env.

#![feature(type_alias_impl_trait)]

trait MyBound {
    fn value(&self) -> i32;
}

impl MyBound for i32 {
    fn value(&self) -> i32 {
        *self
    }
}

// The opaque type itself has NO MyBound constraint
type Opaque = impl Sized; //~ ERROR unconstrained opaque type

// But the defining function has T: MyBound — with the bug, the hidden
// type's WF check used this function's stronger param_env
fn define_opaque<T: MyBound>(x: T) -> Opaque {
    x //~ ERROR mismatched types
}

fn main() {
    let _val: Opaque = define_opaque(42i32);
}
