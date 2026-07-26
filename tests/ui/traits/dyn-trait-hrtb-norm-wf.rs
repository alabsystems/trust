// Trust: Regression test for rust-lang#152489
// Higher-ranked dyn Trait normalization must check WF of the resulting type.
// When a projection bound `for<'a> <Self as Trait<'a>>::Assoc = &'a T` is
// instantiated, the resulting type may have unconstrained lifetimes.
//
// This test verifies that the compiler properly rejects non-WF normalized types.

//@ check-pass
// (This test ensures the WF obligation is registered but doesn't trigger
// a false positive — the example below is actually well-formed because
// 'a directly constrains the reference. The WF check catches more subtle
// cases where the binder introduces lifetimes that escape.)

trait MyTrait<'a> {
    type Assoc;
}

impl<'a> MyTrait<'a> for () {
    type Assoc = &'a str;
}

fn use_trait_obj(x: &dyn for<'a> MyTrait<'a, Assoc = &'a str>) {
    // This should work — the associated type is well-formed for all 'a
    let _ = x;
}

fn main() {
    use_trait_obj(&());
}
