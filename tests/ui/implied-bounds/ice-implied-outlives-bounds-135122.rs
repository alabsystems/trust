// Regression test for https://github.com/rust-lang/rust/issues/135122
// (formerly the known-bug corpus entry tests/crashes/135122.rs).
//
// Upstream rustc ICEs here with `assertion failed: !ty.has_non_region_infer()`
// in `implied_outlives_bounds` (rustc_trait_selection/src/traits/outlives_bounds.rs)
// while comparing the `add` impl item against its trait: the unconstrained
// impl type parameter leaks an unresolved inference variable into the
// implied-bounds computation. Trust compiles this without crashing and emits
// the ordinary diagnostics asserted below, so the crashes-suite entry is
// replaced by this test (the upstream-sanctioned process once a crash test
// stops ICEing).

trait Add {
    type Output;
    fn add(_: (), _: Self::Output) {}
}

trait IsSame<Lhs> {
    type Assoc;
}

trait Data {
    type Elem;
}

impl<B> IsSame<i16> for f32 where f32: IsSame<B, Assoc = B> {}
//~^ ERROR not all trait items implemented, missing: `Assoc`
//~| ERROR the type parameter `B` is not constrained by the impl trait, self type, or predicates

impl<A> Add for i64
where
    f32: IsSame<A>,
    i8: Data<Elem = A>,
    //~^ ERROR the trait bound `i8: Data` is not satisfied
{
    type Output = <f32 as IsSame<A>>::Assoc;
    fn add(_: Data, _: Self::Output) {}
    //~^ WARN trait objects without an explicit `dyn` are deprecated
    //~| WARN this is accepted in the current edition
    //~| ERROR the value of the associated type `Elem` in `Data` must be specified
}

fn main() {}
