// Trust: regression test for rust-lang#149743
// Projection normalization must verify WF of the result type.
//
// When `<T as Trait>::Assoc` normalizes to a concrete type, the well-formedness
// of that concrete type must be checked in the calling context. Without this
// check, normalization can produce types where required bounds (like outlives
// requirements) are not verified, leading to potential unsoundness.

//@ check-pass

// Test 1: Nested projection normalization checks WF of final result.
trait Mapper {
    type Output;
}

trait HasAssoc {
    type Assoc: Mapper;
}

// Force normalization of a nested projection.
fn use_nested_projection<T: HasAssoc>(
    x: <<T as HasAssoc>::Assoc as Mapper>::Output,
) -> <<T as HasAssoc>::Assoc as Mapper>::Output {
    x
}

// Test 2: Projection in return position through impl candidate.
trait Producer {
    type Item;
    fn produce(&self) -> Self::Item;
}

struct Concrete;
impl Producer for Concrete {
    type Item = Vec<u32>;
    fn produce(&self) -> Self::Item {
        Vec::new()
    }
}

fn call_produce<T: Producer>(t: &T) -> <T as Producer>::Item {
    t.produce()
}

// Test 3: Param-env candidate normalization checks WF.
fn with_param_env_bound<T, U>(x: U) -> U
where
    T: Mapper<Output = U>,
    U: Sized,
{
    x
}

// Test 4: Projection normalization with lifetime-bearing result types.
// The normalized result `&'a [u8]` has WF requirement `[u8]: 'a` which
// must be verified.
trait LifetimeAssoc<'a> {
    type Ref;
}

impl<'a> LifetimeAssoc<'a> for () {
    type Ref = &'a [u8];
}

fn use_lifetime_assoc<'a>(x: <() as LifetimeAssoc<'a>>::Ref) -> &'a [u8] {
    x
}

fn main() {
    let _ = call_produce(&Concrete);
    let s = vec![1u8, 2, 3];
    let _ = use_lifetime_assoc(s.as_slice());
}
