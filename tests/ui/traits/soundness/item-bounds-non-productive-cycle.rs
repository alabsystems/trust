// Trust: Regression test for rust-lang#135246
// Part of #859
//
// Item bounds can be used to non-productively prove themselves, creating
// unsoundness. When proving `<T as Trait>::Assoc: Bound`, the compiler
// should not use the item bound `type Assoc: Bound` on the same
// associated type without a productive step (i.e., normalization to a
// concrete type that actually satisfies the bound).
//
// This test verifies the compiler rejects the transmute pattern from
// the upstream issue, where a cyclically-defined trait with item bounds
// on Proof creates a non-productive cycle.

trait Trait<R>: Sized {
    type Proof: Trait<R, Proof = Self>;
}

// Indirection prevents eagerly normalizing away the cycle.
trait Indir<L: Trait<R>, R>: Trait<R, Proof = <L::Proof as Trait<R>>::Proof> {}
impl<L, R> Indir<L, R> for R
where
    L: Trait<R>,
    R: Trait<R, Proof = <L::Proof as Trait<R>>::Proof>,
{}

impl<L, R> Trait<R> for L
where
    L: Trait<R>,
    R: Indir<L, R>,
{
    type Proof = R;
}

fn transmute<L: Trait<R>, R>(r: L) -> <L::Proof as Trait<R>>::Proof {
    r
}

fn main() {
    // This must fail. If item bounds can prove themselves non-productively,
    // this would compile and allow transmuting Vec<u8> into String.
    let s: String = transmute::<_, String>(vec![65_u8, 66, 67]);
    //~^ ERROR overflow evaluating the requirement
    println!("{}", s);
}
