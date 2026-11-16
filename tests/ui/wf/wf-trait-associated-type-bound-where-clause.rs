// Trust: D0.7 static-semantics source map, row TRAITS-TRAITS.
//
// An associated type's bound must be well-formed: `A<u32>` requires `u32: B`
// by the where-clause of `A`, and no impl provides it.

trait A<T>
where
    T: B,
{
}

trait B {}

trait C {
    type Assoc: A<u32>; //~ ERROR E0277
}

fn main() {}
