//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (ADT registration identity — `canonical_adt_args`): the reduced
//! `tests/ui/derives/deriving-associated-types.rs` shape. A tuple struct whose
//! fields are spelled through CONCRETE projections (`Option<<B as
//! DeclaredTrait>::Type>`, `Option<C::Type>` under a where-clause) is
//! constructed with `None` values typed `Option<i32>`: one type, one enum.
//! Before the fix they keyed on the unnormalized `GenericArgs` and registered
//! as two enums, and the constructing `InsertField`s were
//! `OperandTypeMismatch { expected: enum.1, actual: enum.0 }` (8 per body) —
//! an INVALID module the moment wave-BS let `main` lower clean. NOT under
//! `strict`: the derived `fmt`/`eq` bodies are still dirty on their own
//! terms, and this pin is about `main`'s module VALIDITY, which the producer
//! sweep's `modules_invalid` ratchets (measured 1 -> 0 on this shape).
pub trait DeclaredTrait {
    type Type;
}

impl DeclaredTrait for i32 {
    type Type = i32;
}

pub trait WhereTrait {
    type Type;
}

impl WhereTrait for i32 {
    type Type = i32;
}

pub mod module {
    pub type Type = i32;
}

#[derive(PartialEq, Debug)]
struct PrivateStruct<T>(T);

#[derive(PartialEq, Debug)]
struct TupleStruct<A, B: DeclaredTrait, C>(
    module::Type,
    Option<module::Type>,
    A,
    PrivateStruct<A>,
    B,
    B::Type,
    Option<B::Type>,
    <B as DeclaredTrait>::Type,
    Option<<B as DeclaredTrait>::Type>,
    C,
    C::Type,
    Option<C::Type>,
    <C as WhereTrait>::Type,
    Option<<C as WhereTrait>::Type>,
    <i32 as DeclaredTrait>::Type,
) where C: WhereTrait;

fn main() {
    let e: TupleStruct<
        i32,
        i32,
        i32,
    > = TupleStruct(
        0,
        None,
        0,
        PrivateStruct(0),
        0,
        0,
        None,
        0,
        None,
        0,
        0,
        None,
        0,
        None,
        0,
    );
    assert_eq!(e, e);

}
