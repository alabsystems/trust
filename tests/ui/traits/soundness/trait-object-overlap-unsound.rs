//@ known-bug: #57893
//@ check-pass
// Trust: regression test for rust-lang#57893
// Part of #859
//
// Builtin trait-object impl and user-written blanket impl can unsoundly
// overlap. The compiler should reject code where a blanket impl like
// `impl<T: ?Sized> Object<U> for T` conflicts with the built-in
// `impl Object<U> for dyn Object<U>`, because it allows constructing
// a `transmute` function in safe Rust.
//
// This PoC is the minimal reproducer from the upstream issue
// (https://github.com/rust-lang/rust/issues/57893#issuecomment-500250283).
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should reject it with a coherence or overlap error.

trait Object<U> {
    type Output;
}

impl<T: ?Sized, U> Object<U> for T {
    type Output = U;
}

fn foo<T: ?Sized, U>(x: <T as Object<U>>::Output) -> U {
    x
}

fn transmute<T, U>(x: T) -> U {
    foo::<dyn Object<U, Output = T>, U>(x)
}

fn main() {
    // If this compiles and runs, it's unsound — it transmutes a Vec<u8>
    // into a String without any validation.
    let _s: String = transmute::<Vec<u8>, String>(vec![255, 255, 255]);
}
