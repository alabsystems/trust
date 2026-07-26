//@ run-pass
#![allow(dead_code)]
// Trust: regression test for rust-lang#109387
// Part of #859
//
// Dyn-incompatible method calls through trait objects. When a trait has
// methods with `Self: Sized` bounds, those methods are excluded from the
// vtable and cannot be dispatched through trait objects. The bug allowed
// the compiler to resolve such method calls on `dyn Trait`, leading to
// potential UB from calling a function pointer that does not exist in
// the vtable.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/109387
//
// STATUS: Fixed. The compiler now filters non-vtable-safe methods during
// probe assembly for trait objects and emits a clear error during
// confirmation.

trait MyTrait {
    // This method is NOT in the vtable because of Self: Sized
    fn sized_only(&self) -> Box<Self>
    where
        Self: Sized,
    {
        panic!("should not be callable via dyn")
    }

    // This method IS in the vtable
    fn dyn_safe(&self) -> i32;
}

struct Concrete;

impl MyTrait for Concrete {
    fn dyn_safe(&self) -> i32 {
        42
    }
}

fn call_dyn_safe(x: &dyn MyTrait) -> i32 {
    // This is fine — dyn_safe is in the vtable
    x.dyn_safe()
}

fn main() {
    let c = Concrete;
    let val = call_dyn_safe(&c);
    assert_eq!(val, 42);
}
