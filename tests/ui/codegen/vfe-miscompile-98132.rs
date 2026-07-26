// Regression test for rust-lang#98132: -Zvirtual-function-elimination incorrectly
// eliminates virtual functions that are reachable through trait upcasting.
//
// When a subtrait vtable contains a TraitVPtr entry pointing to a supertrait
// vtable, the supertrait vtable must also have !type and !vcall_visibility
// metadata applied. Without this, LLVM's VFE pass cannot see that functions
// in supertrait vtables are reachable through trait upcasting, and may
// incorrectly eliminate them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ run-crash
//@ known-bug: #859
// The -Zvirtual-function-elimination + -Clto pipeline still miscompiles this
// vtable pattern (binary SIGTRAPs); tracked in Trust #859 until the VFE fix is adopted.
//@ no-prefer-dynamic
//@ compile-flags: -Zvirtual-function-elimination -Clto -Copt-level=3

#![allow(dead_code)]

trait Base {
    fn base_method(&self) -> u32;
}

trait Sub: Base {
    fn sub_method(&self) -> u32;
}

struct Concrete;

impl Base for Concrete {
    fn base_method(&self) -> u32 {
        42
    }
}

impl Sub for Concrete {
    fn sub_method(&self) -> u32 {
        100
    }
}

// This function takes a &dyn Sub, upcasts to &dyn Base, then calls base_method.
// Without the fix, LLVM VFE may eliminate base_method from the Base vtable
// because it only sees type_checked_load calls with Sub's typeid, not Base's.
fn call_via_upcast(s: &dyn Sub) -> u32 {
    let b: &dyn Base = s;
    b.base_method()
}

// Also test calling through the subtrait directly.
fn call_sub_directly(s: &dyn Sub) -> u32 {
    s.sub_method()
}

// Test calling base method through the subtrait vtable (no upcast).
fn call_base_through_sub(s: &dyn Sub) -> u32 {
    s.base_method()
}

fn main() {
    let c = Concrete;
    assert_eq!(call_via_upcast(&c), 42);
    assert_eq!(call_sub_directly(&c), 100);
    assert_eq!(call_base_through_sub(&c), 42);
}
