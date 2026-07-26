// Trust: regression test for rust-lang#144371 — foreign ABI unwind register
// preservation. Verifies that when calling an extern "C-unwind" function,
// the codegen emits a volatile frame anchor (optimization barrier) and an
// intermediate landing pad to prevent register corruption during unwind.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -C no-prepopulate-passes
//@ needs-unwind
//@ ignore-windows-msvc (MSVC uses SEH which handles this natively)

#![crate_type = "lib"]

extern "C-unwind" {
    fn foreign_may_unwind();
}

// CHECK-LABEL: @call_foreign_unwind_with_cleanup
// Verify that a volatile store (frame anchor) is emitted before the invoke
// CHECK: store volatile i8
// Verify the invoke targets an intermediate landing pad
// CHECK: invoke void @foreign_may_unwind()
// CHECK-NEXT: to label
// CHECK-SAME: unwind label %{{.*}}foreign_unwind_pad
// Verify the intermediate landing pad has a volatile load (register fence)
// CHECK: {{.*}}foreign_unwind_pad:
// CHECK: landingpad
// CHECK: load volatile i8
#[no_mangle]
pub unsafe fn call_foreign_unwind_with_cleanup() {
    // The Drop impl for String provides a cleanup landing pad
    let _guard = String::from("register preservation test");
    foreign_may_unwind();
}

// CHECK-LABEL: @call_rust_no_intermediate_pad
// Verify that Rust-ABI calls do NOT get the intermediate landing pad
// CHECK-NOT: foreign_unwind_pad
#[no_mangle]
pub fn call_rust_no_intermediate_pad(f: fn()) {
    let _guard = String::from("no intermediate pad needed");
    f();
}
