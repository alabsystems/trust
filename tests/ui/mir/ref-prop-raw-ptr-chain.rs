//@ run-pass
// Trust: Regression test for rust-lang#132898
// ReferencePropagation must not propagate through raw pointer chains
// to direct places, as this changes aliasing semantics from
// SharedReadWrite to Unique, invalidating live borrows.
//
// The fix prevents the optimization, not the code itself, so the
// program compiles and runs successfully.

fn main() {
    let mut x: i32 = 42;
    let r1: &mut i32 = &mut x;
    let raw: *mut i32 = r1 as *mut i32;
    // After this point, r1's borrow should be considered potentially
    // invalidated by the raw pointer. ReferencePropagation must not
    // replace uses of `*raw` with direct access to `x`, as that would
    // change the access semantics and could invalidate other borrows.
    unsafe {
        *raw = 100;
    }
    assert_eq!(x, 100);
}
