//@ compile-flags: -Ztrust-verify=off
#![crate_type = "lib"]
// Defines a C symbol that a dependent crate imports by `#[link_name]`.
static T: [i32; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

#[no_mangle]
pub extern "C" fn dep_close(fd: i32) -> i32 {
    T[fd as usize]
}
