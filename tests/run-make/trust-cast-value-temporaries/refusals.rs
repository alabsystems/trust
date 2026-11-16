#![crate_type = "lib"]

// A direct raw-pointer parameter may expose its address, but a retyped pointer
// expression does not acquire that parameter's provenance permission.
pub fn retyped_pointer_to_integer(value: *const u32) -> usize {
    (value as *const u8) as usize
}

// The existing integer-to-pointer lane admits unsigned integers only.
pub fn signed_integer_to_pointer(value: isize) -> *const u8 {
    value as *const u8
}
