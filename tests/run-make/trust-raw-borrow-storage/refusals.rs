#![crate_type = "lib"]

#[repr(C, packed)]
pub struct Packed {
    pub pad: u8,
    pub value: u32,
}

// Raw address formation is legal here; the producer's packed-place fence refuses it.
pub fn packed_const(value: &Packed) -> *const u32 {
    &raw const value.value
}

pub fn packed_mut(value: &mut Packed) -> *mut u32 {
    &raw mut value.value
}

// Collecting this address must not grant a raw-pointer parameter a storage slot.
pub fn raw_parameter_address(value: *const u32) -> *const *const u32 {
    &raw const value
}

// Since e0e9606dab a typed INTEGER load through an unchanged incoming raw address
// lowers without borrow rights (`raw_parameter_integer_deref`); every other pointee
// still has no modeled storage, so the refusal is pinned on `bool`.
pub fn raw_parameter_deref(value: *const bool) -> bool {
    unsafe { *value }
}

pub fn raw_parameter_integer_deref(value: *const u32) -> u32 {
    unsafe { *value }
}

// The frame-local raw address is legal to form, but cannot escape this producer.
pub fn raw_escape(value: u32) -> *const u32 {
    &raw const value
}
