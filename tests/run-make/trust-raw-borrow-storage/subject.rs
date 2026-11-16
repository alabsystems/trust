#![crate_type = "lib"]

pub fn parameter_ref_mut(mut value: u32) -> u32 {
    let p = &mut value;
    *p = 7;
    value
}

pub fn parameter_raw_mut(mut value: u32) -> u32 {
    let p = &raw mut value;
    unsafe { *p = 7; }
    value
}

pub fn local_ref_mut(value: u32) -> u32 {
    let mut local = value;
    let p = &mut local;
    *p = 7;
    local
}

pub fn local_raw_mut(value: u32) -> u32 {
    let mut local = value;
    let p = &raw mut local;
    unsafe { *p = 7; }
    local
}

pub fn parameter_ref_const(value: u32) -> u32 {
    let p = &value;
    *p
}

pub fn parameter_raw_const(value: u32) -> u32 {
    let p = &raw const value;
    unsafe { *p }
}

pub fn local_ref_const(value: u32) -> u32 {
    let local = value;
    let p = &local;
    *p
}

pub fn local_raw_const(value: u32) -> u32 {
    let local = value;
    let p = &raw const local;
    unsafe { *p }
}

// An existing raw const address must still observe a later ordinary assignment.
pub fn parameter_raw_const_alias(mut value: u32) -> u32 {
    let p = &raw const value;
    value = 7;
    unsafe { *p }
}

pub fn local_raw_const_alias(value: u32) -> u32 {
    let mut local = value;
    let p = &raw const local;
    local = 7;
    unsafe { *p }
}
