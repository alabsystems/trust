#![crate_type = "lib"]

pub fn parameter_direct(mut value: u32) -> u32 {
    let reference = &mut value;
    *reference = 7;
    *reference
}

pub fn parameter_cast(mut value: u32) -> u64 {
    ({
        let reference = &mut value;
        *reference = 7;
        *reference
    }) as u64
}

pub fn local_direct(value: u32) -> u32 {
    let mut local = value;
    let reference = &mut local;
    *reference = 7;
    *reference
}

pub fn local_cast(value: u32) -> u64 {
    let mut local = value;
    ({
        let reference = &mut local;
        *reference = 7;
        *reference
    }) as u64
}

// This cast already belongs to the assembled direct IR as a saturating operation.
// Re-deriving MIR still refuses it outside the existing integer-only cast fragment.
pub fn saturating_float(value: f64) -> i32 {
    value as i32
}
