pub fn same_home() -> bool {
    let value = 7u32;
    core::ptr::eq(&value, &value)
}

pub fn different_homes() -> bool {
    let left = 3u32;
    let right = 7u32;
    core::ptr::eq(&left, &right)
}

pub fn effect_order() -> u32 {
    let value = 7u32;
    let mut order = 0u32;
    let same = ({ order = order * 10 + 1; core::ptr::eq::<u32> })(
        { order = order * 10 + 2; &value },
        { order = order * 10 + 3; &value },
    );
    order * 10 + same as u32
}

mod same_spelling {
    pub fn eq(_left: *const u32, _right: *const u32) -> bool { false }
}

pub fn unrelated_eq() -> bool {
    let value = 7u32;
    same_spelling::eq(&value, &value)
}

// Full pointer equality includes metadata. This route MUST NOT become a thin
// comparison. Its existing unsupported/bodyless status is retained honestly.
#[cfg(not(trust_cg_native))]
pub fn wide(left: *const [u32], right: *const [u32]) -> bool {
    core::ptr::eq(left, right)
}
