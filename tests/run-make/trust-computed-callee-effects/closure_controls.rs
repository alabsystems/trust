#![crate_type = "lib"]

pub fn closure_literal() -> fn(u32) -> u32 {
    |value| value
}

pub fn closure_alias() -> fn(u32) -> u32 {
    let function = |value| value;
    function
}

pub fn closure_effect(count: &mut u32) -> fn(u32) -> u32 {
    { *count += 1; |value| value }
}

pub fn closure_literal_cast() -> fn(u32) -> u32 {
    (|value| value) as fn(u32) -> u32
}

pub fn closure_effect_cast(count: &mut u32) -> fn(u32) -> u32 {
    ({ *count += 1; |value| value }) as fn(u32) -> u32
}
