#![crate_type = "lib"]

pub fn copied_before_range_effect() -> u32 {
    let mut array = [7u32];
    let slice = &(array as [u32; 1])[{ array[0] = 9; .. }];
    slice[0]
}

#[allow(unreachable_code)]
pub fn returning_range_stops_evaluation() -> u32 {
    let array = [7u32];
    let _slice = &array[{ return 9; .. }];
    0
}
