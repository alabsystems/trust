#[inline(never)]
pub fn read(value: &u32) -> u32 {
    *value
}

#[inline(never)]
pub fn bump(value: &mut u32) {
    *value = value.wrapping_add(7);
}

pub fn shared_item(n: u32) -> u32 {
    let mut sum = 0u32;
    for item in 0..n {
        sum = sum.wrapping_add(read(&item));
    }
    sum
}

pub fn mutated_item(n: u32) -> u32 {
    let mut sum = 0u32;
    for mut item in 0..n {
        bump(&mut item);
        sum = sum.wrapping_add(item);
    }
    sum
}
