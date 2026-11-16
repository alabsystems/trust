#![allow(dead_code, unused_variables)]

pub fn constant_prefix_and_len() -> usize {
    let [first, rest @ ..] = [7u8; 2049];
    first as usize + rest.len()
}

pub fn constant_prefix_suffix_and_len() -> usize {
    let [first, rest @ .., last] = [7u8; 2049];
    first as usize + last as usize + rest.len()
}

pub fn runtime_repeat_once() -> usize {
    let mut n = 3u8;
    let [first, rest @ .., last] = [{ n += 1; n }; 2049];
    n as usize * 10000 + first as usize * 100 + last as usize * 10 + rest.len()
}

pub fn borrowed_rest_copy() -> u32 {
    let source = [7u8; 4];
    let [first, mut rest @ ..] = source;
    {
        let r = &mut rest;
        r[0] = 9;
    }
    {
        let r = &mut rest;
        r[1] = 11;
    }
    first as u32 * 100000 + source[1] as u32 * 10000 + rest[0] as u32 * 1000
        + rest[1] as u32 * 100 + rest[2] as u32 * 10 + rest.len() as u32
}

pub fn pointer_rest_refused(pointer: *const u8) -> usize {
    let [first, rest @ ..] = [pointer; 3];
    rest.len()
}
