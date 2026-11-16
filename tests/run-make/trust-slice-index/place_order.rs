#![allow(dead_code, unused_assignments)]

pub fn reseat_index<'a>(a: &'a [u8], b: &'a [u8], index: usize) -> u8 {
    let mut current = a;
    current[{ current = b; index }]
}

pub fn index_value_is_captured(bytes: &[u8], mut index: usize) -> u8 {
    bytes[{ let old = index; index = 0; old }]
}
