#![allow(dead_code, unused_assignments)]

pub fn reseat_array(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut current = a;
    current[{
        current = b;
        index
    }]
}

pub fn array_index_value_is_captured(bytes: [u8; 4], mut index: usize) -> u8 {
    bytes[{
        let previous = index;
        index = 0;
        previous
    }]
}

pub fn reseat_array_through_alias(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut current = a;
    let alias = &mut current;
    current[{
        *alias = b;
        index
    }]
}
