#![allow(dead_code, unused_assignments)]

pub fn rhs_reseats_array(
    mut current: [u8; 4],
    replacement: [u8; 4],
    index: usize,
    read: usize,
) -> u8 {
    current[index] = {
        current = replacement;
        99
    };
    current[read]
}

pub fn index_reseats_array(
    mut current: [u8; 4],
    replacement: [u8; 4],
    index: usize,
    read: usize,
) -> u8 {
    current[{
        current = replacement;
        index
    }] = 99;
    current[read]
}

pub fn rhs_before_index(mut current: [u8; 4], index: usize) -> u8 {
    let mut position = index;
    current[{
        let captured = position;
        position = 0;
        captured
    }] = {
        position = 2;
        99
    };
    current[2]
}

pub fn rhs_value_is_captured(mut current: [u8; 4], index: usize, value: u8) -> u8 {
    let mut incoming = value;
    current[{
        incoming = 77;
        index
    }] = incoming;
    current[index]
}

pub fn pure_array_write(mut current: [u8; 4], index: usize, value: u8, read: usize) -> u8 {
    current[index] = value;
    current[read]
}

pub fn const_write_preserves_rhs_reseat(
    mut current: [u8; 4],
    replacement: [u8; 4],
    read: usize,
) -> u8 {
    current[1] = {
        current = replacement;
        99
    };
    current[read]
}
