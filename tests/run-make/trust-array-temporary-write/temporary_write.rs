#![allow(dead_code, unused_assignments)]

pub fn cast_temporary_write(mut current: [u8; 4], index: usize, value: u8, read: usize) -> u8 {
    (current as [u8; 4])[index] = value;
    current[read]
}

pub fn cast_temporary_index_reseats(
    mut current: [u8; 4], replacement: [u8; 4], index: usize, value: u8, read: usize,
) -> u8 {
    (current as [u8; 4])[{ current = replacement; index }] = value;
    current[read]
}

pub fn cast_temporary_rhs_reseats(
    mut current: [u8; 4], replacement: [u8; 4], index: usize, value: u8, read: usize,
) -> u8 {
    (current as [u8; 4])[index] = { current = replacement; value };
    current[read]
}

pub fn index_promotes_destination(
    mut current: [u8; 4], replacement: [u8; 4], index: usize, read: usize,
) -> u8 {
    current[{ let alias = &mut current; *alias = replacement; index }] = 99;
    current[read]
}

pub fn ordinary_array_write(mut current: [u8; 4], index: usize, value: u8, read: usize) -> u8 {
    current[index] = value;
    current[read]
}
