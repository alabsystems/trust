#![allow(unused_assignments)]

pub fn cast_reference_value(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut reference = &a;
    (*(reference as &[u8; 4]))[{
        reference = &b;
        index
    }]
}

pub fn reference_place(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut reference = &a;
    (*reference)[{
        reference = &b;
        index
    }]
}

pub fn block_array_value(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut current = a;
    ({ current })[{
        current = b;
        index
    }]
}

pub fn cast_slice_value(a: &[u8], b: &[u8], index: usize) -> u8 {
    let mut current = a;
    (current as &[u8])[{
        current = b;
        index
    }]
}

pub fn cast_array_value(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut current = a;
    (current as [u8; 4])[{
        current = b;
        index
    }]
}
