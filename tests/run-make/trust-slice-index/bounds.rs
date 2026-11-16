#![allow(dead_code)]

pub fn read_slice(bytes: &[u8], index: usize) -> u8 {
    bytes[index]
}

pub fn read_zst(values: &[()], index: usize) {
    values[index]
}

pub fn write_slice(bytes: &mut [u8], index: usize, value: u8) {
    bytes[index] = value;
}

pub fn read_array(bytes: [u8; 4], index: usize) -> u8 {
    bytes[index]
}
