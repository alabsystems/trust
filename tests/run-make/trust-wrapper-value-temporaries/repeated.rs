#![crate_type = "lib"]

pub fn parameter_repeated_unsize(mut value: u32) -> u32 {
    let array = [{ let p = &mut value; *p = 7; *p }];
    let left: &[u32] = &array;
    let right: &[u32] = &array;
    left[0] ^ right[0]
}

pub fn local_repeated_full_range(value: u32) -> u32 {
    let mut local = value;
    let array = [{ let p = &mut local; *p = 7; *p }];
    let left: &[u32] = &array[..];
    let right: &[u32] = &array[..];
    left[0] ^ right[0]
}

pub fn parameter_copied_unsize(mut value: u32) -> u32 {
    let array = [{ let p = &mut value; *p = 7; *p }];
    let left: &[u32] = &array;
    let right: &[u32] = &(array as [u32; 1]);
    left[0] ^ right[0]
}

pub fn local_copied_full_range(value: u32) -> u32 {
    let mut local = value;
    let array = [{ let p = &mut local; *p = 7; *p }];
    let left: &[u32] = &array[..];
    let right: &[u32] = &(array as [u32; 1])[..];
    left[0] ^ right[0]
}

pub struct Wide { number: f64, count: u32 }

pub fn shared_struct_repeated_unsize(value: f64) -> u32 {
    let array = [Wide { number: value, count: 7 }];
    let left: &[Wide] = &array;
    let right: &[Wide] = &array;
    left[0].count ^ right[0].count
}

pub fn caller_array_copy(value: &[u32; 1]) -> u32 {
    let left: &[u32] = value;
    let right: &[u32] = &(*value as [u32; 1]);
    left[0] ^ right[0]
}
