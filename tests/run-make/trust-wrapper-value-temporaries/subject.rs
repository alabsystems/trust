#![crate_type = "lib"]
#![feature(type_ascription)]

pub fn parameter_array_bound(mut value: u32) -> u32 {
    let array = [{ let p = &mut value; *p = 7; *p }];
    let slice: &[u32] = &array;
    slice[0]
}

pub fn parameter_unsize(mut value: u32) -> u32 {
    let slice: &[u32] = &[{ let p = &mut value; *p = 7; *p }];
    slice[0]
}

pub fn local_array_bound(value: u32) -> u32 {
    let mut local = value;
    let array = [{ let p = &mut local; *p = 7; *p }];
    let slice: &[u32] = &array;
    slice[0]
}

pub fn local_unsize(value: u32) -> u32 {
    let mut local = value;
    let slice: &[u32] = &[{ let p = &mut local; *p = 7; *p }];
    slice[0]
}

pub fn parameter_value_direct(mut value: u32) -> u32 {
    let p = &mut value;
    *p = 7;
    *p
}

pub fn parameter_value_ascribed(mut value: u32) -> u32 {
    type_ascribe!({ let p = &mut value; *p = 7; *p }, u32)
}

pub fn local_value_direct(value: u32) -> u32 {
    let mut local = value;
    let p = &mut local;
    *p = 7;
    *p
}

pub fn local_value_ascribed(value: u32) -> u32 {
    let mut local = value;
    type_ascribe!({ let p = &mut local; *p = 7; *p }, u32)
}

pub fn parameter_place_direct(mut value: u32) -> u32 {
    *{ let p = &mut value; *p = 7; p }
}

pub fn parameter_place_ascribed(mut value: u32) -> u32 {
    type_ascribe!(*{ let p = &mut value; *p = 7; p }, u32)
}

pub fn local_place_direct(value: u32) -> u32 {
    let mut local = value;
    *{ let p = &mut local; *p = 7; p }
}

pub fn local_place_ascribed(value: u32) -> u32 {
    let mut local = value;
    type_ascribe!(*{ let p = &mut local; *p = 7; p }, u32)
}
