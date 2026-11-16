#![allow(dead_code, unused_assignments)]

pub fn reseat_deref_pointee(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut current = a;
    let pointer = &mut current;
    (*pointer)[{
        *pointer = b;
        index
    }]
}

pub fn reseat_tuple_field(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut holder = (a,);
    holder.0[{
        holder.0 = b;
        index
    }]
}

pub fn change_pointer_not_pointee(a: [u8; 4], b: [u8; 4], index: usize) -> u8 {
    let mut pointer = &a;
    (*pointer)[{
        pointer = &b;
        index
    }]
}

fn make_array(count: &mut usize) -> [u8; 4] {
    *count = (*count).wrapping_add(1);
    [11, 22, 33, 44]
}

pub fn call_base_runs_once() -> u8 {
    let mut count = 0;
    make_array(&mut count)[{
        let index = count;
        count = 0;
        index
    }]
}
