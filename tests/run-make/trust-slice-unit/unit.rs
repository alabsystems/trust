#![allow(dead_code, unused_assignments)]

pub fn read_unit(values: &[()], index: usize) {
    values[index]
}

pub fn unit_index_effect(values: &[()], mut index: usize) -> usize {
    values[{
        let previous = index;
        index = 0;
        previous
    }];
    index
}

pub fn reseat_unit(a: &[()], b: &[()], index: usize) {
    let mut current = a;
    current[{
        current = b;
        index
    }]
}

pub fn read_generic<T: Copy>(values: &[T], index: usize) -> T {
    values[index]
}

pub fn read_nonunit_zst(values: &[[(); 0]], index: usize) -> [(); 0] {
    values[index]
}
