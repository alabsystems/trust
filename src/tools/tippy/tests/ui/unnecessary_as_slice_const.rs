// Trust: rustfix must keep the explicit slice borrow when Vec dereferencing is not const.
#![warn(clippy::unnecessary_as_slice)]
#![allow(clippy::const_is_empty, clippy::ptr_arg)]
#![expect(unused)]

// Direct Vec methods remain valid const-context suggestions.
const fn const_vec_methods(values: &mut Vec<u32>) -> (usize, bool) {
    let len = values.as_slice().len();
    //~^ unnecessary_as_slice
    let empty = values.as_mut_slice().is_empty();
    //~^ unnecessary_as_slice
    (len, empty)
}

// Removing either explicit conversion requires non-const Vec dereferencing.
const fn const_last(values: &Vec<u32>) -> Option<&u32> {
    values.as_slice().last()
}

const fn const_split(values: &Vec<u32>) -> (&[u32], &[u32]) {
    values.as_slice().split_at(0)
}

const fn const_split_mut(values: &mut Vec<u32>) -> (&mut [u32], &mut [u32]) {
    values.as_mut_slice().split_at_mut(0)
}

// Runtime code can still use Vec's ordinary Deref implementation.
fn runtime_slice_methods(values: &mut Vec<u32>) {
    let _ = values.as_slice().last();
    //~^ unnecessary_as_slice
    let _ = values.as_mut_slice().split_at_mut(0);
    //~^ unnecessary_as_slice
}

fn main() {}
