extern crate shared_a;
extern crate shared_b;

#[inline(never)]
pub fn call_both(x: i32) -> i32 {
    shared_a::contracted(x) + shared_b::contracted(x)
}

#[inline(never)]
pub fn call_both_generic(x: i32) -> i32 {
    shared_a::generic(x) + shared_b::generic(x)
}

#[inline(never)]
pub fn call_distinct_rendered_args(x: i32) -> i32 {
    shared_a::arg_identity(shared_a::Marker(x)).0
        + shared_a::arg_identity(shared_b::Marker(x)).0
}

#[inline(never)]
pub fn call_contracted_generic(x: i32) -> i32 {
    shared_a::contracted_generic(x)
}

#[inline(never)]
pub fn concrete_cmp(a: i32, b: i32, x: u8, y: u8) -> (i32, i32, u8, u8) {
    (core::cmp::min(a, b), core::cmp::max(a, b), x.min(y), x.max(y))
}
