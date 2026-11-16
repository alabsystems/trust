// Trust: native regression for the shared-storage reborrow admission boundary.
#![crate_type = "lib"]

pub struct Wide { pub number: f64, pub count: u32 }

#[inline(never)]
fn read_wide(value: &Wide) -> f64 { value.number }
#[inline(never)]
fn bump(value: &mut i32) { *value = value.wrapping_add(1); }
#[inline(never)]
fn touch_wide(_: &mut Wide) {}
#[inline(never)]
fn read_float(value: &f64) -> f64 { *value }
#[inline(never)]
fn read_empty(value: &[i32; 0]) -> usize { value.len() }

pub fn same_root_reborrow(mut value: Wide) -> f64 {
    touch_wide(&mut *(&mut value));
    read_wide(&value)
}

// A reference parameter's pointee has no syntactically known local root.
pub fn unknown_root_reborrow(value: Wide, other: &mut i32) -> f64 {
    bump(&mut *other);
    read_wide(&value)
}

pub fn raw_root(value: Wide, count: i32) -> f64 {
    let mut other = count;
    let _raw = &raw mut other;
    read_wide(&value)
}

pub fn ref_mut_pattern(value: Wide, mut count: i32) -> f64 {
    let ref mut other = count;
    bump(other);
    read_wide(&value)
}

// The original float and empty-array lanes still require no mutable borrow
// anywhere in the body, even when that borrow has a different known root.
pub fn float_local_with_disjoint_mutation(number: f64, count: i32) -> f64 {
    let value = number;
    let mut other = count;
    bump(&mut other);
    read_float(&value)
}

pub fn float_parameter_with_disjoint_mutation(value: f64, count: i32) -> f64 {
    let mut other = count;
    bump(&mut other);
    read_float(&value)
}

pub fn empty_array_with_disjoint_mutation(count: i32) -> usize {
    let value = [];
    let mut other = count;
    bump(&mut other);
    read_empty(&value)
}
