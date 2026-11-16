use std::cell::Cell;

pub struct Counter { pub hits: Cell<i32> }

#[inline(never)]
pub fn make(value: i32) -> Counter { Counter { hits: Cell::new(value) } }

#[inline(never)]
pub fn increment(counter: &Counter) {
    counter.hits.set(counter.hits.get().wrapping_add(1));
}

#[inline(never)]
pub fn read_after_write(value: i32) -> i32 {
    let counter = make(value);
    increment(&counter);
    counter.hits.get()
}

#[inline(never)]
pub fn bump_scalar(value: &mut i32) { *value = value.wrapping_add(1); }

#[inline(never)]
pub fn same_scalar(left: &i32, right: &i32) -> bool { std::ptr::eq(left, right) }

#[inline(never)]
pub fn shared_identity_after_mutation(value: i32) -> bool {
    let mut local = value;
    bump_scalar(&mut local);
    same_scalar(&local, &local)
}

#[inline(never)]
pub fn copied_value_has_distinct_storage(value: i32) -> bool {
    let mut local = value;
    bump_scalar(&mut local);
    same_scalar(&local, &(local as i32))
}

#[inline(never)]
pub fn read_scalar(value: &i32) -> i32 { *value }

#[inline(never)]
pub fn frozen_control(value: i32) -> i32 {
    let local = value;
    read_scalar(&local)
}

#[inline(never)]
pub fn bump_cell(cell: &Cell<i32>) { cell.set(cell.get().wrapping_add(1)); }

#[inline(never)]
pub fn read_cell(cell: &Cell<i32>) -> i32 { cell.get() }

// No field access or mutable borrow requests promotion of this local.
#[inline(never)]
pub fn read_after_hidden_write(value: i32) -> i32 {
    let cell = Cell::new(value);
    bump_cell(&cell);
    read_cell(&cell)
}

#[inline(never)]
pub fn shared_identity_without_mutation(value: i32) -> bool {
    let local = value;
    same_scalar(&local, &local)
}

#[inline(never)]
pub fn copied_value_without_mutation(value: i32) -> bool {
    let local = value;
    same_scalar(&local, &(local as i32))
}

#[inline(never)]
pub fn by_value_cell_parameter(cell: Cell<i32>) -> i32 {
    bump_cell(&cell);
    read_cell(&cell)
}

#[inline(never)]
pub fn scalar_reassignment(value: i32) -> i32 {
    let mut local = value;
    let before = read_scalar(&local);
    local = before.wrapping_add(1);
    read_scalar(&local)
}

#[inline(never)]
pub fn shared_borrow_in_match_guard(value: i32) -> i32 {
    let local = value;
    match value {
        0 if read_scalar(&local) >= 0 => 1,
        _ => 0,
    }
}

#[inline(never)]
pub fn read_f32(value: &f32) -> f32 { *value }

#[inline(never)]
pub fn read_f64(value: &f64) -> f64 { *value }

#[inline(never)]
pub fn same_f64(left: &f64, right: &f64) -> bool { std::ptr::eq(left, right) }

#[inline(never)]
pub fn shared_f32_reassignment(initial: f32, replacement: f32) -> f32 {
    let mut local = initial;
    let _before = read_f32(&local);
    local = replacement;
    read_f32(&local)
}

#[inline(never)]
pub fn shared_f64_reassignment(initial: f64, replacement: f64) -> f64 {
    let mut local = initial;
    let _before = read_f64(&local);
    local = replacement;
    read_f64(&local)
}

#[inline(never)]
pub fn shared_f64_identity(value: f64) -> bool {
    let local = value;
    same_f64(&local, &local)
}

#[inline(never)]
pub fn shared_f64_temporary(value: f64) -> bool {
    let local = value;
    same_f64(&local, &(local as f64))
}

#[inline(never)]
pub fn read_empty_array(value: &[i32; 0]) -> usize { value.len() }

#[inline(never)]
pub fn shared_empty_array() -> usize {
    let local = [];
    let _before = read_empty_array(&local);
    read_empty_array(&local)
}

pub struct Wide { pub number: f64, pub count: u32 }

#[inline(never)]
pub fn same_wide(left: &Wide, right: &Wide) -> bool { std::ptr::eq(left, right) }

#[inline(never)]
pub fn shared_wide_parameter(value: Wide) -> bool { same_wide(&value, &value) }

#[inline(never)]
pub fn shared_wide_local(number: f64) -> bool {
    let local = Wide { number, count: 7 };
    same_wide(&local, &local)
}

#[inline(never)]
pub fn same_unit(left: &(), right: &()) -> bool { std::ptr::eq(left, right) }

#[inline(never)]
pub fn shared_unit_parameter(value: ()) -> bool { same_unit(&value, &value) }

#[inline(never)]
pub fn read_reference(value: &&i32) -> i32 { **value }

#[inline(never)]
pub fn shared_reference_parameter(value: &i32) -> i32 {
    let first = read_reference(&value);
    let second = read_reference(&value);
    first.wrapping_add(second).wrapping_add(*value)
}

#[inline(never)]
pub fn shared_reference_deref(value: &i32) -> i32 {
    let outer = &value;
    **outer
}

pub enum Payload { Number(i32), Empty }

#[inline(never)]
pub fn same_reference_address(left: &&i32, right: &&i32) -> bool { std::ptr::eq(left, right) }

#[inline(never)]
pub fn shared_payload_reference(left: &Payload, right: &Payload) -> bool {
    match (left, right) {
        (Payload::Number(a), Payload::Number(b)) => {
            same_reference_address(&a, &a) && *a == *b
        }
        _ => false,
    }
}
