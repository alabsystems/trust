// Trust: native regression for the shared-storage reborrow admission boundary.
#![crate_type = "lib"]

pub struct Wide { pub number: f64, pub count: u32 }

#[inline(never)]
pub fn same_wide(left: &Wide, right: &Wide) -> bool { std::ptr::eq(left, right) }

#[inline(never)]
pub fn bump(value: &mut i32) { *value = value.wrapping_add(1); }

// The mutable borrow is a direct reborrow of a different local, just as rustc's
// Range::next adjustment is &mut *(&mut iter) in the formatting-loop fixture.
#[inline(never)]
pub fn shared_parameter_with_direct_reborrow(value: Wide, count: i32) -> bool {
    let mut other = count;
    let before = same_wide(&value, &value);
    bump(&mut *(&mut other));
    before && same_wide(&value, &value)
}

#[inline(never)]
pub fn shared_local_with_direct_reborrow(number: f64, count: i32) -> bool {
    let value = Wide { number, count: 7 };
    let mut other = count;
    let before = same_wide(&value, &value);
    bump(&mut *(&mut other));
    before && same_wide(&value, &value)
}

#[inline(never)]
pub fn same_raw_pointer_location(left: &*const u32, right: &*const u32) -> bool {
    std::ptr::eq(left, right)
}

// Borrow the pointer object, not the allocation it might address. A null raw
// pointer remains an ordinary value, and no dereference is performed here.
#[inline(never)]
pub fn shared_raw_pointer_parameter(value: *const u32) -> bool {
    same_raw_pointer_location(&value, &value)
        && same_raw_pointer_location(&value, &value)
}
