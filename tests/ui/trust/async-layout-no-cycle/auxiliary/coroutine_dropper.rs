//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! Generic code that drops a value of its type parameter in place: what a
//! future combinator does with the future it owns (futures-util's `Map` via
//! pin-project-lite's `project_replace`).

pub fn drop_it<T>(t: T) {
    let mut m = core::mem::ManuallyDrop::new(t);
    unsafe { core::mem::ManuallyDrop::drop(&mut m) }
}

pub fn replace_in_place<T>(slot: &mut T, new: T) {
    unsafe {
        core::ptr::drop_in_place(slot);
        core::ptr::write(slot, new);
    }
}
