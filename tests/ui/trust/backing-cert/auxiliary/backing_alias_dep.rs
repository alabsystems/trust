//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency outside the sysroot that keeps a raw `*mut T` and WRITES through it from
//! `&self` (final review of `tinv/alab-blockers`): its field must keep its raw-pointer
//! reading in the escape census, not the by-value pointee reading the census gives to
//! authenticated sysroot types such as `Vec` and `Box`.

pub struct Alias<T>(*mut T);

impl<T> Alias<T> {
    pub fn from_box(b: Box<T>) -> Self {
        Alias(Box::into_raw(b))
    }

    pub fn poke(&self) {
        unsafe { core::ptr::write_bytes(self.0 as *mut u8, 0xff, core::mem::size_of::<T>()) }
    }

    pub fn get(&self) -> &T {
        unsafe { &*self.0 }
    }
}

/// A third-party handle over an `UnsafeCell<T>` that writes through `&self` (round 4).
pub struct Shared<T>(core::cell::UnsafeCell<T>);

impl<T> Shared<T> {
    pub fn new(t: T) -> Self {
        Shared(core::cell::UnsafeCell::new(t))
    }

    pub fn poke(&self) {
        unsafe { core::ptr::write_bytes(self.0.get() as *mut u8, 0xff, core::mem::size_of::<T>()) }
    }

    pub fn get(&self) -> &T {
        unsafe { &*self.0.get() }
    }
}

/// Overwrites the contents of a sysroot `Cell` through a shared reference (round 4).
pub fn zap<T>(c: &core::cell::Cell<T>) {
    unsafe { c.as_ptr().write_bytes(0xff, 1) }
}
