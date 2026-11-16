//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A registry that keeps a `'static` callback and calls it later from a
//! function given nothing (MIR in metadata, since `#[inline]`).

static mut SLOT: Option<&'static mut dyn FnMut()> = None;

#[inline]
pub fn register(f: &'static mut dyn FnMut()) {
    unsafe { SLOT = Some(f) }
}

#[inline]
pub fn fire_registered() {
    if let Some(f) = unsafe { (*std::ptr::addr_of_mut!(SLOT)).as_mut() } {
        f()
    }
}
