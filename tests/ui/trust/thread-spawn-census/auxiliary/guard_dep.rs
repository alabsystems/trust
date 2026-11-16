//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A guard whose `Drop` calls the callback it borrows: external code that
//! invokes a `&mut dyn FnMut()` from its drop glue (MIR in metadata, since
//! `#[inline]`).

pub struct OnDrop<'a>(pub &'a mut dyn FnMut());

impl Drop for OnDrop<'_> {
    #[inline]
    fn drop(&mut self) {
        (self.0)()
    }
}
