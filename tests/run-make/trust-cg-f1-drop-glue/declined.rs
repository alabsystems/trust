//! A destructor the producer declines (an atomic read-modify-write): the glue has no admitted
//! destructor body to call, so neither the glue nor the drop of an `A` resolves.
use std::sync::atomic::{AtomicU32, Ordering};
pub static LOG: AtomicU32 = AtomicU32::new(0);
pub struct A(pub u32);
impl Drop for A {
    fn drop(&mut self) {
        LOG.fetch_add(self.0, Ordering::SeqCst);
    }
}
#[inline(never)]
pub fn make2(x: u32) -> u32 {
    let _a = A(x);
    x ^ 2
}
