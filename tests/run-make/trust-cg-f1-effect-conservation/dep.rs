//! The cross-crate drop case of the 2026-10-01 producer review: `Fd`'s destructor counts its
//! runs.
use std::sync::atomic::{AtomicU32, Ordering};

pub static CLOSED: AtomicU32 = AtomicU32::new(0);

pub struct Fd(pub i32);

impl Drop for Fd {
    fn drop(&mut self) {
        CLOSED.fetch_add(1, Ordering::SeqCst);
    }
}
