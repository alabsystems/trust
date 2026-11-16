//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency whose `Hasher` and `BuildHasher` panic. Nothing in this file is
//! verified. Consumed by `hasher_must_be_std_all_the_way_down.rs`; see that file for the
//! defect this pins.

use std::hash::{BuildHasher, Hasher};

#[derive(Default)]
pub struct PanicHasher(u64);

impl Hasher for PanicHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let _ = bytes;
        panic!("PanicHasher::write");
    }
}

#[derive(Clone, Default)]
pub struct PanicBuild;

impl BuildHasher for PanicBuild {
    type Hasher = PanicHasher;

    fn build_hasher(&self) -> PanicHasher {
        PanicHasher(0)
    }
}
