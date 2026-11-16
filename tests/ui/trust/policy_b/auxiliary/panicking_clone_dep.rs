//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! An unverified dependency whose `Clone` panics (review round 63: `Cloned` inside an
//! erased extend ran it).
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Ck(pub u8);

impl Clone for Ck {
    fn clone(&self) -> Ck {
        if self.0 == 7 {
            panic!("Ck::clone panics")
        }
        Ck(self.0)
    }
}

/// `Copy`, yet its `Clone` is hand-written and panics (review round 64: `Vec`'s
/// `Extend<&T>` clones each item itself).
#[derive(Copy, PartialEq, Eq, Debug)]
pub struct CopyCk(pub u8);

impl Clone for CopyCk {
    fn clone(&self) -> CopyCk {
        if self.0 == 7 {
            panic!("CopyCk::clone panics")
        }
        CopyCk(self.0)
    }
}
