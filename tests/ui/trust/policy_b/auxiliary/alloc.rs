//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency SPOOFING the sysroot crate name `alloc` (its file name makes its
//! declared crate name `alloc`), built verify-OFF the way Targo compiles every
//! dependency unit. `boom` PANICS. Its declared crate name is `alloc`, but its
//! `CrateNum` is NOT the real alloc's and it owns NO sysroot lang item — so the
//! authenticated foundational check (`crate_is_authentic_foundational`, by
//! lang-item ownership) must NOT trust it. It exists so the caller can prove a
//! `--crate-name alloc` spoof stays fatal beside a `println!`.
#[inline(never)]
pub fn boom(x: i32) -> i32 {
    if x >= 0 {
        panic!("spoofed-alloc boom: {}", x);
    }
    x
}

/// A type with a PANICKING `Drop`, in a crate whose declared name is `alloc` but
/// whose `CrateNum` is not the real alloc's and which owns no sysroot lang item.
/// The authenticated drop-glue check must NOT treat its `Drop` as foundational.
pub struct Bomb(pub i32);
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("spoofed-alloc Bomb dropped: {}", self.0);
    }
}
