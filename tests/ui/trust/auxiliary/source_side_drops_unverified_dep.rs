//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so NOTHING in this file is verified. Each type's
//! `Drop` panics when its field is `7`, and each reaches a downstream
//! `collect`/`extend` only as a drop that runs on the SOURCE side, INSIDE that call:
//!  * `DropBuild`, a hash collection's `BuildHasher`: `HashMap::into_iter` and
//!    `HashSet::into_iter` drop it;
//!  * `ErrBomb`, a `Result`'s `Err` payload: `Result::into_iter` is `self.ok()`;
//!  * `Bomb`, an item: a `Take`/`Zip` remainder, or an item a `Skip`, `StepBy` or
//!    `Filter` discards, even through `&mut`.
//! Used by `collect_extend_source_side_drops.rs` and its run twin
//! `collect_extend_source_side_drops_run.rs`.

use std::hash::{BuildHasher, DefaultHasher};

#[derive(Default)]
pub struct DropBuild(pub u8);

impl Drop for DropBuild {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("hasher drop bomb")
        }
    }
}

impl BuildHasher for DropBuild {
    type Hasher = DefaultHasher;
    fn build_hasher(&self) -> DefaultHasher {
        DefaultHasher::new()
    }
}

pub struct ErrBomb(pub u8);

impl Drop for ErrBomb {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("err drop bomb")
        }
    }
}

pub struct Bomb(pub u8);

impl Drop for Bomb {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("item drop bomb")
        }
    }
}
