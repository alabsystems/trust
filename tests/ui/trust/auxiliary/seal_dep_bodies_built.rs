//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of the `clean_island_seal_check_build_*_holds.rs` fixtures:
//! the source of `seal_dep_bodies_checked.rs`, built in full, so that the MIR
//! of its generic fns is in its metadata and its plain fns are exported.
//! Safe, and sound: nothing here writes what it is handed.

use std::marker::PhantomData;

/// Holds what it is given; its drop reads it and writes nothing.
pub struct Proxy<T> {
    pub held: T,
}

impl<T> Drop for Proxy<T> {
    fn drop(&mut self) {
        let _ = std::mem::size_of_val(&self.held);
    }
}

/// A number tagged with a type: its clone copies the number.
pub struct Tag<T> {
    pub n: u32,
    pub of: PhantomData<T>,
}

impl<T> Clone for Tag<T> {
    fn clone(&self) -> Self {
        Tag { n: self.n, of: PhantomData }
    }
}

/// Shows its number, never what it holds.
pub struct Shown<T> {
    pub n: u32,
    pub held: T,
}

impl<T> std::fmt::Debug for Shown<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Shown({})", self.n)
    }
}

/// A plain fn: counts nothing, writes nothing.
pub fn tick() -> u32 {
    1
}

/// `tick`, as a constant's value.
pub const TICK: fn() -> u32 = tick;

/// Measures what it is handed, after calling `tick`.
pub async fn measure<T>(held: T) -> usize {
    let _ = tick();
    std::mem::size_of_val(&held)
}

/// The same, calling `tick` through the constant `TICK`.
pub async fn measure_through<T>(held: T) -> usize {
    let _ = TICK();
    std::mem::size_of_val(&held)
}
