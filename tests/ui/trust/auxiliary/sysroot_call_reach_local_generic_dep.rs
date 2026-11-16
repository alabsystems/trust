//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! Trust: a concrete generic dispatch can reach this dependency even when its
//! receiver type is foundational. Keep both a constant and an actual panic: the
//! reach rule must not confuse locality of `u32` with locality of its impl.

pub trait Constant {
    fn act(&self) -> u32;
}

impl Constant for u32 {
    #[inline(never)]
    fn act(&self) -> u32 {
        1
    }
}

pub trait Panics {
    fn act(&self) -> u32;
}

impl Panics for u32 {
    #[inline(never)]
    fn act(&self) -> u32 {
        panic!("a dependency impl reached through the local generic iterator")
    }
}

// The controls may name a dependency type without executing dependency code.
// It deliberately has no destructor or trait implementations.
pub struct Plain(pub u32);
