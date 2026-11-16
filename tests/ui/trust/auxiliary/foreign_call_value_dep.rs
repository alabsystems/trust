//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! `foreign_call_value_refutation_held.rs`'s foreign crate: a length the caller
//! cannot see into, and a value it has no body for.
pub struct Cap {
    v: Vec<u8>,
}

impl Cap {
    pub fn new() -> Cap {
        Cap { v: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.v.len()
    }
}

pub fn val() -> u8 {
    7
}
