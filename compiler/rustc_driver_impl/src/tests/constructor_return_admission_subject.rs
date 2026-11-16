// Trust: unchanged original sources, exercised through current TyCtxt/preopt MIR.
// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
#![allow(dead_code)]

#[path = "../../../../tests/ui/trust/native_bundle_member_link_symbols_distinct.rs"]
mod members;
#[path = "../../../../tests/ui/trust/native_constructor_return_same_short_types_prove.rs"]
mod same_short;

pub struct Plain(pub u32);
impl Plain {
    pub fn generic<T>(value: u32) -> Self {
        Self(value)
    }
    #[unsafe(no_mangle)]
    pub fn exported(value: u32) -> Self {
        Self(value)
    }
    pub unsafe fn unsafe_signature(value: u32) -> Self {
        Self(value)
    }
}
pub fn free_function(value: u32) -> Plain {
    Plain(value)
}

pub trait Maker {
    fn make(value: u32) -> Self;
}
pub struct TraitOwner(pub u32);
impl Maker for TraitOwner {
    fn make(value: u32) -> Self {
        Self(value)
    }
}

pub struct UserDrop(pub u32);
impl Drop for UserDrop {
    fn drop(&mut self) {}
}
impl UserDrop {
    pub fn new(value: u32) -> Self {
        Self(value)
    }
}

#[repr(align(16))]
pub struct Padded(pub u32);
impl Padded {
    pub fn new(value: u32) -> Self {
        Self(value)
    }
}
