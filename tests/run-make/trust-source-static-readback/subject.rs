// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual Rust inputs for the cold-storage diagnostic, not a Clean-helper proof.
#![allow(dead_code)]

use std::sync::LazyLock;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TypeName {
    pub tag: u64,
    pub name: &'static str,
}

pub enum Literal {
    Nat(u64),
    String(&'static str),
}

#[inline(never)]
pub fn init_nat() -> TypeName {
    TypeName { tag: 11, name: "Nat" }
}

#[inline(never)]
pub fn init_string() -> TypeName {
    TypeName { tag: 29, name: "String" }
}

pub static FIRST: LazyLock<TypeName> = LazyLock::new(init_nat);
pub static SECOND: LazyLock<TypeName> = LazyLock::new(init_string);
// Equal cold initializer bytes do not merge distinct source allocations.
pub static SAME_AS_FIRST: LazyLock<TypeName> = LazyLock::new(init_nat);

// Match Clean's closure-coerced initializer style without copying its Name or
// Expr implementation. These are compiler-readback controls, not helper proofs.
pub static CLOSURE_NAT: LazyLock<TypeName> =
    LazyLock::new(|| TypeName { tag: 11, name: "Nat" });
pub static CLOSURE_STRING: LazyLock<TypeName> =
    LazyLock::new(|| TypeName { tag: 29, name: "String" });

#[inline(never)]
pub fn infer_literal_type(literal: &Literal) -> TypeName {
    match literal {
        Literal::Nat(_) => *FIRST,
        Literal::String(_) => *SECOND,
    }
}

#[inline(never)]
pub fn infer_closure_literal_type(literal: &Literal) -> TypeName {
    match literal {
        Literal::Nat(_) => *CLOSURE_NAT,
        Literal::String(_) => *CLOSURE_STRING,
    }
}

#[inline(never)]
pub fn first_address() -> &'static LazyLock<TypeName> {
    &FIRST
}

#[inline(never)]
pub fn first_address_again() -> &'static LazyLock<TypeName> {
    &FIRST
}

#[inline(never)]
pub fn equal_initializer_address() -> &'static LazyLock<TypeName> {
    &SAME_AS_FIRST
}

#[inline(never)]
pub fn equal_initializer_pair() -> (&'static LazyLock<TypeName>, &'static LazyLock<TypeName>) {
    (&FIRST, &SAME_AS_FIRST)
}

#[repr(C)]
pub struct SelfRef {
    pub next: &'static SelfRef,
}

pub static SELF_REF: SelfRef = SelfRef { next: &SELF_REF };

#[inline(never)]
pub fn self_reference_address() -> &'static SelfRef {
    &SELF_REF
}

// This is compiled separately: a refused capture must never publish the other
// roots as a successful, silently truncated graph.
#[cfg(readback_too_large)]
pub static TOO_LARGE: [u8; 65_537] = [0; 65_537];

#[cfg(readback_too_large)]
#[inline(never)]
pub fn too_large_address() -> &'static [u8; 65_537] {
    &TOO_LARGE
}

// CTFE creates a Synthetic/NestedStatic for this mutable backing allocation.
// It deliberately has no Rust type; reading its initializer must not query type_of.
pub static mut NESTED_BACKING: &mut [u64; 1] = &mut [17];
#[inline(never)]
pub unsafe fn nested_backing_address() -> *mut [u64; 1] {
    unsafe { NESTED_BACKING as *mut _ }
}

// A non-promotable immutable tail temporary has the same no-type standing.
pub static NESTED_IMMUTABLE: &[u64; 1] = { let element = 29; &[element] };
#[inline(never)]
pub fn nested_immutable_address() -> &'static [u64; 1] { NESTED_IMMUTABLE }
