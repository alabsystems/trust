//! The drop-glue ORACLE corpus (step 2 increment 4c): local-closed types — local `Drop` impls over
//! local structs, enums, tuples, closures and arrays of them — each dropped by value by one
//! `#[inline(never)]` function, so the collector lists its glue and channel C compares the
//! synthesized glue with rustc's own drop shim. Plus one subject per refusal class of design §4.3
//! that this corpus can reach.
#![allow(dead_code)]

use std::mem::ManuallyDrop;

pub static mut LOG: u32 = 0;

fn log(v: u32) {
    unsafe { LOG = LOG.wrapping_mul(31).wrapping_add(v) };
}

pub struct A(pub u32);
impl Drop for A {
    fn drop(&mut self) {
        log(self.0);
    }
}

pub struct Empty;
impl Drop for Empty {
    fn drop(&mut self) {}
}

/// A destructor and fields rustc reorders (`x` is placed last).
pub struct B {
    pub x: u8,
    pub a: A,
    pub e: Empty,
    pub a2: A,
}
impl Drop for B {
    fn drop(&mut self) {
        log(100);
    }
}

/// No destructor of its own: field glue only, nested.
pub struct Outer {
    pub b: B,
    pub n: u64,
    pub a: A,
}

/// A direct-tag enum with a destructor; one variant drops nothing.
pub enum E {
    One(A),
    Two(u8, B),
    Three,
}
impl Drop for E {
    fn drop(&mut self) {
        log(7);
    }
}

/// A niche enum: `None`'s tag lives in `A2`'s `bool`.
pub struct A2(pub A, pub bool);
pub enum N {
    Some(A2),
    None,
}

/// Several niche variants in one byte.
pub enum M {
    Payload(A, bool),
    X,
    Y,
    Z,
}

/// Explicit, negative discriminants under a narrow repr.
#[repr(i8)]
pub enum R {
    Neg(A) = -2,
    Zero = 0,
    Pos(Outer) = 5,
}

/// A single-variant enum: rustc stores no tag.
pub enum Single {
    Only(A, Empty),
}

/// An uninhabited variant beside a live one.
pub enum Never {
    Live(A),
    Dead(A, std::convert::Infallible),
}

/// A union with a destructor: its fields are never dropped.
pub union U {
    pub a: ManuallyDrop<A>,
    pub n: u32,
}
impl Drop for U {
    fn drop(&mut self) {
        log(9);
    }
}

/// `ManuallyDrop` fields are skipped.
pub struct Md {
    pub keep: ManuallyDrop<A>,
    pub a: A,
}

#[inline(never)]
pub fn consume_a(_v: A) {}
#[inline(never)]
pub fn consume_empty(_v: Empty) {}
#[inline(never)]
pub fn consume_b(_v: B) {}
#[inline(never)]
pub fn consume_outer(_v: Outer) {}
#[inline(never)]
pub fn consume_e(_v: E) {}
#[inline(never)]
pub fn consume_n(_v: N) {}
#[inline(never)]
pub fn consume_m(_v: M) {}
#[inline(never)]
pub fn consume_r(_v: R) {}
#[inline(never)]
pub fn consume_single(_v: Single) {}
#[inline(never)]
pub fn consume_never(_v: Never) {}
#[inline(never)]
pub fn consume_u(_v: U) {}
#[inline(never)]
pub fn consume_md(_v: Md) {}
#[inline(never)]
pub fn consume_option(_v: Option<A>) {}
#[inline(never)]
pub fn consume_tuple(_v: (A, u8, B, (Empty, A))) {}
#[inline(never)]
pub fn consume_array(_v: [A; 3]) {}
#[inline(never)]
pub fn consume_nested_array(_v: [[Outer; 2]; 2]) {}
/// A closure environment: its upvars, like a tuple's fields.
#[inline(never)]
pub fn drop_closure(a: A, b: B, n: u8) {
    // Whole values used by value inside: the closure captures `a` and `b` themselves (edition
    // 2021 would otherwise capture only the copied fields `a.0` and `b.x`).
    let _c = move || {
        let (a, b) = (a, b);
        a.0 + u32::from(b.x) + u32::from(n)
    };
}

// ── Refusals (design §4.3) ──────────────────────────────────────────────────────────────────

/// `Box`'s dealloc is `alloc`'s: `[upstream-body]`.
#[inline(never)]
pub fn consume_box(_v: Box<A>) {}

/// `String`'s glue reaches `Vec`'s `Drop` impl in `alloc`: `[upstream-body]`.
pub struct Named {
    pub name: String,
    pub a: A,
}
#[inline(never)]
pub fn consume_named(_v: Named) {}

/// A needs-drop field of a packed struct: rustc moves it to an aligned temporary first.
/// Refused by shape.
#[repr(packed)]
pub struct Packed {
    pub b: u8,
    pub a: A,
}
#[inline(never)]
pub fn consume_packed(_v: Packed) {}

/// A coroutine's glue (`coroutine_drop`): refused by shape.
pub async fn fut(a: A) -> u32 {
    a.0
}
#[inline(never)]
pub fn drop_future(a: A) {
    let _f = fut(a);
}
