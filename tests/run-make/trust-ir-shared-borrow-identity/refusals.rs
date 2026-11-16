#![feature(coroutines, coroutine_trait)]

use std::ops::Coroutine;

#[inline(never)]
fn read_scalar(value: &i32) -> i32 { *value }

#[inline(never)]
fn read_reference(value: &&i32) -> i32 { **value }

// Storing a ledgered reference inside another local slot remains unsupported.
pub fn reference_valued_local(value: i32) -> i32 {
    let reference = &value;
    read_reference(&reference)
}

// Destructured bindings do not have the simple-let storage admission.
pub fn destructured_local(pair: (i32, i32)) -> i32 {
    let (left, _) = pair;
    read_scalar(&left)
}

// Duplicating this arm must not reuse the first sibling's allocation.
pub fn duplicated_arm(pair: (i32, i32)) -> i32 {
    match pair {
        (1, value) | (2, value) => {
            let local = value;
            read_scalar(&local)
        }
        _ => 0,
    }
}

// A plain coroutine's activation-local allocation cannot survive suspension.
pub fn activation_slot_across_suspend() -> impl Coroutine<Yield = (), Return = i32> {
    #[coroutine]
    || {
        let local = 7;
        read_scalar(&local);
        yield;
        read_scalar(&local)
    }
}

async fn leaf() {}

// The frame's memory survives, but a binding-local GEP does not dominate the
// continuation reached directly from the resume dispatch.
pub async fn shared_frame_across_await() {
    let local = 7;
    read_scalar(&local);
    leaf().await;
    read_scalar(&local);
}

// The storage pre-pass sees this later borrow even though no pointer has been
// registered at the suspension yet.
pub async fn shared_frame_borrowed_after_await() {
    let local = 7;
    leaf().await;
    read_scalar(&local);
}

#[inline(never)]
fn read_float(value: &f64) -> f64 { *value }

#[inline(never)]
fn write_float(value: &mut f64) { *value = 1.0; }

pub fn mutable_float_storage(value: f64) -> f64 {
    let mut local = value;
    write_float(&mut local);
    read_float(&local)
}

pub fn raw_mutable_float_storage(value: f64) -> f64 {
    let mut local = value;
    let _raw = &raw mut local;
    read_float(&local)
}

pub fn mutable_pattern_float_storage(value: f64) -> f64 {
    let mut local = value;
    match local {
        ref mut borrowed => *borrowed = 2.0,
    }
    read_float(&local)
}

#[inline(never)]
fn read_empty_references(value: &[&i32; 0]) -> usize { value.len() }

pub fn empty_array_of_references() -> usize {
    let local = [];
    read_empty_references(&local)
}

#[inline(never)]
fn write_empty_array(value: &mut [i32; 0]) { *value = []; }

#[inline(never)]
fn read_empty_array(value: &[i32; 0]) -> usize { value.len() }

pub fn mutable_empty_array_storage() -> usize {
    let mut local = [];
    write_empty_array(&mut local);
    read_empty_array(&local)
}

#[inline(never)]
fn read_empty_opaque(value: &[Option<(u32, u32)>; 0]) -> usize { value.len() }

// The Option-discriminant lane spells this element Bool. Zero length must not
// let that placeholder pass the primitive Rust element admission.
pub fn empty_array_of_opaque_elements() -> usize {
    let local = [];
    read_empty_opaque(&local)
}

pub struct Wide { pub number: f64, pub count: u32 }

#[inline(never)]
fn read_wide(value: &Wide) -> f64 { value.number }

pub fn reassigned_wide_parameter(mut value: Wide) -> f64 {
    let before = read_wide(&value);
    value = Wide { number: before, count: 8 };
    read_wide(&value)
}

pub fn projected_write_wide_parameter(mut value: Wide) -> f64 {
    value.number = 2.0;
    read_wide(&value)
}

pub fn mutable_wide_parameter(mut value: Wide) -> f64 {
    let _pointer = &mut value;
    read_wide(&value)
}

pub fn reassigned_reference_parameter<'a>(mut value: &'a i32, replacement: &'a i32) -> i32 {
    let before = read_reference(&value);
    value = replacement;
    before.wrapping_add(read_reference(&value))
}

pub fn raw_const_wide_parameter(mut value: Wide) -> f64 {
    let raw = &raw const value;
    unsafe { (*(raw as *mut Wide)).number = 4.0; }
    read_wide(&value)
}

pub fn projected_borrow_wide_parameter(value: Wide) -> f64 {
    let _whole = read_wide(&value);
    read_float(&value.number)
}

pub fn duplicated_wide_local(pair: (i32, i32)) -> f64 {
    match pair {
        (1, count) | (2, count) => {
            let value = Wide { number: 1.0, count: count as u32 };
            read_wide(&value)
        }
        _ => 0.0,
    }
}

#[inline(never)]
fn take_dyn_reference(_: &&dyn std::fmt::Display) -> usize { 1 }

pub fn shared_dyn_parameter(value: &dyn std::fmt::Display) -> usize {
    take_dyn_reference(&value)
}

pub fn escape_reference_parameter(value: &i32) -> *const &i32 {
    let outer = &value;
    outer as *const &i32
}

// Trust: extend the outer reference's lifetime without introducing the raw
// borrow adjustment that intentionally prevents shared-slot admission above.
pub fn escape_shared_reference_lifetime(value: &i32) -> &'static &'static i32 {
    unsafe { std::mem::transmute::<&&i32, &'static &'static i32>(&value) }
}

// A raw parameter carries no storage the producer models. Since e0e9606dab a typed
// INTEGER load through an unchanged incoming raw address lowers (no borrow rights are
// granted); every other pointee still refuses, so the refusal is pinned on `bool`.
pub fn raw_parameter_deref(value: *const bool) -> bool {
    unsafe { *value }
}

pub fn raw_parameter_integer_deref(value: *const u8) -> u8 {
    unsafe { *value }
}

pub enum Payload { Number(i32), Empty }

pub fn guarded_payload_reference(left: &Payload, right: &Payload) -> bool {
    match (left, right) {
        (Payload::Number(a), Payload::Number(b)) if read_reference(&a) >= 0 => *a == *b,
        _ => false,
    }
}
