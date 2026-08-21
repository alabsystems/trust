//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ENUM and UNION carriers, isolated so nothing else can produce the error.
//!
//! `AdtDef::all_fields` iterates EVERY variant's fields, so an enum payload and a
//! union field are covered by the same walk as a struct field. This file asserts
//! that rather than reasoning it, and it does so through the shortest path that
//! exists: the carrier is a root parameter the body never reads.
//!
//! ## Why the carrier is UNUSED, and why that is the sharper test
//!
//! `observe_bundle_body` poisons on the TYPE of every root parameter, not on any
//! use of it. So `_h` alone must poison `Emit`, and the only `dyn` site in the
//! body is `local.emit(1)` — whose vtable IS witnessed, whose target IS proved
//! panic-free, and which therefore discharges cleanly when nothing poisons.
//! Removing the parameter makes this file compile clean; that is the assertion.
//!
//! Reading the payload instead (`match h { H::One(s) => s.emit(2) }`) was tried
//! and REJECTED as a fixture: measured on the pre-fix binary it did discharge the
//! `dyn` site, but the crate still errored — from an unrelated refusal, "native
//! typed-TrustIr lowering did not complete". An `ERROR` annotation there would
//! have passed for the wrong reason, which is precisely the defect this slice is
//! also repairing in `dyn_dispatch_reliance_open_sink_stays_closed.rs`. A fixture
//! whose error can arrive from a second mechanism tests neither.
#![no_std]
#![allow(dead_code)]

pub trait Emit {
    fn emit(&mut self, n: u32) -> u32;
}

pub struct Good;

impl Emit for Good {
    fn emit(&mut self, n: u32) -> u32 {
        n.wrapping_add(1)
    }
}

pub enum H<'a> {
    One(&'a mut dyn Emit),
    Two,
}

pub union U<'a> {
    pub raw: *mut (dyn Emit + 'a),
    pub tag: usize,
}

pub fn drive_enum(_h: &mut H<'_>) -> u32 {
    //~^ ERROR Trust strict verification failed
    let mut g = Good;
    let local: &mut dyn Emit = &mut g;
    local.emit(1)
}

pub fn drive_union(_u: &U<'_>) -> u32 {
    //~^ ERROR Trust strict verification failed
    let mut g = Good;
    let local: &mut dyn Emit = &mut g;
    local.emit(1)
}
