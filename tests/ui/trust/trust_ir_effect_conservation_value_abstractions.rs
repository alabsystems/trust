//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! D28 (docs/DECISION_QUEUE.md, TAKEN 2026-10-01): a body lowered through a VALUE-ABSTRACTION
//! lane is tagged and never passes `-Ztrust-ir-lower=strict`.
//!
//! Three direct-producer lanes store less than the program does and push no `unsupported` tag
//! (docs/KNOWN_HAZARDS.md, "abstraction lanes are reported lowered with no tag"):
//!
//! * the opaque `()` field lane — `self.rows = rows_after_close(fd)` on a struct registered
//!   WITHOUT a layout (its `Vec` field is a `()` placeholder) stores nothing;
//! * the Option-discriminant `bool` lane — `self.p = Some(Pair(bump(), &ANCHOR))` stores only
//!   `true`, at offset 0 of what is really a 16-byte `Option<Pair>`;
//! * the whole-value `undef` store — `self.boxed = close_then_some(fd)` stores `undef bool`, and
//!   aterm-uds's `LaneCommand::stdin` (`self.stdin = slot`) stores `undef enum` and also elides
//!   the drop of the old `ChildStdio`.
//!
//! Each was spliced, strict-clean and codegen-licensed; measured on this tree before the
//! effect-conservation gate, this file compiled under strict with exit 0. Now each is refused,
//! with its lanes named. The plain-data setters (`Outer::set_pair`, `Outer::set_opt`) store the
//! value they compute and stay clean. `clear_pair` is the Option-discriminant lane in a store
//! through a pointer (`set_flag`, a real `bool` store, stays clean); the same lane in a call
//! ARGUMENT needs a callee the producer declines, so it is pinned by
//! `tests/run-make/trust-effect-conservation` (strict would stop at that callee).

use std::ffi::OsString;
use std::os::fd::OwnedFd;

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

#[inline(never)]
fn rows_after_close(fd: i32) -> Vec<u32> {
    unsafe { close(fd) };
    Vec::new()
}

#[inline(never)]
fn close_then_some(fd: i32) -> Option<Box<i32>> {
    unsafe { close(fd) };
    None
}

pub static mut COUNT: u32 = 0;

#[inline(never)]
pub fn bump() -> u32 {
    unsafe {
        COUNT += 1;
        COUNT
    }
}

pub struct S {
    pub rows: Vec<u32>,
    pub boxed: Option<Box<i32>>,
    pub n: i32,
}

impl S {
    /// The opaque `()` lane: the new `Vec` is not stored, the old one is not dropped.
    pub fn set_rows_call(&mut self, fd: i32) {
        //~^ ERROR Abstracted(opaque-lane
        self.rows = rows_after_close(fd);
    }

    /// The whole-value `undef` store.
    pub fn set_boxed_call(&mut self, fd: i32) {
        //~^ ERROR Abstracted(undef
        self.boxed = close_then_some(fd);
    }
}

pub struct Pair(pub u32, pub &'static u32);
pub static ANCHOR: u32 = 7;

pub struct Holder {
    pub p: Option<Pair>,
    pub n: u32,
}

impl Holder {
    /// The Option-discriminant lane, in a struct that DOES carry a layout.
    pub fn set_pair(&mut self) {
        //~^ ERROR Abstracted(opaque-lane
        self.p = Some(Pair(bump(), &ANCHOR));
    }
}

pub enum ChildStdio {
    Null,
    Inherit,
    Fd(OwnedFd),
}

pub struct LaneCommand {
    pub program: OsString,
    pub stdin: ChildStdio,
}

impl LaneCommand {
    /// aterm-uds `spawnfd::LaneCommand::stdin`, reduced.
    pub fn stdin(&mut self, slot: ChildStdio) -> &mut Self {
        //~^ ERROR Abstracted(drop
        self.stdin = slot;
        self
    }
}

#[derive(Clone, Copy)]
pub struct Inner {
    pub a: u32,
    pub b: u32,
}

pub struct Outer {
    pub pair: (u32, u32),
    pub inner: Inner,
    pub opt: Option<u32>,
    pub n: u32,
}

impl Outer {
    /// Plain data, stored as computed: clean.
    pub fn set_pair(&mut self, a: u32, b: u32) {
        self.pair = (a, b);
    }

    /// Plain data, stored as computed: clean.
    pub fn set_opt(&mut self, a: u32) {
        self.opt = Some(a);
    }
}

/// The Option-discriminant lane in a STORE through a pointer: `*slot = None` is stored as one
/// `false` byte where the program writes an 8-byte `Option<(u32, u32)>`.
pub fn clear_pair(slot: &mut Option<(u32, u32)>) {
    //~^ ERROR Abstracted(opaque-lane
    *slot = None;
}

/// A real `bool` stored through a pointer: clean.
pub fn set_flag(slot: &mut bool) {
    *slot = true;
}
