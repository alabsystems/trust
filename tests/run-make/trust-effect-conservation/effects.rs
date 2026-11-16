//! The effect-conservation fixture: every shape the 2026-10-01 producer review found shipped as
//! the program while missing an effect or modelling a value by abstraction, plus the plain
//! bodies the gate must leave alone. `rmake.rs` reads the verdicts back from the dump's
//! `effects.effect-conservation.json` sidecar and from probe channel C.

use std::ffi::OsString;
use std::os::fd::OwnedFd;

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

#[inline(never)]
pub fn close_ret(fd: i32) -> i32 {
    unsafe { close(fd) }
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

/// A store to a `static`: conserved.
#[inline(never)]
pub fn bump() -> u32 {
    unsafe {
        COUNT += 1;
        COUNT
    }
}

/// A store through a `&mut` parameter: conserved.
pub fn store_through(p: &mut i32, fd: i32) {
    *p = close_ret(fd);
}

/// An integer-range `for` loop of foreign calls: conserved (the range calls are the audited
/// equivalence, the `close` calls are in the loop).
pub fn close_range(lo: i32, hi: i32) {
    for fd in lo..hi {
        unsafe { close(fd) };
    }
}

/// Plain arithmetic: conserved.
pub fn max3(a: i64, b: i64, c: i64) -> i64 {
    let m = if a > b { a } else { b };
    if m > c { m } else { c }
}

pub struct Guard(pub i32);

impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { close(self.0) };
    }
}

/// Drop elided: `Guard::drop` never runs.
pub fn guard_scope(fd: i32) {
    let _g = Guard(fd);
}

/// Moved into `mem::drop`: conserved.
pub fn guard_explicit_drop(fd: i32) {
    let g = Guard(fd);
    drop(g);
}

pub struct S {
    pub rows: Vec<u32>,
    pub boxed: Option<Box<i32>>,
    pub n: i32,
}

impl S {
    /// The opaque `()` lane: stores nothing, drops nothing.
    pub fn set_rows_call(&mut self, fd: i32) {
        self.rows = rows_after_close(fd);
    }

    /// The whole-value `undef` store.
    pub fn set_boxed_call(&mut self, fd: i32) {
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
    /// The Option-discriminant `bool` lane in a struct WITH a layout.
    pub fn set_pair(&mut self) {
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
    /// aterm-uds `spawnfd::LaneCommand::stdin`, reduced: `undef enum` stored, old value not
    /// dropped.
    pub fn stdin(&mut self, slot: ChildStdio) -> &mut Self {
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
    pub n: u32,
}

impl Outer {
    /// Plain data stored as computed: conserved.
    pub fn set_pair(&mut self, a: u32, b: u32) {
        self.pair = (a, b);
    }
}

/// A callee whose `Option<(u16, u16)>` parameter the producer declines (its signature would carry
/// the Option-discriminant lane), so it is never lowered itself.
#[inline(never)]
pub fn resize_px(master: i32, px: Option<(u16, u16)>) -> i32 {
    match px {
        Some((a, b)) => master + a as i32 + b as i32,
        None => master,
    }
}

/// The Option-discriminant lane in a CALL ARGUMENT: `None` is passed as `const bool false` (aterm
/// pty's `unix::resize`, which calls `resize_with_cell_px(master, rows, cols, None)`).
pub fn resize(master: i32) -> i32 {
    resize_px(master, None)
}

/// The Option-discriminant lane in a STORE: `*slot = None` is stored as one `false` byte where
/// the program writes an 8-byte `Option<(u32, u32)>`.
pub fn clear_pair(slot: &mut Option<(u32, u32)>) {
    *slot = None;
}

/// A real `bool` stored through a pointer: conserved.
pub fn set_flag(slot: &mut bool) {
    *slot = true;
}

// ── The 2026-10-01 review of the first gate (97de0ab9ac) ──────────────────────

/// A collapsed `Option<(u32, u32)>` inside a returned TUPLE: `ret (bool true, u32 4)`, the
/// payload gone. The first gate looked for the placeholder only in a lone position.
pub fn ret_tuple(a: u32) -> (Option<(u32, u32)>, u32) {
    (Some((a, a)), 4)
}

/// A pointer to a collapsed value, passed on (`&*o`): it holds no value of the enum. Conserved.
#[inline(never)]
pub fn consume_ref(o: &Option<(u32, u32)>) -> u32 {
    if o.is_some() { 1 } else { 0 }
}

/// An elided drop whose glue only frees memory: `abstracted(drop)` alone, no `destructor` (a
/// reader that models no allocation may accept it; `guard_scope`'s may not be).
pub fn drop_string(s: String) -> usize {
    s.len()
}

/// A write through a `Box` the CALLER owns (the parameter): an effect, carried. Conserved.
pub fn set_box(mut b: Box<u32>) -> Box<u32> {
    *b = 5;
    b
}

impl PartialEq for Guard {
    fn eq(&self, o: &Guard) -> bool {
        unsafe { close(o.0) == 0 }
    }
}

/// An exempt string-pattern comparison listed before a user `PartialEq::eq` of the same trait
/// method. The first gate's `FnDef`-only, MIR-order pairing reported the user call lost.
/// Conserved.
pub fn str_then_user(s: &str, a: &Guard, b: &Guard) -> u32 {
    let k = match s {
        "x" => 1,
        _ => 2,
    };
    if *a == *b { k } else { 0 }
}

// Under `-Ztrust-ir-lower-mutate-rhs-effects` the expression building each opaque
// `Option<(u32, u32)>` payload below is skipped, so the payload's effect is lost. The first gate
// judged every one of them conserved on its effects (2026-10-01 review, findings 1, 2 and 4).

/// A division-by-zero check (finding 1; the review linked this body built by trust-cg and it
/// returned where the program must panic).
pub fn div_lost(x: u32, y: u32) -> u32 {
    let o: Option<(u32, u32)> = Some((x / y, 2));
    if let Some(_) = o { 1 } else { 0 }
}

/// An overflow check (finding 1).
pub fn ovf_lost(x: u32) -> bool {
    let o: Option<(u32, u32)> = Some((x + 1, 2));
    o.is_some()
}

/// A bounds check (finding 1).
pub fn index_lost(a: &[u32], i: usize) -> bool {
    let o: Option<(u32, u32)> = Some((a[i], 2));
    o.is_some()
}

/// A user `<Guard as PartialEq>::eq` (it closes a descriptor) next to an exempt
/// `<str as PartialEq>::eq` of the same trait method (finding 2): the `str` call must not stand
/// in for it.
pub fn payload_eq_then_str(s: &str, t: &str, a: &Guard, b: &Guard) -> bool {
    let o: Option<(u32, u32)> = Some(((*a == *b) as u32, 5));
    let e = *s == *t;
    o.is_some() && e
}

/// A write through a `Box::from_raw` box, i.e. the caller's memory (finding 4).
pub fn via_box_raw(p: *mut u32) -> bool {
    let mut b = unsafe { Box::from_raw(p) };
    let o: Option<(u32, u32)> = Some((
        {
            *b = 5;
            1
        },
        2,
    ));
    std::mem::forget(b);
    o.is_some()
}

/// A write through a `Box` parameter returned to the caller (finding 4).
pub fn via_box_param(mut b: Box<u32>) -> (bool, Box<u32>) {
    let o: Option<(u32, u32)> = Some((
        {
            *b = 5;
            1
        },
        2,
    ));
    (o.is_some(), b)
}

/// A PROMOTED root spelled trivially droppable: borrowing a field (`&t.0`) gives `t` a slot,
/// and the slot's type is `(i32, bool)`, the `Option` collapsed to its discriminant. Its drop
/// has no canonical trust-ir v55 spelling, so it is not placed: `abstracted(drop)`, and the
/// crate module still validates (a `drop (i32, bool)` would fail all of it, `NonCanonicalDrop`).
pub fn promoted_collapsed_root(fd: i32) -> i32 {
    let t = (fd, Some((close_ret(fd), Vec::<u8>::new())));
    let r = &t.0;
    *r
}

// Step 2 increment 4b residuals: one body per shape 4b did not place. Each is conserved (the
// producer places the drop rustc's elaboration performs); `rmake.rs` shows a TEST-ONLY mutation
// of each placement (`TRUST_IR_LOWER_MUTATE_DROPS`) refused by the gate.

#[inline(never)]
pub fn mk_guard(fd: i32) -> Guard {
    Guard(fd)
}

#[inline(never)]
pub fn peek_guard(g: &Guard) -> i32 {
    g.0
}

/// A discarded temporary: dropped at the statement's end.
pub fn temp_discard(fd: i32) -> i32 {
    mk_guard(fd);
    fd
}

/// A borrowed temporary: dropped at the statement's end, through the slot the borrow points at.
pub fn temp_borrow(fd: i32) -> i32 {
    let n = peek_guard(&mk_guard(fd));
    n
}

/// A by-value pattern binding moving the payload out of the parameter: the binding is dropped
/// at the arm's end; the parameter's drop is OPEN and drops nothing.
pub fn bind_some(o: Option<Guard>) -> i32 {
    match o {
        Some(g) => g.0,
        None => 0,
    }
}

pub struct Held {
    pub g: Guard,
    pub n: u32,
}

/// A destructuring `let`: the binding is dropped at the block's end; the struct's open drop
/// drops nothing (its one needs-drop field moved), so rustc's elaboration removes it.
pub fn bind_destructure(h: Held) -> u32 {
    let Held { g, n } = h;
    g.0 as u32 + n
}

/// Drop-and-replace through a `&mut`: the old `Guard` is dropped through `slot`.
pub fn replace_through(slot: &mut Guard, fd: i32) {
    *slot = Guard(fd);
}

// The 4b residuals review (2026-10-08): a borrowed temporary's drop must run on the object the
// program used. `f(&g())` lowers its reborrow through the shared-borrow snapshot lane, which hands
// the callee a COPY of the borrow's slot; the first cut dropped the stale original (a `Cell`
// bumped through the copy, then the destructor closing the old descriptor; a `RefCell`'s buffer
// freed through the copy and again by the drop). `rmake.rs` pins the drop's pointer to the
// operand the callee receives, and a TEST-ONLY mutation (`temp-borrow-slot`) that restores the
// first cut is caught there (the gate never reads an `Inst::Drop`'s pointer).

pub struct Counter {
    pub hits: std::cell::Cell<i32>,
}

impl Drop for Counter {
    fn drop(&mut self) {
        unsafe { close(self.hits.get()) };
    }
}

#[inline(never)]
pub fn mk_counter(fd: i32) -> Counter {
    Counter { hits: std::cell::Cell::new(fd) }
}

#[inline(never)]
pub fn bump_counter(c: &Counter) -> i32 {
    c.hits.set(c.hits.get() + 1);
    0
}

/// rustc: `bump_counter` increments the temporary through the borrow; its destructor then
/// closes `fd + 1`. The trust-ir drops the slot the callee received.
pub fn cell_temp(fd: i32) -> i32 {
    let n = bump_counter(&mk_counter(fd));
    n
}

#[inline(never)]
pub fn mk_refcell(b: u8) -> std::cell::RefCell<Vec<u8>> {
    std::cell::RefCell::new(vec![b])
}

#[inline(never)]
pub fn refill(r: &std::cell::RefCell<Vec<u8>>) {
    *r.borrow_mut() = vec![1, 2, 3];
}

/// rustc: `refill` frees `[b]` and stores `[1, 2, 3]` in the temporary, which its drop frees.
pub fn refcell_temp(b: u8) {
    refill(&mk_refcell(b));
}
