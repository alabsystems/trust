//! Bodies that move addressable storage (`MaybeUninit`, spelled `Ty::Storage` since
//! `060a4cd7ff`) by value, beside by-reference controls over the same rows.
use std::cell::{Cell, RefCell, UnsafeCell};
use std::mem::MaybeUninit;
use std::sync::OnceLock;

pub struct W {
    pub a: u32,
    pub m: MaybeUninit<u64>,
}

/// Own signature and entry block parameter carry `W` by value.
pub fn get(w: W) -> u32 {
    w.a
}

/// Takes and returns `W` by value.
pub fn pass(w: W) -> W {
    w
}

/// Passes `W` by value to a local function.
pub fn forwards(w: W) -> u32 {
    get(w)
}

/// A typed load of the whole `W` out of a reference.
pub fn copy_out(w: &W) -> u32 {
    let v = unsafe { std::ptr::read(w) };
    v.a
}

/// `Option<MaybeUninit<_>>` by value.
pub fn opt(o: Option<MaybeUninit<u64>>) -> bool {
    o.is_some()
}

/// A by-reference read of a sibling of storage nested in a cell.
pub struct S {
    pub cell: UnsafeCell<MaybeUninit<u64>>,
    pub tag: u8,
}

pub fn tag(s: &S) -> u8 {
    s.tag
}

/// Binds a storage-typed result of a local callee and of a std callee.
pub fn new_uninit() -> MaybeUninit<u64> {
    MaybeUninit::uninit()
}

pub fn binds() {
    let _w = new_uninit();
}

pub fn std_caller() -> u32 {
    let _m = MaybeUninit::<u64>::uninit();
    1
}

/// A row whose layout the producer withholds (the declined `Option<(u64, u64)>` payload) and that
/// also holds storage, taken by value: the crate assembler's R2 refuses it without the
/// storage-value-traffic flag; the flag names it first.
pub struct Z {
    pub c: RefCell<Option<(u64, u64)>>,
    pub m: MaybeUninit<u64>,
}

pub fn mk(z: Z) -> u64 {
    let _ = z;
    0
}

/// A static initializer returning a `OnceLock` (which holds `MaybeUninit`) by value.
pub static ONCE: OnceLock<u64> = OnceLock::new();

thread_local! {
    /// A lazy thread-local: its `__RUST_STD_INTERNAL_VAL` is `LazyStorage`, which holds
    /// `MaybeUninit`.
    static LAZY: Cell<u64> = Cell::new(std::process::id() as u64);
    /// Control: a `const` thread-local has no `LazyStorage`.
    static CONSTED: Cell<u64> = const { Cell::new(3) };
}

pub fn lazy() -> u64 {
    LAZY.with(|c| c.get())
}

pub fn consted() -> u64 {
    CONSTED.with(|c| c.get())
}

/// Controls: `W` behind a reference carries no storage by value.
pub fn ctl(w: &W) -> u32 {
    w.a
}

pub fn ctl_caller(w: &W) -> u32 {
    ctl(w)
}
