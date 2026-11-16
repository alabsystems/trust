#![crate_type = "lib"]
//! Fixture for `rmake.rs`: every `pub fn` here stores into a struct field, and the right-hand
//! side of the store has an EFFECT — a foreign `close`, a write to a static, a loop. On main
//! f5dd1d805a (and since c78b82bb50, 2026-07-18) the opaque-field and Option-discriminant
//! lanes of the direct producer did not lower that right-hand side at all: each body below
//! marked `main: erased` was spliced with the effect GONE, reported lowered with no tag,
//! passed `-Ztrust-ir-lower=strict`, and counted `ok` in probe channel C. The `Outer` setters
//! store plain data and used to store `undef` in place of the value they had just computed.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub static mut COUNT: u32 = 0;
pub static ANCHOR: u32 = 7;

#[inline(never)]
pub fn bump() -> u32 {
    unsafe {
        COUNT += 1;
        COUNT
    }
}

#[inline(never)]
fn close_ret(fd: i32) -> i32 {
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

pub enum Mode {
    A(Vec<u8>),
    B,
}

pub struct S {
    pub rows: Vec<u32>,
    pub boxed: Option<Box<i32>>,
    pub mode: Mode,
    pub name: String,
    pub n: i32,
}

impl S {
    /// main: erased — `load; extractfield (); insertfield; store; ret`, no call.
    pub fn set_rows_call(&mut self, fd: i32) {
        self.rows = rows_after_close(fd);
    }
    /// main: erased — `undef bool` stored, `close_then_some` never called.
    pub fn set_boxed_call(&mut self, fd: i32) {
        self.boxed = close_then_some(fd);
    }
    /// main: erased — `const bool true` stored, the `close_ret` in the payload dropped.
    pub fn set_boxed_some(&mut self, fd: i32) {
        self.boxed = Some(Box::new(close_ret(fd)));
    }
    /// main: erased — the `if` and its `close_ret` call dropped with the right-hand side.
    pub fn set_mode_if(&mut self, fd: i32) {
        self.mode = if close_ret(fd) == 0 { Mode::B } else { Mode::B };
    }
    /// main: erased — `close_ret(fd).to_string()` dropped.
    pub fn set_name(&mut self, fd: i32) {
        self.name = close_ret(fd).to_string();
    }
    /// Control (faithful on main too): a scalar lane lowers and stores its right-hand side.
    pub fn set_n(&mut self, fd: i32) {
        self.n = close_ret(fd);
    }
    /// Control: an effect-free right-hand side may stay unlowered (`None` is a constant).
    pub fn clear_boxed(&mut self) {
        self.boxed = None;
        self.n += 1;
    }
}

pub struct Spawn {
    pub argv: Vec<u8>,
    pub n: u32,
}

impl Spawn {
    /// main: erased — the `for` loop that closes `lo..hi` sits in the right-hand side.
    pub fn reset_and_close(&mut self, lo: i32, hi: i32) {
        self.argv = {
            for fd in lo..hi {
                unsafe { close(fd) };
            }
            Vec::new()
        };
    }
    /// main: erased — the same, beside an unrelated faithful loop (channel C said `ok`).
    pub fn reset_and_close_counted(&mut self, lo: i32, hi: i32) {
        let mut i = 0u32;
        while i < 3 {
            i += 1;
        }
        self.n = i;
        self.argv = {
            for fd in lo..hi {
                unsafe { close(fd) };
            }
            Vec::new()
        };
    }
}

/// main: erased — `Option<(i32, Vec<u8>)>` is an opaque-lane `Option` (a tuple payload is not an
/// admissible variant field), so the value-position constructor lowers as its discriminant,
/// `const bool true`, and the `close_ret` in the payload was dropped with it.
pub fn some_tuple_is_some(fd: i32) -> bool {
    let o = Some((close_ret(fd), Vec::<u8>::new()));
    o.is_some()
}

pub struct Pair(pub u32, pub &'static u32);

pub struct Holder {
    pub p: Option<Pair>,
    pub n: u32,
}

impl Holder {
    /// main: erased — the static write in `bump()` dropped with the `Some` payload.
    pub fn set_pair(&mut self) {
        self.p = Some(Pair(bump(), &ANCHOR));
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
    pub arr: [u32; 2],
    pub opt: Option<u32>,
    pub n: u32,
}

impl Outer {
    /// main: the tuple is built, then `undef (u32, u32)` is stored in its place.
    pub fn set_pair(&mut self, a: u32, b: u32) {
        self.pair = (a, b);
    }
    /// main: `undef struct` stored.
    pub fn set_inner(&mut self, a: u32) {
        self.inner = Inner { a, b: 7 };
    }
    /// main: `undef [u32; 2]` stored.
    pub fn set_arr(&mut self, a: u32) {
        self.arr = [a, a];
    }
    /// main: `undef enum` stored.
    pub fn set_opt(&mut self, a: u32) {
        self.opt = Some(a);
    }
}

pub struct Guard(pub i32);

impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { close(self.0) };
    }
}

/// The producer models no drop yet (plan step 2, increment 4): this is spliced as `ret` and
/// `Guard::drop` never runs (docs/KNOWN_HAZARDS.md, OPEN 2026-10-01, drop elision). Pinned here
/// only through probe channel C, which must not call it coverage.
pub fn guard_scope(fd: i32) {
    let _g = Guard(fd);
}
