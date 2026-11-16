//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! A field store whose right-hand side has an effect the producer cannot lower must FAIL
//! `-Ztrust-ir-lower=strict`; it may not pass as a lowered body with the right-hand side gone.
//!
//! Until 2026-10-01 (since c78b82bb50) the opaque `Ty::Unit` field lane (a `Vec`/`String`/
//! data-enum field of a `&mut self` struct) and the Option-discriminant field lane never lowered
//! the right-hand side of a store at all, and the body carried NO unsupported tag. Strict reads
//! only that tag list, so this file compiled under strict on main f5dd1d805a (measured: exit 0,
//! no error) while the trust-ir of the two refused bodies below was the bare field round trip
//! (`load; extractfield; insertfield; store; ret`, and `const bool true; store`): the
//! `close_ret` calls gone.
//!
//! Now a right-hand side the lane does not model is lowered for its effects (`set_rows_call`
//! passes: its call is in the body) or, when it cannot be, the body declines with
//! `Assign(opaque field rhs effects)` / `Assign(option flag rhs effects)` and strict names it.
//! `tests/run-make/trust-field-store-no-effect-erasure` checks the IR of the passing shapes.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

#[inline(never)]
fn close_ret(fd: i32) -> i32 {
    unsafe { close(fd) }
}

#[inline(never)]
fn rows_after_close(fd: i32) -> Vec<u8> {
    unsafe { close(fd) };
    Vec::new()
}

pub struct S {
    pub v: Vec<u8>,
    pub boxed: Option<Box<i32>>,
    pub n: i32,
}

impl S {
    pub fn set_rows_call(&mut self, fd: i32) {
        self.v = rows_after_close(fd);
    }

    pub fn push_built(&mut self, fd: i32) {
        //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
        self.v = {
            let mut x = Vec::new();
            x.push(close_ret(fd) as u8);
            x
        };
    }

    pub fn closure_payload(&mut self, fd: i32) {
        //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
        self.boxed = Some(Box::new((|| close_ret(fd))()));
    }
}
