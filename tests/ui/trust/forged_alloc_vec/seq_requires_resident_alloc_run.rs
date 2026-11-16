//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: alloc=alloc.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on -Cpanic=abort
//@ error-pattern: attempt to subtract with overflow
//@ ignore-wasm different `main` convention
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A type that carries std's `Vec` diagnostic item is not std's `Vec` unless it comes
//! from this compiler's own resident `alloc` (SEQ-RESIDENCY-1).
//!
//! `auxiliary/alloc.rs` is a dependency named `alloc` whose `vec::Vec` declares
//! `#[rustc_diagnostic_item = "Vec"]` and whose `Deref` returns `a` and `b` on
//! alternate calls. This crate is `#![no_std]`, so the real `alloc` is not loaded to
//! contest the attribute. The extractor lowered every type carrying that diagnostic
//! item to `Ty::Seq`, which every vcgen consumer reads as std's `Vec`. So the deref
//! length hop (DEREF-ANCHOR-1's receiver anchor) accepted `w`, the two `w.len()` in
//! `h` were tied to one `coll_len(w)`, and `w.len() - 1` under `w.len() == 0 =>
//! return` read `overflow:sub` proved (Clean-kernel Certified). The callee half could
//! not refuse it: the call is `<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref`,
//! defined by core (real sysroot), and with no duplicate crate name in the graph the
//! producer tags no generic argument.
//!
//! BEFORE (the stage 1 of `fc62d8ba05`, `integ/wave12`, 2026-10-04; the wave-12 review
//! measured the same on the stage 1 of `ee3f51541d` and on `stage1-w11fix`): this file
//! builds exit 0, `TRUST_ELIDE_DEBUG=1` prints `elided 1 kernel-certified overflow
//! checks` in `h`, and the binary prints `18446744073709551615` and exits 0. Built
//! `-Ztrust-verify=off`, it panics `attempt to subtract with overflow` (exit 101).
//!
//! AFTER: `ty_convert::is_std_vec` also requires `convert::is_real_sysroot_crate`
//! (artifact residency, which no attribute can claim). The forged `Vec` lowers to a
//! `Ty::Adt` whose name the impersonation stamp marks, the hop is refused, the row is
//! not proved, the check stays, and the run panics. The check-fail twin is
//! `seq_requires_resident_alloc.rs`.
#![no_std]
#![no_main]
#![feature(lang_items)]
#![allow(internal_features)]

extern crate alloc;

use core::cell::Cell;
use core::ffi::{c_char, c_int};
use core::fmt::Write;
use core::panic::PanicInfo;

#[cfg_attr(all(not(target_vendor = "apple"), unix), link(name = "c"))]
#[cfg_attr(target_vendor = "apple", link(name = "System"))]
unsafe extern "C" {
    fn write(fd: c_int, buf: *const u8, count: usize) -> isize;
    fn exit(code: c_int) -> !;
}

#[inline(never)]
pub fn h(w: &alloc::vec::Vec<u32>) -> usize {
    if w.len() == 0 {
        return 0;
    }
    w.len() - 1
}

struct Fd(c_int);

impl Write for Fd {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        unsafe { write(self.0, s.as_ptr(), s.len()) };
        Ok(())
    }
}

#[panic_handler]
fn panic(info: &PanicInfo<'_>) -> ! {
    let _ = writeln!(Fd(2), "{}", info.message());
    unsafe { exit(101) }
}

#[lang = "eh_personality"]
extern "C" fn rust_eh_personality(
    _version: i32,
    _actions: i32,
    _exception_class: u64,
    _exception_object: *mut (),
    _context: *mut (),
) -> i32 {
    loop {}
}

static A: [u32; 1] = [7];
static B: [u32; 0] = [];

#[no_mangle]
extern "C" fn main(_argc: c_int, _argv: *const *const c_char) -> c_int {
    let w = alloc::vec::Vec { a: &A, b: &B, flip: Cell::new(false) };
    let r = h(core::hint::black_box(&w));
    let _ = writeln!(Fd(1), "{}", r);
    0
}
