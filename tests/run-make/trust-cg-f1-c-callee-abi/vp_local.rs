//! The VARIADIC `asprintf(strp, fmt, ...)` declared in a LOCAL `extern "C"` block. Its first fixed
//! parameter is a POINTER TO A POINTER, outside the direct-scalar profile of the producer's
//! original-FnAbi reader (`foreign_signature::read`), so this callee keeps the producer's
//! UNSIGNED `(...) -> (i32)` declaration with no ABI record: the C-15 spelling that loses both
//! fixed arguments (`strp` in `x0`, `fmt` in `x1`, the anonymous `v` on the stack).
#![crate_name = "vp"]
use core::ffi::{c_char, c_void};

unsafe extern "C" {
    fn asprintf(strp: *mut *mut c_void, fmt: *const c_char, ...) -> i32;
}

pub fn f1_format(strp: *mut *mut c_void, fmt: *const c_char, v: i32) -> i32 {
    unsafe { asprintf(strp, fmt, v) }
}
