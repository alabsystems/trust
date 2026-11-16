//! NON-variadic C callees reached through `libc::` (cross-crate foreign items, whose ABI the
//! producer reads off `tcx.fn_sig(def).abi()`). Each result proves its arguments arrived: `dup2`
//! returns its SECOND argument only when the first named an open descriptor, and `lseek` returns
//! its offset only when the descriptor and `whence` were both valid.
#![crate_name = "nv"]
#![feature(rustc_private)]
extern crate libc;

pub fn f1_dup2(old: i32, new: i32) -> i32 {
    unsafe { libc::dup2(old, new) }
}

pub fn f1_lseek(fd: i32, offset: i64, whence: i32) -> i64 {
    unsafe { libc::lseek(fd, offset, whence) }
}
