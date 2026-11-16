//! The same NON-variadic C callees as `nv_libc.rs`, declared in a LOCAL `extern "C"` block (the
//! item's own HIR header says nothing about the ABI; the block does).
#![crate_name = "nv"]

unsafe extern "C" {
    fn dup2(src: i32, dst: i32) -> i32;
    fn lseek(fd: i32, offset: i64, whence: i32) -> i64;
}

pub fn f1_dup2(old: i32, new: i32) -> i32 {
    unsafe { dup2(old, new) }
}

pub fn f1_lseek(fd: i32, offset: i64, whence: i32) -> i64 {
    unsafe { lseek(fd, offset, whence) }
}
