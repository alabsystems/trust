//! Built by the DEFAULT backend; calls `nv`'s functions, built by whichever backend is under test.
#![feature(rustc_private)]
extern crate libc;
extern crate nv;

use std::os::fd::AsRawFd;

fn main() {
    let file = std::fs::File::create("nv-scratch.bin").expect("scratch file");
    let fd = file.as_raw_fd();
    // `dup2` answers its second argument only if its first named an open descriptor.
    let dup = nv::f1_dup2(fd, 77);
    // `lseek` answers its offset only if the descriptor and `whence` were valid ...
    let off = nv::f1_lseek(77, 1234, libc::SEEK_SET);
    // ... and the host's own view of the ORIGINAL descriptor's offset proves 77 is its duplicate.
    let shared = unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) };
    println!("dup2={dup} lseek={off} shared={shared}");
}
