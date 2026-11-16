//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cdebug-assertions=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency whose `-> !` (and `-> Void`) functions are NAMED like the panic,
//! abort and UB entry points the diverging-site encoding recognizes: `panic_nounwind`,
//! `panicking::anything`, the thirteen R177 terminals (`unwrap_failed`,
//! `raw_vec::handle_error`, `process::abort`, ...) and `intrinsics::unreachable`.
//! Every body writes through its pointer argument and exits, so a caller passing
//! `null_mut()` segfaults. `boom` and `void::boom` are the same body under a name no
//! recognizer matches: the controls. Built with verification off (as `targo` builds
//! every dependency), so each body is absent from the caller's bundle
//! (`diverging_site_requires_sysroot_callee.rs`, DIVERGE-ANCHOR-1).

pub enum Void {}

pub fn panic_nounwind(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub mod panicking {
    pub fn anything(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
pub fn unwrap_failed(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub fn expect_failed(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub mod raw_vec {
    pub fn handle_error(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
    pub fn capacity_overflow(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
pub fn handle_alloc_error(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub fn __rust_alloc_error_handler(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub fn __rdl_oom(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub mod process {
    pub fn abort(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
pub mod intrinsics {
    pub fn abort(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
    pub fn unreachable(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
pub fn slice_index_fail(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub mod do_panic {
    pub fn runtime(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
pub mod int_log10 {
    pub fn panic_for_nonpositive_argument(p: *mut u32) -> ! {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
pub mod thread {
    pub mod local {
        pub fn panic_access_error(p: *mut u32) -> ! {
            unsafe { *p = 1; }
            std::process::exit(0)
        }
    }
}
pub fn boom(p: *mut u32) -> ! {
    unsafe { *p = 1; }
    std::process::exit(0)
}
pub mod void {
    pub mod panicking {
        pub fn x(p: *mut u32) -> crate::Void {
            unsafe { *p = 1; }
            std::process::exit(0)
        }
    }
    pub mod process {
        pub fn abort(p: *mut u32) -> crate::Void {
            unsafe { *p = 1; }
            std::process::exit(0)
        }
    }
    pub mod intrinsics {
        pub fn unreachable(p: *mut u32) -> crate::Void {
            unsafe { *p = 1; }
            std::process::exit(0)
        }
    }
    pub fn boom(p: *mut u32) -> crate::Void {
        unsafe { *p = 1; }
        std::process::exit(0)
    }
}
