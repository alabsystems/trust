//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cdebug-assertions=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency whose uninhabited `panicking::V` implements core's `From<*mut u32>`
//! and `Default`, each by a body that writes through a null pointer and exits, so a
//! caller reaching one segfaults. `m::V` is the same type under a module name no
//! panic recognizer matches: the control. Built with verification off (as `targo`
//! builds every dependency), so each impl body is absent from the caller's bundle
//! (`diverging_site_requires_entry_identity.rs`, DIVERGE-ENTRY-1).
//!
//! A call `dep::panicking::V::from(p)` is a call to core's TRAIT method
//! `From::from` (its `callee_key` says `core`, real sysroot) whose rendering,
//! `<dep::panicking::V as core::convert::From<*mut u32>>::from`, contains
//! `::panicking::`; the impl that runs is this crate's.

pub mod panicking {
    pub enum V {}
    impl From<*mut u32> for V {
        fn from(p: *mut u32) -> V {
            unsafe { *p = 1; }
            std::process::exit(0)
        }
    }
    impl Default for V {
        fn default() -> V {
            let p = core::hint::black_box(core::ptr::null_mut::<u32>());
            unsafe { core::ptr::write_volatile(p, 1); }
            std::process::exit(0)
        }
    }
}

pub mod m {
    pub enum V {}
    impl From<*mut u32> for V {
        fn from(p: *mut u32) -> V {
            unsafe { *p = 1; }
            std::process::exit(0)
        }
    }
    impl Default for V {
        fn default() -> V {
            let p = core::hint::black_box(core::ptr::null_mut::<u32>());
            unsafe { core::ptr::write_volatile(p, 1); }
            std::process::exit(0)
        }
    }
}
