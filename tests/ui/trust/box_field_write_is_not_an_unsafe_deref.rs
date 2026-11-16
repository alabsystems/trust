//@ needs-trust-verify
//@ revisions: ok bug uaf uafr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict -Ztrust-verify-profile=unix_hardened --crate-type lib
//@[ok] check-pass
//@[bug] check-fail
//@[uaf] check-fail
//@[uafr] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bug] dont-require-annotations: HELP
//@[uaf] dont-require-annotations: HELP
//@[uafr] dont-require-annotations: HELP
//! Trust (2026-10-01): a safe write into a boxed field is not a raw-pointer
//! write.
//!
//! `ElaborateBoxDerefs` spells `self.cold.b = v` (with `cold: Box<Cold>`) as a
//! store through the raw pointer it mints from the box. The separation engine
//! already treated a READ through that pointer like the `&T` deref it is
//! (047d35ba90), but charged the WRITE four `[unsafe:sep:*]` rows (null,
//! allocation validity, alignment, write permission) — every `&mut self` setter
//! of a boxed field failed the hardened lane
//! (docs/issues/2026-09-30-verified-lane-blockers-measured-on-alab-repos.md,
//! item 3; ay-sat's `Box<ColdState>` config). Measured before the fix on stage 1:
//! `set_b` 1 proved, 4 failed; after: 1 proved, 0 failed.
//!
//! `bug` keeps the same setter and adds a USER raw-pointer write, which must
//! still fail: the box exemption is the compiler-nominated temp, nothing else.
//!
//! `uaf` writes through a box after freeing it through a DERIVED pointer. The
//! credit's fences watch the box slot, not its pointee, so that free was
//! invisible to them; the write credit now requires a body with no unsafe
//! operation, and `uaf_write` must fail (docs/KNOWN_HAZARDS.md, OPEN
//! 2026-10-01). `uafr` is the READ twin (DECISION_QUEUE D33, ruled (a)
//! 2026-10-01): `uaf_read` must fail on its box read too.

pub struct Cold {
    pub a: u32,
    pub b: bool,
}

pub struct Config {
    pub cold: Box<Cold>,
    pub n: u64,
}

impl Config {
    pub fn a(&self) -> u32 {
        self.cold.a
    }

    pub fn set_b(&mut self, v: bool) {
        self.cold.b = v;
    }

    pub fn replace(&mut self, cold: Cold) {
        *self.cold = cold;
    }
}

#[cfg(bug)]
pub fn user_raw_write(p: *mut u32) {
    unsafe { *p = 5 };
}

#[cfg(uaf)]
pub fn uaf_write(b: Box<u32>) {
    let mut b = b;
    let p = &mut *b as *mut u32;
    // UNSOUND, deliberately: the fixture frees the box's pointee.
    unsafe { std::alloc::dealloc(p as *mut u8, std::alloc::Layout::new::<u32>()) }
    *b = 5;
    std::mem::forget(b);
}

#[cfg(uafr)]
pub fn uaf_read(b: Box<u32>) -> u32 {
    let mut b = b;
    let p = &mut *b as *mut u32;
    // UNSOUND, deliberately: the fixture frees the box's pointee.
    unsafe { std::alloc::dealloc(p as *mut u8, std::alloc::Layout::new::<u32>()) }
    let x = *b;
    std::mem::forget(b);
    x
}
