//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency whose `#[inline]` body (MIR in its metadata) stores a callable
//! into an `extern` static of its own.

unsafe extern "C" {
    static mut TRUST_DEP_HOOK: Option<extern "C" fn()>;
}

#[inline]
pub fn register(f: extern "C" fn()) {
    unsafe { TRUST_DEP_HOOK = Some(f) }
}
