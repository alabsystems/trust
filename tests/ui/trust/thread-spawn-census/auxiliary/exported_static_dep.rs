//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency that exports a static holding a callable that spawns. Both
//! functions are `#[inline]`, so their MIR is in the metadata (a MIR-less one
//! would be opaque, R2).

#[inline]
pub fn dep_spawn() {
    let _handle = std::thread::spawn(|| {});
}

#[inline]
pub extern "C" fn dep_launch() {
    dep_spawn()
}

#[unsafe(no_mangle)]
pub static TRUST_DEP_CALLBACK: extern "C" fn() = dep_launch;
