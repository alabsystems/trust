//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency that starts threads. Its generic and `#[inline]` functions
//! carry MIR in its metadata, so the consuming crate's census walks them; its
//! plain non-generic function does not (R2).

pub fn spawn_generic<T: Send + 'static>(value: T) {
    let _handle = std::thread::spawn(move || drop(value));
}

#[inline]
pub fn spawn_inline() {
    let _handle = std::thread::spawn(|| {});
}

pub fn spawn_plain() {
    let _handle = std::thread::spawn(|| {});
}
