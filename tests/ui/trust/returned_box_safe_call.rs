//@ needs-trust-verify
//@ edition: 2021
//@ revisions: free let_bind method trait_static closure free_o2plain let_bind_o2plain write_through
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[free_o2plain] compile-flags: -Copt-level=2
//@[let_bind_o2plain] compile-flags: -Copt-level=2
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (D8, 2026-09-24): A `Box` RETURNED BY A SAFE DIRECT CALL IS A VALIDITY
//! ROOT — parity with a `Box` parameter and a returned `&T`.
//!
//! `pub fn defaults() -> Box<u32> { Box::new(3) } pub fn count() -> u32 { *defaults() }`
//! was refused on the stage-1 `trustc` of 2026-09-24 (wave 0 landed) at `-O0`
//! AND `-O2`, every revision below: `count` carried `3× [hardened_unsafe_operation]
//! FAILED (structural-unsafe-demand-finding)` (the separation engine's null /
//! allocation-validity / alignment rows for the synthesized `*box`), two unknown
//! `UnmodeledSafetyAssert(Null|MisalignedPointerDereference)` rows and one
//! runtime-checked assert — 6 obligations not proved, rc=1. `closure` was
//! refused the same way at `-O0`.
//!
//! The root needs a session that runs no value-changing MIR optimization —
//! under the inliner an inlined sysroot `unsafe fn` loses its row inside the
//! CALLEE and the callee's verification stops discharging the premise
//! (KNOWN_HAZARDS). A Trust proof session is such a session at every
//! `-Copt-level`: it runs the `-O0` MIR pipeline (-O parity, 2026-09-25) and
//! refuses every MIR-pipeline option by name (T6), so the root is ON with
//! exactly the `-O0` premise. `free_o2plain` and `let_bind_o2plain` pin it:
//! `*defaults()`, refused under `-Zmir-opt-level=2` before -O parity, verifies
//! at a plain `-Copt-level=2` (measured on the stage-1 build of -O parity; the
//! program built verify-off and run 100 000 times returns 3 every time — it is
//! `Box::new(3)`).
//!
//! The root is decided by ONE predicate, `trust_mir_extract::returned_box_root`,
//! read by both twins (the extractor's assert discharge and, through
//! `VcgenContext::with_returned_box_root_blocks`, vcgen's separation engine):
//! a direct, safe, Rust-ABI, non-foreign call that resolves to a plain item
//! (never `dyn`, never a shim) with no `#[trust::assume_total]`/`#[trust::skip]`,
//! no `#[no_mangle]`/`#[export_name]`, not naked and no target feature, writing
//! a whole `Box<T, Global>` local. The refusals it must keep are
//! `returned_box_refused_calls.rs`.
//!
//! If a revision here fails, find WHICH twin did not fire before touching
//! anything: `count` keeping `[hardened_unsafe_operation] FAILED` is the vcgen
//! twin (certificate or fence), keeping `UnmodeledSafetyAssert` is the extractor
//! twin (`origin_of_box_local`).

#[cfg(any(free, free_o2plain))]
pub fn defaults() -> Box<u32> {
    Box::new(3)
}
#[cfg(any(free, free_o2plain))]
pub fn count() -> u32 {
    *defaults()
}

#[cfg(any(let_bind, let_bind_o2plain))]
pub fn defaults() -> Box<u32> {
    Box::new(3)
}
#[cfg(any(let_bind, let_bind_o2plain))]
pub fn count() -> u32 {
    let b = defaults();
    let v = *b;
    v / 2
}

#[cfg(method)]
pub struct S;
#[cfg(method)]
impl S {
    pub fn mk(&self) -> Box<u32> {
        Box::new(3)
    }
}
#[cfg(method)]
pub fn count() -> u32 {
    *S.mk()
}

// A trait method on a CONCRETE receiver resolves statically to the impl item;
// only the `dyn` call (`returned_box_refused_calls.rs`, `dyn_call`) is refused.
#[cfg(trait_static)]
pub trait Mk {
    fn mk(&self) -> Box<u32>;
}
#[cfg(trait_static)]
pub struct S;
#[cfg(trait_static)]
impl Mk for S {
    fn mk(&self) -> Box<u32> {
        Box::new(5)
    }
}
#[cfg(trait_static)]
pub fn count() -> u32 {
    *S.mk()
}

// `<{closure} as Fn<()>>::call` resolves to the closure's own body (`Item`).
#[cfg(closure)]
pub fn count() -> u32 {
    let f = || Box::new(3u32);
    *f()
}

// D34 (a), 2026-10-01: a safe WRITE through a box a certified call returned is
// credited like the read (the box is valid, uniquely owned and borrowck admitted
// the write); the body has no unsafe operation, so D33's fence does not apply.
// Moved here from `returned_box_refused_calls.rs`, where it pinned the earlier
// "a write is never nominated" rule.
#[cfg(write_through)]
pub fn defaults() -> Box<u32> {
    Box::new(3)
}
#[cfg(write_through)]
pub fn count() -> u32 { let mut b = defaults(); *b = 4; *b }
