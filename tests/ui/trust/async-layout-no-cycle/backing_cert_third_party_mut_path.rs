//@ revisions: refmut_future pin_future refmut_vec_of_futures dyn_future dyn_any_sync
//@ revisions: dyn_closure_from_dependency
//@ revisions: hold_only dyn_shared dyn_owned
//@ aux-build:backing_escape_zap.rs
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ rustc-env:TRUST_CERT_DEBUG=1
//@ forbid-output: backing inventory INCOMPLETE
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@[refmut_future] forbid-output: "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
//@[pin_future] forbid-output: "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
//@[refmut_vec_of_futures] forbid-output: "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
//@[dyn_future] forbid-output: "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
//@[dyn_any_sync] forbid-output: "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
//@[dyn_closure_from_dependency] forbid-output: "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
//! SOUNDNESS PIN (escape census, 2026-09-30): a third-party callee handed a
//! mutable path to storage that holds `Buf` only through a coroutine's saved
//! local, or only behind a `dyn`.
//!
//! `Buf`'s certificate makes `get`'s `[unsafe:sep:offset]` row (line 88) PROVED,
//! sound only if no code outside the inventory can write `Buf`'s bytes. A SAFE
//! function of a non-sysroot crate (`backing_escape_zap`, whose `poke*` hold
//! `unsafe` blocks) may write whatever it is handed a `&mut`/raw path to, so the
//! census denies `Buf` when such a callee is handed one that reaches it.
//!
//! * `refmut_future`, `pin_future`, `refmut_vec_of_futures`: the path is
//!   `&mut F`, `Pin<&mut F>` or `&mut Vec<F>` for the future `F` of `hold`, which
//!   holds `Buf` in a SAVED LOCAL across its `.await`. The census's `&mut` walk
//!   followed a coroutine's upvars but not its saved locals, so `Buf` certified
//!   with the row PROVED on the async-layout branch before this fix (reviewer
//!   probes `u3`, `u4`, `u5`; a runtime twin segfaulted on the read the
//!   certificate called in bounds). Its type walks now share one storage step
//!   (`push_storage_components`).
//! * `dyn_future`, `dyn_any_sync`: the path is `Pin<&mut dyn Future>` or
//!   `&mut dyn Any`, after `Buf` (in the future, or in `Wrap`) was erased into
//!   that `dyn`. The callee can discard the vtable itself, and no type says what
//!   was erased, so `Census::finish` denies every struct erased into a `dyn` —
//!   as for an in-crate `dyn`-to-thin cast. `dyn_any_sync` certified on `main`
//!   too (probe `d1`); `dyn_future` (`d2`) on the async-layout branch.
//! * `dyn_closure_from_dependency`: the dependency RETURNS a
//!   `Box<dyn FnMut(&mut Buf)>` whose body is its own, and this crate calls it
//!   with `&mut Buf`. That virtual call resolves to no body the census sees, and
//!   the `&mut` walk stopped at the `dyn`; it now walks the `dyn`'s trait
//!   arguments too, so `writer::<Buf>` is a callee handed a `&mut` path to `Buf`.
//!   Certified with the row PROVED on `main` and on the async-layout branch
//!   (probe `r1`).
//!
//! The two dummy `u64` saved locals keep `hold`'s saved-local stores off variant
//! fields 0 and 1, which the certifier's coarse field check would otherwise
//! refuse — so the census, not the certifier, is what these revisions exercise.
//!
//! Precision control, which must still certify: `hold_only` (no hand-off). `dyn_shared`
//! (`&dyn Any`, read-only) and `dyn_owned` (`Box<dyn Any>`, ownership away) are GIVEN UP
//! since 2026-10-11 (CENSUS-THIRD-PARTY-1; see the note above their pins at the end).

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code, unused_mut)]

#[cfg(not(hold_only))] extern crate backing_escape_zap as zap; // CENSUS-THIRD-PARTY-1

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[trust::backing]
pub struct Buf {
    ptr: *const u8,
    len: usize,
}

impl Buf {
    // Sole establishing constructor: the mapping is exactly `len` bytes.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn get(&self, i: usize) -> u8 {
        if i < self.len { unsafe { *self.ptr.add(i) } } else { 0 }
    }
}

pub struct Wrap {
    pub b: Buf,
}

#[inline(never)]
fn mk_u64(x: u64) -> u64 {
    x
}

pub async fn hold() -> u8 {
    let d0 = mk_u64(1);
    let d1 = mk_u64(2);
    let b = unsafe { Buf::map(4) };
    std::future::ready(()).await;
    core::hint::black_box(d0 ^ d1);
    b.get(100)
}

#[cfg(refmut_future)]
pub fn evil() {
    let mut f = hold();
    zap::poke(&mut f, 3, 1 << 20);
    core::mem::forget(f);
}

#[cfg(pin_future)]
pub fn evil() {
    let mut f = core::pin::pin!(hold());
    zap::poke_pin(f.as_mut(), 3, 1 << 20);
}

#[cfg(refmut_vec_of_futures)]
pub fn evil() {
    let mut v = vec![hold()];
    zap::poke(&mut v, 0, 0);
}

#[cfg(dyn_future)]
pub fn evil() {
    let mut f: core::pin::Pin<Box<dyn core::future::Future<Output = u8>>> = Box::pin(hold());
    zap::poke_dyn_fut(f.as_mut(), 3, 1 << 20);
}

#[cfg(dyn_any_sync)]
pub fn evil(w: &mut Wrap) {
    zap::poke_dyn(w as &mut dyn core::any::Any, 1, 1 << 20)
}

#[cfg(dyn_closure_from_dependency)]
pub fn evil(b: &mut Buf) {
    let mut g = zap::writer::<Buf>();
    g(b);
}

#[cfg(dyn_shared)]
pub fn look(w: &Wrap) -> usize {
    zap::peek(w as &dyn core::any::Any)
}

#[cfg(dyn_owned)]
pub fn give(w: Wrap) -> usize {
    zap::take(Box::new(w) as Box<dyn core::any::Any>)
}

fn main() {}

//[refmut_future]~? RAW DENIED: `zap::poke`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `evil`
//[pin_future]~? RAW DENIED: `zap::poke_pin`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `evil`
//[refmut_vec_of_futures]~? RAW DENIED: `zap::poke`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `evil`
//[dyn_future]~? RAW DENIED: it is erased into a `dyn Trait` and `zap::poke_dyn_fut`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer to a `dyn` in `evil`
//[dyn_any_sync]~? RAW DENIED: it is erased into a `dyn Trait` and `zap::poke_dyn`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer to a `dyn` in `evil`
//[dyn_closure_from_dependency]~? RAW DENIED: `zap::writer`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `evil`
//[refmut_future,pin_future,refmut_vec_of_futures,dyn_future,dyn_any_sync]~? RAW established = {}
//[dyn_closure_from_dependency]~? RAW established = {}
//[dyn_closure_from_dependency]~? RAW "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"failed"
//[refmut_future,pin_future,refmut_vec_of_futures,dyn_future,dyn_any_sync]~? RAW "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"failed"
//[hold_only]~? RAW established = {"backing_cert_third_party_mut_path::Buf"}
//[hold_only]~? RAW "line_start":88,"col_start":36,"line_end":88,"col_end":51},"outcome":"proved"
// `dyn_shared` / `dyn_owned` were precision controls (a shared `&dyn Any` grants only reads;
// an owned `Box<dyn Any>` transfers ownership away). Since 2026-10-11 they are DENIED by
// CENSUS-THIRD-PARTY-1 (DECISION_QUEUE): a crate that calls third-party code gets no
// certificate, because three review rounds kept finding third-party forge/corrupt paths the
// precise rules missed. Restoring them needs the dependency verified into the inventory.
//[dyn_shared]~? RAW DENIED: the crate uses third-party code (the crate graph links `backing_escape_zap`; first use found: `look` calls the third-party `zap::peek`)
//[dyn_owned]~? RAW DENIED: the crate uses third-party code (the crate graph links `backing_escape_zap`; first use found: `give` calls the third-party `zap::take`)
//[dyn_shared,dyn_owned]~? RAW established = {}
