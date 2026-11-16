//@ needs-trust-verify
//@ edition: 2021
//@ revisions: dyn_call fn_ptr unsafe_fn from_raw transmute_callee transmute_callee_opt
//@ revisions: closure_transmute
//@ revisions: extern_safe extern_unsafe extern_c_def no_mangle no_mangle_opt export_name
//@ revisions: assume_total_safe assume_total_safe_opt assume_total_transmute skip_callee
//@ revisions: ptr_read raw_deref mixed_def escaped_slot option_box
//@ revisions: o2_neo_o2plain o2_neo_helper_o2plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[transmute_callee_opt] compile-flags: -Copt-level=2
//@[no_mangle_opt] compile-flags: -Copt-level=2
//@[assume_total_safe_opt] compile-flags: -Copt-level=2
//@[o2_neo_o2plain] compile-flags: -Copt-level=2
//@[o2_neo_helper_o2plain] compile-flags: -Copt-level=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code, improper_ctypes_definitions)]
#![cfg_attr(any(o2_neo_o2plain, o2_neo_helper_o2plain), feature(transmute_neo))]
//! Trust (D8, 2026-09-24): the RAILS of the returned-`Box` validity root
//! (`returned_box_safe_call.rs` holds the positives). Every revision must stay
//! refused. Each pins WHICH function must keep refusing:
//!
//! * most revisions annotate the CALLER (`count`) with the separation engine's
//!   `[hardened_unsafe_operation] FAILED` rows — the rows the root would drop.
//!   A caller that stops carrying them means the root admitted a call it must
//!   not: an indirect / `dyn` / shim call, an `unsafe fn`, a foreign import, a
//!   non-Rust ABI, an exported (`#[no_mangle]`/`#[export_name]`) symbol that can
//!   be interposed at link or load time, or a user axiom (`#[trust::assume_total]`,
//!   `#[trust::skip]` — an ASSUMED body, D8 critique k4/k5);
//! * `transmute_callee`/`_opt` is the memo's `p1_chain` KEY negative: the caller
//!   `*mk()` IS rooted after D8 at `-O0` (the callee is a safe local fn), so the
//!   refusal must come from `mk` itself — the D8-P0 `[unsafe:validity-transmute]`
//!   creation row. Without P0 this revision is a false proof (the binary twin
//!   SIGSEGVs, exit 139). `closure_transmute` is the same shape through a local
//!   closure: the closure's own creation row must refuse it;
//! * `ptr_read`, `raw_deref`, `mixed_def`, `escaped_slot`: the box does not
//!   reach the deref as the ONE value a certified call wrote. (`write_through`,
//!   a safe `*b = 4` through a returned box, moved out on 2026-10-01: DECISION_QUEUE
//!   D34 (a) credits a write through a rooted box in a body with no unsafe
//!   operation. Its positives live in `returned_box_safe_call.rs#write_through`
//!   and, since 2026-10-09 when a store through a rooted box is nominated and
//!   verifies, `ref_box_args/store_through_rooted_box.rs#returned_box`);
//! * `option_box` is the v1 BOUNDARY, not a soundness rail: a `Box` inside a
//!   returned `Option` is not a whole-local `Box` destination. Move it to the
//!   passing fixture if the root is ever extended to it;
//! * `o2_neo_o2plain` and `o2_neo_helper_o2plain`: at a plain `-O2` the root is
//!   ON, with the `-O0` premise, because a Trust proof session runs the `-O0`
//!   MIR pipeline at every `-Copt-level` and refuses every option that would
//!   add the inliner or GVN (T6). The `transmute_neo` CALL in `mk` / `mk2` is
//!   not inlined, so its own row survives and refuses `mk` / `mk2` while
//!   `count` is rooted — measured on the stage-1 build of -O parity
//!   (2026-09-25). Under the MIR inliner (`o2_neo`, `o2_neo_helper`, removed
//!   with T6's refusal) an inlined `transmute_neo` lost its row, `mk` verified
//!   while making `Box(0x4)`, and only `count`'s deref rows refused the program
//!   (KNOWN_HAZARDS, "an inlined sysroot `unsafe fn` loses its call-site row at
//!   `-O`"); that is why the refusal is the root's precondition
//!   (`returned_box_root`, condition 0). `transmute_callee_opt`, `no_mangle_opt`
//!   and `assume_total_safe_opt` stay at a plain `-O2`: each rail holds at `-O`
//!   with the root ON (same errors, same lines).
//!
//! BEFORE, on the stage-1 `trustc` of 2026-09-24 (wave 0 landed): `count`
//! refused with 3–9 `[hardened_unsafe_operation]` FAILED rows plus the unmodeled
//! null/misaligned assert rows. Measured through THIS file for `dyn_call`,
//! `fn_ptr`, `unsafe_fn`, `from_raw`, `transmute_callee`, `transmute_callee_opt`
//! and `extern_safe`; every other revision except the three below was measured
//! as the standalone D8 probe with the same body (`n_*.rs` at `-O0` and `-O2`,
//! `m_box` at `-O2` for `o2_gate`, `o2/h_neo`/`h_helper2` for `o2_neo*`; all
//! rc=1). `skip_callee` (the memo's `s1` measured only the skipped callee, a
//! strict error) and `closure_transmute` have NO before-measurement of `count`.

// ── indirect and dynamic calls ─────────────────────────────────────────────

#[cfg(dyn_call)]
pub trait Mk {
    fn mk(&self) -> Box<u32>;
}
#[cfg(dyn_call)]
pub struct S;
#[cfg(dyn_call)]
impl Mk for S {
    fn mk(&self) -> Box<u32> {
        Box::new(5)
    }
}
// A `dyn` call HAS a callee identity (`<dyn Mk as Mk>::mk`, concrete args); it is
// refused because it resolves to `InstanceKind::Virtual`, not to an item body.
#[cfg(dyn_call)]
pub fn count(m: &dyn Mk) -> u32 { *m.mk() }
//[dyn_call]~^ ERROR safety verification incomplete
//[dyn_call]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(fn_ptr)]
pub fn count(f: fn() -> Box<u32>) -> u32 { *f() }
//[fn_ptr]~^ ERROR safety verification incomplete
//[fn_ptr]~| NOTE [hardened_unsafe_operation] FAILED

// ── unsafe and foreign callees ─────────────────────────────────────────────

#[cfg(unsafe_fn)]
pub unsafe fn mk(p: *mut u32) -> Box<u32> {
    unsafe { Box::from_raw(p) }
}
#[cfg(unsafe_fn)]
pub fn count(p: *mut u32) -> u32 { *unsafe { mk(p) } }
//[unsafe_fn]~^ ERROR safety verification incomplete
//[unsafe_fn]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(from_raw)]
pub fn count(p: *mut u32) -> u32 { *unsafe { Box::from_raw(p) } }
//[from_raw]~^ ERROR safety verification incomplete
//[from_raw]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(any(transmute_callee, transmute_callee_opt))]
pub fn mk() -> Box<u32> { unsafe { core::mem::transmute::<usize, Box<u32>>(4) } }
//[transmute_callee]~^ ERROR safety verification incomplete
//[transmute_callee_opt]~^^ ERROR safety verification incomplete
#[cfg(any(transmute_callee, transmute_callee_opt))]
pub fn count() -> u32 {
    *mk()
}

// The closure body is its own verified MIR body; its creation row must refuse
// the program even though `<{closure} as Fn>::call` resolves to an `Item`.
#[cfg(closure_transmute)]
pub fn count() -> u32 { let f = || unsafe { core::mem::transmute::<usize, Box<u32>>(4) }; *f() }
//[closure_transmute]~^ ERROR safety verification incomplete

#[cfg(extern_safe)]
unsafe extern "C" {
    safe fn trust_d8_mk_box_c() -> Box<u32>;
}
#[cfg(extern_safe)]
pub fn count() -> u32 { *trust_d8_mk_box_c() }
//[extern_safe]~^ ERROR safety verification incomplete
//[extern_safe]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(extern_unsafe)]
extern "C" {
    fn trust_d8_mk_box_c2() -> Box<u32>;
}
#[cfg(extern_unsafe)]
pub fn count() -> u32 { *unsafe { trust_d8_mk_box_c2() } }
//[extern_unsafe]~^ ERROR safety verification incomplete
//[extern_unsafe]~| NOTE [hardened_unsafe_operation] FAILED

// A Rust-bodied `extern "C" fn` is an FFI entry point: refused on its ABI.
#[cfg(extern_c_def)]
pub extern "C" fn mk() -> Box<u32> {
    Box::new(3)
}
#[cfg(extern_c_def)]
pub fn count() -> u32 { *mk() }
//[extern_c_def]~^ ERROR safety verification incomplete
//[extern_c_def]~| NOTE [hardened_unsafe_operation] FAILED

// ── exported symbols (interposable at link / load time) ────────────────────

#[cfg(any(no_mangle, no_mangle_opt))]
#[no_mangle]
pub fn trust_d8_mk_exported() -> Box<u32> {
    Box::new(3)
}
#[cfg(any(no_mangle, no_mangle_opt))]
pub fn count() -> u32 { *trust_d8_mk_exported() }
//[no_mangle]~^ ERROR safety verification incomplete
//[no_mangle]~| NOTE [hardened_unsafe_operation] FAILED
//[no_mangle_opt]~^^^ ERROR safety verification incomplete
//[no_mangle_opt]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(export_name)]
#[export_name = "trust_d8_mk_export_named"]
pub fn mk() -> Box<u32> {
    Box::new(3)
}
#[cfg(export_name)]
pub fn count() -> u32 { *mk() }
//[export_name]~^ ERROR safety verification incomplete
//[export_name]~| NOTE [hardened_unsafe_operation] FAILED

// ── user axioms: an ASSUMED body discharges nothing (critique k4/k5) ────────

#[cfg(any(assume_total_safe, assume_total_safe_opt))]
#[trust::assume_total]
fn mk() -> Box<u32> {
    Box::new(3)
}
#[cfg(any(assume_total_safe, assume_total_safe_opt))]
pub fn count() -> u32 { *mk() }
//[assume_total_safe]~^ ERROR safety verification incomplete
//[assume_total_safe]~| NOTE [hardened_unsafe_operation] FAILED
//[assume_total_safe_opt]~^^^ ERROR safety verification incomplete
//[assume_total_safe_opt]~| NOTE [hardened_unsafe_operation] FAILED

// `mk` is verified in full since D8-P0 (its body is unsafe) and refused on its
// creation row; `count` must ALSO keep its rows, pinning the axiom exclusion
// independently of P0.
#[cfg(assume_total_transmute)]
#[trust::assume_total]
fn mk() -> Box<u32> {
    unsafe { core::mem::transmute::<usize, Box<u32>>(4) }
}
#[cfg(assume_total_transmute)]
pub fn count() -> u32 { *mk() }
//[assume_total_transmute]~^ ERROR safety verification incomplete
//[assume_total_transmute]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(skip_callee)]
#[trust::skip]
fn mk() -> Box<u32> {
    Box::new(3)
}
#[cfg(skip_callee)]
pub fn count() -> u32 { *mk() }
//[skip_callee]~^ ERROR safety verification incomplete
//[skip_callee]~| NOTE [hardened_unsafe_operation] FAILED

// ── the box is not the one value a certified call wrote ────────────────────

#[cfg(ptr_read)]
pub fn count(p: *const Box<u32>) -> u32 { let b: Box<u32> = unsafe { core::ptr::read(p) }; *b }
//[ptr_read]~^ ERROR safety verification incomplete
//[ptr_read]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(raw_deref)]
pub fn count(p: *const Box<u32>) -> u32 { unsafe { **p } }
//[raw_deref]~^ ERROR safety verification incomplete
//[raw_deref]~| NOTE [hardened_unsafe_operation] FAILED

#[cfg(mixed_def)]
pub fn defaults() -> Box<u32> {
    Box::new(3)
}
#[cfg(mixed_def)]
pub fn count(p: *mut u32, c: bool) -> u32 {
    //[mixed_def]~^ ERROR safety verification incomplete
    //[mixed_def]~| NOTE [hardened_unsafe_operation] FAILED
    let b = if c { defaults() } else { unsafe { Box::from_raw(p) } };
    *b
}

#[cfg(escaped_slot)]
pub fn defaults() -> Box<u32> {
    Box::new(3)
}
#[cfg(escaped_slot)]
pub fn count(p: *mut u32) -> u32 {
    //[escaped_slot]~^ ERROR safety verification incomplete
    //[escaped_slot]~| NOTE [hardened_unsafe_operation] FAILED
    let mut b = defaults();
    let r = &mut b;
    unsafe { core::ptr::write(r, Box::from_raw(p)) };
    *b
}

// v1 boundary (see the header): `Option<Box<u32>>` is not a `Box` destination.
#[cfg(option_box)]
pub fn mk() -> Option<Box<u32>> {
    Some(Box::new(3))
}
#[cfg(option_box)]
pub fn count() -> u32 { match mk() { Some(b) => *b, None => 0 } }
//[option_box]~^ ERROR safety verification incomplete
//[option_box]~| NOTE [hardened_unsafe_operation] FAILED

// ── optimized sessions: the root is OFF while the inlined-sysroot-`unsafe fn`
// hazard is open ─────────────────────────────────────────────────────────────

#[cfg(o2_neo_o2plain)]
pub fn mk() -> Box<u32> {
//[o2_neo_o2plain]~^ ERROR safety verification incomplete
//[o2_neo_o2plain]~| NOTE [hardened_unsafe_operation] FAILED
    unsafe { core::mem::transmute_neo::<usize, Box<u32>>(4) }
}
#[cfg(o2_neo_o2plain)]
pub fn count() -> u32 { *mk() }

#[cfg(o2_neo_helper_o2plain)]
fn mk2() -> Box<u32> {
//[o2_neo_helper_o2plain]~^ ERROR safety verification incomplete
//[o2_neo_helper_o2plain]~| NOTE [hardened_unsafe_operation] FAILED
    unsafe { core::mem::transmute_neo::<usize, Box<u32>>(4) }
}
#[cfg(o2_neo_helper_o2plain)]
pub fn mk() -> Box<u32> {
    mk2()
}
#[cfg(o2_neo_helper_o2plain)]
pub fn count() -> u32 { *mk() }
