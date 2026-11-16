//@ needs-trust-verify
//@ edition: 2021
//@ revisions: box_int box_from_ref box_null_raw param_chain
//@ revisions: ref_null ref_lifetime
//@ revisions: option_box bool_int fnptr_null vec_forge
//@ revisions: box_int_o2plain param_chain_o2plain ref_lifetime_o2plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[box_int_o2plain] compile-flags: -Copt-level=2
//@[param_chain_o2plain] compile-flags: -Copt-level=2
//@[ref_lifetime_o2plain] compile-flags: -Copt-level=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! -O parity (2026-09-25): every `_opt` revision now states `-Zmir-opt-level=2`.
//! A verifying session runs the MIR inliner and GVN only when asked for them
//! explicitly (the default is the `-O0` MIR pipeline at every `-Copt-level`), and
//! the `_opt` rows are the MIR half of this row in the sessions that still inline.
//! `box_int_o2plain`, `param_chain_o2plain` and `ref_lifetime_o2plain` pin the
//! plain `-Copt-level=2` default: the same row as the `-O0` twin, at the same line.
//! Trust (D8-P0, 2026-09-23): A TRANSMUTE THAT MANUFACTURES A `Box` OR A
//! REFERENCE IS CHARGED WHERE IT IS MADE — the `[unsafe:validity-transmute]` row
//! (`compiler/rustc_mir_transform/src/trust_verify/validity_transmute.rs`).
//!
//! # The defect this pins
//!
//! The extractor models a `Transmute` into a `Box` as a plain cast with no
//! obligation, "because the deref's own validity obligation handles pointee
//! validity separately". Commit `047d35ba90`'s Box-PARAMETER validity root made
//! that false: `fn f(b: Box<u32>) -> u32 { *b }` mints no deref rows because its
//! callers are verified, and nothing in the caller charged the transmute.
//! Measured on the stage-1 `trustc` of 2026-09-23 (this file, `--cfg <rev>`),
//! every revision below marked "rc=0" compiled with NO error — thirteen live false
//! proofs — and the runtime witnesses (the same programs built as binaries by
//! the D8 decision probes) crashed:
//!
//! | revision | shape | before |
//! |---|---|---|
//! | `box_int`, `box_int_opt` | `transmute::<usize, Box<u32>>(4)` (`c1`) | rc=0 |
//! | `box_from_ref` | `&'static u32` → `Box<u32>` (`c6`; freeing a static) | rc=0 |
//! | `box_null_raw` | null `*mut u32` → `Box<u32>`, fed to the Box param root (`h4`) | rc=0 (binary aborts) |
//! | `param_chain`, `param_chain_opt` | `f(mk())`, `f(b: Box<u32>)` derefs (`h1`/`o_tmute`) | rc=0 at O0 and O2 (the O0 binary SIGSEGVs, exit 139) |
//! | `ref_null` | null `*const u32` → `&'static u32`, then `*mk()` (`h3`) | rc=0 (binary SIGSEGV) |
//! | `ref_lifetime`, `ref_lifetime_opt` | `transmute::<&u32, &'static u32>(&local)` (`h6`) | rc=0 |
//! | `struct_ref_opt` | `usize` → `struct W(&'static u32)`, then `*mk().0` | rc=0 at O2 (refused at O0 by other rows) |
//! | `mut_ref_opt` | `usize` → `&'static mut u32` | rc=0 at O2 (refused at O0 by other rows) |
//! | `option_box`, `bool_int`, `fnptr_null`, `vec_forge` | `Option<Box>`, `bool` from 2, null `fn`, a forged `Vec` | refused ONLY by lowering gaps today |
//! | `maybe_uninit_box_opt` | `transmute::<usize, MaybeUninit<Box<u32>>>(4).assume_init()`, fed to the Box param root (review of D8-P0) | rc=0 at O2 (refused at O0); the binary twin SIGSEGVs, exit 139 |
//! | `maybe_uninit_ref_opt` | the same through `MaybeUninit<&'static u32>`, then `*mk()` | rc=0 at O2 |
//!
//! The last row's revisions were already refused, but by a lowering gap that
//! any future lowering work would close; the NOTE pins that the creation row
//! itself now fires, so the refusal no longer depends on that gap.
//!
//! # The `*_box_opt` rails (required by the D8 critique)
//!
//! `zeroed_box_opt`, `assume_init_box_opt`, `transmute_copy_box_opt` and
//! `ptr_read_box_opt` make a `Box` through a SYSROOT channel at `-O2`, where the
//! channel's body is inlined into `mk` and any transmute inside it is exempt from
//! the creation row (nearest inlined instance = an authenticated sysroot def).
//! They were already refused before D8-P0 by rows that survive inlining, and
//! must stay refused: if one starts compiling, the sysroot-inline exemption is
//! hiding a validity break. (Known NOT to hold at `-O2`, and recorded in
//! KNOWN_HAZARDS rather than pinned here: `transmute_neo`, `slice::from_raw_parts`
//! of a dangling pointer, `NonNull::as_ref` — an inlined sysroot `unsafe fn`
//! loses its call-site row.)
//!
//! # Why the `maybe_uninit_*_opt` revisions matter
//!
//! A UNION target is walked field by field, not treated as inert. The first
//! draft of the row called `MaybeUninit<Box<T>>` inert on the theory that the
//! later field read is charged by `[unsafe:union-field]`; at `-O2` that read is
//! inside core's inlined `assume_init`, the unsafe call's own row is lost to
//! inlining, and GVN folds `mk` to `const Box(0x4)` — no transmute and no union
//! projection left in the MIR. The only surviving evidence is the HIR call.
//!
//! # Why the `ref_lifetime` revisions matter
//!
//! `InstSimplify` runs at EVERY opt-level and rewrites a transmute whose types
//! are equal after region erasure into a plain copy: `mk`'s `-O0` MIR is
//! `_0 = &_1; return`, with no transmute left for a MIR scan to see. The row is
//! therefore also charged from the body's HIR `transmute` calls, typed by
//! `typeck`. A "simplification" that keeps only the MIR scan re-opens `h6`.
//!
//! Positive controls — `Box::new`, a `Box` parameter, and inert transmutes
//! (`u32 -> i32`, `&u32 -> *const u32`) that must keep verifying — live in
//! `validity_transmute_inert_controls.rs`; the `#[trust::assume_total]` half of
//! the same change in `assume_total_does_not_cover_unsafe.rs`.

use std::mem::transmute;

#[cfg(any(box_int, box_int_o2plain))]
#[inline(never)]
pub fn mk() -> Box<u32> {
    //[box_int,box_int_o2plain]~^ ERROR safety verification incomplete
    //[box_int,box_int_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<usize, Box<u32>>(4) }
}

#[cfg(box_from_ref)]
pub fn mk() -> Box<u32> {
    //[box_from_ref]~^ ERROR safety verification incomplete
    //[box_from_ref]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<&'static u32, Box<u32>>(&3) }
}

#[cfg(box_null_raw)]
pub fn mk() -> Box<u32> {
    //[box_null_raw]~^ ERROR safety verification incomplete
    //[box_null_raw]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<*mut u32, Box<u32>>(core::ptr::null_mut()) }
}

#[cfg(box_null_raw)]
pub fn f(b: Box<u32>) -> u32 {
    let v = *b;
    core::mem::forget(b);
    v
}

#[cfg(box_null_raw)]
pub fn g() -> u32 {
    f(mk())
}

#[cfg(any(param_chain, param_chain_o2plain))]
#[inline(never)]
pub fn mk() -> Box<u32> {
    //[param_chain,param_chain_o2plain]~^ ERROR safety verification incomplete
    //[param_chain,param_chain_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<usize, Box<u32>>(4) }
}

// The Box-parameter root: this body stays row-free BY DESIGN — the caller's
// creation row above is what makes that sound.
#[cfg(any(param_chain, param_chain_o2plain))]
#[inline(never)]
pub fn f(b: Box<u32>) -> u32 {
    *b
}

#[cfg(any(param_chain, param_chain_o2plain))]
pub fn g() -> u32 {
    f(mk())
}

#[cfg(ref_null)]
#[inline(never)]
pub fn mk() -> &'static u32 {
    //[ref_null]~^ ERROR safety verification incomplete
    //[ref_null]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<*const u32, &'static u32>(core::ptr::null()) }
}

#[cfg(ref_null)]
#[inline(never)]
pub fn h() -> u32 {
    *mk()
}

#[cfg(any(ref_lifetime, ref_lifetime_o2plain))]
pub fn mk() -> &'static u32 {
    //[ref_lifetime,ref_lifetime_o2plain]~^ ERROR safety verification incomplete
    //[ref_lifetime,ref_lifetime_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    let x = 5u32;
    unsafe { transmute::<&u32, &'static u32>(&x) }
}

#[cfg(any(ref_lifetime, ref_lifetime_o2plain))]
pub fn h() -> u32 {
    *mk()
}

#[cfg(option_box)]
pub fn mk() -> Option<Box<u32>> {
    //[option_box]~^ ERROR safety verification incomplete
    //[option_box]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<usize, Option<Box<u32>>>(4) }
}

#[cfg(bool_int)]
pub fn mk() -> bool {
    //[bool_int]~^ ERROR safety verification incomplete
    //[bool_int]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<u8, bool>(2) }
}

#[cfg(fnptr_null)]
pub fn mk() -> fn() -> u32 {
    //[fnptr_null]~^ ERROR safety verification incomplete
    //[fnptr_null]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<usize, fn() -> u32>(0) }
}

#[cfg(vec_forge)]
pub fn mk() -> Vec<u32> {
    //[vec_forge]~^ ERROR safety verification incomplete
    //[vec_forge]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { transmute::<[usize; 3], Vec<u32>>([3, 4, 3]) }
}
