//@ revisions: rl rr i64r u8l callonce slice
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[rl] check-pass
//@[rr] check-pass
//@[i64r] check-pass
//@[u8l] check-pass
//@[callonce] check-pass
//@[slice] check-fail
//@[rl] forbid-output: an unresolved indirect call
//@[rr] forbid-output: an unresolved indirect call
//@[i64r] forbid-output: an unresolved indirect call
//@[u8l] forbid-output: an unresolved indirect call
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! core's TOTAL integer `rotate_left` / `rotate_right`, handed to a callee as a
//! function ITEM, is admitted under the default policy like its same-signature
//! siblings (ROTATE-ITEM-NAME-1; 2026-10-06).
//!
//! A sysroot fn item passed as a value runs inside the callee, where no call-site
//! row is minted, so the compiler admits it only when `trust_vcgen::
//! callee_has_call_site_panic_family` names no panic family for it. That union's
//! bounds-panicking mutator arm (`rotate_left`/`rotate_right`, `split_off`, `drain`,
//! ...) matched the method tail with no owner, so core's integer
//! `core::num::<impl u32>::rotate_left` — `intrinsics::rotate_left(self, n)`, which
//! cannot panic — was withheld, and the function refused ("an unresolved indirect
//! call keeps the function fail-closed"), while `fold(1u32, u32::wrapping_shl)` (same
//! signature, same owner) and the closure twin `|a, b| a.rotate_left(b)` were
//! admitted. The arm now skips core's authenticated primitive-integer inherent
//! (`numeric_panic::int_inherent`). The slice's `rotate_left`, which panics when `mid
//! > len`, stays refused (`slice`).
//!
//! BEFORE (the stage 1 of `46e9afaf95`, `scratchpad/stage1-w21before`, measured
//! 2026-10-09 with this header's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata --error-format=json -A unused`): `rl`,
//! `rr`, `i64r`, `u8l` and `callonce` each exit 1 with one error, "Trust strict
//! verification failed" for their one function; `slice` exits 1 with exactly the
//! annotated error. With `TRUST_VANILLA_DEBUG=1`, `rl`'s `fold` callee is
//! `vanilla=false` with `[CALLABLE_TYPE_ARG] unresolved fn(u32, u32) -> u32
//! {core::num::<impl u32>::rotate_left}`, while the closure twin's direct call
//! `core::num::<impl u32>::rotate_left` is `vanilla=true`. The same shapes with
//! `u32::wrapping_shl` (`fold` and `call_once`) and `i64::wrapping_shr` build exit 0 on
//! that compiler. The run twin (`int_rotate_fn_item_admitted_run.rs`): `total` exits
//! 0 (`fold(1u32, u32::rotate_left)` over `[0, 31, 32, 1000, u32::MAX]` is 64), and
//! `slice` panics "assertion failed: mid <= self.len()" (exit 101).
//!
//! AFTER, MEASURED 2026-10-10 (wave-21 integration) on the stage 1 of `d58bad8195`
//! (`integ/wave21`: origin/main `32b6ef82d6` plus wave 21), against the stage 1 of
//! origin/main `32b6ef82d6` (`scratchpad/stage1-w21base`), same flags:
//!
//!   * `callonce` exits 0 (it exited 1 before, on "an unresolved indirect call keeps
//!     the function fail-closed"). Its one row, the `call_once` shim's `[assert]`, is
//!     `runtime-checked` on both compilers; with the item no longer withheld
//!     (`TRUST_VANILLA_DEBUG`: `vanilla=false` before, `vanilla=true` after), the
//!     default policy reports that row and builds. `certify` still refuses it.
//!   * `rl`, `rr`, `i64r` and `u8l` are STILL refused (before, each exited 1 with the
//!     deny-list's "an unresolved indirect call" note), now by a different gate. The
//!     fn-item deny-list no longer withholds the item (`TRUST_VANILLA_DEBUG`: the
//!     `fold` callee is `vanilla=true`, and the "an unresolved indirect call" note is
//!     gone, which each revision's `forbid-output` pins). But ZERO-ROW-GATE, which
//!     landed on `main` after this lane branched, refuses a zero-obligation body
//!     whose call no authenticated registry discharges. The `fold` call is
//!     discharged only by the sysroot panic census (`arm=typed-self-total`, as
//!     `fold(1u32, u32::wrapping_shl)` is), and the census answers `total=false`
//!     here: core's `intrinsics::rotate_left`/`rotate_right` fallback body computes
//!     `shift % (mem::size_of::<T>() as u32 * 8)`, and the census does not fold
//!     `<T as SizedTypeProperties>::SIZE as u32 * 8`, so it reports "a `remainder by
//!     zero` check in `core::intrinsics::rotate_left`"
//!     (`TRUST_SYSROOT_CENSUS_DEBUG=1`). That refusal is fail-closed and is not this
//!     lane's to lift (docs/KNOWN_HAZARDS.md, ROTATE-ITEM-NAME-1). When the census
//!     folds that divisor, these four revisions should exit 0 and become check-pass.
//!   * `slice` is unchanged. `-Ztrust-policy=certify` and `memory-safe` admit only
//!     structurally accounted items and are not affected either way.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): `rl`, `rr`, `i64r` and `u8l` build
//! (check-pass), as `callonce` does. Their `fold` is no longer a zero-obligation body:
//! the merged bundle carries the counted panic-freedom aggregate for the bundled
//! `fold`, and the census's `remainder by zero` check in core's rotate fallback stays
//! a `runtime_checked` row (`0 proved, 1 runtime-checked`), which the default policy
//! reports and builds, exactly as it does `callonce`'s `call_once` shim row. The census
//! still does not fold the divisor; `certify` would still refuse these.

#![cfg_attr(any(callonce, slice), feature(fn_traits))]

#[cfg(rl)]
pub fn rl(v: &[u32]) -> u32 {
    v.iter().copied().fold(1u32, u32::rotate_left)
}

#[cfg(rr)]
pub fn rr(v: &[u32]) -> u32 {
    v.iter().copied().fold(1u32, u32::rotate_right)
}

#[cfg(i64r)]
pub fn i64r(v: &[u32]) -> i64 {
    v.iter().copied().fold(3i64, i64::rotate_right)
}

#[cfg(u8l)]
pub fn u8l(v: &[u32]) -> u8 {
    v.iter().copied().fold(3u8, u8::rotate_left)
}

#[cfg(callonce)]
pub fn callonce(x: u32, k: u32) -> u32 {
    core::ops::FnOnce::call_once(u32::rotate_left, (x, k))
}

#[cfg(slice)]
pub fn slc(s: &mut [u8], k: usize) {
    //[slice]~^ ERROR Trust strict verification failed for `int_rotate_fn_item_admitted::slc`
    core::ops::FnOnce::call_once(<[u8]>::rotate_left, (s, k))
}
