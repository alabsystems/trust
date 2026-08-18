//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Dropping a path's `{{extern}}` segment does not merely SHORTEN it: it MERGES
//! the `extern` block's imports into the block's GRANDPARENT namespace, where an
//! ordinary same-named item can already live. rustc's printer dropped that
//! segment unconditionally, so the bodyless foreign `boom` below and the LOCAL
//! `fn boom` — two `DefId`s, one bodyless import and one real body — rendered
//! ONE callee key. `trust_ir_bridge`'s `resolve_call_target` then found the local
//! body under that key and bound the FFI call to it, and the FFI result stopped
//! being havoc'd: the verifier read `a` as the local body's constant `1` and
//! PROVED the `a + b` overflow away.
//!
//! This is the `#0` case, and it is the COMMON one — a function with a single
//! `extern` block. It is NOT sibling ambiguity: the two `boom`s have DIFFERENT
//! `DefPath` parents (`{{extern}}#0` vs `go`), so no `DisambiguatedDefPathData`
//! disambiguator can separate them; only the dropped segment can. A gate on
//! `disambiguator != 0` closes the alias at `{{extern}}#1`
//! (`abi_total_key_alias_extern_block_stays_closed.rs`, which pins that case)
//! and leaves this one open, which is why the seam keeps the segment on EVERY
//! foreign path. Rendered spelling: `t_krate::go::{extern#0}::boom`.
//!
//! Two extern blocks in one MODULE cannot declare the same name (E0428), and a
//! block-scoped `fn` cannot share a scope with an import of the same name — so
//! the shape needs two BLOCKS of one function. Blocks are not `DefId`s, so both
//! hang off `go` and only the `{{extern}}` segment stands between them.
//!
//! MEASURED, both states, one identifier apart, on real compilers. The
//! observable is the OBLIGATION ROW SET, not the exit code: every FFI call also
//! mints a `hardened_ffi_boundary` row that is UNKNOWN either way (a CHC
//! construction gap), so this file is red on both sides — the same caveat
//! `abi_total_key_alias_extern_block_stays_closed.rs` carries. What flips is
//! whether a FAILING obligation exists at all.
//!
//! ```text
//! dropped {{extern}} segment (pristine, and the shipped stage2 trustc):
//!   Trust verification: 1 proved, 0 FAILED, 1 unknown out of 2 obligation(s)
//!     -- `a + b` PROVED. `a` is an `extern "C"` return; it can be u32::MAX.
//!
//! segment kept (with_def_path_disambiguators):
//!   Trust verification: 0 proved, 1 failed, 1 unknown out of 2 obligation(s)
//!     + note: [overflow:add] FAILED; counterexample: a = 4294967295, b = 1
//! ```
//!
//! Renaming ONLY the local `fn boom` to `boom2` reproduces the second state on
//! BOTH compilers, which is what pins the alias — not the arithmetic — as the
//! mechanism.
//!
//! SCOPE, stated so nobody over-reads it: under compiletest this file is
//! DOCUMENTATION, NOT A GUARD. It is `check-fail` on BOTH sides and carries
//! `dont-check-compiler-stderr`, so no compiletest observable distinguishes the
//! gate being present from the gate being removed — reopening the alias would
//! leave this file green. The differential above lives in the obligation ROW
//! SET, which compiletest is not reading here. The extern class consequently has
//! NO compiletest-visible guard; the gate's own falsification is the rig matrix
//! recorded on `with_def_path_disambiguators`. Giving this class an observable
//! needs the `hardened_ffi_boundary` UNKNOWN closed first (four shapes were
//! tried — `extern "C"` vs `"C-unwind"`, safe vs `unsafe fn`, `wrapping_add` vs
//! `+` — and it survives all of them).
#![no_std]
#![allow(dead_code)]

pub fn go(x: u32) -> u32 {
    let a = {
        // The ONLY extern block in `go`, so its segment is `{{extern}}#0` — the
        // one a disambiguator-indexed gate would still drop.
        unsafe extern "C" {
            safe fn boom(x: u32) -> u32;
        }
        boom(x)
    };
    let b = {
        // An ordinary local body under the SAME `DefPath` parent. Its constant
        // return is what the FFI call used to be proved against.
        fn boom(_x: u32) -> u32 {
            1
        }
        boom(x)
    };
    a + b
}
