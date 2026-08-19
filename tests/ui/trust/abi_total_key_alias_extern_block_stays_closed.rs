//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The `abi_total_panic_free` lane is the one whose donation is INVISIBLE: it
//! emits no obligation and no assumption row, so a call that collects a
//! neighbour's ABI credit simply disappears from the report. This file pins the
//! `{{extern}}` half of the key-NARROWING repair. It is a NARROWING, not an
//! injectivity guarantee: see the residual list on `direct_call_def_path`.
//!
//! `collect_expected_absent_callees` inserts a call into `abi_total_out` when the
//! callee is a rustc-authenticated bodyless FOREIGN import whose ABI is
//! NON-UNWINDING. `extern "C"` qualifies; `extern "C-unwind"` deliberately does
//! NOT, because it may unwind into this frame. rustc's path printer DROPPED the
//! `{{extern}}` segment unconditionally, which MERGES every extern block's
//! imports into the block's GRANDPARENT namespace — so the two `boom` imports
//! below, two distinct `DefId`s with two different ABIs, rendered ONE callee key
//! and the `extern "C"` insert discharged the `extern "C-unwind"` call too.
//!
//! SCOPE: this file is the TWO-BLOCK case. The hazard is the MERGE, not sibling
//! ambiguity, so it is equally present with a SINGLE extern block — a foreign
//! import merging with an ordinary item of the same name under one function.
//! That case is `foreign_import_key_alias_grandparent_merge_stays_closed.rs`,
//! and it is why the seam keeps the segment on EVERY foreign path rather than
//! only where an extern-block disambiguator is nonzero. An earlier revision of
//! this repair gated on `disambiguator != 0` and left the single-block case
//! open; the rationale it shipped ("two extern blocks under one parent are
//! #0/#1, keep the skip for the unambiguous #0") was MEASURED FALSE.
//!
//! Two extern blocks in one MODULE cannot declare the same name (E0428), which is
//! why the shape needs two BLOCKS of one function: blocks are not `DefId`s, so
//! both extern blocks hang off `go` and the two `boom`s are in separate
//! name-resolution scopes.
//!
//! MEASURED, both states, on two real compilers built from this tree. The
//! observable is the OBLIGATION COUNT, not the exit code: every raw FFI call also
//! mints `hardened_ffi_boundary` / `hardened_unsafe_operation` rows that never
//! prove, so this file is red either way and its raw error-pattern annotation
//! alone cannot witness the gate (the same caveat
//! `static_str_write_fmt_placeholder_site_stays_closed.rs` carries). Do not
//! spell that annotation literally in prose: compiletest scans for the marker
//! ANYWHERE in the file, comments included, and would register this sentence as
//! a second expected diagnostic.
//!
//! ```text
//! dropped {{extern}} segment (pristine, and the shipped stage2 trustc):
//!   Trust verification: 0 proved, 2 failed, 2 unknown, 0 runtime-checked out of 4 obligation(s)
//!
//! segment kept (with_def_path_disambiguators):
//!   Trust verification: 0 proved, 2 failed, 2 unknown, 1 runtime-checked out of 5 obligation(s)
//!   + note: an unproven panic-freedom obligation for a call to an absent callee …
//!   + vc:…__go:assertion:panic-freedom:0
//! ```
//!
//! The fifth obligation is the `extern "C-unwind"` call's panic-freedom row: the
//! row the `extern "C"` sibling used to pay for.
#![no_std]
#![allow(dead_code)]

pub unsafe fn go(x: u32) -> u32 {
    let a = {
        // Non-unwinding foreign import: legitimately enters `abi_total_panic_free`.
        extern "C" {
            fn boom(x: u32) -> u32;
        }
        unsafe { boom(x) }
    };
    let b = {
        // MAY UNWIND into this frame, so it must never enter that set — and must
        // not collect its identically-named neighbour's membership either.
        extern "C-unwind" {
            fn boom(x: u32) -> u32;
        }
        unsafe { boom(x) }
    };
    a.wrapping_add(b)
}
