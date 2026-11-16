//@ needs-trust-verify
//@ revisions: plain_off plain_on optimized_off optimized_on
//@ check-fail
//@ compile-flags: -Ztrust-verify=off -Ztrust-policy=strict
//@ [plain_off] compile-flags: -Copt-level=0 -Ztrust-ir-lower=off
//@ [plain_on] compile-flags: -Copt-level=0 -Ztrust-ir-lower=on
//@ [optimized_off] compile-flags: -Copt-level=3 -Ztrust-ir-lower=off
//@ [optimized_on] compile-flags: -Copt-level=3 -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

// THE `_off` HOLE IS CLOSED (2026-09-16), and the revision qualifiers went with
// it. This file's annotations used to name `plain_on` / `optimized_on` only,
// with a comment recording that "the `_off` revisions do not produce this
// diagnostic at all -- the Clean-origin gates are reachable only under
// `-Ztrust-ir-lower=on`. That hole is real ... the `_off` revisions stay RED on
// purpose rather than being pinned as passing."
//
// The gate lives in the `optimized_mir` PROVIDER for the Clean-origin def, so
// WHEN it runs was decided by who demanded that MIR -- and the only demand was
// inside `rustc_interface`'s `-Ztrust-ir-lower` block. `passes.rs` now demands
// it at the analysis seam for every Clean-origin def this crate's Rust code
// NAMES, on every lane, because the island is a LANGUAGE surface (ruling v7/D1)
// and its kernel-backed call gate is deliberately not behind
// `-Ztrust-verify=off` either.
//
// MEASURED on this file: all four revisions now emit byte-identical diagnostics
// -- same error, same note, same span -- so the four qualified annotations
// collapse to two unqualified ones. That collapse is the evidence: while the
// hole was open the two halves could not have shared a spelling, and a
// regression that re-opened it would put two of the four revisions back in the
// "expected error never arrived" state this file spent months in.



// Trust: a Call destination can overwrite a reference through a frame alias
// without an Assign to that local. Its earlier frame provenance then becomes
// stale. Pin the MIR shape so destination propagation cannot erase this test.
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

// `extern crate core;` is required: this fixture is compiled at the ui suite's
// default edition, where a bare `use core::…` resolves nothing and fails E0433
// "cannot find `core` in the crate root" — which then cascades into "cannot find
// macro `mir`". Without it the file never compiled at all, so the refusal it
// pins was never exercised.
extern crate core;

use core::intrinsics::mir::*;

static GLOBAL: u64 = 23;

fn global_reference() -> &'static u64 {
    &GLOBAL
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read(a: u64) -> u64 {
    mir! {
        let reference: &u64;
        let alias: &mut &u64;
        {
            reference = &a;
            alias = &mut reference;
            Call(*alias = global_reference(), ReturnTo(done), UnwindContinue())
        }
        done = {
            RET = *reference;
            Return()
        }
    }
}

clean {
    def applyRead (a : UInt64) : UInt64 := read a
}
//~^^ ERROR cannot be called from Rust
//~| NOTE may only call a PURE Rust fn
// Trust: annotate outside the Clean island because `//` is not a Clean comment.
// The referenced Clean declaration must refuse this impure Rust callee in
// all four revisions, including metadata-only checks with IR lowering off.
// Historical compilers missed that demand; keep their failures as evidence.
// These assertions state the required behavior, not a completed runtime check.

fn main() {
    assert_eq!(applyRead(7), 23);
}
