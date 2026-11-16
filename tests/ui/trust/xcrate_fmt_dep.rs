//@ needs-trust-verify
//@ aux-build:xcrate_fmt_dep.rs
//@ aux-build:xcrate_fmt_dep_nomir.rs
//@ aux-build:xcrate_fmt_dep_on.rs
//@ revisions: declared format_declared undeclared bad err_dep format_err_dep oob via_helper
//@ revisions: exported drops unsafe_noop tmute_region budget_body budget_count
//@ revisions: nomir on_undeclared on_declared
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[declared] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[format_declared] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[bad] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[err_dep] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[format_err_dep] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[oob] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[via_helper] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[exported] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[drops] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[unsafe_noop] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[tmute_region] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[budget_body] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[budget_body] rustc-env:TRUST_REDERIVE_MAX_BODY_BLOCKS=0
//@[budget_count] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[budget_count] rustc-env:TRUST_REDERIVE_MAX_BODIES=0
//@[nomir] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep_nomir
//@[on_declared] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep_on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[declared] check-pass
//@[format_declared] check-pass
//@[on_declared] check-pass
//@[undeclared] check-fail
//@[bad] check-fail
//@[err_dep] check-fail
//@[format_err_dep] check-fail
//@[oob] check-fail
//@[via_helper] check-fail
//@[exported] check-fail
//@[drops] check-fail
//@[unsafe_noop] check-fail
//@[tmute_region] check-fail
//@[budget_body] check-fail
//@[budget_count] check-fail
//@[nomir] check-fail
//@[on_undeclared] check-fail
//! D4 increment A (2026-09-24) — a DEPENDENCY's `Debug` impl at a formatting
//! sink is credited only by RE-DERIVING it here, never by importing a verdict.
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED. A refused revision going green
//! is a possible FALSE PROOF until shown otherwise. Fix the compiler, never
//! this file.
//!
//! # The decision
//!
//! D4 rejected an rmeta "compiled under a verifying lane" bit (a verdict import;
//! `false` for every dependency on the `targo trust` lane; and a verify-on crate
//! still ships panicking functions). Instead the shared panic-freedom bar
//! (`dyn_target_is_verified_panic_free`) accepts a NON-LOCAL impl only when this
//! compilation can re-derive it (`trust_verify/foreign_rederivation.rs`): its
//! crate is DECLARED (`-Ztrust-bundle-foreign-crate`) and is the crate bound
//! under that name, is statically linked, is not the sysroot, encodes MIR, the
//! body exports no interposable symbol, carries no user `unsafe` source (a fact
//! the dependency's own compiler encoded beside its MIR), and fits the cost
//! bound. The verdict is then computed HERE, under this compilation's policy,
//! by the same bar a local impl clears, and a formatting sink ALSO requires
//! error transparency (D1 increment 0), read off the same encoded MIR.
//!
//! # Measured BEFORE
//!
//! Stage-1 snapshot at `4e9fe36bf` (current main, without this change), through
//! a compiletest-equivalent harness: EVERY revision refused, the `println!`
//! ones with "a value is formatted through a user `Display`/`Debug`
//! implementation whose panic-freedom was not established" and the `format!`
//! ones with "Trust strict verification failed" — `declared`,
//! `format_declared` and `on_declared` included. On the same compiler a LOCAL
//! copy of `Good` builds rc=0 through both `println!` and `format!`; a local
//! `UnsafeNoop` builds rc=0; a local `TmuteRegion` and a local `format!` of
//! `ErrE` are refused.
//!
//! # The revisions
//!
//! Every refusal pins the NOTE naming WHY (`fmt_error_transparency::
//! foreign_formatter_note`), so a revision cannot pass for an unrelated reason.
//!
//! * `declared` / `on_declared` — check-pass: `Good` re-derived from a verify-off
//!   (resp. verify-on) dependency. Both must give the SAME answer: the
//!   dependency's own verification is never read.
//! * `undeclared`, `on_undeclared` — not declared: nothing is re-derived, and a
//!   verify-on dependency buys nothing by itself (no rmeta bit).
//! * `nomir` — declared, but no `-Zalways-encode-mir`: nothing to re-derive.
//! * `bad` — the impl panics. `oob` — it indexes out of bounds on this input.
//!   Both are re-derived (pinned) and fail the bar.
//! * `via_helper` — the panic is in a non-generic helper of the dependency, a
//!   bundled MEMBER of the re-derived root, not in the impl's own body.
//! * `format_declared` — check-pass: `Good` through `format!`.
//! * `err_dep` / `format_err_dep` — PANIC-FREE but returns `Err(fmt::Error)`:
//!   `println!`/`format!` panic inside std (the F1 class, cross-crate). The bar
//!   alone accepts it (`err_dep` pins the bar's "is verified" answer); error
//!   transparency refuses it.
//! * `exported` — `Good`'s body under `#[no_mangle]`: link-time interposition
//!   means the checked body need not be the one that runs.
//! * `drops` — `Good`'s body plus a `drop` of a dependency type with a `Drop`
//!   impl: the X1 rule (a dependency's `Drop` is never credited from its MIR)
//!   leaves that row unproved, so the impl is not panic-free here.
//! * `unsafe_noop` — `Good`'s body plus an `unsafe` block around a SAFE
//!   expression. Its MIR has no unsafe operation and a local copy verifies, so
//!   only the SOURCE FACT can decline it: this revision is the liveness control
//!   for the fact (a deliberate completeness cost — any user `unsafe` declines).
//! * `tmute_region` — a lifetime-only `transmute` InstSimplify erases from the
//!   encoded MIR; a local copy is refused by the HIR half of
//!   `validity_transmute`, which cannot see a dependency body. The adversarial
//!   review's FALSE-ACCEPT finding #1: declined on the source fact.
//! * `budget_body` / `budget_count` — the cost bound, lowered to zero through
//!   its lower-only environment knobs: `Good` is declined as too large, and as
//!   over the per-crate body count.
extern crate xcfmt_dep;
extern crate xcfmt_dep_nomir;
extern crate xcfmt_dep_on;

#[cfg(any(declared, undeclared, budget_body, budget_count))]
pub fn f() {
    //[undeclared,budget_body,budget_count]~^ ERROR a value is formatted through a user
    //[undeclared]~| NOTE was not re-derived in this compilation: it is not local to this crate and its crate is not in the declared bundling scope
    //[budget_body]~| NOTE was not re-derived in this compilation: it exceeds the per-body re-derivation cost bound
    //[budget_count]~| NOTE was not re-derived in this compilation: it exceeds this compilation's re-derivation budget
    println!("{:?}", xcfmt_dep::Good);
}

#[cfg(bad)]
pub fn f() {
    //[bad]~^ ERROR a value is formatted through a user
    //[bad]~| NOTE was re-derived in this compilation from its crate's encoded MIR
    println!("{:?}", xcfmt_dep::Bad);
}

#[cfg(err_dep)]
pub fn f() {
    //[err_dep]~^ ERROR a value is formatted through a user
    //[err_dep]~| NOTE error transparency: `<xcfmt_dep::ErrE as
    //[err_dep]~| NOTE the shared panic-freedom bar's answer for it: is verified (no decline)
    println!("{:?}", xcfmt_dep::ErrE);
}

#[cfg(format_declared)]
pub fn f() -> String {
    format!("{:?}", xcfmt_dep::Good)
}

#[cfg(format_err_dep)]
pub fn f() -> String {
    //[format_err_dep]~^ ERROR Trust strict verification failed
    //[format_err_dep]~| NOTE error transparency: `<xcfmt_dep::ErrE as
    format!("{:?}", xcfmt_dep::ErrE)
}

#[cfg(oob)]
pub fn f() {
    //[oob]~^ ERROR a value is formatted through a user
    //[oob]~| NOTE was re-derived in this compilation from its crate's encoded MIR
    println!("{:?}", xcfmt_dep::Oob(7));
}

#[cfg(via_helper)]
pub fn f() {
    //[via_helper]~^ ERROR a value is formatted through a user
    //[via_helper]~| NOTE was re-derived in this compilation from its crate's encoded MIR
    println!("{:?}", xcfmt_dep::ViaHelper(7));
}

#[cfg(exported)]
pub fn f() {
    //[exported]~^ ERROR a value is formatted through a user
    //[exported]~| NOTE was not re-derived in this compilation: it exports an unmangled or linkage-controlled symbol
    println!("{:?}", xcfmt_dep::Exported);
}

#[cfg(drops)]
pub fn f() {
    //[drops]~^ ERROR a value is formatted through a user
    //[drops]~| NOTE was re-derived in this compilation from its crate's encoded MIR
    println!("{:?}", xcfmt_dep::Drops);
}

#[cfg(unsafe_noop)]
pub fn f() {
    //[unsafe_noop]~^ ERROR a value is formatted through a user
    //[unsafe_noop]~| NOTE was not re-derived in this compilation: it contains user `unsafe` source
    println!("{:?}", xcfmt_dep::UnsafeNoop);
}

#[cfg(tmute_region)]
pub fn f() {
    //[tmute_region]~^ ERROR a value is formatted through a user
    //[tmute_region]~| NOTE was not re-derived in this compilation: it contains user `unsafe` source
    println!("{:?}", xcfmt_dep::TmuteRegion(std::hint::black_box(5)));
}

#[cfg(nomir)]
pub fn f() {
    //[nomir]~^ ERROR a value is formatted through a user
    //[nomir]~| NOTE its crate encodes no MIR for it
    println!("{:?}", xcfmt_dep_nomir::Good);
}

#[cfg(any(on_declared, on_undeclared))]
pub fn f() {
    //[on_undeclared]~^ ERROR a value is formatted through a user
    //[on_undeclared]~| NOTE was not re-derived in this compilation: it is not local to this crate and its crate is not in the declared bundling scope
    println!("{:?}", xcfmt_dep_on::Good);
}
