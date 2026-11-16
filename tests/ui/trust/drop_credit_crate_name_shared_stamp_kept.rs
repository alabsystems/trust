//@ needs-trust-verify
// `aux-crate`, not `aux-build`: the aux's crate name IS this crate's name (its
// file stem is this file's), and `--extern dep=` binds it under a name that
// cannot collide in the extern prelude.
//@ aux-crate: dep=drop_credit_crate_name_shared_stamp_kept.rs
//@ revisions: scope_end holder certify bin_shape
//@ compile-flags: -Ztrust-verify=on
//@[scope_end] compile-flags: --crate-type lib -Ztrust-policy=strict
//@[holder] compile-flags: --crate-type lib -Ztrust-policy=strict
//@[certify] compile-flags: --crate-type lib -Ztrust-policy=certify
//@[bin_shape] compile-flags: --crate-type bin -Ztrust-policy=strict
//@ dont-check-compiler-stderr
// `bin_shape`'s `main` keeps an advisory warning on its panic-freedom row (the
// native module fails validation) on every compiler measured, the BEFORE of the
// collision fix included; it is not a drop row.
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! DROP-NAME-COLLIDE-1 (wave 15), WHAT THE WITHDRAWAL MUST NOT TAKE: a crate
//! that merely shares its dependency's NAME keeps the drop-glue verdicts of
//! types that have no namesake anywhere in the graph, when the extraction stamp
//! (`AdtAuth::TotalDrop`) certifies them.
//!
//! EVERY REVISION MUST STAY GREEN. Fix the compiler, never this file.
//!
//! # The defect this pins
//!
//! The fix for the collision (`drop_credit_crate_name_collision.rs`) first
//! JOINED every withdrawn path into the bundle's `drop_reach_open_adts`. The
//! bridge consults that set before EVERY arm of `is_panic_free_drop_ext`,
//! including the `AdtAuth::TotalDrop` stamp, which `tcx_drop_is_total` computes
//! on the concrete type (no user `Drop` anywhere in the owned tree, `has_dtor`)
//! and never by name. So in a crate named like its dependency, `Cfg { name:
//! String }` lost its verdict although no other crate has a `Cfg` and the credit
//! never needed the path at all. Measured 2026-10-05 (review of `444376149e`):
//!
//! | compiler | Cargo bin shape, `strict` | lib twin, `strict` / `certify` |
//! |---|---|---|
//! | `76a6ea45b2` (before the collision fix) | exit 0, `scope_end` proved | exit 0 / exit 0 |
//! | `444376149e` (the joined withdrawal) | exit 1, `[trust-drop-glue-assumption]` on `Cfg` | exit 1 / exit 1 |
//!
//! and with the dependency renamed (`bar`), exit 0 on both compilers. The debug
//! lane named the cause: `[DROP_GATE] ty=foo::Cfg RECURSIVE_VERDICT=false ...
//! reach_open={"foo::Cfg"}`.
//!
//! # The rule
//!
//! A shared-name path is withheld from the two NAME-keyed credits only — the
//! structural set and the bundled-destructor set — never joined into
//! `drop_reach_open_adts`. The collision fixture's revisions stay refused: the
//! dependency's `Conn` has a `Drop`, so it never carries the stamp.
extern crate dep;

// `scope_end` / `certify`: a `String`-owning struct dropped at scope end. Its
// glue is `String`'s, an audited std owner, so the extractor stamps it.
#[cfg(any(scope_end, certify))]
pub struct Cfg {
    pub name: String,
}
#[cfg(any(scope_end, certify))]
pub fn run(c: Cfg) -> usize {
    c.name.len()
}

// `holder` / `certify`: a `Box`-owning struct, the same stamp.
#[cfg(any(holder, certify))]
pub struct Holder {
    pub a: Box<u8>,
    pub b: u8,
}
#[cfg(any(holder, certify))]
pub fn take(h: Holder) -> u8 {
    h.b
}

// `bin_shape`: the Cargo layout itself — a BIN whose crate name is its lib's.
#[cfg(bin_shape)]
struct Cfg {
    name: String,
}
#[cfg(bin_shape)]
fn scope_end(c: Cfg) -> usize {
    c.name.len()
}
#[cfg(bin_shape)]
fn touch(_u: dep::Unit) {}
#[cfg(bin_shape)]
fn main() {
    touch(dep::Unit);
    let _ = scope_end(Cfg { name: String::from("x") });
}
