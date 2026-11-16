//@ needs-trust-verify
// `aux-crate`, not `aux-build`: the aux's crate name IS this crate's name (its
// file stem is this file's), and `--extern dep=` binds it under a name that
// cannot collide in the extern prelude.
//@ aux-crate: dep=drop_credit_crate_name_collision.rs
//@ revisions: same_name structural bin_shape renamed
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@[same_name] compile-flags: --crate-type lib
//@[structural] compile-flags: --crate-type lib
//@[renamed] compile-flags: --crate-type lib
//@[bin_shape] compile-flags: --crate-type bin
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! DROP-NAME-COLLIDE-1 (wave 15, 2026-10-03) — DROP-GLUE CREDIT KEYED BY A
//! CRATE-NAME-QUALIFIED PATH, INHERITED BY A SAME-NAMED CRATE'S SAME-PATH TYPE.
//!
//! EVERY REVISION MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! # The defect
//!
//! `collect_structural_drop_adts` (`rustc_mir_transform/src/trust_verify.rs`)
//! credits an ADT's drop glue when the ADT has no `Drop` impl, or has one whose
//! body proved panic-free, by inserting its `safe_def_path_str` into the bundle's
//! structural set. The bridge's `is_panic_free_drop_ext` then credits EVERY
//! `Ty::Adt` of that name. The path spells the crate NAME, not its identity, so
//! when two crates share a name — Cargo's bin+lib layout (both `foo`), two
//! versions of one crates.io crate, or this file and its aux — a credit earned
//! by one crate's `Conn` was spent on the other's, and the dependency's
//! panicking `drop` was never charged.
//!
//! BEFORE, measured 2026-10-05 on a stage 1 whose drop-credit code matches
//! `d5da8dc314` (`scratchpad/stage1-w13fix`), each revision built with its own
//! flags plus `--emit=metadata`, the aux with its own:
//!
//! | revision | exit | report |
//! |---|---|---|
//! | `same_name` | 0 | 2/2 verified; `run`'s panic-freedom row `proved` (trust-full-verifier) |
//! | `structural` | 0 | `run`'s panic-freedom row `proved`, beside the vacuous global-alloc row |
//! | `bin_shape` | 0 | 3/3 verified (`run`, `main`, the local `drop`) |
//! | `renamed` | 1 | `run` refused: the dependency `Conn`'s drop glue `runtime_checked` |
//!
//! `bin_shape` built as a real binary under the same certify flags exits 101
//! ("dependency Conn dropped with 7"), and so did a two-version graph (two rlibs
//! both `--crate-name foo`, a `Pair` of `foo_v1::S` and `foo_v2::S`: certify
//! exit 0, 1/1 verified, the program exit 101; docs/KNOWN_HAZARDS.md).
//!
//! # The fix
//!
//! `trust_mir_extract::crate_name_is_shared` is the one duplicate-crate-name
//! rule (also read by the extractor's callee disambiguation and by the X1
//! destructor-admission shadow check). The structural walk no longer credits an
//! ADT whose crate's name is shared: it WITHDRAWS the path, which the bundle keeps
//! out of its structural set and subtracts from `bundled_destructor_adts`, the
//! bridge's two NAME-keyed credits. Both same-path `Conn`s keep their
//! `[trust-drop-glue-assumption]` row: neither carries the extraction stamp
//! (`AdtAuth::TotalDrop`), which `tcx_drop_is_total` computes per concrete type
//! and keeps off any type with a user `Drop`. (Narrowed 2026-10-05: the first cut
//! joined the withdrawals into `drop_reach_open_adts`, which also cancelled that
//! stamp for namesake-free types; `drop_credit_crate_name_shared_stamp_kept.rs`
//! pins what the withdrawal must not take.)
//!
//! AFTER, measured 2026-10-05 on the stage 1 of `444376149e` (main `2a1adf641f`
//! plus wave 15): every revision exits 1 with "Trust strict verification failed"
//! on `run` (`bin_shape` also on `main`), as the twins without the local credit
//! did; on the BEFORE stage 1 of `76a6ea45b2` only `renamed` was refused.
//!
//! # The cost, on purpose
//!
//! `renamed` (and every revision's own local types) loses credit too: in a graph
//! with a duplicate crate name, EVERY ADT of those crates loses its NAME-keyed
//! drop credit (the structural set, the bundled-destructor set), so the bin target
//! of a Cargo bin+lib package refuses drops of its types that only those credits
//! covered — a type with a user `Drop`, even an empty one, or one that owns such
//! a type. A type whose whole owned tree has no user `Drop` keeps the stamp.
//! Fail-closed; ruled in docs/DECISION_QUEUE.md (DROP-NAME-COLLIDE-1).
//! The runtime witness that the dependency's `drop` really panics is
//! `drop_credit_crate_name_collision_run.rs`.
extern crate dep;

// `same_name`: a local `Conn` with an EMPTY `Drop` (proved total, so credited)
// beside the dependency's panicking `Conn`, both rendered
// `drop_credit_crate_name_collision::Conn`.
#[cfg(same_name)]
pub struct Conn(pub u8);
#[cfg(same_name)]
impl Drop for Conn {
    fn drop(&mut self) {}
}
#[cfg(same_name)]
pub fn run(local: Conn, remote: dep::Conn) -> u8 { //[same_name]~ ERROR Trust strict verification failed
    let r = local.0;
    drop(remote);
    r
}

// `structural`: the no-`Drop` arm — a local `Conn` whose glue is only its fields.
// (A `Conn(u8)` would not do: it has no drop glue, so no `Drop` terminator
// names it and nothing credits the path.)
#[cfg(structural)]
pub struct Conn(pub u8, pub Box<u8>);
#[cfg(structural)]
pub fn run(local: Conn, remote: dep::Conn) -> u8 { //[structural]~ ERROR Trust strict verification failed
    let r = local.0;
    drop(remote);
    r
}

// `bin_shape`: the Cargo layout itself — a BIN whose crate name is its lib's.
#[cfg(bin_shape)]
struct Conn(u8);
#[cfg(bin_shape)]
impl Drop for Conn {
    fn drop(&mut self) {}
}
#[cfg(bin_shape)]
fn run(local: Conn, remote: dep::Conn) -> u8 { //[bin_shape]~ ERROR Trust strict verification failed
    let r = local.0;
    drop(remote);
    r
}
#[cfg(bin_shape)]
fn main() {
    let _ = run(Conn(1), dep::Conn(7));
}

// `renamed`: the CONTROL — the same program with the local type renamed, so no
// path collides. Refused before and after: the collision was the whole cause.
#[cfg(renamed)]
pub struct Local(pub u8);
#[cfg(renamed)]
impl Drop for Local {
    fn drop(&mut self) {}
}
#[cfg(renamed)]
pub fn run(local: Local, remote: dep::Conn) -> u8 { //[renamed]~ ERROR Trust strict verification failed
    let r = local.0;
    drop(remote);
    r
}
