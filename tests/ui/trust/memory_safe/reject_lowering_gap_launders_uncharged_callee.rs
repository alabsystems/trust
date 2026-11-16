//@ needs-trust-verify
//@ aux-build: memory_safe_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! ADVERSARIAL CONTROL: an unmodelled construct must never turn a refusal into a
//! pass.
//!
//! `read_returning` is the refused twin. Its unverified dependency call
//! `dep::deref_raw` (an arbitrary-address read in a crate compiled
//! `-Ztrust-verify=off`) is charged by the native bundle as
//! `[trust-absent-callee-assumption] … may panic`, and memory-safe does not admit
//! that charge.
//!
//! When the native typed-TrustIr lowering of a no-`unsafe` body does not
//! complete, memory-safe collapsed the failure into ONE `assumption:native-lowering`
//! row and admitted it, and the charges the bundle would have minted for the
//! body's OTHER calls were never created. The `vec_macro_*` bodies build a `Vec`
//! with `vec![..]` and index it: the bundle refuses the Assert-bearing member
//! `<usize as SliceIndex<[u32]>>::index` behind `Vec::index`, the lowering stops,
//! and the dependency call went with it. Measured on stage-1 `f0e3202c07` with this
//! file: both built with no error and no warning, their JSON rows a proof, the
//! skipped collapse row and the skipped `GlobalAlloc::dealloc` contract row (for
//! `vec_macro_then_dep_ub`, over a call into `unreachable_unchecked`), while every
//! other function here was refused. The collapse now stands only for a body whose
//! every call resolves to a local, verified function
//! (`memory_safe_assumption_uncharged_edges`), the gate refuses a lowering failure
//! that no collapse row accounts for, and the refusal names the edges.
//!
//! **The vehicle changed on 2026-09-28 (local line).** A `Vec` scalar index now lowers
//! (`vec_scalar_index_on_seq_receiver.rs`), so `vec![..]` plus `v[1]` no longer stops the
//! lowering. The two bodies were then refused on the direct charge, and this file had
//! stopped testing the collapse at all. The `to_string_*` bodies were added then as a
//! construct that still stopped it: `u32::to_string`, whose `_fmt_inner` member the
//! bundle refused (a guarded `Assert`). Main reached the same conclusion
//! independently (W4, below) and moved the collapse pin to the `generic_then_dep_*`
//! twins, whose stop is a LOCAL generic member and holds on any std. Since the merge
//! (2026-10-14) `_fmt_inner` is an authentic std member, so main's `de66170e69`
//! disposition may keep its refused `Assert` as a runtime-checked row and let the
//! lowering complete; the `to_string_*` bodies therefore pin only the REFUSAL (on
//! the charge or on the collapse gate, whichever is reached), not the named-edge
//! note. What this file needs is a no-`unsafe` body whose lowering does NOT
//! complete — today that is `generic_then_dep_*`.
//!
//! The `*_behind_*` bodies are the salvage's first triggers: a guard calling an
//! unrecognized `-> !` callee with no cleanup edge, which the lowering used to
//! refuse. On stage-1 `b4bc7cdf9d` each of them was admitted the same way. Since
//! `a84aa67936` (T2) that call lowers, the bundle charges it, and they are refused
//! on the charge like `read_returning` (measured on `f0e3202c07`); they stay here
//! so that neither path can re-open them. The negative control is
//! `admit_lowered_bodies_with_sysroot_calls.rs`.
//!
//! The `vec_macro_*` bodies no longer reach the collapse on a compiler with W4
//! VEC-AS-SLICE (branch `w4-vecslice`, re-pinned at the W4 salvage rebase onto
//! `296873da69`, 2026-09-29): the `Vec` index is charged at the caller's row and its
//! member `Assert` forwarded, so the lowering completes, the bundle charges the
//! dependency call itself (`[trust-absent-callee-assumption] call to absent callee
//! memory_safe_unverified_dep::deref_raw` / `::get`, runtime-checked, in the
//! `-Ztrust-verify-output=both` rows) and memory-safe refuses that charge, as it
//! refuses `read_returning`. Their NOTE pins that row count instead of the gap note
//! (since 2026-09-30 the line counts the published rows, so the refuted `v[1]` that
//! memory-safe demotes is "skipped" there, as in the JSON, not "failed").
//! The `generic_then_dep_*` twins keep the collapse gate's named-edge refusal pinned:
//! their lowering still stops, at the Assert-bearing bundled member `bump::<u32>` — a
//! LOCAL generic instance, so its `Overflow(Add)` Assert is neither exempt (the
//! own-root run verified the polymorphic body) nor eligible for the runtime-checked
//! std-member disposition (not a sysroot body) — and they are refused with the edge
//! named (measured on the W4 landing stage 1 `0.10.0+g452d2eef7`, on origin/main
//! `fbb9fa383d`). `bump` itself is refuted (`k + len` can overflow) and memory-safe
//! demotes that to a warning.
//!
//! (W4 landing, 2026-09-29: the twins used to be `count_then_dep_*`, whose lowering
//! stopped at `.count()`'s bundled `Iterator::count::{closure#0}`. That member's
//! `Overflow(Add)` Assert exists only in a std built with overflow checks, and since
//! main's `de66170e69` an authentic std member's refused Assert keeps the bundle as a
//! runtime-checked row: `.count()` no longer stops the lowering, the dependency call is
//! charged directly, and the named-edge note is gone. A local generic member stops the
//! lowering on any std.)
extern crate memory_safe_unverified_dep as dep;

fn bump<T>(w: &[T], k: u32) -> u32 {
    k + w.len() as u32
}

pub fn read_returning(v: &[u32], i: usize, p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::read_returning`
    if i >= v.len() {
        return 0;
    }
    v[i] ^ dep::deref_raw(p)
}

pub fn vec_macro_then_dep_read(p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::vec_macro_then_dep_read`
    //~| NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 4 obligation(s)
    let v = vec![1u32, 2, 3];
    v[1] ^ dep::deref_raw(p)
}

pub fn vec_macro_then_dep_ub(w: &[u32]) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::vec_macro_then_dep_ub`
    //~| NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 4 obligation(s)
    let v = vec![1u32, 2, 3];
    v[1] ^ dep::get() ^ w.len() as u32
}

pub fn to_string_then_dep_read(n: u32, p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::to_string_then_dep_read`
    n.to_string().len() as u32 ^ dep::deref_raw(p)
}

pub fn to_string_then_dep_ub(n: u32, w: &[u32]) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::to_string_then_dep_ub`
    n.to_string().len() as u32 ^ dep::get() ^ w.len() as u32
}

pub fn generic_then_dep_read(w: &[u32], p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::generic_then_dep_read`
    //~| NOTE `dep::deref_raw` in bb
    bump(w, 1) ^ dep::deref_raw(p)
}

pub fn generic_then_dep_ub(w: &[u32]) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::generic_then_dep_ub`
    //~| NOTE `dep::get` in bb
    bump(w, 1) ^ dep::get()
}

pub fn read_behind_exit(v: &[u32], i: usize, p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::read_behind_exit`
    if i >= v.len() {
        std::process::exit(1);
    }
    v[i] ^ dep::deref_raw(p)
}

pub fn read_behind_resume_unwind(v: &[u32], i: usize, p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::read_behind_resume_unwind`
    if i >= v.len() {
        std::panic::resume_unwind(Box::new(0u8));
    }
    v[i] ^ dep::deref_raw(p)
}

pub fn read_behind_panic_any(v: &[u32], i: usize, p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::read_behind_panic_any`
    if i >= v.len() {
        std::panic::panic_any(0u8);
    }
    v[i] ^ dep::deref_raw(p)
}

pub fn read_behind_dep_never(v: &[u32], i: usize, p: *const u32) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::read_behind_dep_never`
    if i >= v.len() {
        dep::never();
    }
    v[i] ^ dep::deref_raw(p)
}

/// The same shape where the dependency call is itself undefined behaviour, and the
/// guard is the dependency's own `-> !` function.
pub fn get_behind_dep_never(v: &[u32], i: usize) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_lowering_gap_launders_uncharged_callee::get_behind_dep_never`
    if i >= v.len() {
        dep::never();
    }
    v[i] ^ dep::get()
}
