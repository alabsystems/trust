//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! `[T; N]` -> `[T]` adds a LENGTH. It mints no vtable, so it must not poison the
//! case split — not even when `T` itself is a trait object.
//!
//! ## THE `&[&dyn Emit]` LINE IS THE ASSERTION — DELETING IT SILENTLY GUTS THE TEST
//!
//! `items` looks like dead scaffolding. It is the entire point. Before the fix,
//! `observe_unsize` classified `&[&dyn Emit; 2]` -> `&[&dyn Emit]` as a vtable
//! coercion — the target's principals are `{Emit}`, and the source is an ARRAY
//! rather than a concrete `Self`, so it fell through to the refusal arm and
//! poisoned `Emit` for the whole bundle. That discarded an enumeration which had
//! already succeeded: `A`'s vtable came from the `&a` -> `&dyn Emit` coercion two
//! lines up and was sitting in the recorded set.
//!
//! Measured on the pre-fix compiler, this exact file against the same file with
//! only `items`/`n` removed:
//!
//! ```text
//! with the slice coercion     C-FLOW declined: trait Emit poisoned      2 errors
//! without it                  C-FLOW admitted 1 target(s)  DISCHARGED   0 errors
//! ```
//!
//! Nothing else differs. If a later edit drops `items` for being unused, this file
//! keeps passing and the regression returns unnoticed.
//!
//! Note `items.len()` is load-bearing twice over: it uses the binding so it cannot
//! be optimized away, and `<[T]>::len` is panic-free so it adds no obligation of
//! its own. Beware that an ARRAY has no inherent `len`, so writing
//! `let items: &[&dyn Emit; 2]` does NOT avoid the coercion — the `.len()` call
//! unsizes it anyway. That near-miss is how easy this shape is to reach.
//!
//! ## WHY A LOCAL TRAIT AND NOT `derive(Debug)`, WHICH IS WHERE THIS WAS FOUND
//!
//! The defect was found in real code, in `derive(Debug)`. rustc's derive switches
//! lowering at five fields (`const CUTOFF: usize = 5` in
//! `rustc_builtin_macros/src/deriving/debug.rs`): at or below, it emits
//! `debug_struct_field{1..5}_finish` and passes each field as its own `&dyn Debug`
//! argument; above, it builds an array for
//! `Formatter::debug_struct_fields_finish(.., values: &[&dyn Debug])` and performs
//! precisely the coercion this file pins. So a SIX-field struct was refused where a
//! five-field one discharged — a boundary nobody could defend, invisible because
//! every fixture here sat under the cutoff. It surfaced only by compiling two files
//! that differed in nothing but field count.
//!
//! That derive pair CANNOT be a test. Both arities fail either way on unproved
//! `<u8 as Debug>::fmt` and `PadAdapter::write_str`, and their stderr is
//! byte-identical before and after the fix — verified, not assumed. The difference
//! lives only in the `TRUST_DYN_RELIANCE_PROBE` decline string, which no UI test
//! can see. A `derive`-based fixture would be a test that has never failed and
//! never could. Hence a local trait, whose impl is provably panic-free, so the
//! poison is the ONLY thing standing between this file and a clean verdict.
//!
//! To re-check the real shape by hand, compile two crates differing only in field
//! count with `TRUST_DYN_RELIANCE_PROBE=1` and compare the decline strings: below
//! the cutoff names a concrete target, above it must not say "poisoned".
#![no_std]
#![allow(dead_code)]

pub trait Emit {
    fn emit(&self) -> u32;
}

pub struct A;

impl Emit for A {
    // Provably panic-free: a constant, no panic-capable construct.
    fn emit(&self) -> u32 {
        1
    }
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dyn_dispatch_reliance_slice_of_dyn_not_a_vtable::total`
//~v NOTE this function has no obligation of its own
pub fn total() -> u32 {
    let a = A;
    // The one vtable minted in this bundle. Enumeration: `{A}`.
    let d: &dyn Emit = &a;
    // Length coercion, NOT a vtable. Must leave the enumeration above intact.
    let items: &[&dyn Emit] = &[d, d];
    let n = items.len() as u32;
    // Discharged by case split against `<A as Emit>::emit`, which is proved
    // panic-free right here — no allowlist, no totality model.
    d.emit().wrapping_add(n)
}
