//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Two same-named siblings in DIFFERENT NAMESPACES under one parent rendered ONE
//! def path. rustc's `DisambiguatedDefPathData` disambiguator counts siblings per
//! `(parent, DefPathData)`, and `DefPathData::TypeNs(sym)` and `ValueNs(sym)` are
//! DIFFERENT VARIANTS — so the `fn S` and the `struct S` below are BOTH `#0` and
//! nothing inside `print_path_with_simple` can separate them: the disambiguator
//! it prints is already the right one for the namespace it was counted in.
//!
//! Blocks are not `DefId`s, so both `S`s hang off `go`; that is what makes them
//! siblings and what makes the collision writable in one function.
//!
//! MEASURED, both states. The observable is the def path in the diagnostic, and
//! it is the same string `trust_ir_bridge`'s `resolve_call_target` binds a call
//! to a bundled body by (`known_functions.get(callee)`):
//!
//! ```text
//! before (pristine a27d636271, and the seam's build at the time)
//!   -Ztrust-dump=mir: FOUR bundled bodies under THREE def paths — the two
//!   DISTINCT `m` bodies BOTH keyed `krate::go::S::m`
//!   native-bundle:    vc:…__go__S__m:trust_mc_default_function:0
//!                     vc:…__go__S__m:arithmetic_safety:0     <- ONE key
//!   consumer:         2 obligations where the one-identifier control had 1,
//!                     and a #[trust::assume_total] donation row that read
//!                     "compiler retained the existing assertion" instead of
//!                     "solver trust-assumed-total reported Proved"
//!
//! after (re-measured 2026-08-21 on the STAGE2 trustc from ddb545d35b, crate
//!        name `nsclash`; the `before` column above is the RECORDED pristine
//!        state — no pre-fix binary survives on this machine to re-run it)
//!   -Ztrust-dump=mir: FOUR bodies under FOUR paths — nsclash::go::S::m
//!                     and nsclash::go::S::m#ns1v
//!   native-bundle:    vc:h0_nsclash__go__S__m_x23ns1v:trust_mc_default_function:0
//!                     vc:nsclash__go__S__m:arithmetic_safety:0    <- TWO keys
//!   consumer:         clash and control both report
//!                     "0 proved, 1 failed ... out of 1 obligation(s)"
//! ```
//!
//! Both columns used to size those bodies in bytes. Don't: a dump embeds the
//! absolute source path in every span, so the sizes move with the checkout —
//! measured on one program and one binary as 3956/1992 B from `/tmp/nsA`,
//! 4244/2136 B from an 80-char path, 3928/1978 B from a relative file name. The
//! stable observable is the PATH SET.
//!
//! This file is a REAL GUARD, unlike the `{{extern}}` fixture next to it, and the
//! reason is the ERROR annotation below: the arithmetic is planted in the
//! FN-SCOPED `m`, which is the side that gets tagged, so the tag appears inside
//! the annotated diagnostic text. (Do not spell a `~`-sigil annotation marker
//! inside this prose — compiletest's `parse_expected` regex matches it ANYWHERE
//! on a line, doc comment included, and would register a bogus expected error
//! against line 45.) The failing state was OBSERVED, not assumed —
//! renaming the `struct S` to `S2` removes the collision and the same compiler
//! prints `cross_namespace_key_alias_stays_closed::go::S::m`, without the
//! `#ns1v`, which is exactly the text a de-tagged seam would print here.
//!
//! Read `#ns1v` as: the segment at DEPTH 1 of this `DefPath` is the ValueNs half
//! of a cross-namespace pair. Of the PAIR itself only the non-`TypeNs` half's own
//! segment is marked, so the `impl S` body keeps `…::go::S::m` byte-for-byte, and
//! `#` is not spellable in a Rust path so no source item can impersonate the
//! tagged form. Do NOT read that as "`TypeNs` spellings never move": the mark is
//! a suffix over the whole `DefPath` CHAIN, so a `struct`, `trait` or `mod`
//! declared INSIDE this `fn S` moves too — measured, `k::go::S::Inner#ns1v`
//! against a one-identifier control's `k::go::S::Inner`. What actually keeps the
//! `core::`/`alloc::`/`std::` spellings byte-identical is the `!def_id.is_local()`
//! early return, and nothing else.
//!
//! SCOPE. This pins ONE collision class and the key is NARROWED, not injective —
//! `trust_mir_extract::direct_call_def_path` enumerates the residuals, and
//! `apply_cross_namespace_tag` enumerates three that belong to this tag: it stops
//! at the crate boundary (7a — a tagged DEFINITION is spelled `k::S#ns0v` while
//! every downstream crate renders the same `DefId` as `k::S`), a collision inside
//! a FOREIGN crate is not detected at all (7b), because the sibling index is
//! built from `tcx.hir_crate_items(())`, and the tag never reaches a type
//! rendered INSIDE a path — generic `args`, an impl `Self` type, a trait ref
//! (7c), so two distinct local types can still share one args spelling.
#![no_std]
#![allow(dead_code, non_snake_case)]

pub fn go(x: u32) -> u32 {
    let a = {
        fn S(v: u32) -> u32 {
            fn m(v: u32) -> u32 {
                //~^ ERROR incomplete for `cross_namespace_key_alias_stays_closed::go::S::m#ns1v`
                v + 1
            }
            m(v)
        }
        S(x)
    };
    let b = {
        struct S;
        impl S {
            fn m(v: u32) -> u32 {
                v
            }
        }
        S::m(x)
    };
    a.wrapping_add(b)
}
