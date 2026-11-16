//@ needs-trust-verify
//@ aux-build: fmt_member_tolerance_dep.rs
//@ revisions: count_match_field count_match_field_default mapcount_match_field
//@ revisions: count_fmt_write_sink count_formatter_helper
//@ revisions: args_param_format args_param_format_default args_param_struct_field
//@ revisions: args_param_fmt_write
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type lib
//@[count_match_field] compile-flags: -Ztrust-policy=strict
//@[mapcount_match_field] compile-flags: -Ztrust-policy=strict
//@[count_fmt_write_sink] compile-flags: -Ztrust-policy=strict
//@[count_formatter_helper] compile-flags: -Ztrust-policy=strict
//@[args_param_format] compile-flags: -Ztrust-policy=strict
//@[args_param_struct_field] compile-flags: -Ztrust-policy=strict
//@[args_param_fmt_write] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Refuted 2026-09-28: the same hole as `fmt_member_tolerance_derive_dep_refused.rs`,
//! in shapes that reach it with a RELEASE std (no debug assertions, no overflow
//! checks — the sealed channel's configuration), so these are red-before on every
//! machine, not only where std carries debug assertions.
//!
//! The refused member here is not the formatting machinery at all:
//! `iter().filter(..).count()` and `iter().map(..).count()` bundle core's
//! `<usize as Sum>::sum::{closure#0}` / `Iterator::count::{closure#0}`, whose
//! `count + 1` is an `#[rustc_inherit_overflow_checks]` `Overflow(Add)` Assert that
//! is present in release std's MIR too. The admission lane refuses it, the whole
//! bundle is discarded, and the discarded bundle also held the row for the dyn call
//! core's formatting machinery makes on a dependency value — `DebugTuple::field`'s
//! `<dyn Debug as Debug>::fmt`, or `core::fmt::write`'s `<dyn fmt::Write>::write_str`.
//! So checking the REFUSED member (its path, its generic arguments) cannot fix this;
//! what reaches the dependency is what the ROOT hands to core.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): every revision is still refused, now on
//! the success path's own fail-closed row. The refused member no longer discards the bundle
//! (it is kept, and the member's Assert rides the counted `runtime_checked` aggregate), so
//! the bundle keeps the edge to the dependency's code — the dyn `Debug::fmt` / `fmt::Write`
//! the root hands to core, or the caller-packed `Arguments` — as an unproved generic-absent-
//! callee or extern-call row, which no policy tolerates. The formatting-machinery tolerance
//! gate therefore never runs, and its named error and note are gone; each function's own
//! strict refusal is pinned in their place (measured on the merged stage 1 under each
//! revision's flags).
//!
//! * `count_match_field` / `count_match_field_default`: `filter().count()`, an enum
//!   `match` (so the root owns one PROVED row and no gap row is synthesized), then
//!   `f.debug_tuple(name).field(&self.d)` with `d: dep::Inner`.
//! * `mapcount_match_field`: the same through `map(..).count()` — a PLAIN-path
//!   refused member (`core::iter::traits::iterator::Iterator::count::{closure#0}`).
//! * `count_fmt_write_sink`: `filter().count()`, then `core::fmt::write` into a
//!   dependency's `fmt::Write` sink handed over as `&mut dyn fmt::Write`.
//! * `count_formatter_helper`: the same hole through the `Formatter`'s own writer.
//!   A function that is NOT a formatting impl, handed a `&mut Formatter` whose
//!   writer it does not know, calls `Formatter::write_str`. Without the refused
//!   member the native bundle keeps the writer edge as an unproved absent-callee
//!   row and the function is refused (measured on the fixed stage-1: "Trust strict
//!   verification failed for `c::helper`: 1 obligation(s) were not fully
//!   verified"); with `filter().count()` beside it the bundle was discarded and the
//!   tolerance accepted it (measured BEFORE with a std built WITH debug assertions:
//!   exit 0, the tolerance fired). Only a formatting impl's own `&mut Formatter`
//!   parameter carries the writer-relative premise.
//! * `args_param_format` / `args_param_format_default`, `args_param_struct_field`,
//!   `args_param_fmt_write`: the same hole through a `fmt::Arguments` this body did
//!   NOT pack — a parameter handed to `alloc::fmt::format`, a parameter struct's
//!   field handed to it, and a parameter handed to `core::fmt::write` with a
//!   `String` sink. The formatters an `Arguments` carries were judged by the packer
//!   gate only where they were packed; one built by the caller (here, a verify-off
//!   `main` packing `format_args!("{:?}", dep::Inner(7))`) was judged by nothing.
//!   Found by review of the first cut of the fix, which exempted every `Arguments`
//!   on its type alone: on that compiler, with a debug std and with a release std
//!   (and at `-Copt-level=2`), `args_param_format`'s shape built exit 0 under strict
//!   and default with `functions_verified` 2 of 2 and 0 unknown rows, the tolerance
//!   fired, and the driven program panicked in the dependency (exit 101); the
//!   struct-field shape the same; `core::fmt::write` the same. Without
//!   `filter().count()` (no refused member) the success path already flags
//!   `alloc::fmt::format` as an unproved assumption — so the tolerance was the
//!   more permissive path.
//!
//! MEASURED BEFORE (stage-1 `trustc` at `f992e2c307d`, with a std built WITHOUT
//! debug assertions or overflow checks, `-Copt-level=0`, these shapes with this
//! aux): `count_match_field` and `mapcount_match_field` exit 0 under strict and
//! under the default policy, crate summary `functions_verified:2` of 2,
//! `total_unknown:0`; `count_fmt_write_sink` exit 0 with one disclosed
//! `native-verification-gap` row. A verify-off `main` driving each rlib with the
//! dependency's panicking value exited 101 in the dependency. The same held with a
//! std built WITH debug assertions. `-Ztrust-policy=certify` refused all three.
//! This file on stage-1 `9edd8e85013` WITHOUT the fix, both std configurations:
//! every revision failed with "ui test did not emit an error".
//!
//! Trust (2026-09-29): the lowering-failure tolerance is gone — the refused member
//! is now KEPT under the runtime-checked disposition
//! (`trust_verify/runtime_checked_std_member.rs`) and the function is judged with
//! every other member's rows. Every revision here stays refused with the same pins:
//! the same re-judgement (renamed `fmt_machinery_reach_without_verdict`) now
//! withholds the disposition, because the kept bundle's panic-freedom aggregate is
//! reported as runtime-checked and does not refuse these hand-offs on its own
//! (MEASURED without the re-judgement, both std configurations: `args_param_format`,
//! `args_param_format_default` and `args_param_struct_field` built exit 0). The
//! headline now reads "a bundled std/core/alloc member's internal Assert was kept as
//! a runtime check, and the formatting machinery this function calls can reach code
//! that carries no verdict"; the pinned phrase and the NOTEs are unchanged.
//!
//! AFTER: refused. The tolerance re-judges every call into core's inherent
//! formatting machinery (`lowering_failure_fmt_machinery_reach`): the `&dyn Debug`
//! is minted from `&dep::Inner` and the `&mut dyn fmt::Write` from `&mut dep::Sink`,
//! neither of which carries a verdict, `helper`'s `Formatter` is not a formatting
//! impl's own parameter, and the `args_param_*` `Arguments` were not packed in the
//! refused body (`fmt_arguments_operand_packed_in_body`). The controls that must
//! KEEP the tolerance — `filter().count()` alone, and `Arguments` this body packed
//! itself (`format_count`, `write_into_string`) — are in
//! `fmt_member_tolerance_internal_assert_control.rs` (where, since 2026-09-29,
//! `write_into_string` is refused on the success path; see there).
//!
//! PINS name this path's own error and, in a NOTE, which hand-off refused, so a
//! refusal by some other check (the generic "lowering did not complete", or the
//! success path's "Trust strict verification failed") cannot satisfy them. Every
//! revision here reaches this path with either std configuration (each built exit
//! 0 on both before the fix), so the pins hold on both.
extern crate fmt_member_tolerance_dep as dep;
use std::fmt;

#[cfg(any(
    count_match_field,
    count_match_field_default,
    mapcount_match_field,
    args_param_format,
    args_param_format_default,
    args_param_struct_field,
    args_param_fmt_write
))]
pub enum Tag {
    A,
    B,
}
#[cfg(any(count_match_field, count_match_field_default, mapcount_match_field))]
pub struct W {
    pub tag: Tag,
    pub v: [u32; 3],
    pub d: dep::Inner,
}

#[cfg(any(count_match_field, count_match_field_default))]
impl fmt::Debug for W {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[count_match_field,count_match_field_default]~^ ERROR Trust strict verification failed for `<fmt_member_tolerance_release_std_refused::W as core::fmt::Debug>::fmt`
        // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
        let k = self.v.iter().filter(|x| **x > 1).count();
        let name = match self.tag {
            Tag::A => "A",
            Tag::B => "B",
        };
        if k == 7 {
            return Ok(());
        }
        f.debug_tuple(name).field(&self.d).finish()
    }
}

#[cfg(mapcount_match_field)]
impl fmt::Debug for W {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[mapcount_match_field]~^ ERROR Trust strict verification failed for `<fmt_member_tolerance_release_std_refused::W as core::fmt::Debug>::fmt`
        // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
        let k = self.v.iter().map(|x| x & 1).count();
        let name = match self.tag {
            Tag::A => "A",
            Tag::B => "B",
        };
        if k == 7 {
            return Ok(());
        }
        f.debug_tuple(name).field(&self.d).finish()
    }
}

#[cfg(count_fmt_write_sink)]
pub fn put(v: &[u32; 3], s: &mut dep::Sink) -> fmt::Result {
    //[count_fmt_write_sink]~^ ERROR Trust strict verification failed for `fmt_member_tolerance_release_std_refused::put`
    // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
    let k = v.iter().filter(|x| **x > 1).count();
    if k == 7 {
        return Ok(());
    }
    fmt::write(s, format_args!("abcdefg"))
}

#[cfg(count_formatter_helper)]
pub fn helper(f: &mut fmt::Formatter<'_>, v: &[u32; 3]) -> fmt::Result {
    //[count_formatter_helper]~^ ERROR Trust strict verification failed for `fmt_member_tolerance_release_std_refused::helper`
    // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
    let k = v.iter().filter(|x| **x > 1).count();
    f.write_str(if k == 7 { "a" } else { "b" })
}

#[cfg(any(args_param_format, args_param_format_default))]
pub fn render(tag: Tag, v: &[u32; 3], a: fmt::Arguments<'_>) -> String {
    //[args_param_format,args_param_format_default]~^ ERROR Trust strict verification failed for `fmt_member_tolerance_release_std_refused::render`
    // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
    let k = v.iter().filter(|x| **x > 1).count();
    let name = match tag {
        Tag::A => "A",
        Tag::B => "B",
    };
    if k == 7 {
        return String::from(name);
    }
    fmt::format(a)
}

#[cfg(args_param_struct_field)]
pub struct Msg<'a> {
    pub tag: Tag,
    pub a: fmt::Arguments<'a>,
}

#[cfg(args_param_struct_field)]
pub fn render_msg(m: &Msg<'_>, v: &[u32; 3]) -> String {
    //[args_param_struct_field]~^ ERROR Trust strict verification failed for `fmt_member_tolerance_release_std_refused::render_msg`
    // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
    let k = v.iter().filter(|x| **x > 1).count();
    let name = match m.tag {
        Tag::A => "A",
        Tag::B => "B",
    };
    if k == 7 {
        return String::from(name);
    }
    fmt::format(m.a)
}

#[cfg(args_param_fmt_write)]
pub fn render_into(tag: Tag, v: &[u32; 3], a: fmt::Arguments<'_>) -> String {
    //[args_param_fmt_write]~^ ERROR Trust strict verification failed for `fmt_member_tolerance_release_std_refused::render_into`
    // (re-pinned 2026-10-15: the tolerance gate's note; see the header)
    let k = v.iter().filter(|x| **x > 1).count();
    let name = match tag {
        Tag::A => "A",
        Tag::B => "B",
    };
    let mut s = String::new();
    if k == 7 {
        s.push_str(name);
        return s;
    }
    let _ = fmt::write(&mut s, a);
    s
}
