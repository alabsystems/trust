//@ needs-trust-verify
//@ revisions: strict default field_u32 nested_local_clean format_count write_into_string
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[field_u32] compile-flags: -Ztrust-policy=strict
//@[nested_local_clean] compile-flags: -Ztrust-policy=strict
//@[format_count] compile-flags: -Ztrust-policy=strict
//@[write_into_string] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@[strict] check-pass
//@[default] check-pass
//@[format_count] check-pass
//@[field_u32] check-pass
//@[nested_local_clean] check-pass
//@[write_into_string] check-fail
//! CONTROLS for `fmt_member_tolerance_derive_dep_refused.rs` and
//! `fmt_member_tolerance_release_std_refused.rs`: the policy-B bundled std-member
//! tolerance still fires where it is honest, including beside core's formatting
//! machinery when everything handed to it carries a verdict.
//!
//! Trust (2026-09-29, read this first): the tolerance is GONE. A refused bundled
//! std member no longer discards the bundle; it is kept under the runtime-checked
//! disposition (`trust_verify/runtime_checked_std_member.rs`) and owes a
//! `runtime_checked` row, and the function is judged on the success path with
//! every other member's rows intact. What that changed here, measured on
//! stage-1 with a release-like std and with m3's debug std:
//!
//! * `strict` / `default` / `format_count`: still pass, with the same advisory
//!   headline. `k` is still not counted verified — it now publishes the member's
//!   `runtime_checked` rows instead of one `native-verification-gap` row, so the
//!   crate summary reads `total_unknown` 0 (re-pinned below).
//! * `field_u32`, `nested_local_clean`, `write_into_string`: now REFUSED
//!   (`check-fail`). Each passed ONLY because `count()` discarded its bundle: the
//!   same body WITHOUT `count()` is refused by the success path, for the same row
//!   the kept bundle now carries — "a generic absent callee" (the `<dyn Debug as
//!   Debug>::fmt` core's debug builder makes) for the two `Debug` impls, "an extern
//!   call" (`core::fmt::write`) for `put` — measured on origin/main `f6773df328e`
//!   (release-like std): count-free twins rc=1 with those rows, the `count()`
//!   versions rc=0 through the tolerance. Adding `count()` no longer changes the
//!   verdict. A capability loss against the old tolerance, recorded in
//!   docs/KNOWN_HAZARDS.md ("CLOSED 2026-09-29 — the bundled std-member tolerance
//!   …"); their refusals are pinned below.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): `field_u32` and
//! `nested_local_clean` build again (`check-pass`, measured on the merged stage 1
//! under `strict`). The `<dyn Debug as Debug>::fmt` site core's debug builder makes
//! is still KEPT (`TRUST_DYN_RELIANCE_PROBE`: "site=<dyn core::fmt::Debug as
//! core::fmt::Debug>::fmt (2 site(s)) => kept"), but it no longer surfaces as a
//! fail-closed generic-absent-callee row: it is folded into the bundled std member's
//! `runtime_checked` panic-freedom aggregate, so each `fmt` reads `1 runtime-checked`
//! and the policy reports it. The only bodies that site reaches here are std's
//! `u32` `Debug` and the local, verified `Inner::fmt`; the dependency twin
//! (`fmt_member_tolerance_derive_dep_refused.rs`) stays refused on the same stage 1.
//! `write_into_string` (an extern `core::fmt::write`) stays refused.
//!
//! The rest of this header is the 2026-09-28 record.
//!
//! `v.iter().filter(..).count()` bundles core's `<usize as Sum>::sum::{closure#0}`,
//! whose `count + 1` is an `#[rustc_inherit_overflow_checks]` `Overflow(Add)` Assert
//! (present with a release std and with a debug std). The admission lane refuses
//! it and the bundle is discarded.
//!
//! * `strict` / `default`: `filter().count()` alone. Nothing that bundle could reach
//!   is user code without a verdict: the one non-sysroot body is the local closure,
//!   verified as its own root, and no value reaches core's formatting machinery. So
//!   std's own retained check is the only undischarged obligation, which is what
//!   the tolerance reports. Pinned: the advisory names `k`, and `k` is NOT counted
//!   verified — it publishes one `native-verification-gap` row (`unknown`), while
//!   its closure is proved. The crate summary was identical with a std built with
//!   and without debug assertions (stage-1 `f992e2c307d`, both configurations), and
//!   a `main` printing `k(&[1, 2, 3])` against the rlib printed `2`.
//! * `field_u32`: the refused shape of `fmt_member_tolerance_release_std_refused.rs`
//!   with a `u32` field instead of the dependency's value — core's own `Debug` at a
//!   foundational type, handed over with this formatting impl's own `Formatter`.
//! * `nested_local_clean`: a LOCAL nested type whose `Debug` only writes — a local
//!   formatting impl with a verdict of its own (the nested-formatter bar).
//! * `format_count`: `format!` of the count — a `fmt::Arguments` THIS body packed
//!   (`rt::Argument::new_display::<usize>` into an array, `Arguments::new`), whose
//!   formatted type the packer gate judged; `alloc::fmt::format` its sink. With
//!   `write_into_string`, the control for the provenance test that refuses an
//!   `Arguments` this body did NOT pack
//!   (`fmt_member_tolerance_release_std_refused.rs#args_param_*`).
//! * `write_into_string`: `core::fmt::write` into a `String` — a trait object minted
//!   from a foundational sink, and a literal `Arguments` packed here.
//!
//! Not a control here: `core::fmt::write(s, format_args!("k={}", k))` written
//! directly in the function. The tolerance fires for it, but the strict and the
//! default lane both refuse it on a separate Level 0 row ("[unsafe] missing SAFETY
//! comment on unsafe block", the `unsafe` block `format_args!` expands to) —
//! measured 2026-09-28 under strict and the default policy with this change, and
//! under the default policy on origin/main `56c474d6e83`, so not this check.
//!
//! Each pins the advisory, so a revision that passed without the tolerance (or
//! was refused) would fail here. All six revisions passed on stage-1
//! `9edd8e85013` with and without the first cut of the fix, with a std built with
//! debug assertions and with a release std (measured 2026-09-28, all four
//! combinations).

#[cfg(any(strict, default))]
pub fn k(v: &[u32; 3]) -> usize {
    v.iter().filter(|x| **x > 1).count()
}

#[cfg(field_u32)]
pub mod field_u32 {
    use std::fmt;
    pub enum Tag {
        A,
        B,
    }
    pub struct W {
        pub tag: Tag,
        pub v: [u32; 3],
        pub n: u32,
    }
    impl fmt::Debug for W {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let k = self.v.iter().filter(|x| **x > 1).count();
            let name = match self.tag {
                Tag::A => "A",
                Tag::B => "B",
            };
            if k == 7 {
                return Ok(());
            }
            f.debug_tuple(name).field(&self.n).finish()
        }
    }
}

#[cfg(nested_local_clean)]
pub mod nested_local_clean {
    use std::fmt;
    pub struct Inner(pub u32);
    impl fmt::Debug for Inner {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("i")
        }
    }
    pub struct W {
        pub v: [u32; 3],
        pub d: Inner,
    }
    impl fmt::Debug for W {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let k = self.v.iter().filter(|x| **x > 1).count();
            if k == 7 {
                return Ok(());
            }
            f.debug_tuple("W").field(&self.d).finish()
        }
    }
}

#[cfg(format_count)]
pub fn show(v: &[u32; 3]) -> String {
    let k = v.iter().filter(|x| **x > 1).count();
    format!("{k}")
}

#[cfg(write_into_string)]
pub fn put(v: &[u32; 3], s: &mut String) -> std::fmt::Result {
    let k = v.iter().filter(|x| **x > 1).count();
    if k == 7 {
        return Ok(());
    }
    std::fmt::write(s, format_args!("abcdefg"))
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(d)): `filter().count()`
// over a slice iterator is now decided total by the drive-only consumer lane (the closure's
// own verdict, a counter that cannot pass the slice's length), so std's `Sum` body leaves the
// bundle and no member owes a runtime-checked row. `k` publishes `no_obligations` and is
// counted verified (2 of 2), `show` keeps only its own proved row and the skipped
// global-alloc disclosure (no advisory), and `put` is refused exactly as before.
//[strict,default]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"fmt_member_tolerance_internal_assert_control","functions_analyzed":2,"functions_verified":2,"total_proved":2,"total_failed":0,"total_unknown":0
//[format_count]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"fmt_member_tolerance_internal_assert_control","functions_analyzed":2,"functions_verified":1,
//[write_into_string]~? RAW Trust strict verification failed for `fmt_member_tolerance_internal_assert_control::put`: 1 obligation(s) were not fully verified
//[write_into_string]~? RAW an unproved assumption-panic row — an extern call — keeps the function fail-closed
//[field_u32]~? RAW Trust verification advisory for `<fmt_member_tolerance_internal_assert_control::field_u32::W as core::fmt::Debug>::fmt`
//[nested_local_clean]~? RAW Trust verification advisory for `<fmt_member_tolerance_internal_assert_control::nested_local_clean::W as core::fmt::Debug>::fmt`
