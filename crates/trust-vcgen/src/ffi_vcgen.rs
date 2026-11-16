// trust_vcgen/ffi_vcgen.rs: FFI call site VC generation
//
// Bridges FfiSummaryDb contracts into the verification pipeline. When
// generate_vcs() encounters an extern call, this module looks up the callee
// in the summary database and generates targeted VCs (null checks, range
// checks, aliasing checks) instead of the conservative Bool(true) VCs from
// unsafe_verify. Return contracts are the callee's guarantee — an assumption,
// not an obligation — and are NOT emitted until an assumption channel exists
// (see generate_call_site_vcs step 2).
//
// Inspired by angr's SimProcedures (replace foreign calls with executable
// summaries) and Ghidra's type recovery at FFI boundaries.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

use crate::ffi_summary::{
    FfiSummary, FfiSummaryDb, SafetyLevel, SideEffect, generate_ffi_vcs_with_extents,
    is_printf_family, printf_family_format_index,
};

/// Build a conservative, fail-closed obligation for an FFI call whose behavior
/// we cannot prove safe (no summary, or a summary marked `UnsafeUnknown`).
///
/// Convention (matches the side-effect VCs above): `Formula::Bool(true)` is
/// always SAT, so the obligation can never be discharged — the call is reported
/// Unknown/Failed rather than silently Proved. A conservative false-FAIL here is
/// correct; a silent false-PROVE of an unmodeled FFI call is a soundness hole.
fn unmodeled_ffi_obligation(
    func_name: &str,
    short_name: &str,
    span: &SourceSpan,
    desc: &str,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::FfiBoundaryViolation {
            callee: short_name.to_string(),
            desc: desc.to_string(),
        },
        function: func_name.into(),
        location: span.clone(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

/// Detect whether a callee name refers to an extern/FFI function.
///
/// NAME-FALLBACK ONLY: `is_foreign` (tcx.is_foreign_item, carried on the
/// Call terminator) is the authoritative FFI signal; this heuristic exists
/// for synthetic/test MIR that lacks the flag. Patterns, each a deliberate
/// over-approximation SHRUNK to spellings real Rust paths cannot collide
/// with (T1 + T6, reports/ffi-name-collision-over-refutation-2026-07-06.md):
/// - `libc::*` / `*::libc::*` prefixes
/// - a literal `extern` path segment, or the `extern "<abi>"` fn-pointer
///   TYPE spelling (non-FnDef constant callees stringify as their type)
/// - a non-std `::ffi::` module path (std's `core/std/alloc::ffi::` are
///   safe APIs, excluded modulo the modeled-libc-terminal carve — judged per
///   `ffi` path the callee names, so a std ffi type in a qualified-path header
///   or a generic argument is excluded too: [`ffi_paths_are_std_namespaces`])
/// - a bare (un-pathed) name matching a summary or the printf family
///
/// The unkeyed form: production asks [`is_extern_call_for`] with the call's key.
#[must_use]
#[cfg(test)]
pub(crate) fn is_extern_call(callee: &str, db: &FfiSummaryDb) -> bool {
    is_extern_call_for(callee, None, db)
}

/// [`is_extern_call`] for a call whose extractor-resolved [`trust_types::CalleeKey`] is `key`.
///
/// Trust: G1 (2026-10-27) — pattern 1 (`libc::`) routes only a callee the
/// extractor did NOT identify as a Rust item. A keyed callee is a `FnDef` the
/// extractor resolved to a `DefId`; for it, `is_foreign` (`tcx.is_foreign_item`)
/// and the key's `foreign_block_leaf` are the whole answer to "is this foreign
/// code", and a keyed callee outside every extern block is a Rust function with
/// its own MIR body — the libc crate's `const fn WIFEXITED(status) -> bool`, its
/// `CMSG_*`/`FD_*` helpers. Routing such a callee here posed the unmodeled-FFI
/// stand-in over ordinary Rust code: wrong in kind, since the code is Rust that
/// the cross-crate call policy (the absent-callee rule, a lent summary) judges
/// exactly as it judges any other dependency's function. A foreign item is never
/// lost by this: it carries `is_foreign`, which the caller ORs in before asking
/// this. Unkeyed callees (synthetic/test MIR, `fn`-pointer callees) keep the
/// name fallback unchanged; patterns 2a, 2b and 4 are unchanged for every
/// callee.
#[inline]
fn starts_with_ignore_ascii_case(s: &str, prefix: &str) -> bool {
    s.as_bytes()
        .get(..prefix.len())
        .is_some_and(|head| head.eq_ignore_ascii_case(prefix.as_bytes()))
}

#[inline]
fn contains_ignore_ascii_case(s: &str, needle: &str) -> bool {
    let hb = s.as_bytes();
    let nb = needle.as_bytes();
    if nb.is_empty() {
        return true;
    }
    if hb.len() < nb.len() {
        return false;
    }
    hb.windows(nb.len()).any(|w| w.eq_ignore_ascii_case(nb))
}

#[must_use]
pub(crate) fn is_extern_call_for(
    callee: &str,
    key: Option<&trust_types::CalleeKey>,
    db: &FfiSummaryDb,
) -> bool {
    let hb = callee.as_bytes();
    let check_libc = key.is_none();
    // Pattern 1: libc:: prefix — name fallback for unkeyed callees only.
    if check_libc && starts_with_ignore_ascii_case(callee, "libc::") {
        return true;
    }

    // Single linear pass to detect `::`, `::libc::`, `::ffi::`, and `extern`
    // before running multi-pass splits or `FxHashMap` summary probes.
    let mut has_double_colon = false;
    let mut has_extern = false;
    let mut has_ffi_mod = false;
    let len = hb.len();
    let mut i = 0;
    while i < len {
        let b = hb[i];
        if b == b':' && i + 1 < len && hb[i + 1] == b':' {
            has_double_colon = true;
            if check_libc
                && hb.get(i + 2..i + 8).is_some_and(|s| s.eq_ignore_ascii_case(b"libc::"))
            {
                return true;
            }
            if hb.get(i + 2..i + 7).is_some_and(|s| s.eq_ignore_ascii_case(b"ffi::")) {
                has_ffi_mod = true;
            }
        } else if (b | 0x20) == b'e'
            && i + 6 <= len
            && (hb[i + 1] | 0x20) == b'x'
            && hb.get(i..i + 6).is_some_and(|s| s.eq_ignore_ascii_case(b"extern"))
        {
            has_extern = true;
        }
        i += 1;
    }

    // Pattern 2a: an explicit `extern` marker. Tightened from
    // `lower.contains("extern")` (T6, report addendum): a SUBSTRING match
    // routed any Rust path merely containing the letters (`my::external_id`,
    // `extern_spec_registry::collect_entries`) into the FFI lane, where the
    // no-summary branch fails closed — a spurious, undischargeable
    // unmodeled-FFI obligation on safe code. Two genuine spellings remain:
    //   - a literal `extern` path SEGMENT (synthetic/test MIR only: `extern`
    //     is a Rust keyword, so no real def-path segment can equal it);
    //   - an fn-POINTER-typed callee: a constant callee that is not a FnDef
    //     stringifies as its TYPE (trust-mir-extract `func_operand_name`'s
    //     `format!("{ty}")` arm), e.g. `unsafe extern "C" fn(i32) -> i32` or
    //     `for<'a> extern "C" fn(&'a u8)` — recognized by the `extern "<abi>"`
    //     spelling. Def-path strings render generics as TURBOFISH (`::<`)
    //     while type strings never do, so `Vec::<extern "C" fn()>::push` (a
    //     safe method whose generic ARG is an fn-pointer type) is excluded.
    if has_extern
        && (callee.split("::").any(|segment| segment == "extern")
            || (contains_ignore_ascii_case(callee, "extern \"") && !callee.contains("::<")))
    {
        return true;
    }

    // Pattern 2b: a user-defined `ffi` module path (`my_sys::ffi::do_io`).
    // The std namespaces `core::ffi::` / `std::ffi::` / `alloc::ffi::` are
    // EXCLUDED (T6): they are ordinary safe Rust APIs — e.g.
    // `core::ffi::c_str::CStr::as_ptr` is a safe accessor, and routing it
    // here sent every `CStr::as_ptr` call into the fail-closed no-summary
    // branch, a false refutation of safe code. Within those std namespaces,
    // only a terminal segment that IS a modeled libc name still routes (the
    // `core::ffi::c_str::strlen` synthetic-binding shape); no safe std
    // ffi-namespace method shares a name with a modeled libc function, so the
    // `RwLock::write`-style terminal collision (T1) cannot re-enter through
    // this carve.
    //
    // Trust: 2026-10-25 (FFI-STD-QPATH-1) — the std exemption is judged per
    // `ffi` PATH the callee names, not by the callee string's first bytes.
    // The `::ffi::` test reads the WHOLE string — generic arguments and a
    // qualified `<Self as Trait>` header included — while the exemption read
    // only `starts_with("std::")`. Every callee whose std ffi type sat anywhere
    // but the head therefore routed here and failed closed:
    // `<std::ffi::os_str::OsString as core::ops::deref::Deref>::deref`,
    // `<alloc::vec::Vec<std::ffi::os_str::OsString> as core::clone::Clone>::clone`,
    // `<core::slice::iter::Iter<'_, std::ffi::os_str::OsString> as …>::map::<…>`
    // (24 of the 44 `hardened_ffi_boundary` rows claude-code-alab's strict gate
    // listed on 2026-10-25, and 33 of agy-alab's 62, none a foreign call).
    // See [`ffi_paths_are_std_namespaces`] for what is exempted and why each
    // newly exempted callee cannot hide a foreign call.
    if has_ffi_mod {
        if !ffi_paths_are_std_namespaces(callee) {
            return true;
        }
        if terminal_segment_pair(callee)
            .into_iter()
            .flatten()
            .any(|segment| db.lookup(segment).is_some() || is_printf_family(segment))
        {
            return true;
        }
    }

    // Pattern 3 (last-segment match) DELETED — the ffi-name-collision
    // over-refutation (reports/ffi-name-collision-over-refutation-2026-07-06.md):
    // a qualified Rust path whose TERMINAL segment collides with a libc name
    // (`std::sync::RwLock::<T>::write`, `io::Write::write`, `std::ptr::read`)
    // is NOT an extern call, and binding it to the POSIX summary refuted
    // zero-unsafe registry code (38 obligations in aterm-types alone). Genuine
    // foreign imports carry `is_foreign` (tcx.is_foreign_item) from extraction
    // — the AUTHORITATIVE signal (round-19 #3); this name fallback exists ONLY
    // for synthetic/test MIR, whose callees are written bare (`malloc`) or
    // libc::-qualified (Pattern 1). Bare names still match the full-string
    // lookup below; the printf-family check likewise applies to bare names
    // only, so `my::mod::printf`-shaped Rust methods no longer over-fire.

    // Pattern 4: Full name matches a known summary (bare synthetic-MIR names)
    if has_double_colon {
        return db.has_path_separator() && db.lookup(callee).is_some();
    }
    db.lookup_prechecked_bare(callee).is_some() || is_printf_family(callee)
}

/// Whether every `ffi` module path `callee` names is one of std's safe ffi
/// namespaces (`core::ffi`, `alloc::ffi`, `std::ffi`, `std::os::*::ffi`, …):
/// pattern 2b's exemption, before its modeled-libc terminal carve.
///
/// Two shapes are exempt:
///
/// 1. the callee IS a std-rooted def path (`std::ffi::OsStr::to_str`) — the T6
///    shape, unchanged; its generic arguments are not the item being called;
/// 2. any other callee, when EVERY path token it contains that names an `ffi`
///    module is itself std-rooted — the qualified `<Self as Trait>::method`
///    and generic-argument shapes (`<std::ffi::os_str::OsString as
///    core::ops::deref::Deref>::deref`, `<alloc::vec::Vec<std::ffi::os_str::
///    OsString> as core::clone::Clone>::clone`, `my::f::<std::ffi::OsString>`).
///
/// WHY WITHHOLDING THE ROW FROM SHAPE 2 IS SOUND. The row this withholds is the
/// name FALLBACK's `unmodeled FFI call` stand-in on a callee that is NOT a
/// foreign item; it is not the defense against a foreign call, and it never was:
///
/// * A DIRECT call of a foreign item carries `is_foreign` (`tcx.is_foreign_item`,
///   set at extraction) and is routed by `generate::entry` whatever this returns.
///   Every newly exempt callee has `is_foreign == false`: a qualified-path or
///   generic-carrying callee is never itself a foreign item (foreign items are
///   free functions without type parameters, E0044, never trait or inherent
///   methods).
/// * Such a callee may still CALL a foreign function — one it reaches in its own
///   body, or one handed to it as a generic argument (a foreign fn item, a
///   reified `fn` pointer, a `&dyn Fn`; review counterexample 3, 2026-10-26).
///   What refuses those is the rule for the call that actually reaches the
///   foreign code: its own body's `is_foreign` row when that body is verified,
///   the absent-callee policy when it is not — including the
///   `[trust-absent-callee-assumption]` row on the `Fn*::call` of a foreign fn
///   item, a `fn` pointer or a `dyn Fn` that a generic body or std adaptor
///   invokes. None of those reads the callee's spelling.
/// * The proof that the spelling was never load-bearing: every program whose
///   callee this newly exempts has a SPELLING TWIN — the same calls, with each
///   std ffi type replaced by a non-ffi type (`core::ffi::c_void` -> `u8`,
///   `std::ffi::OsString` -> `alloc::string::String`) — whose callee names no
///   `ffi` module and was therefore never routed by this fallback, before or
///   after. Whatever refuses the twin refuses the original; if nothing refuses
///   the twin, that is a hole in one of the rules above, older than this
///   exemption, and it is fixed there. (MEASURED 2026-10-26: a safe foreign
///   `strlen(*const c_void)` handed to `Iterator::map`, to a user generic
///   `apply<F: Fn(..)>` and through a `&dyn Fn` is still refused after this
///   exemption, and with the SAME rows as its twin `labs(i64)` — the
///   `[trust-absent-callee-assumption]` row on `<fn(..) {strlen} as
///   FnMut<..>>::call`, a strict-lane error; the `unmodeled FFI call` row the
///   `c_void` spelling used to add was the only difference.
///   `tests/ui/trust/ffi_std_qpath_foreign_fn_in_generic_arg.rs` pins it.)
///
/// What this still routes: patterns 1 and 2a (`libc::`, an `extern` segment, an
/// `extern "<abi>"` fn-pointer type) run before this and scan the whole string;
/// a user `ffi` module anywhere in the string — head, `Self` type, trait, or
/// generic argument (`<my_sys::ffi::Handle as Drop>::drop`,
/// `<std::vec::Vec<my_sys::ffi::Handle> as Clone>::clone`) — keeps the callee
/// routed, the pre-existing conservative choice.
///
/// WHAT A `std::` TOKEN INSIDE THE CALLEE IS WORTH. Only the ROOT of a rendered
/// path is stamped `__trust_crate@…` when its crate is not the compiler's own
/// sysroot crate ([`trust_types::path_root_is_authenticated_sysroot_crate`]);
/// a type rendered INSIDE a qualified `<Self as Trait>` header or a generic
/// argument is not stamped. For those positions the producer writes the
/// duplicate-crate-name argument fingerprint `::<__trust_args@…>` instead,
/// exactly when some def the generic arguments name lives in a crate whose
/// rendered name does not identify it (`--crate-name std`, or two crates of one
/// name), and a reader that compares a TYPE PATH read from those arguments must
/// DECLINE on it ([`trust_types::args_display_may_name_a_same_named_crate`],
/// ARGS-FINGERPRINT-READ-1). Shape 2 is such a reader, so a tagged callee is
/// never exempt here. MEASURED (review, 2026-10-26): a dependency built
/// `--crate-name std` renders `<std::ffi::Handle as core::clone::Clone>::clone::
/// <__trust_args@…>` and `<alloc::vec::Vec<std::ffi::Handle> as core::clone::
/// Clone>::clone::<__trust_args@…>` — no stamp anywhere, the fingerprint on both.
/// (Those two are refused by the absent-callee policy either way; the decline
/// keeps this exemption from ever being the step that reads a forged `std`.)
/// Shape 1 reads only the ROOT, which IS stamped, and keeps its pre-existing
/// meaning on a tagged callee.
///
/// Tokens are maximal runs of ASCII alphanumerics, `_`, `:` and every NON-ASCII
/// character, so a non-ASCII identifier cannot split a user path into a forged
/// `std::` root (`my_crate::éstd::ffi::f` is ONE token, not `std::ffi::f`). A
/// std root is case-sensitive.
fn ffi_paths_are_std_namespaces(callee: &str) -> bool {
    if trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return false;
    }
    if trust_types::path_root_is_authenticated_sysroot_crate(callee) {
        return true;
    }
    // Trust: 2026-10-26 (FFI-STD-QPATH-1 review, finding 2) — the type paths
    // below are read out of a qualified header / generic arguments, which the
    // producer does not stamp; its fingerprint is the decline signal there.
    if trust_types::args_display_may_name_a_same_named_crate(callee) {
        return false;
    }
    callee
        .split(|c: char| c.is_ascii() && !(c.is_ascii_alphanumeric() || c == '_' || c == ':'))
        .filter(|token| contains_ignore_ascii_case(token, "::ffi::"))
        .all(trust_types::path_root_is_authenticated_sysroot_crate)
}

/// The candidate TERMINAL item segments of `callee`, for pattern 2b's
/// modeled-libc carve: the last `::` segment (the T6 spelling), and, when the
/// callee ends in turbofish groups (`<S as T>::m::<A>::<__trust_elem_bytes@8>`),
/// the last depth-0 segment that is not one (`m`). Answering BOTH can only
/// route more: the carve is a fail-closed recovery, so a mis-scan of an exotic
/// generic argument (a `'>'` const) costs at most the extra candidate.
fn terminal_segment_pair(s: &str) -> [Option<&str>; 2] {
    let first = s.rsplit("::").next().unwrap_or(s);
    let mut out = [Some(first), None];
    if !s.contains('<') {
        return out;
    }
    let bytes = s.as_bytes();
    let mut depth: i64 = 0;
    let mut start = 0usize;
    let mut last_non_generic: Option<&str> = None;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' if i == 0 || bytes[i - 1] != b'-' => depth -= 1,
            b':' if depth == 0 && bytes.get(i + 1) == Some(&b':') => {
                let segment = &s[start..i];
                if !segment.is_empty() && !segment.starts_with('<') {
                    last_non_generic = Some(segment);
                }
                start = i + 2;
                i += 2;
                continue;
            }
            _ => {}
        }
        if depth < 0 {
            return out;
        }
        i += 1;
    }
    if depth != 0 {
        return out;
    }
    let final_segment = &s[start..];
    if !final_segment.is_empty() && !final_segment.starts_with('<') {
        last_non_generic = Some(final_segment);
    }
    if let Some(item) = last_non_generic
        && item != first
    {
        out[1] = Some(item);
    }
    out
}

#[cfg(test)]
fn terminal_segments(callee: &str) -> Vec<&str> {
    terminal_segment_pair(callee).into_iter().flatten().collect()
}

/// Extract the short function name from a possibly qualified callee string.
///
/// E.g., `libc::malloc` -> `malloc`, `std::ffi::c_str::strlen` -> `strlen`.
pub(crate) fn extract_callee_name(callee: &str) -> &str {
    callee.rsplit("::").next().unwrap_or(callee)
}

/// What the extractor says about one call, for [`summary_for_call`]: `is_foreign`
/// (`tcx.is_foreign_item`), the call's [`trust_types::CalleeKey`], and how many
/// arguments it passes.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CallIdentity<'a> {
    pub(crate) is_foreign: bool,
    pub(crate) key: Option<&'a trust_types::CalleeKey>,
    pub(crate) arg_count: usize,
}

/// The summary that binds this call: the row named by the callee's last segment (else
/// its whole string), kept only if [`FfiSummary::binds_call`] admits the call's
/// identity. `None` sends the call down the fail-closed no-summary branch.
pub(crate) fn summary_for_call<'db>(
    db: &'db FfiSummaryDb,
    callee: &str,
    call: CallIdentity<'_>,
) -> Option<&'db FfiSummary> {
    db.lookup(extract_callee_name(callee))
        .or_else(|| db.lookup(callee))
        .filter(|summary| summary.binds_call(call.is_foreign, call.key, call.arg_count))
}

/// Generate targeted VCs for an FFI call site using summary-based contracts.
///
/// This is the main entry point called from `generate_vcs()` in lib.rs.
/// Returns a non-empty vec if a summary was found, or empty vec if not
/// (in which case the caller falls through to conservative VCs).
///
/// For each matching summary, generates:
/// 1. Parameter contract VCs (null, range, aliasing) via `generate_ffi_vcs()`
/// 2. Side effect VCs for allocation/deallocation/callback operations
///
/// The summary's RETURN contract is deliberately NOT emitted: it is the
/// callee's guarantee (an assumption), and this layer has no assumption
/// channel — see the in-body comment at step 2.
#[cfg(test)]
#[must_use]
pub(crate) fn generate_call_site_vcs(
    func_name: &str,
    callee: &str,
    args: &[Formula],
    dest_var: &str,
    span: &SourceSpan,
    db: &FfiSummaryDb,
    // Arg positions with proven non-null provenance (see
    // `generate::ffi_nonnull_locals`) — their null VCs are discharged at
    // generation. Empty set = no discharge (the prior behavior, fail-closed).
    nonnull_args: &std::collections::HashSet<usize>,
) -> Vec<VerificationCondition> {
    // Synthetic MIR carries no key: a `SummaryBinding::UpstreamLibcSymbol` row never
    // binds here, and every legacy `DeclName` row binds as before.
    generate_call_site_vcs_with_extents(
        func_name,
        callee,
        args,
        dest_var,
        span,
        db,
        (nonnull_args, &Default::default()),
        CallIdentity { is_foreign: false, key: None, arg_count: args.len() },
    )
}

/// The production caller supplies must-proven byte extents at this exact call.
/// The no-facts entry above deliberately retains an unknown capacity obligation.
/// `call` is the call's identity, which decides whether a summary binds it
/// ([`summary_for_call`]).
#[allow(clippy::too_many_arguments)]
pub(crate) fn generate_call_site_vcs_with_extents(
    func_name: &str,
    callee: &str,
    args: &[Formula],
    dest_var: &str,
    span: &SourceSpan,
    db: &FfiSummaryDb,
    provenance: (&std::collections::HashSet<usize>, &std::collections::HashMap<usize, u64>),
    call: CallIdentity<'_>,
) -> Vec<VerificationCondition> {
    let (nonnull_args, byte_extents) = provenance;
    let short_name = extract_callee_name(callee);
    // A summary whose binding the call's identity does not meet is no summary
    // (FFI-SCALAR-LIBC-1): the call keeps the `unmodeled FFI call` row below.
    let summary = match summary_for_call(db, callee, call) {
        Some(s) => s,
        None => {
            // Recognized extern (the caller gates on `is_extern_call`) with no
            // modeled summary. We cannot prove the call safe, so fail closed:
            // emit a conservative obligation in addition to any format check.
            // (round-19: previously this returned empty for any non-printf
            // extern, silently treating an unmodeled FFI call as safe — a
            // false-PROVE. `is_unsafe_fn_call` matches `::ffi::` but NOT bare
            // `libc::`/`extern`, so unsafe_verify did not backstop it.)
            let mut vcs: Vec<VerificationCondition> =
                format_string_violation_vc(func_name, short_name, args, span).into_iter().collect();
            vcs.push(unmodeled_ffi_obligation(
                func_name,
                short_name,
                span,
                "unmodeled FFI call: no summary, cannot prove safe",
            ));
            return vcs;
        }
    };

    let mut vcs = Vec::new();
    let fn_sym: trust_types::Symbol = func_name.into();

    if let Some(vc) = format_string_violation_vc(func_name, short_name, args, span) {
        vcs.push(vc);
    }

    // Consult the modeled safety level. An `UnsafeUnknown` function has
    // unmodeled behavior (arbitrary side effects per the enum docs), so even
    // with a summary registered we cannot prove the call safe — fail closed.
    // (round-19: `safety_level` was dead metadata; this is its first consumer.)
    if summary.safety_level == SafetyLevel::UnsafeUnknown {
        vcs.push(unmodeled_ffi_obligation(
            func_name,
            short_name,
            span,
            "FFI safety_level=UnsafeUnknown: behavior unmodeled, cannot prove safe",
        ));
    }

    // 1. Parameter contract VCs (null checks, range checks, aliasing)
    // Use the existing generate_ffi_vcs but re-tag with FfiBoundaryViolation kind.
    let param_vcs =
        generate_ffi_vcs_with_extents(func_name, summary, args, nonnull_args, byte_extents);
    for vc in param_vcs {
        // Re-wrap the Assertion VCs as FfiBoundaryViolation for richer categorization.
        let desc = match vc.kind {
            VcKind::Assertion { message } => message,
            other => other.description(),
        };
        vcs.push(VerificationCondition {
            kind: VcKind::FfiBoundaryViolation { callee: short_name.to_string(), desc },
            function: fn_sym.clone(),
            location: span.clone(),
            formula: vc.formula,
            contract_metadata: None,
            obligation: None,
        });
    }

    // 2. Return contract: NOT an obligation (T6 machinery fix (b), report
    //    addendum). The summary's return contract is the CALLEE'S GUARANTEE
    //    about `dest_var` (e.g. write(2) returns >= -1) — an ASSUMPTION the
    //    caller may rely on, never something the caller must discharge. It
    //    used to be emitted here as an assertion of `Not(contract)` against
    //    the havoc'd (unconstrained) dest: always SAT by construction, so
    //    EVERY summarized call with a return contract refuted — semantically
    //    backwards. This layer has no assumption channel: it returns only
    //    `Vec<VerificationCondition>` (obligations), and no Assume-fact
    //    plumbing reaches the sibling call-site VCs, so the contract cannot
    //    yet be registered as a usable fact. The backwards obligation is
    //    therefore DROPPED. Precision loss only, never soundness: an
    //    assumption can only help DISCHARGE other obligations, so omitting it
    //    can only lose proofs (a caller branching on `ret >= -1` stays
    //    Unknown), never mint one. When a fact channel lands, instantiate
    //    `apply_summary(summary, args).rename_var("__ffi_ret", dest_var)` as
    //    an assumed fact here.

    // 3. Side effect VCs for allocation/deallocation operations.
    for effect in &summary.side_effects {
        match effect {
            SideEffect::AllocatesMemory => {
                // VC: the returned pointer is either null or a valid allocation.
                // This is already captured by the return contract for malloc/calloc.
                // Generate an additional VC asserting the allocation is non-null
                // (conservative: caller should check return value).
                vcs.push(VerificationCondition {
                    kind: VcKind::FfiBoundaryViolation {
                        callee: short_name.to_string(),
                        desc: "allocation may return null".to_string(),
                    },
                    function: fn_sym.clone(),
                    location: span.clone(),
                    formula: Formula::Eq(
                        Box::new(Formula::var(dest_var, Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                    obligation: None,
                });
            }
            SideEffect::FreesMemory => {
                // VC: the freed pointer must have been previously allocated.
                // Conservative: we assert the pointer is non-null (as a necessary
                // condition for a valid free, though free(NULL) is technically ok).
                if let Some(_arg) = args.first() {
                    vcs.push(VerificationCondition {
                        kind: VcKind::FfiBoundaryViolation {
                            callee: short_name.to_string(),
                            desc: "freed pointer must be valid allocation".to_string(),
                        },
                        function: fn_sym.clone(),
                        location: span.clone(),
                        // Conservative: always SAT = "cannot verify allocation provenance"
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                        obligation: None,
                    });
                }
            }
            SideEffect::WritesGlobal(_) => {
                // NO obligation (T6 machinery fix (a), report addendum). This
                // arm used to emit a `Bool(true)` (always-SAT, undischargeable
                // by construction) VC "for audit purposes" — but the FFI
                // lane's VCs land as hardened obligations, so the
                // informational flag refuted every call to a summarized
                // function carrying a WritesGlobal effect (`write`'s
                // `WritesGlobal("fd")` was part of the 38-obligation
                // aterm-types refutation in the report). The soundness rule:
                // an obligation must be dischargeable in principle, or it is
                // mis-laned. A global write is not a caller-dischargeable
                // proof obligation; it is state invalidation, which the
                // pipeline already models by leaving the affected state
                // havoc'd (nothing here constrains it). Contrast the arms
                // that STAY fail-closed — AllocatesMemory (nullability of the
                // returned allocation), FreesMemory (allocation provenance),
                // CallsCallback (arbitrary non-local effects): each guards a
                // genuinely unverifiable-at-this-layer property where a
                // conservative false-FAIL is the deliberate, commented
                // semantic.
            }
            SideEffect::CallsCallback => {
                // Conservative: callback may modify any non-local state.
                vcs.push(VerificationCondition {
                    kind: VcKind::FfiBoundaryViolation {
                        callee: short_name.to_string(),
                        desc: "calls callback (non-local state havoced)".to_string(),
                    },
                    function: fn_sym.clone(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });
            }
            // ReadsGlobal and None have no verification obligations.
            _ => {}
        }
    }

    vcs
}

fn format_string_violation_vc(
    func_name: &str,
    callee: &str,
    args: &[Formula],
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let format_index = printf_family_format_index(callee)?;
    let format_arg = args.get(format_index)?;
    let evidence = unsafe_format_argument_evidence(format_arg)?;

    Some(VerificationCondition {
        kind: VcKind::FormatStringViolation { callee: callee.to_string(), evidence },
        function: func_name.into(),
        location: span.clone(),
        // Bad-state VC convention: SAT means a violation is possible. If the
        // current model only tells us the format is symbolic/tainted, fail closed.
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    })
}

pub(crate) fn unsafe_format_argument_evidence(format_arg: &Formula) -> Option<String> {
    if formula_is_constant(format_arg) {
        return None;
    }

    if formula_has_taint_evidence(format_arg) {
        return Some("format argument carries taint evidence".to_string());
    }

    Some("format argument is not a recovered constant".to_string())
}

fn formula_is_constant(formula: &Formula) -> bool {
    matches!(
        formula,
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. }
    )
}

fn formula_has_taint_evidence(formula: &Formula) -> bool {
    formula_has_var_matching(formula, &|name| {
        let bytes = name.as_bytes();
        let contains_ignore_ascii_case =
            |pat: &[u8]| bytes.windows(pat.len()).any(|w| w.eq_ignore_ascii_case(pat));
        contains_ignore_ascii_case(b"taint")
            || contains_ignore_ascii_case(b"user")
            || contains_ignore_ascii_case(b"input")
            || contains_ignore_ascii_case(b"network")
            || contains_ignore_ascii_case(b"extern")
    })
}

fn formula_has_var_matching(formula: &Formula, predicate: &impl Fn(&str) -> bool) -> bool {
    trust_types::any_formula_node(formula, &mut |node| match node {
        Formula::Var(name, _) => predicate(name),
        Formula::SymVar(name, _) => predicate(name.as_str()),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ffi_summary::FfiSummaryDb;

    #[test]
    fn test_is_extern_call_libc_prefix() {
        let db = FfiSummaryDb::new();
        assert!(is_extern_call("libc::malloc", &db));
        assert!(is_extern_call("std::libc::free", &db));
        assert!(is_extern_call("core::ffi::c_str::strlen", &db));
        assert!(is_extern_call("weird:::ffi::strlen", &db));
        assert!(is_extern_call("weird:::libc::free", &db));
    }

    #[test]
    fn test_is_extern_call_known_name() {
        let db = FfiSummaryDb::new();
        // Bare synthetic-MIR names still match by full-string lookup.
        assert!(is_extern_call("malloc", &db));
        assert!(is_extern_call("libc::malloc", &db));
        assert!(is_extern_call("core::ffi::c_str::strlen", &db));
        // T1 flip (ffi-name-collision over-refutation): a QUALIFIED Rust path
        // whose TERMINAL segment collides with a libc name is NOT an extern
        // call. The deleted Pattern 3 bound `some::module::memcpy` to the
        // memcpy(3) summary and `RwLock::write` to write(2), refuting
        // zero-unsafe registry code (38 obligations in aterm-types).
        assert!(!is_extern_call("some::module::memcpy", &db));
        assert!(!is_extern_call("std::sync::RwLock::<T>::write", &db));
        assert!(!is_extern_call("std::sync::RwLock::<T>::read", &db));
        assert!(!is_extern_call("std::io::Write::write", &db));
        assert!(!is_extern_call("std::ptr::read", &db));
    }

    #[test]
    fn test_is_extern_call_unknown() {
        let db = FfiSummaryDb::new();
        assert!(!is_extern_call("std::vec::Vec::push", &db));
        assert!(!is_extern_call("my_safe_function", &db));
    }

    #[test]
    fn test_is_extern_call_extern_segment_not_substring() {
        // T6: `extern` must match as a whole path SEGMENT (or the
        // `extern "<abi>"` fn-pointer type spelling), never as a substring —
        // `contains("extern")` used to route these safe Rust paths into the
        // fail-closed no-summary branch.
        let db = FfiSummaryDb::new();
        assert!(!is_extern_call("my::external_id", &db));
        assert!(!is_extern_call("extern_spec_registry::collect_entries", &db));
        assert!(!is_extern_call("crate::internals::externalize", &db));
        // Genuine spellings still route:
        // synthetic/test MIR with a literal `extern` segment...
        assert!(is_extern_call("some::extern::shim_fn", &db));
        // ...and an fn-pointer-typed callee (`func_operand_name`'s
        // `format!("{ty}")` arm stringifies the TYPE as the callee).
        assert!(is_extern_call("unsafe extern \"C\" fn(i32) -> i32", &db));
        assert!(is_extern_call("for<'a> extern \"C\" fn(&'a u8)", &db));
        // A safe generic method whose TURBOFISH carries an fn-pointer type is
        // a def path, not a type — excluded by the `::<` discriminator.
        assert!(!is_extern_call("std::vec::Vec::<extern \"C\" fn()>::push", &db));
        // The identity seam now renders the `{{extern}}` DefPath segment that
        // rustc's printer dropped, and it renders as `{extern#N}` — NOT as the
        // bare keyword `extern`. So pattern 2a's segment equality does NOT
        // newly fire on every foreign def path, and this heuristic's verdict is
        // BYTE-UNCHANGED by the seam (`t_k::go::boom` and
        // `t_k::go::{extern#0}::boom` agree). That is the intended behaviour,
        // not an oversight: genuine foreign imports carry `is_foreign`
        // (tcx.is_foreign_item) from extraction, the authoritative signal, and
        // making this fallback fire on `{extern#N}` would route every foreign
        // call into the no-summary fail-closed branch — a NEW spurious
        // obligation on code that already routes correctly.
        assert!(!is_extern_call("t_k::go::{extern#0}::boom", &db));
        assert!(!is_extern_call("t_k::go::boom", &db));
    }

    /// G1: pattern 1 (`libc::`) routes only an UNKEYED callee. A keyed callee
    /// outside every extern block is a Rust function with a MIR body (the libc
    /// crate's `const fn WIFEXITED`), which the FFI lane must not stand in for;
    /// an unkeyed `libc::` callee (synthetic MIR) still routes, and a keyed
    /// callee whose other patterns fire (a user `ffi` module) still routes.
    #[test]
    fn test_is_extern_call_pattern1_routes_only_unkeyed_callees() {
        let db = FfiSummaryDb::new();
        let rust_item = |krate: &str| trust_types::CalleeKey {
            sysroot_item: None,
            krate_is_real_sysroot: false,
            krate_name_is_ambiguous: false,
            stable_crate_id: 7,
            krate_name: krate.to_string(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        };
        let wifexited = "__trust_crate@bd801d157b387ef8::libc::unix::bsd::apple::WIFEXITED";
        // Positive control: unkeyed, the name fallback routes it.
        assert!(is_extern_call(wifexited, &db));
        assert!(is_extern_call_for(wifexited, None, &db));
        // Keyed as a Rust item: not routed.
        assert!(!is_extern_call_for(wifexited, Some(&rust_item("libc")), &db));
        assert!(!is_extern_call_for("libc::WEXITSTATUS", Some(&rust_item("libc")), &db));
        // Other patterns are unchanged for a keyed callee.
        assert!(is_extern_call_for("my_sys::ffi::do_io", Some(&rust_item("my_sys")), &db));
        assert!(is_extern_call_for("some::extern::shim_fn", Some(&rust_item("some")), &db));
    }

    #[test]
    fn test_is_extern_call_std_ffi_namespace_is_not_extern() {
        // T6: `::ffi::` must not match the std namespaces — CStr::as_ptr is a
        // SAFE accessor; routing it into the FFI lane's no-summary branch
        // refuted safe code. A USER `ffi` module still routes.
        let db = FfiSummaryDb::new();
        assert!(!is_extern_call("core::ffi::c_str::CStr::as_ptr", &db));
        assert!(!is_extern_call("std::ffi::OsStr::to_str", &db));
        assert!(!is_extern_call("alloc::ffi::c_str::CString::new", &db));
        assert!(is_extern_call("my_sys::ffi::do_io", &db));
        // std-namespace carve: a terminal segment that IS a modeled libc name
        // keeps the synthetic-binding shape routable.
        assert!(is_extern_call("std::ffi::c_str::strlen", &db));
        // `strlen` is a genuine FOREIGN import in an `extern` block inside
        // `CStr::from_ptr`'s body, so `safe_def_path_str` now renders the
        // `{extern#N}` segment rustc's printer used to drop (that drop merged the
        // import into its GRANDPARENT namespace and aliased a real call key).
        // This lane is a RECOVERY — it binds the call to a modeled summary
        // instead of the fail-closed unmodeled-FFI obligation — so it must keep
        // routing. Both matches used here are namespace-position-independent:
        // `contains("::ffi::")` and the LAST segment.
        assert!(is_extern_call("core::ffi::c_str::{extern#0}::strlen", &db));
        assert!(is_extern_call("std::ffi::c_str::{extern#0}::strlen", &db));
        // The T1 over-refutation guard is unchanged by the new segment: a
        // qualified Rust path is still not an extern call.
        assert!(!is_extern_call("std::sync::RwLock::<T>::write", &db));
    }

    /// FFI-STD-QPATH-1 (2026-10-25). The callee strings below are copied byte for
    /// byte from REAL extracted MIR (`-Ztrust-dump=mir`, atpkg Trust 15698,
    /// `trustc 1.99.0-dev (20565c325 2026-10-19)`) of the claude-code-alab
    /// shapes (`Vec<OsString>` argument parsing, `derive(Clone, PartialEq)` over
    /// `Vec<OsString>`, `OsString` deref and comparison). Every one is a SAFE std
    /// call with `is_foreign: false`, and every one reached the fail-closed
    /// no-summary branch as `unmodeled FFI call: no summary, cannot prove safe`
    /// because the std exemption read only `starts_with("std::")`.
    const STD_QPATH_CALLEES: &[&str] = &[
        "<std::ffi::os_str::OsString as core::ops::deref::Deref>::deref",
        "<alloc::vec::Vec<std::ffi::os_str::OsString> as core::clone::Clone>::clone",
        "<alloc::vec::Vec<std::ffi::os_str::OsString> as core::iter::traits::collect::IntoIterator>::into_iter",
        "<alloc::vec::into_iter::IntoIter<std::ffi::os_str::OsString> as core::iter::traits::iterator::Iterator>::peekable",
        "<core::iter::adapters::peekable::Peekable<alloc::vec::into_iter::IntoIter<std::ffi::os_str::OsString>> as core::iter::traits::iterator::Iterator>::next",
        "<core::iter::adapters::peekable::Peekable<alloc::vec::into_iter::IntoIter<std::ffi::os_str::OsString>> as core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<std::ffi::os_str::OsString>>::<__trust_elem_bytes@24>",
        "<alloc::vec::Vec<std::ffi::os_str::OsString> as core::ops::index::Index<usize>>::index",
        "<std::ffi::os_str::OsString as core::cmp::PartialEq<&str>>::eq",
        "<&std::ffi::os_str::OsString as core::cmp::PartialEq>::eq",
        "<&alloc::vec::Vec<std::ffi::os_str::OsString> as core::cmp::PartialEq>::eq",
        "<core::slice::iter::Iter<'_, std::ffi::os_str::OsString> as core::iter::traits::iterator::Iterator>::map::<core::option::Option<alloc::string::String>, {closure@a1.rs:17:21: 17:24}>",
        "<core::iter::adapters::map::Map<core::slice::iter::Iter<'_, std::ffi::os_str::OsString>, {closure@a1.rs:17:21: 17:24}> as core::iter::traits::iterator::Iterator>::collect::<core::option::Option<alloc::vec::Vec<alloc::string::String>>>::<__trust_elem_bytes@24>",
        // agy-alab's spellings (atpkg 15698 dumps): std's unix extension trait,
        // whose own path is a std `ffi` module, and a `dyn Fn` whose output is a
        // std ffi type (that dispatch keeps its open-principal rows; it is
        // simply not a foreign call).
        "<std::ffi::os_str::OsStr as std::os::unix::ffi::os_str::OsStrExt>::from_bytes",
        "<std::ffi::os_str::OsStr as std::os::unix::ffi::os_str::OsStrExt>::as_bytes",
        "<dyn for<'_> core::ops::function::Fn(&'_ str) -> core::option::Option<std::ffi::os_str::OsString> as core::ops::function::Fn<(&str,)>>::call",
        // A user generic fn instantiated at a std ffi type: the same defect in
        // its plain-path spelling (the head is not std, the ffi path is).
        "my_crate::takes::<std::ffi::os_str::OsString>",
    ];

    #[test]
    fn std_ffi_type_in_a_qualified_path_or_generic_argument_is_not_extern() {
        let db = FfiSummaryDb::new();
        for callee in STD_QPATH_CALLEES {
            // Positive control for the instrument: the callee DOES contain the
            // namespace the pattern keys on, so a `false` below is the exemption
            // deciding, not a pattern that never looked.
            assert!(callee.to_lowercase().contains("::ffi::"), "{callee}");
            assert!(
                !is_extern_call(callee, &db),
                "safe std call routed into the FFI lane: {callee}"
            );
        }
    }

    #[test]
    fn user_ffi_module_anywhere_in_a_callee_still_routes() {
        // Negative controls: a NON-std `ffi` module keeps the callee in the FFI
        // lane wherever it appears — the head, the qualified `Self` type, the
        // trait, a generic argument of a std `Self` type, or beside a std ffi
        // type in the same callee.
        let db = FfiSummaryDb::new();
        for callee in [
            "my_sys::ffi::do_io",
            "my_sys::ffi::f",
            "<my_sys::ffi::Handle as core::ops::drop::Drop>::drop",
            "<my_sys::ffi::Handle as Drop>::drop",
            "<my_sys::ffi::Handle as core::cmp::PartialEq>::eq",
            "<&my_sys::ffi::Handle as core::clone::Clone>::clone",
            "<std::ffi::os_str::OsString as my_sys::ffi::Convert>::convert",
            "<alloc::vec::Vec<my_sys::ffi::Handle> as core::clone::Clone>::clone",
            "<alloc::vec::Vec<my_sys::ffi::Handle> as core::ops::drop::Drop>::drop",
            "<(std::ffi::os_str::OsString, my_sys::ffi::Handle) as core::clone::Clone>::clone",
            "<dyn my_sys::ffi::Tr as core::fmt::Debug>::fmt",
            "<dyn for<'_> core::ops::function::Fn(&'_ str) -> my_sys::ffi::Handle as core::ops::function::Fn<(&str,)>>::call",
            "my_crate::takes::<my_sys::ffi::Handle>",
            // A user module that merely ENDS in `std` cannot forge a std root by
            // a non-ASCII byte splitting the token, nor by case.
            "my_crate::éstd::ffi::f",
            "<my_crate::éstd::ffi::Handle as core::clone::Clone>::clone",
            "Std::ffi::f",
            "<STD::ffi::Handle as core::clone::Clone>::clone",
            // A crate impersonating `std` is stamped by the extractor at the ROOT
            // of a path it renders (the first line is that real shape); the stamp
            // refuses the exemption wherever it sits. The other two are SYNTHETIC
            // belt: the extractor does not stamp inside a qualified header or a
            // generic argument (see the fingerprint controls below for what it
            // writes there).
            "__trust_crate@1973d11b2baa21fa::std::ffi::f",
            "<__trust_crate@1973d11b2baa21fa::std::ffi::Handle as core::clone::Clone>::clone",
            "<alloc::vec::Vec<__trust_crate@1973d11b2baa21fa::std::ffi::H> as core::clone::Clone>::clone",
        ] {
            assert!(is_extern_call(callee, &db), "user ffi callee left the FFI lane: {callee}");
        }
        // Extern fn pointers (the callee is the TYPE) route by pattern 2a,
        // whatever their argument types name.
        assert!(is_extern_call("unsafe extern \"C\" fn(i32) -> i32", &db));
        assert!(is_extern_call("unsafe extern \"C\" fn(*const std::ffi::c_char) -> usize", &db));
        // The modeled-libc terminal carve still applies to an exempt qualified
        // path, including behind trailing turbofish groups.
        assert!(is_extern_call("<std::ffi::c_str::CStr as my_crate::Shim>::strlen", &db));
        assert!(is_extern_call(
            "<std::ffi::c_str::CStr as my_crate::Shim>::strlen::<u8>::<__trust_elem_bytes@1>",
            &db
        ));
    }

    /// FFI-STD-QPATH-1 review, finding 2 (2026-10-26). A dependency built
    /// `--crate-name std` (verify-off, an `ffi` module whose `Handle: Clone` calls a
    /// foreign `write(1, NULL, 1)`) is stamped `__trust_crate@…` only at the ROOT of a
    /// path the extractor renders. Inside a qualified `<Self as Trait>` header or a
    /// generic argument its types render as plain `std::ffi::…`, and the producer
    /// writes the duplicate-crate-name argument fingerprint instead. The two callees
    /// below are copied byte for byte from that probe's real extraction (stage 1 of
    /// this branch at `003c01d50`); before the decline they were exempt.
    #[test]
    fn a_fingerprinted_callee_never_reads_a_std_ffi_type_out_of_its_arguments() {
        let db = FfiSummaryDb::new();
        let forged = [
            "<std::ffi::Handle as core::clone::Clone>::clone::<__trust_args@9959d3f328eac09dccdc30f1579ceda9>",
            "<alloc::vec::Vec<std::ffi::Handle> as core::clone::Clone>::clone::<__trust_args@569bb5ec7e1b21443edeed52c58c536a>",
        ];
        for callee in forged {
            // Instrument controls: no root stamp anywhere (so the stamp rule is not
            // what decides), the producer's fingerprint IS present, and the
            // same spelling without it is exempt — the fingerprint is the decider.
            assert!(!trust_types::path_has_unauthenticated_crate_stamp(callee), "{callee}");
            assert!(trust_types::args_display_may_name_a_same_named_crate(callee), "{callee}");
            let untagged = trust_types::strip_trailing_args_fingerprint(callee);
            assert_ne!(untagged, callee);
            assert!(!is_extern_call(untagged, &db), "positive control: {untagged}");
            assert!(
                is_extern_call(callee, &db),
                "a fingerprinted callee read a possibly forged std ffi type: {callee}"
            );
        }
        // Shape 1 (an authenticated std ROOT, stamped when forged) keeps its
        // pre-existing meaning on a tagged callee: the root is the item called.
        assert!(!is_extern_call(
            "std::ffi::OsStr::new::<my::T>::<__trust_args@00000000000000010000000000000023>",
            &db
        ));
        // The fingerprint also refuses the generic plain-path shape.
        assert!(is_extern_call(
            "my_crate::takes::<std::ffi::os_str::OsString>::<__trust_args@00000000000000010000000000000023>",
            &db
        ));
        assert!(!is_extern_call("my_crate::takes::<std::ffi::os_str::OsString>", &db));
    }

    #[test]
    fn terminal_segments_finds_the_item_behind_turbofish_groups() {
        assert_eq!(terminal_segments("std::ffi::c_str::strlen"), vec!["strlen"]);
        assert_eq!(
            terminal_segments("<std::ffi::os_str::OsString as core::ops::deref::Deref>::deref"),
            vec!["deref"]
        );
        assert_eq!(
            terminal_segments("<A<B> as C>::collect::<D<E>>::<__trust_elem_bytes@24>"),
            vec!["<__trust_elem_bytes@24>", "collect"]
        );
        // `->` inside a generic argument is not a closing bracket.
        assert_eq!(terminal_segments("<A as B>::m::<fn() -> u8>"), vec!["<fn() -> u8>", "m"]);
        // An unbalanced spelling answers only the plain candidate.
        assert_eq!(terminal_segments("a::b>::c"), vec!["c"]);
    }

    #[test]
    fn test_extract_callee_name() {
        assert_eq!(extract_callee_name("libc::malloc"), "malloc");
        assert_eq!(extract_callee_name("std::ffi::c_str::strlen"), "strlen");
        assert_eq!(extract_callee_name("malloc"), "malloc");
        // The seam's `{extern#N}` segment is a MIDDLE segment, so the summary
        // key — the last segment — is unmoved.
        assert_eq!(extract_callee_name("core::ffi::c_str::{extern#0}::strlen"), "strlen");
        assert_eq!(extract_callee_name("my_sys::ffi::{extern#2}::malloc"), "malloc");
    }

    #[test]
    fn test_generate_call_site_vcs_malloc() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("size".into(), Sort::Int)];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "libc::malloc",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        // malloc: non-null param + range param + return contract + allocation side effect
        assert!(!vcs.is_empty(), "malloc should produce VCs");

        // All VCs should be FfiBoundaryViolation
        for vc in &vcs {
            assert!(
                matches!(&vc.kind, VcKind::FfiBoundaryViolation { .. }),
                "all VCs should be FfiBoundaryViolation, got: {:?}",
                vc.kind
            );
        }

        // Should have null-check VC
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("non-null")
            )),
            "should have non-null parameter check"
        );

        // Should have allocation may return null VC
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("allocation may return null")
            )),
            "should have allocation null check"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_memcpy() {
        let db = FfiSummaryDb::new();
        let args = vec![
            Formula::Var("dest".into(), Sort::Int),
            Formula::Var("src".into(), Sort::Int),
            Formula::Var("n".into(), Sort::Int),
        ];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "memcpy",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        assert!(!vcs.is_empty(), "memcpy should produce VCs");

        // Should have non-alias VC
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("must not alias")
            )),
            "should have aliasing check for memcpy"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_unmodeled_extern_fails_closed() {
        // round-19: a recognized extern with no summary must NOT silently pass.
        // It emits a conservative, never-dischargeable obligation (Bool(true) =
        // always SAT) so the call is reported Unknown/Failed, never Proved.
        let db = FfiSummaryDb::new();
        let vcs = generate_call_site_vcs(
            "test_fn",
            "unknown_extern_fn",
            &[],
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );
        assert_eq!(vcs.len(), 1, "unmodeled extern must emit one conservative VC");
        assert!(
            matches!(vcs[0].kind, VcKind::FfiBoundaryViolation { .. }),
            "expected an FfiBoundaryViolation obligation, got {:?}",
            vcs[0].kind
        );
        assert_eq!(
            vcs[0].formula,
            Formula::Bool(true),
            "unmodeled FFI obligation must be fail-closed (always SAT)"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_unsafe_unknown_summary_fails_closed() {
        // A registered summary marked UnsafeUnknown must also fail closed: the
        // safety_level field is now consulted (was dead metadata).
        use crate::ffi_summary::FfiSummary;
        let mut db = FfiSummaryDb::new();
        db.register(FfiSummary::new("mystery_extern").with_safety(SafetyLevel::UnsafeUnknown));
        let vcs = generate_call_site_vcs(
            "test_fn",
            "mystery_extern",
            &[],
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::FfiBoundaryViolation { desc, .. }
                if desc.contains("UnsafeUnknown"))
                && vc.formula == Formula::Bool(true)),
            "UnsafeUnknown summary must emit a fail-closed obligation; got {vcs:?}"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_printf_symbolic_format_fails_closed() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("user_format".into(), Sort::Int)];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "printf",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        let vc = vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::FormatStringViolation { .. }))
            .expect("symbolic printf format should emit format-string violation VC");

        assert_eq!(vc.formula, Formula::Bool(true));
        match &vc.kind {
            VcKind::FormatStringViolation { callee, evidence } => {
                assert_eq!(callee, "printf");
                assert!(evidence.contains("taint"));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_generate_call_site_vcs_printf_constant_format_no_format_vc() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::BitVec { value: 0x4000, width: 64 }];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "printf",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        assert!(
            !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::FormatStringViolation { .. })),
            "recovered constant format pointer should not emit format-string violation VC"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_printf_family_without_summary_still_checks_format() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("extern_format".into(), Sort::Int)];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "vprintf",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        // The format-string check still fires without a summary (the point of
        // this test). round-19: an unmodeled printf-family extern ALSO now gets
        // the conservative no-summary obligation, so expect both.
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::FormatStringViolation { callee, .. } if callee == "vprintf")),
            "format-string violation must still be checked without a summary; got {vcs:?}"
        );
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("no summary"))
                && vc.formula == Formula::Bool(true)),
            "unmodeled extern must also fail closed; got {vcs:?}"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_return_contract_is_not_an_obligation() {
        // T6 machinery fix (b): the return contract is the CALLEE'S guarantee
        // (an assumption), not a caller obligation. It used to be emitted as
        // `Not(contract)` asserted against the havoc'd dest — always SAT, so
        // every summarized call with a return contract refuted. With no
        // assumption channel at this layer it must simply not be emitted.
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("s".into(), Sort::Int)];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "strlen",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        assert!(
            !vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("return contract")
            )),
            "return contract must not be asserted as an obligation; got {vcs:?}"
        );
        // The genuine caller obligation (non-null string pointer) remains.
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("non-null")
            )),
            "strlen must keep its non-null parameter obligation; got {vcs:?}"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_writes_global_is_not_an_obligation() {
        // T6 machinery fix (a): WritesGlobal is informational (state
        // invalidation the pipeline models by havoc), not a dischargeable
        // obligation. The old Bool(true) audit VC refuted every call to a
        // summarized function carrying the effect (fwrite -> "stream").
        let db = FfiSummaryDb::new();
        let args = vec![
            Formula::Var("ptr".into(), Sort::Int),
            Formula::Var("size".into(), Sort::Int),
            Formula::Var("nmemb".into(), Sort::Int),
            Formula::Var("stream".into(), Sort::Int),
        ];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "fwrite",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        assert!(
            !vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("writes global")
            )),
            "WritesGlobal must not emit an undischargeable obligation; got {vcs:?}"
        );
        // Every remaining fwrite VC is dischargeable in principle (no
        // Bool(true) mis-lanes for a fully modeled Safe summary).
        assert!(
            !vcs.iter().any(|vc| vc.formula == Formula::Bool(true)),
            "fully modeled fwrite call must not carry always-SAT obligations; got {vcs:?}"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_write_keeps_nonnull_and_demands_byte_capacity() {
        // Retain T6's non-null demand and add the missing byte-capacity demand.
        // fd demands are gone (EBADF is errno, not UB — the old
        // [0, i128::MAX] fd range refuted every runtime-provided fd), the
        // count demands are gone (count == 0 is defined and the old
        // "non-null" integer check refuted write(fd, buf, 0)), and
        // WritesGlobal("fd") is dropped.
        let db = FfiSummaryDb::new();
        let args = vec![
            Formula::Var("fd".into(), Sort::Int),
            Formula::Var("buf".into(), Sort::Int),
            Formula::Var("count".into(), Sort::Int),
        ];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "write",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        assert_eq!(vcs.len(), 2, "write must demand non-null and byte capacity; got {vcs:?}");
        assert!(
            matches!(
                &vcs[0].kind,
                VcKind::FfiBoundaryViolation { desc, .. }
                    if desc.contains("parameter 1") && desc.contains("non-null")
            ),
            "the first write demand must remain the parameter-1 null check; got {:?}",
            vcs[0].kind
        );
        // The violation formula is the buf-null case, dischargeable whenever
        // the caller's buffer provably cannot be null.
        assert!(
            matches!(&vcs[0].formula, Formula::Eq(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "buf")
                    && matches!(rhs.as_ref(), Formula::Int(0))),
            "expected `buf == 0` violation formula, got {:?}",
            vcs[0].formula
        );
        assert!(matches!(&vcs[1].kind, VcKind::FfiBoundaryViolation { desc, .. }
            if desc.contains("available byte extent (unknown)")));
        assert_eq!(
            vcs[1].formula,
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("count".into(), Sort::Int)),
                Box::new(Formula::Int(0))
            )))
        );
    }

    #[test]
    fn test_generate_call_site_vcs_free_side_effect() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("ptr".into(), Sort::Int)];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "free",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );

        // free: nullable param (no null check) + FreesMemory side effect
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("freed pointer")
            )),
            "should have deallocation VC"
        );
    }

    #[test]
    fn test_ffi_boundary_violation_proof_level() {
        let kind =
            VcKind::FfiBoundaryViolation { callee: "malloc".into(), desc: "null check".into() };
        assert_eq!(
            kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "FFI boundary violations should be L0 safety"
        );
    }

    #[test]
    fn test_ffi_boundary_violation_description() {
        let kind = VcKind::FfiBoundaryViolation {
            callee: "memcpy".into(),
            desc: "parameters 0 and 1 must not alias".into(),
        };
        let desc = kind.description();
        assert!(desc.contains("memcpy"));
        assert!(desc.contains("must not alias"));
    }

    #[test]
    fn test_ffi_boundary_violation_no_runtime_fallback() {
        let kind = VcKind::FfiBoundaryViolation { callee: "malloc".into(), desc: "test".into() };
        assert!(
            !kind.has_runtime_fallback(true),
            "FFI boundary violations have no runtime fallback"
        );
    }
}
