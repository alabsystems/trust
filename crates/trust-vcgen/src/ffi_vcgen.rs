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
    FfiSummaryDb, SafetyLevel, SideEffect, generate_ffi_vcs, is_printf_family,
    printf_family_format_index,
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
///   safe APIs, excluded modulo the modeled-libc-terminal carve)
/// - a bare (un-pathed) name matching a summary or the printf family
#[must_use]
pub(crate) fn is_extern_call(callee: &str, db: &FfiSummaryDb) -> bool {
    let lower = callee.to_lowercase();

    // Pattern 1: libc:: prefix
    if lower.starts_with("libc::") || lower.contains("::libc::") {
        return true;
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
    if callee.split("::").any(|segment| segment == "extern")
        || (lower.contains("extern \"") && !lower.contains("::<"))
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
    if lower.contains("::ffi::") {
        let is_std_ns = lower.starts_with("core::")
            || lower.starts_with("std::")
            || lower.starts_with("alloc::");
        if !is_std_ns {
            return true;
        }
        let last_segment = callee.rsplit("::").next().unwrap_or(callee);
        if db.lookup(last_segment).is_some() || is_printf_family(last_segment) {
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
    db.lookup(callee).is_some() || (!callee.contains("::") && is_printf_family(callee))
}

/// Extract the short function name from a possibly qualified callee string.
///
/// E.g., `libc::malloc` -> `malloc`, `std::ffi::c_str::strlen` -> `strlen`.
fn extract_callee_name(callee: &str) -> &str {
    callee.rsplit("::").next().unwrap_or(callee)
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
    let short_name = extract_callee_name(callee);
    let summary = match db.lookup(short_name).or_else(|| db.lookup(callee)) {
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
    let param_vcs = generate_ffi_vcs(func_name, summary, args, nonnull_args);
    for vc in param_vcs {
        // Re-wrap the Assertion VCs as FfiBoundaryViolation for richer categorization.
        let desc = match &vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => vc.kind.description(),
        };
        vcs.push(VerificationCondition {
            kind: VcKind::FfiBoundaryViolation { callee: short_name.to_string(), desc },
            function: func_name.into(),
            location: span.clone(),
            formula: vc.formula,
            contract_metadata: None,
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
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Eq(
                        Box::new(Formula::Var(dest_var.to_string(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
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
                        function: func_name.into(),
                        location: span.clone(),
                        // Conservative: always SAT = "cannot verify allocation provenance"
                        formula: Formula::Bool(true),
                        contract_metadata: None,
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
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
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
        let lower = name.to_ascii_lowercase();
        lower.contains("taint")
            || lower.contains("user")
            || lower.contains("input")
            || lower.contains("network")
            || lower.contains("extern")
    })
}

fn formula_has_var_matching(formula: &Formula, predicate: &impl Fn(&str) -> bool) -> bool {
    match formula {
        Formula::Var(name, _) => predicate(name),
        Formula::SymVar(name, _) => predicate(&String::from(*name)),
        _ => formula.children().iter().any(|child| formula_has_var_matching(child, predicate)),
    }
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
    }

    #[test]
    fn test_extract_callee_name() {
        assert_eq!(extract_callee_name("libc::malloc"), "malloc");
        assert_eq!(extract_callee_name("std::ffi::c_str::strlen"), "strlen");
        assert_eq!(extract_callee_name("malloc"), "malloc");
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
            &db, &Default::default());

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
        let vcs =
            generate_call_site_vcs("test_fn", "memcpy", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

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
            &db, &Default::default());
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
            &db, &Default::default());
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
        let vcs =
            generate_call_site_vcs("test_fn", "printf", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

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
        let vcs =
            generate_call_site_vcs("test_fn", "printf", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

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
            &db, &Default::default());

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
        let vcs =
            generate_call_site_vcs("test_fn", "strlen", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

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
        let vcs =
            generate_call_site_vcs("test_fn", "fwrite", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

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
    fn test_generate_call_site_vcs_write_demands_only_buf_nonnull() {
        // T6 summary fix: write(2)'s ONLY caller demand is the non-null
        // buffer. fd demands are gone (EBADF is errno, not UB — the old
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
        let vcs =
            generate_call_site_vcs("test_fn", "write", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

        assert_eq!(vcs.len(), 1, "write must demand exactly one thing (buf non-null); got {vcs:?}");
        assert!(
            matches!(
                &vcs[0].kind,
                VcKind::FfiBoundaryViolation { desc, .. }
                    if desc.contains("parameter 1") && desc.contains("non-null")
            ),
            "the single write demand must be the parameter-1 null check; got {:?}",
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
    }

    #[test]
    fn test_generate_call_site_vcs_free_side_effect() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("ptr".into(), Sort::Int)];
        let vcs =
            generate_call_site_vcs("test_fn", "free", &args, "_ret", &SourceSpan::default(), &db, &Default::default());

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
