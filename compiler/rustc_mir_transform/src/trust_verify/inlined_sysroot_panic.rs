//! Trust (2026-09-29): A PANIC PATH THE MIR INLINER COPIED IN FROM FOREIGN CODE
//! IS NEVER A RUNTIME CHECK THE USER WROTE.
//!
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-29 — under an explicit
//! `-Zinline-mir=yes` (or `-Zmir-opt-level=2`), an inlined std panic is a
//! tolerated runtime-checked row", is the hazard this closes.
//!
//! ## The hole
//!
//! The default policy (ruling B, `TrustPolicy::Strict`) reports rather than
//! fails a gap whose every row keeps a runtime check
//! (`abort_on_full_verification_failure`, `residual_gap_tolerance_denial`), and
//! it lets a kept bundle's std member stand as a runtime-checked row
//! (`runtime_checked_std_member`). The whole-function panic-freedom row is a
//! `VcKind::Assertion`, and an assertion "keeps its runtime check" — which is
//! TRUE of the user's own `assert!`/`panic!`: the user wrote that check, and the
//! program keeps vanilla Rust semantics. It is FALSE of a panic inside a std
//! method: at `-O0` the std call stays a `Call` terminator and its call-site
//! lanes charge it (`o.unwrap()`, `s.split_at(k)`, `d[i]` on a `VecDeque`,
//! `s[..k]` are all refused), because a std panic on a caller-supplied value is
//! a safety obligation about the CALLER's value, not a check the caller wrote.
//! And it is false of a DEPENDENCY's body, whose call is fail-closed at `-O0`
//! (a verify-off crate's code carries no verdict).
//!
//! A verifying session runs the `-O0` MIR pipeline at every `-Copt-level` unless
//! `-Zmir-opt-level`/`-Zinline-mir` is given (ruling R1). An EXPLICIT
//! `-Zinline-mir=yes`, or `-Zmir-opt-level>=2` with `-Copt-level>=2`, is honored,
//! and then the callee's body is copied into the caller before any lane sees it:
//! the `Call` is gone, and what remains is the callee's own panic path
//! (`option::unwrap_failed()`, `option::expect_failed(..)`,
//! `core::str::slice_error_fail(..)`, a bounds `Assert`, a dependency's
//! `std::process::abort()`, ...) inside a scope `(inlined <callee>)`. The bridge
//! folds it into the whole-function panic-freedom row, that row keeps its
//! `Assertion` runtime fallback (or the diverging sysroot call it reaches is a
//! tolerated vanilla absent callee), and the default policy accepted it.
//! Measured on main (`0.10.0+g4715fe060`, source of `7eddcd160b`): `o.unwrap()`,
//! `o.unwrap().unwrap()`, `o.expect(..)`, `s.split_at(s.len() / 2)`,
//! `s.split_at(k)`, `s[..k]` and `d[i]` on a `&VecDeque<u32>` each built rc=0
//! under `-Zinline-mir=yes`, `-Zmir-opt-level=2 -Copt-level=3` or
//! `-Zmir-opt-level=3`, and panicked at run time; so did a call to a
//! verify-off dependency's `#[inline]` function that ends in
//! `std::process::abort()` or `v.get(i).expect(..)` (refused at `-O0`).
//!
//! ## The rule
//!
//! Keyed on what the inliner cannot delete — the SCOPE — exactly as the
//! O2-inline rows are (`inlined_unsafe_evidence`): a PANIC SITE is a terminator
//! through which an execution can end in a panic or an abort — an `Assert`, a
//! `Call` with no return target (a diverging call), a `Call` that returns but
//! can PANIC to a callee this crate does not define (see below), a tail call to
//! such a callee, or inline assembly that is `noreturn` or `may_unwind`. A panic
//! site whose NEAREST inlined instance is a NON-LOCAL def — std/core/alloc, or a
//! dependency — is a foreign panic path copied into this body.
//!
//! A returning call "can panic" unless its `UnwindAction` is `Unreachable` IN A
//! SESSION WHOSE PANIC STRATEGY UNWINDS. There, `Unreachable` marks a callee that
//! is itself nounwind (a non-unwinding ABI, `#[rustc_nounwind]`), whose only
//! panic is an abort on a violated std precondition. Under `-Cpanic=abort` (or
//! `immediate-abort`) the MIR pipeline gives EVERY Rust call an `Unreachable`
//! unwind edge (`AbortUnwindingCalls`: no Rust function unwinds), which says
//! nothing about whether the callee panics — a panic there aborts the process
//! instead of unwinding, and it is the same panic. So under an aborting
//! strategy the edge is not read; the CALLEE'S OWN DECLARATION is: a returning
//! foreign call is a site unless its callee carries the codegen flag
//! `NEVER_UNWIND` (`#[rustc_nounwind]`, an `llvm.*` link name), the first thing
//! `fn_can_unwind` reads in every session and so the fact that gives the same
//! call its `Unreachable` edge when the session unwinds. Measured on main
//! `0.10.0+g07091c92c` (2026-09-30): `u32::from_str_radix(s, radix).unwrap_or(0)`
//! under `-Zinline-mir=yes -Cpanic=abort` inlines to
//! `from_ascii_radix(..) -> [return: bb1, unwind unreachable]`, built rc=0, and
//! is refused at `-O0` with the same `-Cpanic=abort`; the first version of the
//! returning-call rule, which skipped every `Unreachable` edge, missed it.
//! The second version (2026-09-30) made EVERY returning foreign call a site
//! under an aborting strategy, which also named calls that cannot panic in any
//! session: measured on the branch (`0.10.0+g7a237b737`, 2026-10-04, probe
//! `l_helper_tolerated_t15a`, and again 2026-10-08 with plain `-Zinline-mir=yes
//! -Cpanic=abort`), a local helper's `assert!(x.count_ones() <= 32)` was refused
//! on "a call to `ctpop` that can panic", the intrinsic `count_ones` inlines to,
//! while the same source built rc=0 under `-Zinline-mir=yes` alone and under
//! `-Cpanic=abort` alone. The declaration test (2026-10-08) gives both strategies
//! one answer for a callee that is nounwind by declaration; a callee that is
//! nounwind only by its ABI (an `extern "C"` import) is excused when the session
//! unwinds and stays a site when it aborts, which over-refuses and nothing else.
//!
//! The unwinding call is in the set because the inliner stops wherever its
//! thresholds say: `Vec::push` inlines to a `push_mut` call, `str::split_at` to a
//! `split_at_checked` call beside its `slice_error_fail`, and under a lower
//! `-Zinline-mir-threshold` an inlined std method's own panic can live entirely
//! in a callee it left as a returning call. That call is gone from no lane —
//! the call-site lanes are scope-agnostic and charge an inner callee they know
//! (`insert_mut`, `Option::expect`) as they would the user's call — but the OUTER
//! method's `-O0` row is gone, and an inner callee no lane names would ride the
//! tolerance in its place. A callee the crate defines (a closure handed to an
//! inlined std adapter) is verified as its own function and is not a site.
//!
//! When a foreign panic site exists, the default policy's runtime-check
//! tolerance and the runtime-checked std-member disposition are both withheld
//! for the function: every unproved row fails, as the callee's own
//! call-site row fails at `-O0`. A function whose rows all PROVE is untouched —
//! a proved panic-freedom row covers the inlined path too — so what this costs
//! is a gap the `-O0` pipeline might have tolerated on an unrelated row (a user
//! `assert!` left unknown beside an inlined std method), or a foreign panic path
//! the `-O0` call-site classification would have tolerated (an inlined
//! `std::process::abort()` reaching `abort_internal`, an inlined `Vec::push`
//! whose growth row the `-O0` pipeline tolerates beside its `push_mut` call):
//! refusal, never acceptance.
//!
//! A panic site in a LOCAL scope (the function's own, or a local closure/fn
//! inlined into it, even when that sits inside an inlined std scope) keeps
//! ruling B, because the nearest inlined instance decides: the user wrote it.
//!
//! The verifying default runs the MIR inliner only for `#[rustc_force_inline]`
//! callees (the `ForceInline` pass runs at every mir-opt-level; the ordinary
//! inliner is off below `mir-opt-level 2`). No sysroot fn carries that attribute,
//! but a dependency built with `rustc_attrs` can: its body is then copied into
//! the verifying caller with NO flag, and its panic path rode the same
//! tolerance (measured on the same main: a dependency's force-inlined
//! `if x == 7 { std::process::abort() }` built rc=0 at the default, where the
//! same call without the attribute is refused). This rule covers that too;
//! beyond it, the verifying default inlines nothing foreign and the rule finds
//! nothing. The parity-preserving successor — minting each inlined callee's
//! `-O0` call-site rows on its inlined scope, so a guarded inlined `unwrap` can
//! prove — is recorded as remaining work in the KNOWN_HAZARDS entry.

use super::*;

/// The first panic site of `body` whose nearest inlined instance is a non-local
/// def, described for a diagnostic, or `None`.
///
/// See the module doc for what a panic site is and why the nearest inlined
/// instance decides. Walks every basic block, cleanup blocks included (a panic
/// on the unwind path is still a panic), in index order, so the answer is a
/// pure function of the MIR. `TRUST_INLINED_PANIC_TRACE=1` prints every site it
/// finds, the first one included.
pub(super) fn inlined_foreign_panic_site<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<String> {
    use rustc_ast::InlineAsmOptions;
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
    use rustc_middle::mir::{TerminatorKind, UnwindAction};
    let trace = env_flag_enabled("TRUST_INLINED_PANIC_TRACE");
    // Under an aborting panic strategy an `Unreachable` unwind edge is the
    // strategy's, not the callee's (see the module doc).
    let session_unwinds =
        matches!(tcx.sess.panic_strategy(), rustc_target::spec::PanicStrategy::Unwind);
    // A callee this crate defines is verified as its own function (a local
    // closure handed to an inlined std adapter, say), so a call to it transports
    // nothing foreign; any other callee, or an indirect one, can.
    let foreign_callee = |func: &Operand<'tcx>| -> Option<String> {
        match func.const_fn_def() {
            Some((def_id, _)) if def_id.is_local() => None,
            Some((def_id, _)) => Some(format!("`{}`", tcx.def_path_str(def_id))),
            None => Some(String::from("an indirect callee")),
        }
    };
    // Is the callee nounwind BY DECLARATION (`CodegenFnAttrFlags::NEVER_UNWIND`:
    // `#[rustc_nounwind]`, as every arithmetic intrinsic is, or an `llvm.*` link
    // name)? That flag is what `fn_can_unwind` reads first in every session, so
    // it is the fact behind this call's `Unreachable` edge when the session
    // unwinds, and it is still readable when the session aborts and the edge
    // says nothing. Asked only of a fn or associated fn (the def kinds that own
    // codegen attributes and can be a direct callee here); anything else, and an
    // indirect callee, answers no.
    let callee_declared_nounwind = |func: &Operand<'tcx>| -> bool {
        func.const_fn_def().is_some_and(|(def_id, _)| {
            matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
                && tcx.codegen_fn_attrs(def_id).flags.contains(CodegenFnAttrFlags::NEVER_UNWIND)
        })
    };
    let mut first = None;
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else { continue };
        let what = match &term.kind {
            TerminatorKind::Assert { .. } => String::from("an `Assert` runtime check"),
            TerminatorKind::Call { func, target: None, .. } => match func.const_fn_def() {
                Some((def_id, _)) => {
                    format!("a diverging call to `{}`", tcx.def_path_str(def_id))
                }
                None => String::from("a diverging indirect call"),
            },
            // A call that RETURNS can still carry its callee's panic out of it, by
            // unwinding: an inlined std method whose own panic lives in a callee the
            // inliner left as a call (`Vec::push` -> `push_mut`, `split_at` ->
            // `split_at_checked`, whatever a lower `-Zinline-mir-threshold` stops
            // at) has no `Assert` and no diverging call of its own, and its `-O0`
            // call-site row is gone all the same. Only a call whose callee is
            // itself nounwind transports nothing, and `UnwindAction::Unreachable`
            // says so only while the session unwinds: under `-Cpanic=abort` every
            // Rust call carries it (see the module doc), and the callee's panic
            // aborts instead. There the callee's own declaration is asked, so a
            // call that is nounwind in every session (`ctpop`, which `count_ones`
            // inlines to) is no more a site under an aborting strategy than under
            // an unwinding one.
            TerminatorKind::Call { func, unwind, target: Some(_), .. } => {
                if matches!(unwind, UnwindAction::Unreachable)
                    && (session_unwinds || callee_declared_nounwind(func))
                {
                    continue;
                }
                let Some(callee) = foreign_callee(func) else { continue };
                if session_unwinds {
                    format!("a call to {callee} that can unwind")
                } else {
                    format!("a call to {callee} that can panic (an abort, under this strategy)")
                }
            }
            TerminatorKind::TailCall { func, .. } => {
                let Some(callee) = foreign_callee(func) else { continue };
                format!("a tail call to {callee}")
            }
            TerminatorKind::InlineAsm { options, .. } => {
                if !(options.contains(InlineAsmOptions::NORETURN)
                    || options.contains(InlineAsmOptions::MAY_UNWIND))
                {
                    continue;
                }
                String::from("inline assembly that can diverge or unwind")
            }
            _ => continue,
        };
        let Some(instance) = term.source_info.scope.inlined_instance(&body.source_scopes) else {
            continue;
        };
        let owner_def = instance.def_id();
        if owner_def.is_local() {
            continue;
        }
        let owner = if trust_mir_extract::def_is_in_real_sysroot_crate(tcx, owner_def) {
            String::from("std/core/alloc")
        } else {
            format!("the dependency crate `{}`", tcx.crate_name(owner_def.krate))
        };
        let site = format!(
            "{what} in {bb:?}, a panic path inlined from `{}` ({owner})",
            tcx.def_path_str(owner_def)
        );
        if trace {
            eprintln!(
                "TRUST_INLINED_PANIC_TRACE: {}: {site}",
                tcx.def_path_str(body.source.def_id())
            );
        }
        if first.is_none() {
            first = Some(site);
            if !trace {
                break;
            }
        }
    }
    first
}

/// The note every refusal on an inlined foreign panic site carries, so both
/// gates that consult [`inlined_foreign_panic_site`] say the same thing.
pub(super) fn inlined_foreign_panic_note(site: &str) -> String {
    format!(
        "this body carries {site}: the MIR inliner (`-Zinline-mir=yes`, \
         `-Zmir-opt-level>=2`, or a dependency's `#[rustc_force_inline]`) copied the callee's \
         panic path into it, where it no longer carries \
         the call-site row that refuses it at the default `-O0` MIR pipeline. A std panic on a \
         caller-supplied value, or a dependency's panic, is not a runtime check this program \
         wrote, so it is never tolerated as one. Options: prove the panic unreachable, build \
         without the explicit MIR-inlining flag (the verifying default already compiles every \
         `-Copt-level` from the `-O0` MIR pipeline), or `-Z trust-policy=advisory`"
    )
}

/// Trust (2026-10-04, the landing review's open question): under
/// `TRUST_INLINED_PANIC_TRACE=1`, report a body that carries a foreign panic site
/// and leaves `abort_on_full_verification_failure` by one of its two ACCEPTING
/// early returns — no row at all (`which` = "no rows"), or every row proved
/// ("all rows proved") — before the tolerance gate that reads the site is asked.
///
/// Both returns already require that no unproved assumption-panic row remains (a
/// call to a callee whose body the bridge does not model keeps one, and it is
/// never proved) and that no indirect call is unresolved; an `Assert` or a
/// diverging call is a modeled panic the panic-freedom row must prove
/// unreachable. So a body this reports was accepted because its inlined panic
/// path was proved unreachable or charged by a modeled callee's summary. The
/// trace exists so an adversarial round can check that claim against the
/// program's run instead of trusting it. Diagnostic only: it decides nothing,
/// and without the variable it does not scan. Paths are rendered untrimmed, so
/// an accepted build that prints nothing else cannot trip rustc's "a diagnostic
/// must be emitted" expectation.
pub(super) fn trace_early_accept<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, which: &str) {
    if !env_flag_enabled("TRUST_INLINED_PANIC_TRACE") {
        return;
    }
    with_no_trimmed_paths!({
        if let Some(site) = inlined_foreign_panic_site(tcx, body) {
            eprintln!(
                "TRUST_INLINED_PANIC_TRACE: {}: accepted by an early return ({which}) with {site}",
                tcx.def_path_str(body.source.def_id())
            );
        }
    });
}
