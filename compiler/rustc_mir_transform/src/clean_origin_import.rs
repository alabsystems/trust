// Trust (I7, decode half): THE CLEAN-ORIGIN IMPORT PROVIDERS — readmission at
// the extern MIR decode chokepoint. This whole file is Trust-owned; it has no
// upstream counterpart.
//
// CONTRACT (the chokepoint's side lives in rustc_metadata's cstore arms): the
// extern `optimized_mir` / `mir_for_ctfe` decode arms `ensure_done` the
// `trust_clean_extern_readmission` query for every def its exporting crate
// lists in `trust_clean_origin_exports`, BEFORE serving the decoded body.
// This provider either RETURNS — the digest decoded whole, the exporter's
// island sources re-elaborated under the LOCAL kernel, `readmit` accepted
// every field, and every decodable body row re-passed the faithfulness gate
// locally — or FATALS with the refusal's v7/D3 note. There is no third
// outcome, and there is no partial acceptance.
//
// THE ACCEPTANCE CONTROL, verbatim from the design: "an imported certificate
// minted under a different kernel version must be re-checked or refused,
// never accepted on a matching source hash." This wave REFUSES on skew:
// `readmit` puts the kernel-version comparison first, and the local
// re-check-and-mint lane stays the seam `trust-clean-origin/src/admission.rs`
// documents (module docs, "The re-check seam") — deliberately not built here.
//
// Not behind `verification_enabled`, `-Ztrust-verify=off`, or `TRUST_NO_VERIFY`
// — the same rule as the sole local constructor (clean_origin_mir.rs). An
// unverified build may skip PROOFS; it may never run a body that disagrees
// with the declaration it was minted from.
//
// COST, stated: one `CleanIslandSession::check_all` (a full kernel
// elaboration of the exporting crate's islands) plus one `admit_lowering`
// kernel run per decodable MIR row, per imported Clean-origin def actually
// used, per session. None of it is incrementally cached (design doc §8 — a
// defeq verdict is not incrementally cacheable), and folding these runs into
// the exporter's would trade independence for compile time; do not.

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::bug;
use rustc_middle::mir::Body;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::Span;
use trust_clean_origin::VerdictDigest;

use crate::clean_origin_mir;

/// Provider of `trust_clean_extern_readmission` — BOTH halves (the query is
/// deliberately not `separate_provide_extern`; one function owns the
/// decision).
pub(crate) fn trust_clean_extern_readmission(tcx: TyCtxt<'_>, def: DefId) {
    // Local defs are gated at the sole constructor (`clean_origin_mir`),
    // which cannot return a Body without a fresh `Faithful`. Nothing to do.
    if def.is_local() {
        return;
    }
    // The registry-emptiness fast path: every ordinary dependency has an
    // empty exports list, so the total cost for ordinary builds is one
    // arena-cached root-array read per crate (and the chokepoint arms already
    // consult that list before ever invoking this query).
    if !tcx.trust_clean_origin_exports(def.krate).contains(&def.index) {
        return;
    }

    let krate = tcx.crate_name(def.krate);
    let span = tcx.def_span(def);
    // Trust: `with_no_trimmed_paths` — this string only ever reaches FATAL
    // refusal messages below, and computing it eagerly on the happy path via
    // the trimmed-paths machinery arms `must_produce_diag`, which ICEs at
    // session end when readmission SUCCEEDS and no diagnostic follows
    // (measured under compiletest's JSON diagnostics; the seventh-and-a-half
    // member of the synthetic-HIR/diagnostic family).
    let path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def));

    // ── 1. a LISTED def must carry a digest row (I7 risk R1: row-absence is
    //       how importers recognise ordinary Rust, so absence here is never
    //       "demote to ordinary" — it is a refusal) ──────────────────────────
    let Some(bytes) = tcx.trust_clean_verdict_digest(def) else {
        tcx.dcx()
            .struct_span_fatal(
                span,
                format!(
                    "`{path}` is listed as Clean-origin in `{krate}`'s metadata but \
                     carries no verdict digest — a toolchain defect or tampered \
                     metadata; the export provider fatals rather than skipping a row, \
                     so an honest `{krate}` cannot produce this"
                ),
            )
            .with_note(format!(
                "options:\n\
                 - rebuild `{krate}` with this toolchain (a fresh encode writes one \
                   digest row per listed def, enforced by an encoder assertion);\n\
                 - if the rebuild reproduces this, report it with both crate hashes — \
                   the exports list and the digest table are two independent encodings \
                   and they disagree;\n\
                 - call `{path}` from its own crate (the local lane is gated at the \
                   sole constructor and does not need the digest)."
            ))
            .emit()
    };

    // ── 2. the digest must decode whole (fail-closed on truncation, unknown
    //       versions, malformed fields, trailing bytes) ─────────────────────
    let digest = match VerdictDigest::decode(bytes) {
        Ok(digest) => digest,
        Err(refusal) => tcx
            .dcx()
            .struct_span_fatal(
                span,
                format!(
                    "the Clean-origin certificate for `{path}` in `{krate}` does not \
                     decode; refusing to import the definition"
                ),
            )
            .with_note(refusal.note())
            .emit(),
    };

    // ── 3. rebuild the EXPORTER's Clean environment LOCALLY, under the
    //       IMPORTER's kernel — the sources are transport, never authority ──
    let sources = tcx.trust_clean_island_sources(def.krate);
    let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&sources);
    if batch.is_rejected() || session.is_tainted() {
        // A refusal NAMING THE SKEW, not an ICE: the usual reason a
        // once-green island stops elaborating is that the importer links a
        // different kernel/elaborator than the one the exporter minted under,
        // and the digest carries the exporter's version string precisely so
        // this report can name both sides verbatim.
        let minted = digest.kernel_version();
        let local = trust_clean_origin::local_kernel_version();
        tcx.dcx()
            .struct_span_fatal(
                span,
                format!(
                    "the `clean {{ … }}` islands of `{krate}` no longer elaborate \
                     under this compiler's Clean kernel, so the certificate for \
                     `{decl}` cannot be re-admitted",
                    decl = digest.decl(),
                ),
            )
            .with_note(format!(
                "the certificate was minted under Clean kernel {minted}; this build \
                 links kernel {local}.\n\
                 options:\n\
                 - rebuild `{krate}` with this toolchain, so its islands and \
                   certificates are produced by the kernel that will check them;\n\
                 - if the two versions above match, this is elaborator drift under one \
                   kernel version: report it with both strings and the island sources;\n\
                 - cite the declaration from proof position instead — proof-position \
                   citation re-checks under the local kernel and does not import a \
                   certificate."
            ))
            .emit();
    }
    let Some(env) = session.environment() else {
        // Unreachable for an unrejected, untainted session; a fail-closed arm
        // rather than an unwrap, same as `readmit`'s own belt.
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: re-elaborating `{krate}`'s Clean islands reported success \
                 but produced no environment; refusing to import `{path}`. Please \
                 report it."
            ),
        );
    };

    // ── 4. readmit: every digest field against the LOCAL kernel version and
    //       the LOCALLY recomputed content. KernelVersionSkew refuses FIRST —
    //       the acceptance control — and `LocalCarrierWidthUnencodable` is
    //       `readmit`'s own fail-closed arm for a local carrier decision
    //       outside wire format v1's exact fixed widths (unbounded carriers):
    //       consumed here via the ordinary refusal surface, not duplicated. ──
    match trust_clean_origin::readmit(&digest, trust_clean_origin::local_kernel_version(), env) {
        // `Readmitted` is crate-side sealed evidence; it is deliberately
        // dropped here. This query RUNNING TO COMPLETION is the compiler-side
        // fact the chokepoint consumes.
        Ok(_readmitted) => {}
        Err(refusal) => tcx
            .dcx()
            .struct_span_fatal(
                span,
                format!(
                    "cannot import the Clean-origin certificate for `{decl}` from \
                     `{krate}`",
                    decl = refusal.decl(),
                ),
            )
            .with_note(refusal.note())
            .emit(),
    }

    // ── 5. the LOCAL re-gate — the closure of I7 risk R4: a version string is
    //       too coarse to bind the checker (two dev kernels can share one
    //       version and disagree about defeq), so a verdict is NEVER consumed
    //       from the wire. The digest is consistency evidence; the local
    //       kernel is the authority. Re-plan from the locally re-elaborated
    //       environment, re-check the ENCODED signature, and re-earn a
    //       `Faithful` against every body row this crate could decode. ───────
    let plan = match trust_clean_origin::plan_clean_origin_body(env, digest.decl()) {
        Ok(plan) => plan,
        // `NotEmittable` here means the exporting compiler emitted a shape
        // this compiler cannot re-check — per ruling v7/D2 the fix is
        // extending THIS compiler's fragment, never skipping the check. The
        // refusal's own note carries the boundary and the options.
        Err(refusal) => tcx
            .dcx()
            .struct_span_fatal(
                span,
                if refusal.is_compiler_defect() {
                    format!(
                        "internal: the Clean-origin certificate for `{decl}` from \
                         `{krate}` re-admitted, but this compiler cannot re-derive a \
                         body plan for it",
                        decl = digest.decl(),
                    )
                } else {
                    format!(
                        "the Clean-origin definition `{decl}` from `{krate}` is outside \
                         the fragment this compiler can re-check on import",
                        decl = digest.decl(),
                    )
                },
            )
            .with_note(refusal.note())
            .emit(),
    };

    // The signature every call in THIS crate was type-checked against is the
    // exporter's ENCODED `fn_sig`; a divergence from the plan's carriers is
    // the wrong binary no kernel check sees (the cross-crate mirror of the
    // sole constructor's `check_signature_agrees`).
    let fed = tcx.fn_sig(def).instantiate_identity().skip_binder();
    let expected_inputs: Vec<Ty<'_>> = plan
        .param_tys()
        .iter()
        .map(|ty| clean_origin_mir::carrier_to_rustc_ty(tcx, ty, span))
        .collect();
    let expected_output = clean_origin_mir::carrier_to_rustc_ty(tcx, plan.return_ty(), span);
    if fed.inputs() != expected_inputs.as_slice() || fed.output() != expected_output {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: refusing to import Clean-origin `{decl}` from `{krate}` — \
                 the Rust signature its metadata declares (`fn({:?}) -> {:?}`) is not \
                 the one its discharged carriers denote here (`fn({:?}) -> {:?}`). \
                 Every call in this crate was type-checked against the first and the \
                 re-gated body computes at the second, which no kernel check can \
                 catch. This is a compiler defect and nothing you write will change \
                 it. Please report it.",
                fed.inputs(),
                fed.output(),
                expected_inputs,
                expected_output,
                decl = digest.decl(),
            ),
        );
    }

    // Both decodable surfaces are re-gated (I7 risk R8: a `constness` drift
    // that flips the CTFE table choice must not route around the gate). The
    // raw `_unreadmitted_` queries exist precisely so this does not re-enter
    // the guarded arms' ensure (I7 risk R3).
    for (lane, body) in [
        ("optimized_mir", tcx.trust_clean_extern_unreadmitted_optimized_mir(def)),
        ("mir_for_ctfe", tcx.trust_clean_extern_unreadmitted_mir_for_ctfe(def)),
    ] {
        let Some(body) = body else { continue };
        let extracted = trust_mir_extract::extract_function(tcx, body);
        match trust_clean_origin::admit_lowering(env, &plan, &extracted) {
            // Same discipline as the sole constructor: the `Faithful` is the
            // permission, and it is dropped so that reaching the next line is
            // impossible without the gate having run.
            Ok(_faithful) => {}
            Err(refusal) => tcx
                .dcx()
                .struct_span_fatal(
                    span,
                    if refusal.is_compiler_defect() {
                        format!(
                            "internal: the imported `{lane}` body of Clean-origin \
                             `{decl}` from `{krate}` does not agree with its \
                             declaration under this compiler's kernel",
                            decl = digest.decl(),
                        )
                    } else {
                        format!(
                            "the imported `{lane}` body of Clean-origin `{decl}` from \
                             `{krate}` cannot be re-checked by this compiler",
                            decl = digest.decl(),
                        )
                    },
                )
                .with_note(refusal.note())
                .emit(),
        }
    }
}

/// LOCAL arm of `trust_clean_extern_unreadmitted_optimized_mir` — a bug, on
/// purpose: local bodies come from `optimized_mir`, whose sole constructor
/// cannot return a Clean-origin body without a `Faithful`. The decode-only
/// accessor exists solely for the readmission provider's extern re-gate.
pub(crate) fn local_unreadmitted_optimized_mir<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> Option<&'tcx Body<'tcx>> {
    bug!(
        "trust_clean_extern_unreadmitted_optimized_mir asked for LOCAL {def:?}: \
         this decode-only accessor's sole legitimate caller is the extern \
         readmission provider (I7 risk R2)"
    )
}

/// LOCAL arm of `trust_clean_extern_unreadmitted_mir_for_ctfe` — see the twin.
pub(crate) fn local_unreadmitted_mir_for_ctfe<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> Option<&'tcx Body<'tcx>> {
    bug!(
        "trust_clean_extern_unreadmitted_mir_for_ctfe asked for LOCAL {def:?}: \
         this decode-only accessor's sole legitimate caller is the extern \
         readmission provider (I7 risk R2)"
    )
}
