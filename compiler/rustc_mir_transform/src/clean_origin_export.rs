// Trust (I7, encode half): THE CLEAN-ORIGIN VERDICT-DIGEST EXPORT PROVIDERS.
// This whole file is Trust-owned; it has no upstream counterpart.
//
// Decision (a) of the I7 plan: the digest is a QUERY, not session state — a
// Session-registry artifact vanishes on a warm cache (see `trust_ir_of`'s
// note in rustc_middle/src/queries.rs). The `Faithful` earned in
// `build_gated_body` is deliberately dropped and STAYS dropped; this provider
// re-earns its own by re-running plan -> extract -> admit_lowering against the
// CACHED `tcx.optimized_mir(def)` — the very body the metadata encoder
// serializes. Cost, stated: a third kernel run per exporting crate (resolve
// mint + MIR gate + digest mint). Folding the runs together would trade
// independence for compile time; do not.
//
// Not behind `verification_enabled`, `-Ztrust-verify=off`, or any switch —
// same rule as the sole constructor (clean_origin_mir.rs).

use rustc_hir::def_id::{DefIndex, LocalDefId};
use rustc_middle::query::LocalCrate;
use rustc_middle::ty::TyCtxt;

use crate::clean_origin_mir;

/// Local arm of `trust_clean_verdict_digest` (extern arm: rustc_metadata).
///
/// `None` — the ordinary answer — means "not a Clean-origin def". For a
/// registry def every failure is FATAL at the registry span: a def that
/// minted and gated but cannot digest is the "environment disagrees with
/// itself" class, and returning `None` instead would fail OPEN — row-absence
/// is how importers recognise ordinary Rust (I7 risk R1).
pub(crate) fn trust_clean_verdict_digest(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<Vec<u8>> {
    let (name, span) = clean_origin_mir::clean_origin_registry_entry(tcx, def)?;

    let Some(session) = clean_origin_mir::clean_crate_environment(tcx) else {
        tcx.dcx().span_fatal(
            span,
            format!(
                "internal: refusing to export a certificate for Clean declaration `{name}` — \
                 re-checking this crate's Clean islands at metadata-encode time did not produce \
                 a usable environment. The compiler will not export a certificate it cannot put \
                 back to the kernel. Please report it."
            ),
        );
    };
    let env = session.environment().expect("an untainted session has an environment");

    // The same KernelStatus derivation the mint site uses (trust_clean_mint.rs):
    // the certification audit is what records the axiom closure the digest discloses.
    let mut facets = trust_spec_elab::FacetTable::new();
    let status = match trust_certify::clean_island::admit_certified_island_definition(
        env,
        &name,
        &mut facets,
    ) {
        Ok(admission) => admission.status().clone(),
        Err(error) => tcx.dcx().span_fatal(
            span,
            format!(
                "internal: refusing to export a certificate for Clean declaration `{name}` — \
                 the kernel re-check a mint requires did not reproduce at export time: \
                 {error}\nPlease report it."
            ),
        ),
    };

    // The body the digest is ABOUT is the body rmeta serializes: the cached gated
    // optimized_mir, read back through the same extractor the verifier uses.
    let body = tcx.optimized_mir(def);
    let extracted = trust_mir_extract::extract_function(tcx, body);

    match trust_clean_origin::mint_encoded_digest_for_export(env, &name, &status, &extracted) {
        Ok(bytes) => Some(bytes),
        Err(refusal) => tcx
            .dcx()
            .struct_span_fatal(
                span,
                if refusal.is_compiler_defect() {
                    format!(
                        "internal: refusing to export a certificate for Clean declaration \
                         `{name}` — no verdict digest could be minted for the body being \
                         serialized"
                    )
                } else {
                    format!("Clean declaration `{name}` cannot be exported for cross-crate calls")
                },
            )
            .with_note(refusal.note())
            .emit(),
    }
}

/// Local arm of `trust_clean_island_sources` — declaration TRANSPORT (I7
/// decision (e)); the importer re-elaborates under its OWN kernel.
pub(crate) fn trust_clean_island_sources(tcx: TyCtxt<'_>, LocalCrate: LocalCrate) -> Vec<String> {
    match clean_origin_mir::collect_island_sources(tcx) {
        Some(sources) => sources,
        None => {
            if clean_origin_mir::clean_origin_defs(tcx).next().is_some() {
                tcx.dcx().fatal(
                    "internal: this crate minted Clean-origin definitions but their \
                     `clean { … }` island sources could not be recovered for export; an \
                     importer could then never rebuild the environment the certificates \
                     are about. Please report it.",
                );
            }
            Vec::new()
        }
    }
}

/// Local arm of `trust_clean_origin_exports` — the registry projection.
pub(crate) fn trust_clean_origin_exports(tcx: TyCtxt<'_>, LocalCrate: LocalCrate) -> Vec<DefIndex> {
    tcx.resolutions(()).clean_origin_defs.iter().map(|&(def, _, _)| def.to_def_id().index).collect()
}
