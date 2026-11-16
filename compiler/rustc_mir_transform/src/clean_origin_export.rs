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

// Trust (CB3): `DefKind` for the island marker's def-kind precheck.
use rustc_hir::def::DefKind;
// Trust (cross-crate proof citation, increment 2): `LOCAL_CRATE` for the
// transport manifest's crate identity.
use rustc_hir::def_id::{DefIndex, LOCAL_CRATE, LocalDefId};
use rustc_middle::middle::trust_clean_proof::TrustCleanProofManifest;
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
///
/// TWO KNOWN BOUNDARIES ARE NOT FAILURES (2026-09-16), and they answer with a
/// ROW, never with `None`: a def the local gate admitted by an evidence form
/// the certificate wire has no tag for (well-founded and per-equation
/// recursion), and a def that calls a Rust `fn` of this crate. Both used to be
/// fatal HERE, which made the crate that merely DEFINED one — in a private
/// module, used only internally or only in proof position — unbuildable as a
/// library (the encoder demands this query for EVERY registry def, whatever
/// its visibility). They now export a `trust_clean_origin::NonExportableNotice`
/// in the certificate's place: refusal-only bytes with their own magic, which
/// `VerdictDigest::decode` rejects and which the importer's readmission
/// provider turns into a v7/D3 fatal at the first attempt to call, const-
/// evaluate or instantiate the def from another crate. No evidence crosses,
/// no wire tag was added, and the R1 row-presence contract is unchanged.
pub(crate) fn trust_clean_verdict_digest(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<Vec<u8>> {
    let (name, span) = clean_origin_mir::clean_origin_registry_entry(tcx, def)?;
    let declaration = clean_origin_mir::clean_source_name(tcx, &name, span);

    let Some(env) = clean_origin_mir::clean_crate_environment(tcx) else {
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
    let env = &*env;

    // The same KernelStatus derivation the mint site uses (trust_clean_mint.rs):
    // the certification audit is what records the axiom closure the digest discloses.
    let mut facets = trust_spec_elab::FacetTable::new();
    let status = match trust_certify::clean_island::admit_certified_island_definition_for_name(
        env,
        &declaration,
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

    // Trust (W5, Lean-calls-Rust): a def that calls a sibling Rust `fn` is NOT
    // exportable yet — an importer re-plans in a session that has no callee
    // table (its `ResolverGlobalCtxt` carries THIS crate's callees, not the
    // exporter's), so no certificate could be re-admitted there; the
    // cross-crate wire for callee tables is design increment 6. Decided on the
    // callee-aware plan, so the notice names the real boundary rather than
    // "outside the fragment".
    //
    // NOT fatal (2026-09-16): refusing here failed the DEFINING crate, so the
    // whole Lean->Rust edge was bin-crate-only. The def stays callable in this
    // crate — the sole constructor already gated the body the encoder
    // serialized (`encode_mir` runs before this query and forces
    // `optimized_mir`) — and the row says no certificate crosses. The refusal,
    // with the reason and the options (ruling v7/D3), moved to where a cross-
    // crate call is actually attempted: `clean_origin_import`. No `Faithful` is
    // re-earned on this arm because nothing is being certified.
    if let Ok(plan) = trust_clean_origin::plan_clean_origin_body_with_rust_callees_for_name(
        env,
        &declaration,
        &clean_origin_mir::rust_callee_table(tcx),
    ) && let Some(notice) = trust_clean_origin::NonExportableNotice::for_rust_call_chain(&plan)
    {
        return Some(notice.encode());
    }

    // The body the digest is ABOUT is the body rmeta serializes: the cached gated
    // optimized_mir, read back through the same extractor the verifier uses.
    let body = tcx.optimized_mir(def);
    let extracted = trust_mir_extract::extract_function(tcx, body);

    let refusal = match trust_clean_origin::mint_encoded_digest_for_export_for_name(
        env,
        &declaration,
        &status,
        &extracted,
    ) {
        Ok(bytes) => return Some(bytes),
        Err(refusal) => refusal,
    };

    // Trust (2026-09-16): the ONE export refusal that is a known format
    // boundary rather than a failure — the seam re-earned a fresh `Faithful`
    // against the body being serialized and only its METHOD has no wire
    // spelling. `non_exportable_notice` is `Some` for exactly that variant;
    // every other refusal (a mistranslated body, a lost declaration, an
    // unaudited closure …) stays fatal below.
    if let Some(notice) = refusal.non_exportable_notice() {
        return Some(notice.encode());
    }

    tcx.dcx()
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
        .emit_fatal()
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

/// Trust (cross-crate PROOF-position citation, increment 2): local arm of
/// `trust_clean_proof_manifest` — the transport manifest for the island
/// sources `trust_clean_island_sources` returns.
///
/// `None` for a crate with no `clean { … }` island, which is every ordinary
/// crate. `Some` whenever the crate HAS islands, whether or not it minted
/// anything callable: a pure spec crate mints nothing by construction and is
/// exactly the shape cross-crate citation exists for.
///
/// It carries no authority and grants nothing. The kernel version is a string
/// the consumer COMPARES against its own (and refuses on, before elaborating
/// anything); the digest is a string the consumer RECOMPUTES over the bytes
/// that arrived (and refuses on). The sources themselves are then
/// re-elaborated and kernel-checked under the consumer's own kernel, exactly
/// as the CALL lane's readmission requires — never accepted on a matching
/// hash.
///
/// The digest is taken over the SAME vector `trust_clean_island_sources`
/// returns, through the one shared definition in
/// `trust_certify::clean_island::extern_proof_source_digest` that the
/// consuming side also uses. There is deliberately no second spelling of it
/// here: a digest computed by two spellings of one idea is a digest that
/// disagrees at the first refactor.
pub(crate) fn trust_clean_proof_manifest(
    tcx: TyCtxt<'_>,
    LocalCrate: LocalCrate,
) -> Option<TrustCleanProofManifest> {
    let sources = tcx.trust_clean_island_sources(LOCAL_CRATE);
    if sources.is_empty() {
        return None;
    }
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    let kernel_version = clean_kernel::VERSION.to_string();
    let source_digest = trust_certify::clean_island::extern_proof_source_digest(
        crate_name.as_str(),
        tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        &kernel_version,
        sources,
    )
    .unwrap_or_else(|error| {
        // The inputs are this crate's own island bytes and two strings, so a
        // failure here is not something a source file can cause. Fail closed
        // and loudly rather than transporting sources no consumer can
        // identify: a silent `None` would make the crate look island-free.
        tcx.dcx().fatal(format!(
            "internal: this crate's `clean {{ … }}` island sources could not be bound into a \
             Clean proof transport manifest ({error}); a dependent crate could then not tell \
             which bytes it re-elaborated. Please report it."
        ))
    });
    Some(TrustCleanProofManifest { kernel_version, source_digest })
}

/// Local arm of `trust_clean_origin_exports` — the registry projection.
pub(crate) fn trust_clean_origin_exports(tcx: TyCtxt<'_>, LocalCrate: LocalCrate) -> Vec<DefIndex> {
    tcx.resolutions(()).clean_origin_defs.iter().map(|&(def, _, _)| def.to_def_id().index).collect()
}

/// Trust (CB3, 2026-09-28): local arm of `trust_def_is_clean_island` — is this
/// `DefKind::GlobalAsm` def a `clean { … }` / `clean mod` island rather than a
/// real `global_asm!`? (Extern arm: the rmeta `trust_clean_island_item` table,
/// which the encoder fills from THIS answer.)
///
/// The def kind is checked FIRST, so the HIR lookup only ever runs on an item
/// def: a `DefKind::GlobalAsm` def is always a HIR `Item` (either
/// `ItemKind::GlobalAsm` or `ItemKind::CleanIsland`), while an arbitrary local
/// def — a synthetic coroutine body, an RPITIT — may have no HIR node at all.
/// Every def of any other kind answers `false`.
pub(crate) fn trust_def_is_clean_island(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    if tcx.def_kind(def) != DefKind::GlobalAsm {
        return false;
    }
    let rustc_hir::Node::Item(item) = tcx.hir_node_by_def_id(def) else { return false };
    matches!(item.kind, rustc_hir::ItemKind::CleanIsland { .. })
}
