//! Construction of MIR from HIR.

// tidy-alphabetical-start
#![feature(deref_patterns)]
#![feature(try_blocks)]
// tidy-alphabetical-end

// The `builder` module used to be named `build`, but that was causing GitHub's
// "Go to file" feature to silently ignore all files in the module, probably
// because it assumes that "build" is a build-output directory. See #134365.
mod builder;
mod check_tail_calls;
mod check_unsafety;
mod diagnostics;
pub mod thir;
// Trust (typeck-moonshot P1, Phase 3): the CHECKED witness-replay hook body.
mod trust_replay;

use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::Session;
use std::path::PathBuf;

pub fn provide(providers: &mut Providers) {
    providers.queries.check_match = thir::pattern::check_match;
    providers.queries.lit_to_const = thir::constant::lit_to_const;
    providers.queries.closure_saved_names_of_captured_variables =
        builder::closure_saved_names_of_captured_variables;
    providers.queries.check_unsafety = check_unsafety::check_unsafety;
    providers.queries.check_tail_calls = check_tail_calls::check_tail_calls;
    providers.queries.thir_body = thir::cx::thir_body;
    // Trust (B): the direct THIR -> trust-ir lowering as a real query, so the Module survives an
    // incremental replay instead of existing only while `mir_built` happens to execute.
    providers.queries.trust_ir_of = trust_thir_lower::trust_ir_of;
    providers.hooks.build_mir_inner_impl = builder::build_mir_inner_impl;
    // Trust (typeck-moonshot P1, Phase 3): CHECKED witness-replay of the `typeck`
    // query. FAIL-SAFE — the hook returns `None` on any miss / decode / reintern /
    // check failure and the caller falls through to real typeck.
    providers.hooks.trust_witness_try_replay = trust_replay::replay_hook;
    providers.hooks.trust_witness_parity_check = trust_replay::parity_check_hook;
}

/// Prepare a requested direct-TrustIR artifact transaction before any input
/// I/O. Continuing after failure could leave a prior commit marker looking
/// current, so preparation errors terminate compilation.
pub fn trust_ir_prepare_artifact_publication(sess: &Session, crate_name: &str) {
    if let Err(error) =
        trust_thir_lower::crate_module::prepare_artifact_publication(sess, crate_name)
    {
        sess.dcx().fatal(format!(
            "trust-ir-lower artifact target preparation failed for `{crate_name}`: {error}"
        ));
    }
}

/// Opaque pre-input ownership of one direct-TrustIR artifact writer lock.
pub struct TrustIrArtifactPublicationLease(
    trust_thir_lower::crate_module::PreparedArtifactPublication,
);

/// Acquire and invalidate an explicit target before compiler input is selected.
/// The returned lease must be installed in the eventual Session or retained
/// until the invocation exits.
pub fn trust_ir_acquire_artifact_publication_target(
    directory: PathBuf,
    crate_name: &str,
) -> Result<TrustIrArtifactPublicationLease, String> {
    trust_thir_lower::crate_module::acquire_artifact_publication_target(directory, crate_name)
        .map(TrustIrArtifactPublicationLease)
}

/// Transfer the exact pre-input transaction into its compiler Session.
pub fn trust_ir_install_artifact_publication(
    sess: &Session,
    lease: TrustIrArtifactPublicationLease,
) {
    if let Err(error) = trust_thir_lower::crate_module::install_artifact_publication(sess, lease.0)
    {
        sess.dcx().fatal(format!("trust-ir-lower artifact lease installation failed: {error}"));
    }
}

// Trust: P1 Phase-0 — crate-level trust-ir Module assembly finalizer. Exposed here (this crate
// already links trust-thir-lower for the per-body `-Z trust-ir-lower` hook in `builder`) so
// rustc_interface's `analysis` seam can invoke it without a new crate edge. Populated whenever
// `-Z trust-ir-lower` ran (the per-body registry is now unconditional under the flag); the
// artifact write alone additionally requires `-Ztrust-dump=ir:<dir>`. Structural lowering and
// seam verdicts remain debug/artifact output, while malformed or semantically unresolvable
// temporal annotations are a frontend contract violation and fail compilation even without a
// dump. The finalizer also returns a typed direct-obligation capability marker; today it is
// structural/parity-only and grants no proof authority or native-request capability.
pub fn trust_ir_crate_finalize(tcx: TyCtxt<'_>) {
    // rustc_interface prepared and invalidated the explicit artifact identity
    // before input I/O. The finalizer consumes that transaction (or prepares it
    // as a custom-driver fallback) before it forces/replays `mir_built`.
    let summary = trust_thir_lower::crate_module::finalize_and_dump(tcx);
    if !summary.errors.is_empty() {
        tcx.dcx().fatal(format!(
            "trust-ir-lower semantic finalization failed: {}",
            summary.errors.join("; ")
        ));
    }
    tracing::debug!(
        direct_obligation_capability = summary.direct_obligations.marker(),
        proof_authority = summary.direct_obligations.grants_proof_authority(),
        native_verification_requests =
            summary.direct_obligations.emits_native_verification_requests(),
        "trust-ir-lower: direct obligation capability"
    );
    // Trust (B9-A): the crate-seam differential verdicts for call-bearing clean bodies. Re-emit
    // each as the standard `trust-ir-lower: differential` event so the scorecard classifies it
    // exactly like a hook-time verdict. EXPLICIT target: this module's tracing path is
    // `rustc_mir_build`, but the scorecard's event filter keys on `rustc_mir_build::builder` — the
    // reconstructed `LocalDefId` renders the identical `DefId(0:N ~ path)` spelling because the
    // `tcx` TLS is live inside `analysis`.
    for v in &summary.seam {
        let def = rustc_span::def_id::LocalDefId {
            local_def_index: rustc_span::def_id::DefIndex::from_u32(v.def_index),
        };
        tracing::debug!(
            target: "rustc_mir_build::builder",
            ?def,
            equal = v.equal,
            samples = v.samples,
            mode = ?v.mode,
            note = v.note.as_str(),
            "trust-ir-lower: differential"
        );
    }
    if let Some(summary) = summary.dump {
        if !summary.errors.is_empty() {
            tcx.dcx().fatal(format!(
                "trust-ir-lower artifact publication failed for `{}`: {}",
                summary.dir.display(),
                summary.errors.join("; ")
            ));
        }
        tracing::debug!(
            dir = %summary.dir.display(),
            bodies = summary.bodies,
            lowered = summary.lowered,
            spliced = summary.spliced,
            declarations = summary.declarations,
            errors = ?summary.errors,
            "trust-ir-lower: crate module dumped"
        );
    }
}

// Trust (typeck-moonshot P1, Phase 0): drain the recorded mintable typeck roots
// and commit the per-crate witness store. Exposed here (this crate takes the
// `trust-witness` crate edge) so rustc_interface's `analysis` seam can invoke it
// without a new edge, mirroring `trust_ir_crate_finalize`. The commit itself
// re-filters roots by the enabled-set predicate and encodability. Inert unless
// `-Z trust-witness=mint:<dir>` populated the registry.
pub fn trust_witness_crate_finalize(tcx: TyCtxt<'_>) {
    let Some(dir) = tcx.trust_witness_mint_dir() else { return };
    let roots = tcx.trust_witness_drain_minted();
    if let Some(n) = trust_witness::commit(tcx, &dir, &roots, tcx.trust_witness_precise()) {
        tracing::debug!(
            dir = %dir.display(),
            witnesses = n,
            roots = roots.len(),
            "trust-witness: crate store committed"
        );
    }
}

#[cfg(test)]
mod tests;
