//! Construction of MIR from HIR.

// tidy-alphabetical-start
#![feature(deref_patterns)]
#![feature(try_blocks)]
// tidy-alphabetical-end

// The `builder` module used to be named `build`, but that was causing GitHub's
// "Go to file" feature to silently ignore all files in the module, probably
// because it assumes that "build" is a build-output directory. See #134365.
pub mod builder;
mod check_tail_calls;
mod check_unsafety;
mod diagnostics;
pub mod thir;
// Trust (typeck-moonshot P1, Phase 3): the CHECKED witness-replay hook body.
mod trust_replay;

use std::path::PathBuf;

use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::Session;
pub use thir::constant::lit_to_mir_constant;

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
    // Trust: step 2 increment 6 (6.2) — the producer builds the rmeta entries
    // (`trust_thir_lower::rmeta_entry`); rustc_metadata only carries their bytes.
    providers.queries.trust_ir_local_entries = trust_thir_lower::rmeta_entry::local_entries;
    providers.queries.trust_ir_entry = |tcx, def| match tcx
        .trust_ir_local_entries(())
        .entries
        .get(&def.local_def_index.as_u32())
    {
        Some(Ok(blob)) => Some(blob.clone()),
        _ => None,
    };
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
/// Trust (wall A, instance-flip probe): re-exported for rustc_interface's
/// post-codegen seam, mirroring [`trust_ir_crate_finalize`] — this crate already
/// links trust-thir-lower, so no new crate edge. A no-op unless
/// `-Ztrust-instance-flip-probe` is set (see
/// `trust_thir_lower::instance_probe` for what it measures).
pub fn trust_instance_probe_finalize(tcx: TyCtxt<'_>) {
    trust_thir_lower::instance_probe::finalize_probe(tcx);
}

/// Trust (2026-09-24): whether `-Ztrust-ir-lower=strict`'s COVERAGE arms — "the producer
/// could not fully lower this body" and "this body was REFUSED at crate assembly" — apply
/// to `def`. They apply wherever strict is honoured
/// ([`Session::trust_ir_lower_strict`]) except to the test-harness items rustc
/// synthesizes: per test, the `TestDescAndFn` descriptor const and the runner closure
/// inside it (`rustc_builtin_macros::test`), and the harness `main`
/// (`rustc_builtin_macros::test_harness`).
///
/// Trust (CB4, 2026-09-28): WHICH items those are is decided by
/// [`rustc_middle::middle::trust_test_harness::test_harness_synthesized_item`], from the
/// expansion that produced each item's own span. This predicate used to read
/// "`is_test_crate()` and the typeck root carries `#[rustc_test_marker]`", which is
/// forgeable (MEASURED): a user-written `#[rustc_test_marker]` const, and every
/// `#[test_case]` item (the builtin pushes the marker onto the user's OWN fn/const/static),
/// silenced this check over code the author wrote — a `#[test_case]` fn's whole body was
/// exempt. It also did not cover the harness `main`, whose body is equally synthesized.
///
/// Strict's coverage arm is a ratchet over the PROGRAM's bodies — "the unit that grows is
/// the set of files strict is run over" (`builder::build_mir_inner_impl`). The harness
/// items are in no file: the author of a test crate never wrote them and cannot change
/// them. Measured on a one-test crate (`--test -Ztrust-verify=on -Ztrust-ir-lower=strict`):
/// exactly those two bodies failed (`Adt(unsupported field)`/`EnumCtor(fat field seed)` on
/// the descriptor, `Call(unsupported arg)` on the closure), so no strict crate with a
/// `#[test]` could build its tests however far the producer's coverage of the author's
/// own code went. The `#[test]` function itself stays in scope, and so do the
/// DISAGREEMENT arms: a harness body whose trust-ir means something other than its MIR
/// is still an error.
pub(crate) fn trust_ir_strict_coverage_applies(
    tcx: TyCtxt<'_>,
    def: rustc_span::def_id::LocalDefId,
) -> bool {
    // Trust (CB4): provenance, not the forgeable attribute. See the doc comment.
    tcx.sess.trust_ir_lower_strict()
        && rustc_middle::middle::trust_test_harness::test_harness_synthesized_item(tcx, def)
            .is_none()
}

/// Trust: expose emitted Clean callee identities without a mir-transform dependency.
/// The caller demands their gated MIR only after this Session registry borrow ends.
pub fn trust_ir_referenced_clean_origin_defs(
    tcx: TyCtxt<'_>,
) -> Vec<rustc_span::def_id::LocalDefId> {
    trust_thir_lower::crate_module::referenced_clean_origin_defs(tcx)
}

// Trust (IR-1, docs/design/2026-08-27-two-language-direct-to-trust-ir.md §3):
// `clean_origin` is the Clean-origin trust-ir collection from
// `rustc_mir_transform::clean_origin_ir` — threaded through here because this
// crate cannot depend on rustc_mir_transform; `rustc_interface` (which depends
// on both) performs the hand-off. `None` = verification off, the collection
// deliberately did not run.
pub fn trust_ir_crate_finalize(
    tcx: TyCtxt<'_>,
    clean_origin: Option<Vec<trust_thir_lower::clean_origin_join::CleanOriginIrOutcome>>,
) {
    // rustc_interface prepared and invalidated the explicit artifact identity
    // before input I/O. The finalizer consumes that transaction (or prepares it
    // as a custom-driver fallback) before it forces/replays `mir_built`.
    let mut summary = trust_thir_lower::crate_module::finalize_and_dump(tcx, clean_origin);
    // Trust (WS5.5, STAGED): the zero-authority contract-carry shadow. Inert unless
    // `TRUST_CONTRACT_CARRY_SHADOW` names a directory; it installs the staged contract carry on
    // a CLONE of the published module, judges the clone, writes one JSON sidecar, and changes no
    // artifact, no verdict and nothing in `summary` (see `trust_thir_lower::contract_carry_shadow`).
    trust_thir_lower::contract_carry_shadow::run(tcx);
    // Trust (2026-09-17): the finalization ROUTING probe. `-Ztrust-ir-lower-mutate-finalization`
    // appends the real validator's refusals of a SEPARATE one-declaration module built to
    // carry the exact encoding v41 refuses, so the advisory/fail-closed routing below is
    // exercisable from a ui fixture without riding a live producer gap (four such gaps
    // closed under `advisory_invalid_module_is_a_warning.rs` in two days). Test-only,
    // `EvidenceControl`: it can only ADD an error, never remove one, and the crate's own
    // module is untouched — see `trust_thir_lower::finalization_probe`.
    let mut errors = std::mem::take(&mut summary.errors);
    if tcx.sess.opts.unstable_opts.trust_ir_lower_mutate_finalization {
        errors.extend(trust_thir_lower::finalization_probe::manufactured_validator_refusals());
    }
    if !errors.is_empty() {
        // Route on the CLAIM, not on the policy alone: `Session::trust_proof_claimed`
        // is verification on AND a fail-closed policy. A producer-side
        // COMPLETENESS failure is a hard error only there — exactly as the vcgen
        // per-function budget overrun does (`d9d9d675e3`) — and a warning in
        // both lanes that claim nothing: `-Ztrust-policy=advisory`, and
        // `-Ztrust-verify=off` with the direct frontend switched on.
        //
        // WHAT THIS FAILURE IS. `finalize_and_dump` validates the crate-level
        // Trust-IR module. An invalid module is a PRODUCER defect, and its
        // consequence is that the native lane cannot use the bundle — every
        // obligation in the crate loses its native proof route and falls back to
        // whatever else can decide it. That is a loss of COVERAGE, never a loss
        // of soundness: an invalid module proves nothing, so nothing unproved
        // can be smuggled through it.
        //
        // WHY ADVISORY MUST NOT DIE ON IT. Advisory's entire contract is "the
        // crate compiles while the prover is improved, and every obligation is
        // reported". A crate-fatal producer defect breaks that contract in the
        // worst way: the user gets NO census at all — not a partial one — for a
        // defect in the compiler rather than in their code. MEASURED 2026-09-07:
        // `first-party/ty`'s `tla-im` compiled 663 functions, emitted 610
        // warnings, and then threw all of it away on one
        //
        //   CallArgTypeMismatch { block: 1, callee: "nodes::rrb::Size::size",
        //   arg_index: 0, expected: "ptr", actual: "()" } in `Node::<A>::size`
        //
        // raised by the wave-EL opaque-lane collapse handing a `Ty::Unit`
        // receiver to a call whose declaration says `ptr`. The body should have
        // declined; instead the whole crate did. `tests/ui/trust/
        // advisory_invalid_module_is_a_warning.rs` pins the shape.
        //
        // WHY THE OFF LANE MUST NOT DIE ON IT EITHER. `-Ztrust-verify=off` is the
        // master off-switch: no obligation is generated and no claim is made, so
        // there is nothing for an invalid module to invalidate. The frontend
        // runs there only because a config asked for it (`-Ztrust-ir-lower=on`
        // or `strict` is the compat lane's diagnostic opt-in), and what it finds
        // is information, never a verdict. MEASURED 2026-09-22: ay's everyday
        // lane (`targo --unverified`, with the required `-Ztrust-ir-lower=strict`
        // on every unit) died in `autocfg 1.5.1` and `cc 1.2.64` on
        // `StructLayoutInconsistent { reason: "fields overlap" }` — a producer
        // defect in two registry crates the user cannot edit, on a compile that
        // verifies nothing. The routing read `trust_policy.is_advisory()` alone,
        // so the off lane inherited the DEFAULT policy's fatal.
        // `tests/ui/trust/verify_off_invalid_module_is_a_warning.rs` pins it.
        // (The producer gap itself was three defects in trust-thir-lower, since
        // fixed; `trust_ir_niche_descriptor_deep_payload_chain.rs` pins that one.)
        //
        // The strict/certify/memory-safe lanes under verification keep the hard
        // error verbatim: there, a claim is being made, and a claim resting on a
        // module the validator rejects must not be made at all.
        let message = format!("trust-ir-lower semantic finalization failed: {}", errors.join("; "));
        if tcx.sess.trust_proof_claimed() {
            tcx.dcx().fatal(message);
        } else {
            tcx.dcx()
                .struct_warn(message)
                .with_note(
                    "this is a PRODUCER defect, not a finding about your code: the crate-level \
                     Trust-IR module did not validate, so the native verification lane has no \
                     bundle to use and every obligation in this crate loses that proof route",
                )
                .with_note(
                    "a lane that claims no proof reports it and continues: survey mode \
                     (`-Z trust-policy=advisory`) and the off-switch (`-Z trust-verify=off`); the \
                     strict, certify and memory-safe lanes keep it a hard error, because a proof \
                     claim must never rest on a module the validator rejects",
                )
                .emit();
        }
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
        // Trust (A2-D): the THIRD disagreement channel. A DEFERRED (clean + call-bearing) body
        // gets its one real interpretation verdict HERE, not at the per-body hook, so the hook's
        // strict disagreement arm structurally cannot see it. Under `-Ztrust-ir-lower=strict` a
        // seam `MirOracle` verdict is the same error for the same reason: the THIR-derived
        // trust-ir the trust-ir codegen frontend would emit from means something other than the
        // MIR the rest of the compiler uses. `NotRun` (every fail-closed seam gate) and `Agreed`
        // are untouched.
        if tcx.sess.trust_ir_lower_strict()
            && v.mode == trust_thir_lower::differential::DiffMode::MirOracle
        {
            tcx.dcx().span_err(
                tcx.def_span(def),
                format!(
                    "-Ztrust-ir-lower=strict: THIR-derived trust-ir DISAGREES with the built MIR \
                     for this body at the crate-link seam after {} sampled input(s): {}",
                    v.samples, v.note
                ),
            );
        }
    }
    // Trust: the FOURTH disagreement channel, and it closes a contract violation this
    // lane introduced. `54ea2954cd` moved the unsignable-Rust-ABI refusal from "fail the
    // whole crate" to "refuse the minting BODY" — the right change — but it moved the
    // refusal LATER, into the crate-assembly re-splice fixpoint, while strict's only
    // per-body arm (this crate's builder) reads the `mir_built`-time report. Measured on
    // `trust_ir_lower_format_args_residue_still_withdraws.rs`: the sidecar said
    // `lowered: false, spliced: false` with an `UnsignableRustAbiDeclaration` row and
    // `-Ztrust-ir-lower=strict` still exited 0, against the flag's own help text ("a body
    // the producer cannot fully lower [is] a compile error instead of a coverage-only
    // skip"). Reported at the body's own span, with the producer's v7/D3 options text
    // verbatim rather than a paraphrase that can drift from it.
    //
    // Shaped exactly like the seam loop above and placed beside it on purpose: both carry
    // a verdict that CANNOT be known until the whole crate is assembled, and both
    // reconstruct the `LocalDefId` from a `def_index` the producer recorded.
    for refused in &summary.refused_bodies {
        let def = rustc_span::def_id::LocalDefId {
            local_def_index: rustc_span::def_id::DefIndex::from_u32(refused.def_index),
        };
        tracing::debug!(
            target: "rustc_mir_build::builder",
            ?def,
            reason = refused.reason.as_str(),
            "trust-ir-lower: body refused at crate assembly"
        );
        // Trust: the coverage arm, scoped by `trust_ir_strict_coverage_applies`.
        if trust_ir_strict_coverage_applies(tcx, def) {
            tcx.dcx().span_err(
                tcx.def_span(def),
                format!(
                    "-Ztrust-ir-lower=strict: this body was REFUSED at crate assembly, so the \
                     producer did not fully lower it: {}",
                    refused.reason
                ),
            );
        }
    }
    // Trust (effect conservation, D28, 2026-10-01): judge every body the mainline lowering
    // recorded against rustc's own built MIR — calls, stores through escaping pointers, drops,
    // asm — and tag every value abstraction. The check lives in a NEW file
    // (`trust_thir_lower::effect_conservation`) and runs here, right after the frozen assembler,
    // because it needs the final published module and codegen handoff: it withdraws every
    // refused body from the handoff (F1 codegen), installs the verdicts the crate-module lane
    // and channel C read, and writes `<crate>.effect-conservation.json` beside a dump. Strict is
    // this crate's policy, so its arm is here: a CLEAN body (strict's tag arm passed it) whose
    // trust-ir is not the program is an error, named by every tag. The event rides the
    // scorecard's filter target like the seam loop's above.
    // Trust (2026-10-18): at `info`, so a stage built with `rust.debug-logging = false` still
    // emits it; its run-make reader (trust-ir-template-encode) read nothing on such a stage.
    let conservation = trust_thir_lower::effect_conservation::finalize(tcx);
    for body in &conservation.bodies {
        tracing::info!(
            target: "rustc_mir_build::builder",
            def = ?body.def,
            conserved = body.tags.is_empty(),
            clean = body.clean,
            spliced = body.spliced,
            classes = %body.classes.join("+"),
            equivalences = ?body.equivalences,
            detail = %trust_thir_lower::effect_conservation::render_tags(&body.tags),
            "trust-ir-lower: effect conservation"
        );
        if !body.tags.is_empty() && body.clean && trust_ir_strict_coverage_applies(tcx, body.def) {
            tcx.dcx().span_err(
                tcx.def_span(body.def),
                format!(
                    "-Ztrust-ir-lower=strict: the direct trust-ir of this body is not the \
                     program: the effect-conservation check refused it against the built MIR \
                     ({})",
                    trust_thir_lower::effect_conservation::render_tags(&body.tags)
                ),
            );
        }
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
            "trust-witness: crate store finalized"
        );
    }
}

#[cfg(test)]
mod tests;
