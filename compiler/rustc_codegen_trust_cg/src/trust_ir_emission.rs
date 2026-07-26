//! trust_ir_emission: feature-gated MIR-COMPATIBILITY OBSERVABILITY ADAPTER.
//!
//! This module is a *pure composition* of two already-proven passes:
//!
//! 1. `trust_mir_extract::extract_function` (MIR -> `VerifiableFunction`),
//!    which the trust-cg backend already runs during `codegen_crate`, and
//! 2. `trust_ir_bridge::lower_mir_compat_functions_to_trust_ir`
//!    (`&[VerifiableFunction]` -> `trust_ir::Module`).
//!
//! It is not the Rust source frontend and does not produce the shared
//! Rust/Clean source module. It introduces **no new lowering**: the codegen unit's
//! `VerifiableFunction`s are captured at the existing extraction site and
//! forwarded, as a slice, to the multi-function bridge entry point (which
//! resolves direct `Call` targets across the bundle). The result is a single
//! `trust_ir::Module` for the codegen unit.
//!
//! # Drop-in safety
//!
//! Everything in this module is reachable only behind the off-by-default
//! `trust-ir-emission` cargo feature. With the feature OFF the module is not
//! compiled into the backend dylib at all (`#[cfg(feature = ...)]` on the
//! `mod` declaration), the optional `trust-ir` / `serde_json` dependencies are
//! not linked, and the LLVM / default codegen paths — and the trust-cg object
//! emission path — are byte-for-byte unchanged. The adapter only *produces*
//! a Module and logs about it; it never feeds back into emission.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::ty::TyCtxt;
use trust_ir::Module;
use trust_types::VerifiableFunction;

/// Reasons the emission adapter can fail.
///
/// These are *adapter-level* failures (bridge lowering errored, or the
/// produced Module's target triple disagreed with the session target). They
/// are surfaced via logging only — the adapter never changes codegen output —
/// so in release builds a failure is observed, not fatal.
#[derive(Debug)]
pub(crate) enum EmitError {
    /// `trust_ir_bridge::lower_mir_compat_functions_to_trust_ir` returned an error.
    Bridge(trust_ir_bridge::BridgeError),
    /// The emitted Module carries a target triple that disagrees with the
    /// compilation session's target. Carries `(module_triple, session_triple)`.
    TargetTripleMismatch { module: String, session: String },
}

impl std::fmt::Display for EmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitError::Bridge(e) => write!(f, "trust-ir bridge lowering failed: {e}"),
            EmitError::TargetTripleMismatch { module, session } => write!(
                f,
                "trust-ir Module target triple `{module}` does not match session target `{session}`"
            ),
        }
    }
}

impl std::error::Error for EmitError {}

/// Compose the two proven passes into a single `trust_ir::Module` for a codegen
/// unit.
///
/// `funcs` are the `VerifiableFunction`s the backend already extracted from the
/// CGU's MIR (with direct-call name overrides applied); this adapter does NOT
/// re-extract. `cgu_name` becomes the Module name.
///
/// # Target-triple sanity check
///
/// The bridge's multi-function entry (`Module::new`) produces a
/// target-*independent* Module: `target_info` is left `None`. That is the
/// expected shape today, and is NOT an error — a `None` triple is compatible
/// with any session. We only fail (`EmitError::TargetTripleMismatch`) when the
/// Module *does* carry a concrete triple and it disagrees with
/// `tcx.sess.target`. This keeps the check a true sanity guard against a future
/// bridge that stamps the triple, without manufacturing spurious failures for
/// the current target-independent output.
pub(crate) fn emit_trust_ir_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    cgu_name: &str,
    funcs: &[VerifiableFunction],
) -> Result<Module, EmitError> {
    let module = trust_ir_bridge::lower_mir_compat_functions_to_trust_ir(cgu_name, funcs)
        .map_err(EmitError::Bridge)?;

    // Sanity: if the bridge ever stamps a concrete target triple, it must agree
    // with the session target. `None` (today's shape) is target-independent and
    // always acceptable.
    if let Some(target_info) = &module.target_info {
        let session_triple = tcx.sess.target.llvm_target.as_ref();
        if target_info.triple != session_triple {
            return Err(EmitError::TargetTripleMismatch {
                module: target_info.triple.clone(),
                session: session_triple.to_string(),
            });
        }
    }

    Ok(module)
}

/// Fidelity oracle for the emitted Module (feature-gated, log-only).
///
/// Validates the composition two ways and logs any mismatch — it never panics
/// in release and never alters codegen:
///
/// 1. **Determinism / standalone equality.** Re-run the bridge standalone over
///    the same `funcs` and assert the Module equals the one we emitted. The
///    bridge is a pure function of its inputs, so any inequality signals
///    nondeterminism or accidental state leakage in the adapter.
/// 2. **Serde roundtrip.** Serialize the Module to JSON and back; the decoded
///    Module must equal the original (`Module: PartialEq`). This mirrors the
///    `trust-ir-conformance` roundtrip corpus and confirms the emitted Module
///    is a faithful, serializable artifact.
///
/// In debug builds a mismatch additionally trips a `debug_assert!` so it is
/// caught in tests; in release it is logged at `error` level only.
pub(crate) fn validate_emitted_module(
    cgu_name: &str,
    funcs: &[VerifiableFunction],
    emitted: &Module,
) {
    // (1) Fidelity oracle: bridge is deterministic, so a standalone re-run must
    // reproduce the emitted Module exactly.
    match trust_ir_bridge::lower_mir_compat_functions_to_trust_ir(cgu_name, funcs) {
        Ok(standalone) => {
            let equal = &standalone == emitted;
            if !equal {
                tracing::error!(
                    cgu = %cgu_name,
                    "[trust_cg] trust-ir emission FIDELITY mismatch: emitted Module \
                     != standalone bridge Module for identical inputs"
                );
            }
            debug_assert!(
                equal,
                "trust-ir emission fidelity: emitted Module diverged from standalone \
                 bridge Module for `{cgu_name}`"
            );
        }
        Err(e) => {
            tracing::error!(
                cgu = %cgu_name,
                error = %e,
                "[trust_cg] trust-ir emission fidelity re-run errored (the bridge \
                 succeeded once but failed on re-run — nondeterministic lowering)"
            );
        }
    }

    // (2) Serde roundtrip (serialize -> deserialize -> equal).
    match serde_json::to_string(emitted) {
        Ok(json) => match serde_json::from_str::<Module>(&json) {
            Ok(decoded) => {
                let equal = &decoded == emitted;
                if !equal {
                    tracing::error!(
                        cgu = %cgu_name,
                        "[trust_cg] trust-ir emission ROUNDTRIP mismatch: \
                         serde_json decode != original Module"
                    );
                }
                debug_assert!(
                    equal,
                    "trust-ir emission roundtrip: decoded Module diverged from original \
                     for `{cgu_name}`"
                );
            }
            Err(e) => tracing::error!(
                cgu = %cgu_name,
                error = %e,
                "[trust_cg] trust-ir emission roundtrip: serde_json decode failed"
            ),
        },
        Err(e) => tracing::error!(
            cgu = %cgu_name,
            error = %e,
            "[trust_cg] trust-ir emission roundtrip: serde_json encode failed"
        ),
    }
}
