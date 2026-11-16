//! Trust (PM-1, 2026-10-01): the in-process proc-macro boundary, enforced where the
//! code would start running — rustc's crate loader, before it opens a proc-macro
//! crate's dylib.
//!
//! Loading a proc-macro dylib runs its load-time initializers, and every macro it
//! exports runs in this process; both share the verifying compiler's argv, memory,
//! stderr and artifact filesystem, so either could forge the proof transport.
//! Verified Targo already refuses an unaudited proc macro anywhere in a verified
//! unit's Cargo dependency closure, but the loader also finds crates Cargo's graph
//! does not model (an `extern crate` resolved through `-L dependency=`). This check
//! is the backstop: a unit Targo marks with `-Ztrust-proc-macro-boundary` loads only
//! the dylibs it lists with `-Ztrust-audited-proc-macro`. A proof-claiming session
//! refuses any other; an advisory session loads it and says the unit forfeits proof
//! authority. A compile without the boundary flag (raw `trustc`, the vanilla lane,
//! lanes that do not opt in) is unchanged.
//!
//! The boundary is about code in THIS process. Under `-Ztrust-proc-macro-isolation`
//! (D21) the loader opens no proc-macro dylib at all: a sandboxed worker does, and
//! it shares none of the argv, memory, stderr or writable filesystem above. So an
//! isolated session admits every proc-macro crate here, audited or not, on every
//! policy. That is containment, not authority: the expansion is still unaudited
//! input to the unit, verified like the source it lands in (docs/TCB.md,
//! PROC-MACRO ISOLATION).

use std::path::{Path, PathBuf};

use rustc_session::Session;
use rustc_span::Symbol;

/// What the boundary decides for one proc-macro dylib.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ProcMacroBoundary {
    /// Outside the boundary, an audited dylib, or a dylib this process does not
    /// open because a sandboxed worker expands its macros.
    Admitted,
    /// A proof-claiming session refuses to load it.
    Refused(String),
    /// An advisory session loads it and forfeits proof authority.
    Forfeited(String),
}

/// The decision, pure so it is tested without a session.
pub(crate) fn decide(
    boundary: bool,
    verifying: bool,
    proof_claimed: bool,
    isolated: bool,
    audited: &[PathBuf],
    dylib: &Path,
    crate_name: &str,
) -> ProcMacroBoundary {
    if !boundary || !verifying || isolated {
        return ProcMacroBoundary::Admitted;
    }
    let canonical =
        |path: &Path| std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let dylib_canonical = canonical(dylib);
    if audited.iter().any(|path| canonical(path) == dylib_canonical) {
        return ProcMacroBoundary::Admitted;
    }
    if proof_claimed {
        ProcMacroBoundary::Refused(format!(
            "verified Targo refuses to load proc-macro crate `{crate_name}` ({}): it is not an \
             audited provider, and loading it runs third-party code inside the verifying \
             compiler, where it could forge the proof transport (no-proc-macro TCB boundary, \
             PM-1). Remove the dependency that brings it in, or build without a proof claim \
             (`--allow-l0-gaps`, which reports and forfeits)",
            dylib.display()
        ))
    } else {
        ProcMacroBoundary::Forfeited(format!(
            "advisory lane: this unit forfeits proof authority: rustc loaded unaudited \
             proc-macro crate `{crate_name}` ({}) inside the verifying compiler \
             (no-proc-macro TCB boundary, PM-1)",
            dylib.display()
        ))
    }
}

/// Apply [`decide`] to the session: refusal is fatal, forfeiture a warning.
pub(crate) fn check(sess: &Session, dylib: &Path, crate_name: Symbol) {
    let audited: Vec<PathBuf> =
        sess.opts.unstable_opts.trust_audited_proc_macro.iter().map(PathBuf::from).collect();
    match decide(
        sess.opts.unstable_opts.trust_proc_macro_boundary,
        sess.trust_verification_enabled(),
        sess.trust_proof_claimed(),
        sess.opts.unstable_opts.trust_proc_macro_isolation,
        &audited,
        dylib,
        crate_name.as_str(),
    ) {
        ProcMacroBoundary::Admitted => {}
        ProcMacroBoundary::Refused(message) => sess.dcx().fatal(message),
        ProcMacroBoundary::Forfeited(message) => {
            sess.dcx().warn(message);
        }
    }
}

#[cfg(test)]
mod tests;
