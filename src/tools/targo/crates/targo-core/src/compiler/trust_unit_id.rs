//! Trust: which inputs a unit's Cargo `unit_id` hashes in a verified run.
//!
//! Cargo names a unit's files with its `unit_id` (`compilation_files.rs`): the
//! `-C extra-filename` suffix of its artifacts and its fingerprint, dep-info,
//! incremental and build-script output directories. Upstream hashes the unit's
//! rustflags into it verbatim. In a verified run those graph-wide rustflags
//! carry two values that change on every invocation: targo-trust's
//! `-Ztrust-verify-session=<256-bit random nonce>` and
//! `-Ztrust-proof-artifact-root=<private temporary directory>`
//! (`VerificationSession` in `targo-trust/src/pipeline/run.rs`). Hashed
//! verbatim, every unit of every check got a new `unit_id`, so a kept or shared
//! target directory never found a dependency's previous fingerprint: each check
//! compiled the whole graph again, into another copy of every artifact. The
//! fingerprint already leaves both values out (`fingerprint::calculate_normal`),
//! but it could never match, because it lives in a directory the `unit_id`
//! names.
//!
//! [`session_invariant_lane`] decides which key a unit gets.
//!
//! A VERIFICATION-OFF UNIT of a verified run hashes its flags without the
//! per-run transport options ([`without_per_run_transport`]), plus a lane tag
//! and the complete toolchain identity ([`SessionInvariantLane::hash`]). These
//! are the units `trust_unit_protocol_args` compiles with `-Ztrust-verify=off`
//! (dependencies and build-script compilations outside the requested scope),
//! and every build-script execution. What is in their key, and why:
//!
//! * The session nonce is OUT. It authenticates the evidence stream, and a
//!   verification-off unit emits none. rustc reads its value only on the
//!   verifying and certified-monitor paths. It is `TRACKED_NO_CRATE_HASH`, so it
//!   never reaches the crate hash. A build script never sees it
//!   (`custom_build.rs` withholds every Trust control), and targo-trust refuses
//!   any transport from a unit outside the proof inventory. What rustc does with
//!   its presence (the target-spec binding, the llvm-args and early-exit
//!   refusals) is the same in every verified run, and the lane tag records that.
//! * The proof-artifact root is OUT. It is `UNTRACKED` in rustc and read only
//!   when a verifying unit writes a proof artifact.
//! * `-Ztrust-verify-include-dependencies` is OUT as a spelling. Its value is
//!   fixed by the lane: with it on, Targo verifies every compiler unit
//!   (`trust_unit_verification_enabled`), so no compilation reaches this key,
//!   and a build-script execution then depends on a verified compilation whose
//!   `unit_id` keeps the session. Only its spelling (absent, `=no`, `=false`)
//!   would be left to separate files.
//!
//!   These three are exactly what `trust_semantic_compiler_args` projects out
//!   of the unit's fingerprint and of the `semantics_sha256` Targo publishes
//!   for a proof unit. The key uses that one projection, so a unit's name, its
//!   freshness and its published identity cannot disagree about what is
//!   per-run.
//! * Every other flag is IN, byte for byte and in order. That covers the real
//!   compiler flags (`--cfg`, `-C…`) and the rest of the verifier policy
//!   (`-Ztrust-policy`, the level and budgets). Some policy cannot change a
//!   verification-off unit's output, but it is constant across the checks of
//!   one configuration, so keeping it costs no reuse.
//! * Features, profile, mode, compile kind, target, package id and the
//!   `unit_id`s of all dependencies are IN, unchanged: `compute_metadata`
//!   hashes them before the flags. A verified dependency keeps its session (see
//!   below), so every unit built on top of one gets a per-session key too.
//! * The toolchain is IN, completely. For a prerelease rustc (every Trust
//!   build reports `-dev`) upstream's `unit_id` hashes only the channel name
//!   and leaves the rest to the fingerprint. The nonce used to keep every run
//!   apart anyway. Without it, two Trust builds sharing a target directory
//!   would write the same file names and rebuild over each other, so the whole
//!   `rustc -vV` is hashed here.
//! * The verified lane itself is IN, as a tag. In the protocol Targo appends
//!   `-Ztrust-verify=off`, `-Zalways-encode-mir` and role/package metadata at
//!   invocation, after the unit's rustflags. The same unit built by
//!   `targo --unverified` gets none of them, so it must not share the file.
//!
//! EVERY OTHER UNIT keeps upstream's key, raw nonce included:
//!
//! * A verified unit (a proof unit: a primary, a test-execution subject, or
//!   any compilation under `-Ztrust-verify-include-dependencies`). Its
//!   fingerprint carries the session (`targo-trust-unit-scope-v6`) and
//!   targo-trust refuses its `fresh=true`, so it is rebuilt every session
//!   anyway; dropping the nonce would buy no reuse. Keeping it gives each
//!   session's proof artifact, and each unit linked from it (test harnesses,
//!   `CARGO_BIN_EXE_*` binaries), a path of its own. An artifact compiled under
//!   one session's authority is then never the file that a later session's
//!   `--extern`, execution manifest or report names.
//! * A unit that receives the certified-monitor session marker
//!   (`TRUST_TARGO_TEST_MONITOR_SESSION`), whatever its verification scope: its
//!   compilation reads the session's value.
//! * Documentation and doctest units. They are rustdoc jobs outside the rustc
//!   proof protocol, and a doc unit hashes rustdocflags, which carry no session.
//! * A unit whose protocol flags do not resolve, or whose flags do not parse
//!   (a trailing `-Z`). Its compilation reports the error, and until then the
//!   key stays the conservative one.

use std::hash::Hash;

use super::{CompileMode, Unit};
use crate::util::StableHasher;

/// Bump when the session-invariant key changes shape, so an older targo's
/// artifacts can never be read as this one's.
const SESSION_INVARIANT_UNIT_ID_TAG: &str = "targo-trust-verification-off-unit-v1";

/// `args` without the per-run transport options, in either `-Z` spelling, by
/// the projection the fingerprint uses (`trust_semantic_compiler_args`). Every
/// other argument is kept byte for byte and in order. `None` when `args` does
/// not parse: that unit keeps upstream's key.
pub(crate) fn without_per_run_transport(args: &[String]) -> Option<Vec<String>> {
    super::trust_semantic_compiler_args(args).ok()
}

/// The key a verification-off unit of a verified run hashes in place of the
/// per-run values it drops (see the module docs).
pub(crate) struct SessionInvariantLane<'a> {
    /// `rustc -vV`, verbatim.
    pub(crate) rustc_verbose_version: &'a str,
    /// Whether the unit is compiled for the host. A target unit's key leaves
    /// out the `host:` line, as upstream does for a stable compiler, so a cross
    /// build shares artifacts across hosts.
    pub(crate) is_host: bool,
}

impl SessionInvariantLane<'_> {
    pub(crate) fn hash(&self, hasher: &mut StableHasher) {
        SESSION_INVARIANT_UNIT_ID_TAG.hash(hasher);
        for line in self.rustc_verbose_version.lines() {
            if self.is_host || !line.starts_with("host: ") {
                line.hash(hasher);
            }
        }
    }
}

/// `Some` exactly when `unit` is a verification-off unit of a verified run.
/// `None` keeps upstream's key.
pub(crate) fn session_invariant_lane<'a>(
    bcx: &'a super::BuildContext<'_, '_>,
    unit: &Unit,
    is_primary_package: bool,
) -> Option<SessionInvariantLane<'a>> {
    if !super::verified_targo_protocol_active() {
        return None;
    }
    let extra_args = bcx
        .extra_args_for(unit)
        .map(Vec::as_slice)
        .unwrap_or_default();
    // A unit with no resolved session is not in a verified run; one whose
    // protocol flags are malformed fails at compilation.
    super::resolve_trust_verification_protocol(&unit.rustflags, extra_args).ok()??;
    let include_dependencies =
        super::resolve_trust_include_dependencies(&unit.rustflags, extra_args).ok()?;
    // The same decision, from the same inputs, that `prepare_rustc` hands to
    // `trust_unit_protocol_args` for the `-Ztrust-verify=off` switch.
    let verification_enabled = super::trust_unit_verification_enabled(
        unit.target.is_custom_build(),
        super::is_resolved_root_unit(unit, &bcx.roots),
        super::trust_unit_test_execution_subject_context(bcx, unit),
        include_dependencies,
    );
    // The same decision `prepare_rustc` makes for the monitor marker.
    let receives_certified_monitor_session = bcx
        .gctx
        .get_env_os(super::TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION)
        .is_some()
        && super::trust_selected_runtime_unit_context(bcx, unit, is_primary_package);
    session_invariant_unit_id_enabled(
        matches!(
            unit.mode,
            CompileMode::Build | CompileMode::Check { .. } | CompileMode::Test
        ),
        verification_enabled,
        unit.mode == CompileMode::RunCustomBuild,
        receives_certified_monitor_session,
    )
    .then(|| SessionInvariantLane {
        rustc_verbose_version: &bcx.rustc().verbose_version,
        is_host: unit.kind.is_host(),
    })
}

/// Pure policy seam for [`session_invariant_lane`], for a unit of a verified
/// run. `compiled_by_rustc` is a unit that goes through `prepare_rustc`, where
/// Targo appends `-Ztrust-verify=off` exactly when `verification_enabled` is
/// false. A build-script execution runs no compiler, and its environment
/// withholds the session and the artifact root.
fn session_invariant_unit_id_enabled(
    compiled_by_rustc: bool,
    verification_enabled: bool,
    is_build_script_execution: bool,
    receives_certified_monitor_session: bool,
) -> bool {
    !receives_certified_monitor_session
        && ((compiled_by_rustc && !verification_enabled) || is_build_script_execution)
}

#[cfg(test)]
mod tests {
    use super::{session_invariant_unit_id_enabled, without_per_run_transport};

    fn flags(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    #[test]
    fn per_run_transport_leaves_in_every_spelling_and_nothing_else_does() {
        let args = flags(&[
            "--cfg",
            "feature_probe",
            "-Z",
            "trust-verify-session=nonce-a",
            "-Ztrust-policy=advisory",
            "-Ztrust_proof_artifact_root=/private/run-a",
            "-Copt-level=1",
            "-Ztrust-verify-include-dependencies=no",
            "-Z",
            "trust_verify_session=nonce-b",
            "-Z",
            "trust-proof-artifact-root=/private/run b",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-sessionx=not-the-nonce",
        ]);
        assert_eq!(
            without_per_run_transport(&args),
            Some(flags(&[
                "--cfg",
                "feature_probe",
                "-Ztrust-policy=advisory",
                "-Copt-level=1",
                "-Ztrust-verify-level=2",
                "-Ztrust-verify-sessionx=not-the-nonce",
            ])),
        );
        let untouched = flags(&["--cfg", "trust_verify_session", "-Cmetadata=x"]);
        assert_eq!(without_per_run_transport(&untouched), Some(untouched));
        // A vector that does not parse gets no projection, so its unit keeps
        // upstream's key.
        assert_eq!(
            without_per_run_transport(&flags(&["-Ztrust-verify-session=nonce-a", "-Z"])),
            None
        );
    }

    #[test]
    fn only_verification_off_units_leave_the_session_out_of_their_key() {
        // A dependency or build-script compilation outside the requested scope.
        assert!(session_invariant_unit_id_enabled(true, false, false, false));
        // A build-script execution.
        assert!(session_invariant_unit_id_enabled(false, false, true, false));
        // A verified unit keeps the session in its key.
        assert!(!session_invariant_unit_id_enabled(true, true, false, false));
        // So does a unit whose compilation reads the monitor session marker.
        assert!(!session_invariant_unit_id_enabled(true, false, false, true));
        // Documentation and doctest units keep upstream's key.
        assert!(!session_invariant_unit_id_enabled(
            false, false, false, false
        ));
        assert!(!session_invariant_unit_id_enabled(
            false, true, false, false
        ));
    }
}
