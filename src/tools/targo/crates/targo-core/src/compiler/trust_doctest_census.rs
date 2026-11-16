//! Trust (D2d, 2026-09-28): the doctest census of a verified `targo test`.
//!
//! Cargo's default `test` filter adds a Doctest Unit for every doctested
//! library, and verified Targo declares it `deferred-doctest-execution`: it has
//! no authenticated lane that could RUN doctests. `targo trust test` never runs
//! them anyway — phase B selects `--tests` — so that exclusion is honest only
//! when the Unit holds a doctest. A library with zero doctests used to read
//! INCONCLUSIVE forever because of a Unit that could never execute anything.
//!
//! The census asks the authenticated trustdoc to COLLECT (not compile, not
//! run) the Unit's doctests with the exact arguments `run_doc_tests` would give
//! it, via `--test --output-format=doctest`, and reports the count bound to the
//! Unit's declared inventory identity. Anything short of a complete, error-free
//! census emits nothing, so the Unit stays deferred: a real doctest can never
//! vanish from the frontier through a census that failed.
//!
//! In an evidence-grade certified-monitor session the census trustdoc runs
//! under the SAME seal as that session's rustc (`seal_doctest_census_command`):
//! its count can admit a Unit, so it gets no loader channel but the
//! authenticated toolchain closure (+ `/usr/lib`), no `TRUST_*` authority
//! (trustdoc reads none; in particular not the session nonce
//! `TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION`), and rustc's fixed `PATH`.

use std::sync::Arc;

use cargo_util::ProcessBuilder;

use super::fingerprint::VerifiedRustdocLauncherIdentity;
use super::job_queue::{Job, Work};
use super::trust_certified_monitor_seal::CertifiedMonitorSeal;
use super::{BuildRunner, DirtyReason, Unit};
use crate::workspace::profiles::PanicStrategy;
use crate::util::CargoResult;
use crate::util::add_path_args;
use crate::util::machine_message::{self, Message as _};
use crate::util::process_authority::validate_verified_command_runtime_library_authority;

/// The census job for a Doctest Unit, or `None` outside a verified JSON run
/// (where no proof inventory is declared, so there is nothing to refine).
/// `execution_tcb_enforced` is the Unit's certified-monitor seal decision, the
/// same one `compile` and `prepare_rustc` derive for its rustc Units.
pub(super) fn doctest_census_job(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    execution_tcb_enforced: bool,
) -> CargoResult<Option<Job>> {
    if !(super::verified_targo_protocol_active() && build_runner.bcx.build_config.emit_json()) {
        return Ok(None);
    }
    let label = format!("{}::{}", unit.pkg.package_id(), unit.target.name());
    // Inputs this census does not replay keep the Unit deferred rather than
    // being approximated: a build script's `rustc-cfg`/`rustc-env` output and
    // artifact-dependency variables can change which docs exist.
    let unreplayed = if build_runner.find_build_script_metadatas(unit).is_some() {
        Some("its package runs a build script whose cfg/env output the census does not replay")
    } else if !super::artifact::get_env(build_runner, unit, build_runner.unit_deps(unit))?
        .is_empty()
    {
        Some("it carries artifact-dependency environment the census does not replay")
    } else {
        None
    };
    if let Some(reason) = unreplayed {
        let warning = census_unavailable_warning(&label, reason);
        return Ok(Some(Job::new_dirty(
            Work::new(move |state| {
                state.warning(warning);
                Ok(())
            }),
            DirtyReason::FreshBuild,
        )));
    }

    let index = build_runner
        .bcx
        .unit_to_index
        .get(unit)
        .map(|index| index.0)
        .ok_or_else(|| {
            anyhow::anyhow!("doctest Unit `{label}` has no resolved Cargo Unit index")
        })?;
    let trust_unit_identity_sha256 =
        super::trust_declared_unit_identity_sha256(build_runner, unit)?;
    let mut rustdoc = doctest_census_command(build_runner, unit)?;
    let seal = CertifiedMonitorSeal::capture(
        execution_tcb_enforced,
        build_runner.compilation.authenticated_compiler_program(),
        build_runner.bcx.gctx,
    )?;
    let launcher: Option<Arc<VerifiedRustdocLauncherIdentity>> =
        build_runner.verified_rustdoc_launcher.clone();

    Ok(Some(Job::new_dirty(
        Work::new(move |state| {
            // The exec edge, as for rustc: seal, then validate, then spawn.
            if let Err(error) = seal_doctest_census_command(&mut rustdoc, &seal) {
                state.warning(census_unavailable_warning(
                    &label,
                    &format!("its trustdoc launch could not be sealed: {error}"),
                ));
                return Ok(());
            }
            // A launch the exec-edge authority refuses (for example a target
            // directory under a world-writable path) is a census that did not
            // happen: the Unit stays deferred, and the build is not failed for
            // a Unit that was a no-op before the census existed.
            if let Err(error) = validate_verified_command_runtime_library_authority(&rustdoc) {
                state.warning(census_unavailable_warning(
                    &label,
                    &format!("its trustdoc launch was refused: {error:#}"),
                ));
                return Ok(());
            }
            if let Some(identity) = &launcher {
                identity.ensure_current()?;
            }
            state.running(&rustdoc);
            let output = rustdoc.output();
            // Recheck even when the spawn failed: an endpoint replacement is an
            // integrity failure, not a census that merely came back empty.
            if let Some(identity) = &launcher {
                identity.ensure_current()?;
            }
            let census = match output {
                Ok(output) => {
                    doctest_census_count(output.status.success(), &output.stdout, &output.stderr)
                }
                Err(error) => Err(format!("trustdoc could not be executed: {error:#}")),
            };
            match census {
                Ok(doctests) => state.stdout(
                    machine_message::TrustDoctestCensus {
                        schema: machine_message::TRUST_DOCTEST_CENSUS_SCHEMA_V1,
                        index,
                        trust_unit_identity_sha256,
                        doctests,
                    }
                    .to_json_string(),
                )?,
                Err(reason) => state.warning(census_unavailable_warning(&label, &reason)),
            }
            Ok(())
        }),
        DirtyReason::FreshBuild,
    )))
}

/// The certified-monitor seal of the census trustdoc: exactly rustc's graph
/// seal with no per-unit monitor marker (the census compiles no monitored MIR).
/// It deletes every `TRUST_*`, loader, linker and compiler-flag channel —
/// including the session nonce `TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION`,
/// which only Targo reads — reinstalls the captured authenticated loader value
/// (no Cargo-owned `deps`), and pins `PATH` as rustc gets it. Outside an
/// enforced seal the command is left exactly as built.
fn seal_doctest_census_command(
    rustdoc: &mut ProcessBuilder,
    seal: &CertifiedMonitorSeal,
) -> Result<(), String> {
    super::seal_certified_monitor_graph_compiler_environment(rustdoc, seal, None)
}

fn census_unavailable_warning(label: &str, reason: &str) -> String {
    format!(
        "doctest census for `{label}` is unavailable ({reason}); the doctest Unit stays `{}`",
        machine_message::TRUST_EXCLUSION_DEFERRED_DOCTEST
    )
}

/// The rustdoc process `run_doc_tests` builds for this Unit, with the same
/// compile inputs (`Doctest::args` in `BuildRunner::compile`), minus what only
/// EXECUTES doctests (runtool, linker, `--test-args`, run directory), plus
/// `--output-format=doctest` so trustdoc lists the doctests and stops.
fn doctest_census_command(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<ProcessBuilder> {
    let mut rustdoc = build_runner.compilation.rustdoc_process(unit, None)?;
    // Same closed target-origin boundary as `prepare_rustdoc`.
    rustdoc.env_remove("RUST_TARGET_PATH");
    rustdoc.arg("--crate-name").arg(unit.target.crate_name());
    rustdoc.arg("--test");
    add_path_args(build_runner.bcx.ws, unit, &mut rustdoc);
    unit.kind.add_target_arg(&mut rustdoc);
    // `cfg(panic = "...")` can gate documentation, so keep the doctest cfg.
    if unit.profile.panic != PanicStrategy::Unwind {
        rustdoc
            .arg("-C")
            .arg(format!("panic={}", unit.profile.panic));
    }
    rustdoc.args(unit.pkg.manifest().lint_rustflags());
    let mut unstable_opts = false;
    rustdoc.args(&super::extern_args(build_runner, unit, &mut unstable_opts)?);
    rustdoc.args(&super::lib_search_paths(build_runner, unit)?);
    rustdoc.args(&super::lto_args(build_runner, unit));
    rustdoc.args(&super::features_args(unit));
    rustdoc.args(&super::check_cfg_args(unit));
    rustdoc.args(&unit.rustdocflags);
    rustdoc.arg("--error-format").arg("json");
    rustdoc
        .arg("-Zunstable-options")
        .arg("--output-format=doctest");
    Ok(rustdoc)
}

/// The census is complete only when trustdoc exited successfully, reported no
/// error-level diagnostic, and printed exactly one `format_version` 2 document.
/// No single signal is trusted alone: trustdoc still prints a PARTIAL
/// `{"format_version":2,"doctests":[]}` when it aborts on an error (measured
/// 2026-09-28: an unresolved import exits 1 with exactly that stdout).
pub(super) fn doctest_census_count(
    success: bool,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<u64, String> {
    if !success {
        return Err("trustdoc exited unsuccessfully".to_string());
    }
    let stderr = std::str::from_utf8(stderr)
        .map_err(|_| "trustdoc diagnostics were not UTF-8".to_string())?;
    for line in stderr.lines().filter(|line| !line.trim().is_empty()) {
        let diagnostic: serde_json::Value = serde_json::from_str(line)
            .map_err(|_| "trustdoc printed a diagnostic line that is not JSON".to_string())?;
        let level = diagnostic
            .get("level")
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default();
        if level.starts_with("error") {
            let message = diagnostic
                .get("message")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("<no message>");
            return Err(format!("trustdoc reported an error: {message}"));
        }
    }
    // `from_slice` rejects trailing non-whitespace, so this is exactly one
    // document, not a prefix a later line could contradict.
    let document: serde_json::Value = serde_json::from_slice(stdout)
        .map_err(|_| "trustdoc did not print exactly one JSON doctest document".to_string())?;
    if document
        .get("format_version")
        .and_then(serde_json::Value::as_u64)
        != Some(2)
    {
        return Err("trustdoc printed an unsupported doctest document format".to_string());
    }
    let doctests = document
        .get("doctests")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "trustdoc's doctest document has no `doctests` array".to_string())?;
    u64::try_from(doctests.len()).map_err(|_| "doctest count overflowed u64".to_string())
}

#[cfg(test)]
mod tests {
    use super::doctest_census_count;
    #[cfg(unix)]
    use super::{CertifiedMonitorSeal, seal_doctest_census_command};

    const EMPTY: &[u8] = br#"{"format_version":2,"doctests":[]}"#;

    /// D2d: the census counts exactly what trustdoc collected, and refuses
    /// every partial or contradicted result instead of reading it as zero.
    #[test]
    fn doctest_census_is_complete_only_without_errors() {
        assert_eq!(doctest_census_count(true, EMPTY, b""), Ok(0));
        let one = br#"{"format_version":2,"doctests":[{"name":"lib.rs - f (line 1)"}]}"#;
        assert_eq!(doctest_census_count(true, one, b""), Ok(1));
        let warning = br#"{"$message_type":"diagnostic","message":"unused","level":"warning"}"#;
        assert_eq!(doctest_census_count(true, EMPTY, warning), Ok(0));

        // Measured trustdoc behaviour: an aborted collection still prints an
        // empty document. Neither the exit status nor the error diagnostic
        // may be ignored.
        let aborted = br#"{"$message_type":"diagnostic","message":"unresolved import `foo`","level":"error"}"#;
        assert!(doctest_census_count(false, EMPTY, aborted).is_err());
        assert!(doctest_census_count(true, EMPTY, aborted).is_err());
        assert!(doctest_census_count(false, EMPTY, b"").is_err());

        assert!(doctest_census_count(true, EMPTY, b"error: not json\n").is_err());
        let two = [EMPTY, b"\n".as_slice(), EMPTY].concat();
        assert!(doctest_census_count(true, &two, b"").is_err());
        assert!(doctest_census_count(true, br#"{"format_version":1,"doctests":[]}"#, b"").is_err());
        assert!(doctest_census_count(true, br#"{"format_version":2}"#, b"").is_err());
        assert!(doctest_census_count(true, b"", b"").is_err());
    }
    /// Review of D2d (2026-09-28): the census trustdoc's count can admit a
    /// Unit, so in an evidence-grade certified-monitor session it runs under
    /// rustc's seal. Before this it inherited the session nonce, the caller's
    /// `PATH`, and a loader value that carried Cargo's `target/*/deps`
    /// (measured). The census-shaped command below is what `fill_env` hands
    /// it; sealed, it keeps its argv and Cargo's doc-relevant environment and
    /// loses every authority channel. Outside an enforced seal it is untouched.
    #[cfg(unix)]
    #[test]
    fn doctest_census_command_is_sealed_in_the_monitor_lane_and_unchanged_outside_it() {
        use std::ffi::OsStr;

        use cargo_util::ProcessBuilder;

        use crate::util::process_authority::{
            caller_clean_fixture_root, caller_owned_toolchain_fixture,
            validate_command_runtime_library_search,
        };

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (compiler, lib) = caller_owned_toolchain_fixture(&root, "d2d-census-seal-stage2");
        std::fs::write(lib.join("librustc_driver-fixture.dylib"), b"fixture").unwrap();
        let startup_closure = vec![lib.canonicalize().unwrap()];
        let search = cargo_util::paths::dylib_path_envvar();
        let deps = root.join("d2d-census-seal-target/debug/deps");
        let mut fill_env_search = startup_closure.clone();
        fill_env_search.push(deps.clone());
        fill_env_search.push("/usr/lib".into());
        let fill_env_search = std::env::join_paths(&fill_env_search).unwrap();
        let trustdoc = compiler.with_file_name("trustdoc");

        let census_shaped = || {
            let mut rustdoc = ProcessBuilder::new(&trustdoc);
            rustdoc
                .args(&["--crate-name", "fixture", "--test", "src/lib.rs"])
                .args(&["-Zunstable-options", "--output-format=doctest"])
                .env(search, &fill_env_search)
                .env(
                    "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
                    "session-nonce",
                )
                .env("TRUST_TARGO_FRONTEND", "1")
                .env("PATH", "/tmp/caller-first:/usr/bin:/bin")
                .env("DYLD_INSERT_LIBRARIES", "/tmp/evil.dylib")
                .env("dyld_insert_libraries", "/tmp/evil-lowercase.dylib")
                .env("DYLD_LIBRARY_PATH", "/tmp/evil-first")
                .env("LD_PRELOAD", "/tmp/evil.so")
                .env("SDKROOT", "/tmp/evil-sdk")
                .env("CARGO_MANIFEST_DIR", "/fixture")
                .env("CARGO_PKG_NAME", "fixture");
            rustdoc
        };

        // Monitor lane: the seal is enforced and the exec edge is verified.
        let monitor = CertifiedMonitorSeal::capture_for_test(true, true, &compiler).unwrap();
        let authenticated = monitor
            .authenticated_loader_search()
            .expect("the monitor lane captures a loader value")
            .to_os_string();
        let mut sealed = census_shaped();
        // The unsealed census value is not the authenticated one: it carries
        // Cargo's caller-owned `deps` directory.
        assert!(std::env::split_paths(&sealed.get_env(search).unwrap()).any(|path| path == deps));
        seal_doctest_census_command(&mut sealed, &monitor).unwrap();
        assert_eq!(
            sealed.get_env(search).as_deref(),
            Some(authenticated.as_os_str()),
            "exactly the captured authenticated closure (+ /usr/lib), never fill_env's deps"
        );
        assert!(!std::env::split_paths(&authenticated).any(|path| path == deps));
        validate_command_runtime_library_search(&sealed, &startup_closure).unwrap_or_else(
            |error| panic!("the sealed census must pass the exec-edge validator: {error:#}"),
        );
        for name in [
            "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
            "TRUST_TARGO_TEST_MONITOR_SESSION",
            "TRUST_TARGO_FRONTEND",
            "DYLD_INSERT_LIBRARIES",
            "dyld_insert_libraries",
            "DYLD_LIBRARY_PATH",
            "LD_PRELOAD",
            "SDKROOT",
        ] {
            assert_eq!(
                sealed.get_env(name),
                None,
                "{name} survived the census seal"
            );
        }
        assert_eq!(
            sealed.get_env("PATH").as_deref(),
            Some(OsStr::new("/usr/bin:/bin"))
        );
        assert_eq!(
            sealed.get_env("CARGO_MANIFEST_DIR").as_deref(),
            Some(OsStr::new("/fixture"))
        );
        assert_eq!(
            sealed.get_args().collect::<Vec<_>>(),
            census_shaped().get_args().collect::<Vec<_>>()
        );

        // Advisory lane (seal forfeited) and unverified: byte-for-byte unchanged.
        for (enforced, verified) in [(false, true), (false, false)] {
            let seal =
                CertifiedMonitorSeal::capture_for_test(enforced, verified, &compiler).unwrap();
            let mut ordinary = census_shaped();
            seal_doctest_census_command(&mut ordinary, &seal).unwrap();
            let expected = census_shaped();
            assert_eq!(
                ordinary.get_envs(),
                expected.get_envs(),
                "enforced={enforced}"
            );
            assert_eq!(
                ordinary.get_args().collect::<Vec<_>>(),
                expected.get_args().collect::<Vec<_>>()
            );
        }
        let _ = std::fs::remove_dir_all(root.join("d2d-census-seal-stage2"));
    }
}
