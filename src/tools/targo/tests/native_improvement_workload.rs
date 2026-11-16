// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Compile the maintained candidate-comparison Rust fixture with actual Targo,
//! then independently execute its produced app. This is ordinary integration
//! behavior, not candidate-coordinator, compiler-count or proof qualification.
//! ConcurrentConsumers is a separate native-coordinator requirement and is
//! deliberately not counted among this target's five serial scenarios.

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported {
    use std::fs;
    use std::path::Path;
    use std::time::Duration;

    use anyhow::{Context as _, Result, ensure};
    use cargo_util::{CapturedProcess, Jobserver, ProcessBuilder, StreamingOutputLimits};
    use trust_build_tree::admission::{EarlyFixedClaim, FIXED_HANDOFF_ENV, InheritedFixedClaim};
    use trust_qualification::improvement::workload::{Scenario, SourceVariant, WorkloadPlan};

    const SCENARIOS: [Scenario; 5] = [
        Scenario::Cold,
        Scenario::Warm,
        Scenario::PreservedMtimeSourceChange,
        Scenario::FeatureChange,
        Scenario::AmbiguousModuleRefusal,
    ];

    struct Originals {
        scheduler: Option<Jobserver>,
        fixed: Option<InheritedFixedClaim>,
    }

    pub fn main() -> Result<()> {
        // Snapshot every mapped original before any importer can allocate and
        // reuse an advertised slot. These observations do not grant authority.
        let fixed_courier = std::env::var_os(cargo_util::FIXED_CLAIM_HANDOFF_ENV);
        let fixed_snapshot = if fixed_courier.is_none() {
            std::env::var_os(FIXED_HANDOFF_ENV)
                .map(|descriptor| EarlyFixedClaim::snapshot(&descriptor))
                .transpose()?
        } else {
            None
        };
        let sdk_advertised = std::env::var_os("ATERM_SDK_LEASE_V3").is_some();
        let sdk = targo::snapshot_sdk_lease()?;
        let bootstrap =
            targo::workload_service::snapshot_bootstrap(std::env::args_os().nth(1).as_deref())?;
        // SAFETY: this harness=false target has just entered main. No logger,
        // test framework, file opening, child or thread has run above.
        let inherited = unsafe { Jobserver::from_env_with_handoff_checked() }?;
        // SAFETY: only the fixed early GNU importer followed the SDK snapshot;
        // no callbacks, arbitrary FD opens or threads can reuse its mapped slot.
        unsafe { targo::capture_sdk_lease(sdk) }?;
        // SAFETY: only the prescribed GNU and SDK importers ran after the
        // joint original snapshot. Their mapped descriptions are disjoint.
        let bootstrap = unsafe { targo::workload_service::capture_bootstrap(bootstrap) }?;
        let fixed = match fixed_courier {
            Some(advertisement) => Some(InheritedFixedClaim::from_descendant(&advertisement)?),
            None => fixed_snapshot.map(EarlyFixedClaim::capture).transpose()?,
        };
        ensure!(
            !sdk_advertised && !bootstrap.is_present(),
            "this ordinary integration target lacks a hosted SDK/workload forwarding profile; originals were retained, no work launched"
        );
        // Retain the SAME transport through every descendant wait. No private
        // scheduler, CPU pool or second machine admission is created here.
        let scheduler = inherited
            .as_ref()
            .map(|inherited| {
                let mut scheduler = inherited.for_descendant()?;
                scheduler.propagate_make_flags();
                Ok::<_, std::io::Error>(scheduler)
            })
            .transpose()?;
        let originals = Originals { scheduler, fixed };
        let compiler =
            std::env::var_os("RUSTC").context("an explicit genuine Trust compiler is required")?;
        ensure!(
            Path::new(&compiler).is_absolute(),
            "RUSTC must select the actual absolute compiler"
        );
        ensure!(
            std::env::var_os("RUSTC_WRAPPER").is_none()
                && std::env::var_os("RUSTC_WORKSPACE_WRAPPER").is_none(),
            "this genuine compiler regression does not admit compiler wrappers"
        );
        // The world is retained under this checkout's ignored `.ubd/` area,
        // never as an untracked directory of the source tree
        // (TARGO-TEST-TMP-HYGIENE-1; `tests/fixture_retention.rs`).
        let base = std::env::current_dir()?.join(".ubd/native-improvement-workload.noindex");
        fs::create_dir_all(&base)?;
        let world = tempfile::Builder::new()
            .prefix("native-improvement-workload-")
            .tempdir_in(base)?;
        let root = world.path().to_path_buf();
        let result = run(&root, &originals);
        // Preserve actual inputs, produced artifacts and bounded raw captures
        // on either outcome so the coordinator can inspect the executed case.
        let evidence = world.keep();
        eprintln!(
            "native improvement workload evidence: {}",
            evidence.display()
        );
        result
    }

    fn run(root: &Path, originals: &Originals) -> Result<()> {
        let plan = WorkloadPlan::new(1)?;
        let source = root.join("source");
        let target = root.join("target.noindex");
        let home = root.join("home");
        let evidence = root.join("captures");
        fs::create_dir_all(&home)?;
        fs::create_dir(&evidence)?;
        let initial = plan.sources(SourceVariant::Initial);
        ensure!(
            initial.len() == 9,
            "the maintained fixture source population changed"
        );
        for file in &initial {
            let path = source.join(&file.path);
            fs::create_dir_all(path.parent().unwrap())?;
            fs::write(path, &file.bytes)?;
        }

        let mut version = command(Path::new(env!("CARGO_BIN_EXE_targo")), root, originals)?;
        version.arg0("targo").args(&["--unverified", "--version"]);
        let captured = capture(
            &version,
            &evidence,
            "genuine-targo-version",
            Duration::from_secs(30),
        )?;
        ensure!(
            captured.succeeded(),
            "selected image is not runnable genuine Targo: {captured:?}"
        );
        ensure!(
            captured.stdout.starts_with(b"targo ")
                && captured.stdout.windows(7).any(|part| part == b"(targo)"),
            "selected image did not identify the native Targo frontend"
        );
        let compiler =
            std::env::var_os("RUSTC").context("actual compiler selection disappeared")?;
        let mut version = command(Path::new(&compiler), root, originals)?;
        version.arg("-vV");
        let captured = capture(
            &version,
            &evidence,
            "genuine-trustc-version",
            Duration::from_secs(30),
        )?;
        ensure!(
            captured.succeeded()
                && captured
                    .stdout
                    .split(|&byte| byte == b'\n')
                    .any(|line| line.starts_with(b"trust: ")),
            "selected compiler did not identify the actual Trust toolchain: {captured:?}"
        );

        for scenario in SCENARIOS {
            match scenario {
                Scenario::PreservedMtimeSourceChange => {
                    let selected = source.join("leaf/src/implementation.rs");
                    let before = fs::metadata(&selected)?;
                    let modified = filetime::FileTime::from_last_modification_time(&before);
                    let changes = plan
                        .sources(SourceVariant::Changed)
                        .into_iter()
                        .filter(|file| !initial.contains(file))
                        .collect::<Vec<_>>();
                    ensure!(
                        changes.len() == 1 && changes[0].path == "leaf/src/implementation.rs",
                        "fixture source transition changed"
                    );
                    ensure!(
                        before.len() == changes[0].bytes.len() as u64,
                        "source transition must preserve byte length"
                    );
                    fs::write(&selected, &changes[0].bytes)?;
                    filetime::set_file_mtime(&selected, modified)?;
                    ensure!(
                        filetime::FileTime::from_last_modification_time(&fs::metadata(&selected)?)
                            == modified,
                        "source transition did not preserve mtime"
                    );
                }
                Scenario::AmbiguousModuleRefusal => {
                    let changed = plan.sources(SourceVariant::Changed);
                    let additions = plan
                        .sources(SourceVariant::Ambiguous)
                        .into_iter()
                        .filter(|file| !changed.contains(file))
                        .collect::<Vec<_>>();
                    ensure!(
                        additions.len() == 1
                            && additions[0].path == "leaf/src/implementation/mod.rs",
                        "fixture ambiguity transition changed"
                    );
                    let path = source.join(&additions[0].path);
                    fs::create_dir_all(path.parent().unwrap())?;
                    fs::write(path, &additions[0].bytes)?;
                }
                _ => {}
            }
            let mut build = command(
                Path::new(env!("CARGO_BIN_EXE_targo")),
                &source.join("app"),
                originals,
            )?;
            build
                .arg0("targo")
                .args(&[
                    "--unverified",
                    "build",
                    "--locked",
                    "--offline",
                    "--bin",
                    "native_app",
                    "--message-format=json",
                    "-j1",
                    "--target-dir",
                ])
                .arg(&target)
                .env("CARGO_HOME", &home)
                .env("CARGO_CACHE_RUSTC_INFO", "0");
            if !scenario.features().is_empty() {
                build.arg("--features").arg(scenario.features().join(","));
            }
            let built = capture(
                &build,
                &evidence,
                scenario.action(),
                Duration::from_secs(180),
            )?;
            if scenario == Scenario::AmbiguousModuleRefusal {
                ensure!(
                    built.started
                        && built.complete()
                        && built
                            .status
                            .is_some_and(|status| status.code() == Some(101))
                        && built.read_error.is_none()
                        && built.cleanup_error.is_none(),
                    "module refusal did not complete as an ordinary compiler failure: {built:?}"
                );
                let ambiguity = built
                    .stdout
                    .split(|&byte| byte == b'\n')
                    .filter(|line| !line.is_empty())
                    .map(serde_json::from_slice::<serde_json::Value>)
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .iter()
                    .any(|row| {
                        row["reason"] == "compiler-message"
                            && row["message"]["level"] == "error"
                            && row["message"]["code"]["code"] == "E0761"
                    });
                ensure!(
                    ambiguity,
                    "actual compiler did not report the selected ambiguous-module error"
                );
            } else {
                ensure!(
                    built.succeeded(),
                    "actual fixture build failed at {scenario:?}: {built:?}"
                );
                let program = target.join("debug/native_app");
                let metadata = fs::symlink_metadata(&program)?;
                ensure!(
                    metadata.is_file() && metadata.len() > 0,
                    "actual app is missing, empty or a symlink"
                );
                for &argument in plan.arguments() {
                    let mut app = command(&program, &source.join("app"), originals)?;
                    app.arg(argument.to_string());
                    let label = format!("{}-app-{argument}", scenario.action());
                    let output = capture(&app, &evidence, &label, Duration::from_secs(15))?;
                    ensure!(
                        output.succeeded(),
                        "actual produced app failed at {scenario:?}/{argument}: {output:?}"
                    );
                    plan.validate_app_output(
                        scenario,
                        "app",
                        argument,
                        &output.stdout,
                        &output.stderr,
                    )?;
                }
            }
        }
        fs::write(
            root.join("executed-population.txt"),
            "five serial scenarios: cold, warm, preserved-mtime source change, feature change, ambiguous-module refusal\ntwelve independent app executions: four successful scenarios times arguments 0,17,251\nconcurrent consumers: not exercised by this serial integration target\nproof obligations: none; candidate coordinator: not exercised; compiler execution counts: not measured\n",
        )?;
        eprintln!(
            "native improvement workload: 5 serial scenarios and 12 actual app executions passed"
        );
        Ok(())
    }

    fn command(program: &Path, cwd: &Path, originals: &Originals) -> Result<ProcessBuilder> {
        let mut command = ProcessBuilder::new(program);
        command.cwd(cwd);
        if let Some(scheduler) = &originals.scheduler {
            command.inherit_jobserver(scheduler);
        }
        if let Some(fixed) = &originals.fixed {
            fixed.check_current()?;
            command
                .env(
                    cargo_util::FIXED_CLAIM_HANDOFF_ENV,
                    fixed.descendant_advertisement()?,
                )
                .env(FIXED_HANDOFF_ENV, "requires-live-ancestor-v1");
        }
        // Keep ordinary environment, fixed/native couriers, actual compiler,
        // linker and selected GNU descriptions. No blanket env_clear/removal.
        Ok(command)
    }

    fn capture(
        command: &ProcessBuilder,
        evidence: &Path,
        label: &str,
        timeout: Duration,
    ) -> Result<CapturedProcess> {
        let output = command.exec_with_capture(
            StreamingOutputLimits::new(64 * 1024, 2 * 1024 * 1024)
                .with_timeout(timeout)
                .with_child_exit_cleanup(),
        );
        fs::write(evidence.join(format!("{label}.stdout")), &output.stdout)?;
        fs::write(evidence.join(format!("{label}.stderr")), &output.stderr)?;
        fs::write(
            evidence.join(format!("{label}.observation")),
            format!(
                "started={}\nstatus={:?}\nstdout_end={:?}\nstderr_end={:?}\nstdout_truncated={}\nstderr_truncated={}\nfailure={:?}\nread_error={:?}\ncleanup_error={:?}\n",
                output.started,
                output.status,
                output.stdout_end,
                output.stderr_end,
                output.stdout_truncated,
                output.stderr_truncated,
                output.failure,
                output.read_error,
                output.cleanup_error,
            ),
        )?;
        Ok(output)
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn main() -> anyhow::Result<()> {
    supported::main()
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn main() {
    panic!("native improvement workload requires the maintained Unix capture owner");
}
