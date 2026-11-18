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

    /// Set by bootstrap's targo test step (`src/bootstrap/src/core/build_steps/test.rs`)
    /// to the stage-N trustc it tests. Bootstrap hands this test binary its own
    /// tool-build shim as RUSTC and RUSTC_WRAPPER, and that shim's inherited
    /// RUSTC_REAL is the build compiler (the stage-0 seed), not the compiler
    /// under test, so neither may select the compiler here.
    const TESTED_RUSTC_ENV: &str = "TRUST_TARGO_TEST_TESTED_RUSTC";

    /// The Cargo and compiler configuration bootstrap's `Builder::cargo` hands
    /// its own tool build (`src/bootstrap/src/core/builder/cargo.rs`), which
    /// this binary inherits: the tool build's compiler flags, output tree,
    /// build policy, library metadata seed, workspace remap and unstable
    /// switch (`RUSTC_BOOTSTRAP`; the `trust` channel admits the fixture's
    /// unstable flags without it, as on a direct run). With every
    /// `CARGO_PROFILE_` key (`BOOTSTRAP_CARGO_PROFILE_PREFIX`), none reaches a
    /// descendant under bootstrap, so the fixture compiles as a direct
    /// `targo test` run compiles it. Its build directory is set explicitly in
    /// `run` on either path. The compiler selection is pinned separately;
    /// bootstrap's shim context (`RUSTC_REAL`, `RUSTC_STAGE`, ...) is read by
    /// no program a descendant runs once no shim is the compiler.
    const BOOTSTRAP_CARGO_CONFIGURATION: [&str; 12] = [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "RUSTDOCFLAGS",
        "CARGO_ENCODED_RUSTDOCFLAGS",
        "CARGO_TARGET_DIR",
        "CARGO_INCREMENTAL",
        "CARGO_BUILD_WARNINGS",
        "CARGO_UNSTABLE_BUILD_DIR_NEW_LAYOUT",
        "CARGO_UNSTABLE_FINE_GRAIN_LOCKING",
        "__CARGO_DEFAULT_LIB_METADATA",
        "__CARGO_RUSTC_BOOTSTRAP_WS_REMAP",
        "RUSTC_BOOTSTRAP",
    ];

    /// Bootstrap sets the tool build's profile through `CARGO_PROFILE_<P>_*`
    /// (`cargo_profile_var`: strip, debug, opt-level, debug-assertions,
    /// overflow-checks, codegen-units), and with `rust.optimize = false` they
    /// are DEV keys, the fixture's own profile. Under bootstrap every key of
    /// this prefix is removed from every descendant.
    const BOOTSTRAP_CARGO_PROFILE_PREFIX: &str = "CARGO_PROFILE_";

    fn bootstrap_configuration_key(key: &str) -> bool {
        BOOTSTRAP_CARGO_CONFIGURATION.contains(&key)
            || key.starts_with(BOOTSTRAP_CARGO_PROFILE_PREFIX)
    }

    /// The flag the unverified lane itself appends to every native build's
    /// rustc flags (`targo_core`'s `TRUST_TARGO_LANE` documentation): a direct
    /// `targo --unverified build` records it too.
    const UNVERIFIED_LANE_FLAG: &str = "-Ztrust-verify=off";

    struct Originals {
        scheduler: Option<Jobserver>,
        fixed: Option<InheritedFixedClaim>,
        compiler: std::ffi::OsString,
        /// Whether bootstrap's targo test step named the compiler under test.
        bootstrap: bool,
        /// The bootstrap tool build's own rustc flags, inherited by this binary
        /// and removed from every descendant (`BOOTSTRAP_CARGO_CONFIGURATION`).
        /// Empty on a direct run, which keeps its environment.
        bootstrap_rustflags: Vec<String>,
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
        // Under bootstrap the step names the tested compiler; the inherited
        // RUSTC, wrappers and tool-build Cargo configuration are bootstrap's
        // own and reach no descendant (`command` sets RUSTC and removes the
        // rest). A direct run must select the compiler itself, with no wrapper.
        let bootstrap = std::env::var_os(TESTED_RUSTC_ENV).is_some();
        let compiler = match std::env::var_os(TESTED_RUSTC_ENV) {
            Some(tested) => {
                ensure!(
                    Path::new(&tested).is_absolute(),
                    "{TESTED_RUSTC_ENV} must name the actual absolute compiler under test"
                );
                tested
            }
            None => {
                let compiler = std::env::var_os("RUSTC")
                    .context("an explicit genuine Trust compiler is required")?;
                ensure!(
                    Path::new(&compiler).is_absolute(),
                    "RUSTC must select the actual absolute compiler"
                );
                ensure!(
                    std::env::var_os("RUSTC_WRAPPER").is_none()
                        && std::env::var_os("RUSTC_WORKSPACE_WRAPPER").is_none(),
                    "this genuine compiler regression does not admit compiler wrappers"
                );
                compiler
            }
        };
        // Cargo reads CARGO_ENCODED_RUSTFLAGS (0x1f-separated) before RUSTFLAGS.
        let bootstrap_rustflags = if bootstrap {
            match std::env::var("CARGO_ENCODED_RUSTFLAGS") {
                Ok(encoded) => encoded
                    .split('\x1f')
                    .filter(|flag| !flag.is_empty())
                    .map(str::to_owned)
                    .collect(),
                Err(_) => std::env::var("RUSTFLAGS")
                    .unwrap_or_default()
                    .split_whitespace()
                    .map(str::to_owned)
                    .collect(),
            }
        } else {
            Vec::new()
        };
        // The leak check below compares receipts against these flags; with
        // none inherited it would compare against nothing and pass vacuously.
        ensure!(
            !bootstrap || !bootstrap_rustflags.is_empty(),
            "under bootstrap this binary inherited no tool-build rustflags, so the fixture's flag-leak check would check nothing"
        );
        let originals = Originals {
            scheduler,
            fixed,
            compiler,
            bootstrap,
            bootstrap_rustflags,
        };
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
        // The frontend's brand rule (`src/bin/cargo/cli.rs`, `brand`): a build
        // that binds CFG_TRUST_VERSION, as bootstrap does, says `(targo <version>)`,
        // and one that does not says `(targo)`. This target compiles in the
        // same Targo build as the binary, so it reads the same binding.
        let brand = option_env!("CFG_TRUST_VERSION").map_or_else(
            || " (targo)".to_owned(),
            |version| format!(" (targo {version})"),
        );
        let banner = captured
            .stdout
            .split(|&byte| byte == b'\n')
            .next()
            .unwrap_or_default();
        ensure!(
            banner.starts_with(b"targo ") && banner.ends_with(brand.as_bytes()),
            "selected image did not identify the native Targo frontend (expected brand `{brand}`)"
        );
        let mut version = command(Path::new(&originals.compiler), root, originals)?;
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
        if originals.bootstrap {
            // The stage-N trustc this step tests and this Targo build bind one
            // CFG_TRUST_VERSION (bootstrap's `trust_version`, set for the
            // compiler in compile.rs and for this tool in tool.rs). The stage-0
            // seed, or a compiler of another build, names a different identity
            // (a seed's carries its own `+g<sha>`), so any other selection fails.
            let identity = option_env!("CFG_TRUST_VERSION")
                .context("bootstrap built this target without CFG_TRUST_VERSION")?;
            let expected = format!("trust: {identity}");
            ensure!(
                captured
                    .stdout
                    .split(|&byte| byte == b'\n')
                    .any(|line| line == expected.as_bytes()),
                "{TESTED_RUSTC_ENV} did not select the compiler this build tests (expected `{expected}`): {captured:?}"
            );
        }

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
                // Intermediates and receipts stay in this world: an inherited
                // build directory (bootstrap sets its tool tree's) would
                // otherwise receive them, where nothing removes them.
                .env("CARGO_BUILD_BUILD_DIR", &target)
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
        receipts_stayed_in_world(&target, originals)?;
        fs::write(
            root.join("executed-population.txt"),
            "five serial scenarios: cold, warm, preserved-mtime source change, feature change, ambiguous-module refusal\ntwelve independent app executions: four successful scenarios times arguments 0,17,251\nconcurrent consumers: not exercised by this serial integration target\nproof obligations: none; candidate coordinator: not exercised; compiler execution counts: not measured\n",
        )?;
        eprintln!(
            "native improvement workload: 5 serial scenarios and 12 actual app executions passed"
        );
        Ok(())
    }

    /// Every fixture build wrote its build receipt (`<build-dir>/.targo-receipts`)
    /// into this world's target, so its intermediates did too; and under
    /// bootstrap no receipt records a flag of the tool build's own rustc
    /// flags, so the fixture compiled as a direct run compiles it.
    fn receipts_stayed_in_world(target: &Path, originals: &Originals) -> Result<()> {
        let mut receipts = 0usize;
        for entry in fs::read_dir(target.join(".targo-receipts"))
            .context("the fixture builds left no receipt in this world's build directory")?
        {
            let path = entry?.path();
            if path.extension().is_none_or(|extension| extension != "json") {
                continue;
            }
            receipts += 1;
            let receipt: serde_json::Value = serde_json::from_slice(&fs::read(&path)?)?;
            let roots = receipt["selection"]["roots"]
                .as_array()
                .with_context(|| format!("receipt {} has no selected roots", path.display()))?;
            for root in roots {
                let leaked = root["rustflags"]
                    .as_array()
                    .with_context(|| format!("receipt {} root has no rustflags", path.display()))?
                    .iter()
                    .filter_map(serde_json::Value::as_str)
                    .filter(|flag| {
                        *flag != UNVERIFIED_LANE_FLAG
                            && originals.bootstrap_rustflags.iter().any(|own| own == flag)
                    })
                    .collect::<Vec<_>>();
                ensure!(
                    leaked.is_empty(),
                    "the fixture compiled with bootstrap's tool-build flags {leaked:?} ({})",
                    path.display()
                );
            }
        }
        ensure!(
            receipts > 0,
            "the fixture builds left no receipt in this world's build directory"
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
        // Keep ordinary environment, fixed/native couriers, linker and selected
        // GNU descriptions. No blanket env_clear/removal: only the compiler
        // selection is pinned to the one main selected, with no wrapper, so a
        // bootstrap shim this binary inherited never compiles the fixture, and
        // under bootstrap its tool build's Cargo configuration is removed.
        command
            .env("RUSTC", &originals.compiler)
            .env_remove("RUSTC_WRAPPER")
            .env_remove("RUSTC_WORKSPACE_WRAPPER");
        if originals.bootstrap {
            for key in BOOTSTRAP_CARGO_CONFIGURATION {
                command.env_remove(key);
            }
            for (key, _) in std::env::vars_os() {
                if let Some(key) = key.to_str()
                    && bootstrap_configuration_key(key)
                {
                    command.env_remove(key);
                }
            }
            // The environment the child actually receives, not the removals
            // asked for: no bootstrap configuration key may remain in it.
            let reached = command
                .get_effective_envs()?
                .into_keys()
                .filter(|key| key.to_str().is_some_and(bootstrap_configuration_key))
                .collect::<Vec<_>>();
            ensure!(
                reached.is_empty(),
                "bootstrap's tool-build configuration {reached:?} would reach the fixture"
            );
        }
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
