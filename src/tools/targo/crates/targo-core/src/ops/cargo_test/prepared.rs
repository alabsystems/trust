//! Preserve the native compiled test plan across the current proof gate.

use super::*;
use crate::util::machine_message::Message;
use trust_test_execution::results::{HarnessEnd, HarnessExit, HarnessResultFiles};
use trust_test_execution::{self as wire, PreparedTest, PreparedTests, PreparedTestsReceipt};

impl Message for PreparedTestsReceipt {
    fn reason(&self) -> &str {
        "trust-test-execution-plan"
    }
}

pub(super) fn export(
    ws: &Workspace<'_>,
    options: &TestOptions,
    args: &[&str],
    compilation: &Compilation<'_>,
) -> CargoResult<()> {
    let gctx = ws.gctx();
    let Some(_) = gctx.get_env_os(wire::EXPORT_ENV) else {
        return Ok(());
    };
    if !crate::is_targo_invocation() || !crate::trust_verified_targo() {
        anyhow::bail!("prepared test export requires authenticated verified Targo");
    }
    let session = gctx.get_env(wire::EXPORT_SESSION_ENV)?;
    export_plan(ws, options.no_fail_fast, args, compilation, &session, false)?;
    Ok(())
}

pub(super) fn export_retained(
    ws: &Workspace<'_>,
    options: &super::graph::TestGraphOptions,
    compilation: &Compilation<'_>,
    session: &str,
) -> CargoResult<(PreparedTests, PreparedTestsReceipt)> {
    let export_session = ws.gctx().get_env(wire::EXPORT_SESSION_ENV)?;
    anyhow::ensure!(
        export_session == session,
        "retained endpoint differs from the compiler export session"
    );
    let args = options.args.iter().map(String::as_str).collect::<Vec<_>>();
    export_plan(ws, options.no_fail_fast, &args, compilation, session, true)
}

fn export_plan(
    ws: &Workspace<'_>,
    no_fail_fast: bool,
    args: &[&str],
    compilation: &Compilation<'_>,
    session: &str,
    retained: bool,
) -> CargoResult<(PreparedTests, PreparedTestsReceipt)> {
    let gctx = ws.gctx();
    for output in &compilation.tests {
        if crate::compiler::trust_verification_session(&output.unit.rustflags)
            .map_err(anyhow::Error::msg)?
            .as_deref()
            != Some(session)
        {
            anyhow::bail!("prepared test export does not match the current compiler session");
        }
    }
    let path =
        PathBuf::from(gctx.get_env_os(wire::EXPORT_ENV).ok_or_else(|| {
            anyhow::anyhow!("retained tests require a prepared plan export path")
        })?);
    if !path.is_absolute() {
        anyhow::bail!("prepared test export path must be absolute");
    }
    let plan = capture(
        ws,
        no_fail_fast,
        args,
        compilation,
        session,
        retained,
        &path,
    )?;
    let bytes = serde_json::to_vec(&plan)?;
    if bytes.len() as u64 > wire::MAX_PLAN_BYTES {
        anyhow::bail!("prepared test plan exceeds its bound");
    }
    let mut file = fs::OpenOptions::new();
    file.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        file.mode(0o600).custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = file.open(&path)?;
    use std::io::Write as _;
    file.write_all(&bytes)?;
    file.sync_all()?;
    let receipt = PreparedTestsReceipt {
        schema: wire::RECEIPT_SCHEMA.into(),
        session: session.to_owned(),
        path: path
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("prepared test path is not UTF-8"))?
            .into(),
        sha256: Sha256::new().update(&bytes).finish_hex(),
    };
    writeln!(gctx.shell().out(), "{}", receipt.to_json_string())?;
    Ok((plan, receipt))
}

fn capture(
    ws: &Workspace<'_>,
    no_fail_fast: bool,
    args: &[&str],
    compilation: &Compilation<'_>,
    session: &str,
    retained: bool,
    plan_path: &Path,
) -> CargoResult<PreparedTests> {
    if !retained && ws.gctx().build_config()?.test_jobs.unwrap_or(1) != 1 {
        anyhow::bail!("prepared authenticated execution does not yet support concurrent harnesses");
    }
    reject_unbound_test_native_dirs(&compilation.native_dirs)?;
    let worker_budget = worker_budget::WorkerBudget::managed(ws.gctx())?;
    if compilation.tests.len() > 4096 {
        anyhow::bail!("too many prepared test harnesses");
    }
    // Trust: the per-case result channel (`trust_test_execution::results`).
    // `--logfile` is Targo's: a test argument cannot redirect it.
    if args.iter().any(|arg| wire::results::is_logfile_arg(arg)) {
        anyhow::bail!(
            "`--logfile` names Targo's per-case test result channel; a test argument cannot set it"
        );
    }
    if !compilation.tests.is_empty() {
        wire::results::create_results_dir(plan_path)
            .context("cannot create the private test results directory")?;
    }
    let mut tests = Vec::new();
    let mut remaining = wire::MAX_PLAN_BYTES as usize;
    let mut outputs = compilation.tests.iter().collect::<Vec<_>>();
    outputs.sort_by(|left, right| {
        left.unit
            .cmp(&right.unit)
            .then_with(|| left.path.cmp(&right.path))
    });
    for output in outputs {
        let unit = &output.unit;
        reject_unharnessed_certified_test_target(true, unit.target.harness(), unit.target.name())?;
        if compilation.target_runner(unit.kind).is_some() {
            anyhow::bail!("prepared test export refuses custom runners");
        }
        reject_unbound_test_loader_env(output.script_metas.as_deref(), &compilation.extra_env)?;
        // Trust: this harness's own result file, FIRST, sealed with the plan:
        // a test argument after it (`--`, a value-taking `--skip`) cannot
        // swallow it (`trust_test_execution::results`).
        let results =
            HarnessResultFiles::for_harness(plan_path, tests.len()).map_err(anyhow::Error::msg)?;
        let harness_args = results.harness_args(args);
        let harness_args = harness_args.iter().map(String::as_str).collect::<Vec<_>>();
        let (_, mut command) = cmd_builds(
            ws.gctx(),
            ws.gctx().cwd(),
            unit,
            &output.path,
            output.script_metas.as_ref(),
            &output.env,
            &harness_args,
            compilation,
            "unittests",
        )?;
        anyhow::ensure!(
            command
                .get_args()
                .take(2)
                .eq(results.libtest_args().iter().map(std::ffi::OsStr::new)),
            "prepared test arguments must open with the per-case result channel"
        );
        strip_test_execution_authority_env(&mut command);
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        super::auth_scheduling::remove_transport_environment(&mut command);
        if retained {
            anyhow::ensure!(
                !args.iter().any(|arg| arg.starts_with("--test-threads")),
                "retained test actions own libtest's thread budget"
            );
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            super::auth_scheduling::prepare_retained_environment(&mut command);
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            anyhow::bail!("retained authenticated test environments require Linux or macOS");
        } else if let Some(budget) = worker_budget {
            budget.apply(&mut command, args)?;
        }
        if command.get_arg0().is_some() {
            anyhow::bail!("prepared tests do not support an overridden argv[0]");
        }
        let executable = output.path.canonicalize()?;
        if Path::new(command.get_program()).canonicalize()? != executable {
            anyhow::bail!("prepared test command differs from its compiled artifact");
        }
        let (sha256, size) = exact_regular_test_executable_identity(&executable)?;
        let utf8 = |value: &std::ffi::OsStr| {
            value
                .to_str()
                .map(str::to_owned)
                .ok_or_else(|| anyhow::anyhow!("prepared tests require UTF-8 command inputs"))
        };
        let captured = cargo_util::EnvironmentInputs::capture_effective(&command)?;
        for size in captured
            .iter()
            .flat_map(|(name, value)| [name.len(), value.len()])
            .chain(command.get_args().map(|arg| arg.len()))
        {
            remaining = remaining.checked_sub(size).ok_or_else(|| {
                anyhow::anyhow!("prepared test inputs exceed their aggregate bound")
            })?;
        }
        let environment = captured
            .iter()
            .map(|(name, value)| Ok((utf8(name)?, utf8(value)?)))
            .collect::<CargoResult<BTreeMap<_, _>>>()?;
        tests.push(PreparedTest {
            target: unit.target.name().into(),
            executable: utf8(executable.as_os_str())?,
            sha256,
            size,
            cwd: utf8(command.get_cwd().unwrap_or(ws.gctx().cwd()).as_os_str())?,
            args: command
                .get_args()
                .map(|arg| utf8(arg))
                .collect::<CargoResult<Vec<_>>>()?,
            env: environment,
            results: Some(results),
        });
    }
    let plan = PreparedTests {
        schema: wire::PLAN_SCHEMA.into(),
        session: session.into(),
        host_os: std::env::consts::OS.into(),
        host_arch: std::env::consts::ARCH.into(),
        target_directory: ws
            .target_dir()
            .into_path_unlocked()
            .canonicalize()?
            .to_string_lossy()
            .into_owned(),
        no_fail_fast,
        tests,
    };
    let expected = plan
        .tests
        .iter()
        .map(|test| (test.executable.clone(), (test.sha256.clone(), test.size)))
        .collect();
    plan.validate(session, &expected)
        .map_err(anyhow::Error::msg)?;
    Ok(plan)
}

/// Called before workspace discovery and compiler probing. Only the existing
/// authenticated frontend handoff can authorize this execution-only branch.
pub fn try_run_prepared_tests(gctx: &GlobalContext) -> Result<bool, CliError> {
    if gctx.has_retained_test() {
        if [
            TRUST_TARGO_PREPARED_TEST_SESSION,
            TRUST_TARGO_TEST_EXECUTION_MANIFEST,
            TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256,
        ]
        .iter()
        .any(|key| gctx.get_env_os(key).is_some())
        {
            return Err(anyhow::anyhow!(
                "retained execution refuses legacy environment-selected authority"
            )
            .into());
        }
        return Ok(false);
    }
    if [
        TRUST_TARGO_PREPARED_TEST_SESSION,
        TRUST_TARGO_TEST_EXECUTION_MANIFEST,
        TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256,
    ]
    .iter()
    .all(|key| gctx.get_env_os(key).is_none())
    {
        return Ok(false);
    }
    if !crate::is_targo_invocation() || !crate::trust_verified_targo() {
        return Err(
            anyhow::anyhow!("prepared execution requires authenticated verified Targo").into(),
        );
    }
    let authority = load_test_execution_authority(gctx)?
        .ok_or_else(|| anyhow::anyhow!("prepared test authority is absent"))?;
    let plan = authority.prepared.as_ref().ok_or_else(|| {
        anyhow::anyhow!(
            "verified test execution requires a native prepared plan; rebuild the Targo companions"
        )
    })?;
    let expected = authority
        .executables
        .iter()
        .map(|(path, entry)| {
            (
                path.to_string_lossy().into_owned(),
                (entry.sha256.clone(), entry.size),
            )
        })
        .collect();
    let session = gctx.get_env(TRUST_TARGO_PREPARED_TEST_SESSION)?;
    plan.validate(&session, &expected)
        .map_err(anyhow::Error::msg)?;
    if let Err(error) = execute(gctx, &authority, plan) {
        let code = fail_fast_code(&error);
        return Err(CliError::new(error, code));
    }
    Ok(true)
}

fn execute(
    gctx: &GlobalContext,
    authority: &TestExecutionAuthority,
    plan: &PreparedTests,
) -> CargoResult<()> {
    // Check the entire population before the first user process. Changing the
    // allocation between phases requires a new authorized plan, not silently
    // modifying the commands whose bytes the frontend accepted.
    if let Some(budget) = worker_budget::WorkerBudget::managed(gctx)? {
        for test in &plan.tests {
            let args = test.args.iter().map(String::as_str).collect::<Vec<_>>();
            budget
                .validate_prepared(&args, test.env.get("RUST_TEST_THREADS").map(String::as_str))?;
        }
    }
    let scope = cargo_util::StreamingProcessScope::new()?;
    let mut failed = false;
    for test in &plan.tests {
        if cancelled(gctx, &scope) {
            anyhow::bail!("prepared test execution interrupted before the next harness");
        }
        let path = Path::new(&test.executable);
        authority.validate_executable(path)?;
        let mut command = ProcessBuilder::new(path);
        command
            .args(&test.args)
            .cwd(&test.cwd)
            .environment_snapshot(cargo_util::EnvironmentInputs::from_variables(
                test.env
                    .iter()
                    .map(|(key, value)| (OsString::from(key), OsString::from(value))),
            )?);
        strip_test_execution_authority_env(&mut command);
        command.supervised_by(&scope);
        gctx.shell().status("Running", &test.target)?;
        let result = execute_authenticated_test_with_cancel(authority, path, &command, &mut || {
            cancelled(gctx, &scope)
        });
        // The post-execution substitution check runs before the exit record
        // is written, so a harness whose pathname was replaced after the run
        // never has its exit recorded as an exit.
        let validated = authority.validate_executable(path);
        let recorded = record_harness_end(&plan.session, test, &result, &validated);
        if let Err(error) = result.and(recorded) {
            failed = true;
            gctx.shell().error(&error)?;
            if !plan.no_fail_fast {
                return Err(error);
            }
        }
        validated?;
    }
    if cancelled(gctx, &scope) {
        anyhow::bail!(
            "prepared test execution interrupted: {}",
            gctx.root_cancellation_reason()
        );
    }
    scope.finish()?;
    if failed {
        anyhow::bail!("one or more prepared test harnesses failed");
    }
    Ok(())
}

/// Trust: record how one harness ended beside its result file, so the
/// frontend can tell a complete libtest result file from one a crash, a kill
/// or a timeout cut short (`trust_test_execution::results`). Only an exit the
/// harness process itself made, as the top of `result`'s error chain, is an
/// exit (the rule `exit_that_is_the_whole_error` keeps for the exit status);
/// anything else (cancellation, a refused launch, a failed wait, an
/// authentication failure during the run, a reason Targo put above the
/// process's exit) is recorded as no observed exit. So is every outcome when
/// `validated`, the post-execution check that the authorized pathname still
/// names the authorized bytes, failed. A plan without result files records
/// nothing; an exit record already on disk is an error, never overwritten.
pub(super) fn record_harness_end(
    session: &str,
    test: &PreparedTest,
    result: &CargoResult<()>,
    validated: &CargoResult<()>,
) -> CargoResult<()> {
    let Some(files) = &test.results else {
        return Ok(());
    };
    let end = match (validated, result) {
        (Err(_), _) => HarnessEnd::NotObserved {
            reason: "the harness executable failed native Targo's post-execution check".into(),
        },
        (Ok(()), Ok(())) => HarnessEnd::Exited { code: 0 },
        (Ok(()), Err(error)) => match error
            .chain()
            .next()
            .and_then(|top| top.downcast_ref::<ProcessError>())
        {
            Some(ProcessError {
                code: Some(code), ..
            }) => HarnessEnd::Exited { code: *code },
            Some(ProcessError {
                signal: Some(signal),
                ..
            }) => HarnessEnd::Signaled { signal: *signal },
            _ => HarnessEnd::NotObserved {
                reason: "native Targo observed no exit status of the harness".into(),
            },
        },
    };
    wire::results::write_exit(
        Path::new(&files.exit),
        &HarnessExit {
            schema: wire::results::HARNESS_EXIT_SCHEMA.into(),
            session: session.into(),
            executable: test.executable.clone(),
            sha256: test.sha256.clone(),
            logfile: files.logfile.clone(),
            end,
        },
    )
    .with_context(|| format!("cannot record how test harness `{}` ended", test.target))
}

pub(super) fn cancelled(gctx: &GlobalContext, scope: &cargo_util::StreamingProcessScope) -> bool {
    if gctx.poll_root_cancellation() {
        // This sticky gate stops future harness dispatch before acknowledging
        // the controller. The acknowledgement is not a descendant-drain claim.
        scope.cancel();
        gctx.acknowledge_root_stopped();
    }
    scope.interrupted()
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests {
    use super::*;

    #[test]
    fn a_harness_end_is_recorded_only_as_the_harness_process_itself_ended() {
        let root = tempfile::tempdir().unwrap();
        let plan_path = root.path().join("prepared-tests.json");
        wire::results::create_results_dir(&plan_path).unwrap();
        let test_with = |index: usize, results: bool| PreparedTest {
            target: "recorded-image".into(),
            executable: "/authorized/test-image".into(),
            sha256: "ab".repeat(32),
            size: 1,
            cwd: root.path().to_str().unwrap().into(),
            args: Vec::new(),
            env: Default::default(),
            results: results.then(|| HarnessResultFiles::for_harness(&plan_path, index).unwrap()),
        };
        let exit = |code: Option<i32>, signal: Option<i32>| -> anyhow::Error {
            ProcessError {
                desc: "process didn't exit successfully".into(),
                code,
                signal,
                stdout: None,
                stderr: None,
            }
            .into()
        };
        let passed: CargoResult<()> = Ok(());
        let refused: CargoResult<()> = Err(anyhow::anyhow!("authorized bytes were substituted"));
        let not_observed = |end: &HarnessEnd| matches!(end, HarnessEnd::NotObserved { .. });
        let cases: Vec<(
            CargoResult<()>,
            &CargoResult<()>,
            &dyn Fn(&HarnessEnd) -> bool,
        )> = vec![
            (Ok(()), &passed, &|end| {
                *end == HarnessEnd::Exited { code: 0 }
            }),
            (Err(exit(Some(101), None)), &passed, &|end| {
                *end == HarnessEnd::Exited { code: 101 }
            }),
            (Err(exit(None, Some(6))), &passed, &|end| {
                *end == HarnessEnd::Signaled { signal: 6 }
            }),
            // Not the process's own exit: a reason Targo put above it, a
            // launch or wait failure, or a refused post-execution check.
            (
                Err(exit(Some(101), None).context("streaming stdout exceeds its limit")),
                &passed,
                &not_observed,
            ),
            (
                Err(anyhow::anyhow!(
                    "authenticated test cancelled before resume"
                )),
                &passed,
                &not_observed,
            ),
            (Ok(()), &refused, &not_observed),
            (Err(exit(Some(101), None)), &refused, &not_observed),
        ];
        for (index, (result, validated, expected)) in cases.into_iter().enumerate() {
            let test = test_with(index, true);
            record_harness_end("session", &test, &result, validated).unwrap();
            let files = test.results.as_ref().unwrap();
            let record = wire::results::read_exit(Path::new(&files.exit)).unwrap();
            assert!(expected(&record.end), "case {index}: {:?}", record.end);
            assert_eq!(record.schema, wire::results::HARNESS_EXIT_SCHEMA);
            assert_eq!(record.session, "session");
            assert_eq!(record.executable, test.executable);
            assert_eq!(record.sha256, test.sha256);
            assert_eq!(record.logfile, files.logfile);
            // A second record for the same harness is an error; the first stays.
            assert!(record_harness_end("other", &test, &Ok(()), &Ok(())).is_err());
            assert_eq!(
                wire::results::read_exit(Path::new(&files.exit)).unwrap(),
                record
            );
        }
        // A plan without the channel writes nothing.
        let before = fs::read_dir(wire::results::results_dir(&plan_path).unwrap())
            .unwrap()
            .count();
        record_harness_end("session", &test_with(99, false), &Ok(()), &Ok(())).unwrap();
        let after = fs::read_dir(wire::results::results_dir(&plan_path).unwrap())
            .unwrap()
            .count();
        assert_eq!(before, after);
        assert!(
            !Path::new(
                &HarnessResultFiles::for_harness(&plan_path, 99)
                    .unwrap()
                    .exit
            )
            .exists()
        );
    }

    #[test]
    fn ambient_execution_authority_cannot_enter_prepared_execution() {
        for name in [
            TRUST_TARGO_PREPARED_TEST_SESSION,
            TRUST_TARGO_TEST_EXECUTION_MANIFEST,
            TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256,
        ] {
            let mut context = GlobalContext::default().unwrap();
            context.set_env(
                [(name.to_owned(), "forged".to_owned())]
                    .into_iter()
                    .collect(),
            );
            let error = try_run_prepared_tests(&context).unwrap_err();
            assert!(
                error
                    .error
                    .unwrap()
                    .to_string()
                    .contains("authenticated verified Targo")
            );
        }
        let mut context = GlobalContext::default().unwrap();
        context.set_env(Default::default());
        assert!(!try_run_prepared_tests(&context).unwrap());
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the authorized payload must inspect its actual inherited authorization and thread limits without a workspace or compiler context"
    )]
    fn prepared_child_fixture() {
        if let Ok(value) = std::env::var("CARGO_PREPARED_FIXTURE") {
            assert_eq!(value, "authorized");
            assert!(std::env::current_dir().unwrap().is_absolute());
            assert!(std::env::var_os("TRUST_TARGO_VERIFY").is_none());
            if let Ok(expected) = std::env::var("CARGO_PREPARED_EXPECT_THREADS") {
                assert_eq!(std::env::var("RUST_TEST_THREADS").unwrap(), expected);
            }
            if let Some(marker) = std::env::var_os("CARGO_PREPARED_STARTED_MARKER") {
                fs::write(marker, b"started").unwrap();
            }
        }
    }

    #[test]
    fn prepared_execution_uses_authorized_bytes_without_a_workspace_or_compiler() {
        let root = tempfile::tempdir().unwrap();
        let executable = root.path().join("test-image");
        fs::copy(std::env::current_exe().unwrap(), &executable).unwrap();
        let executable = executable.canonicalize().unwrap();
        let (sha256, size) = exact_regular_test_executable_identity(&executable).unwrap();
        let path = executable.to_str().unwrap().to_owned();
        let command = PreparedTest {
            target: "prepared-image".into(),
            executable: path.clone(),
            sha256: sha256.clone(),
            size,
            cwd: root.path().to_str().unwrap().into(),
            args: vec![
                "--exact".into(),
                "ops::cargo_test::prepared::tests::prepared_child_fixture".into(),
            ],
            env: [
                ("CARGO_PREPARED_FIXTURE".into(), "authorized".into()),
                ("CARGO_PREPARED_EXPECT_THREADS".into(), "1".into()),
                ("RUST_TEST_THREADS".into(), "1".into()),
            ]
            .into_iter()
            .collect(),
            results: None,
        };
        let plan = PreparedTests {
            schema: wire::PLAN_SCHEMA.into(),
            session: "current".into(),
            host_os: std::env::consts::OS.into(),
            host_arch: std::env::consts::ARCH.into(),
            target_directory: root.path().canonicalize().unwrap().to_str().unwrap().into(),
            no_fail_fast: false,
            tests: vec![command],
        };
        let authority = TestExecutionAuthority {
            executables: [(
                executable.clone(),
                TestExecutionAuthorityEntry {
                    target: "prepared-image".into(),
                    path: path.clone(),
                    sha256: sha256.clone(),
                    size,
                },
            )]
            .into_iter()
            .collect(),
            prepared: Some(plan.clone()),
        };
        plan.validate("current", &[(path, (sha256, size))].into_iter().collect())
            .unwrap();
        let mut context = GlobalContext::default().unwrap();
        context.set_env(
            [
                ("BUILD_SLOT_HELD".into(), "1".into()),
                ("CARGO_BUILD_JOBS".into(), "1".into()),
            ]
            .into_iter()
            .collect(),
        );
        execute(&context, &authority, &plan).unwrap();
        fs::write(&executable, b"replaced").unwrap();
        assert!(execute(&context, &authority, &plan).is_err());
    }

    #[test]
    fn prepared_budget_drift_blocks_the_whole_population_before_launch() {
        let root = tempfile::tempdir().unwrap();
        let root_path = root.path().canonicalize().unwrap();
        let marker = root_path.join("started");
        let mut tests = Vec::new();
        let mut executables = BTreeMap::new();
        for (name, threads) in [("first", "1"), ("later", "3")] {
            let executable = root_path.join(name);
            fs::copy(std::env::current_exe().unwrap(), &executable).unwrap();
            let (sha256, size) = exact_regular_test_executable_identity(&executable).unwrap();
            let path = executable.to_str().unwrap().to_owned();
            tests.push(PreparedTest {
                target: name.into(),
                executable: path.clone(),
                sha256: sha256.clone(),
                size,
                cwd: root_path.to_str().unwrap().into(),
                args: vec![
                    "--exact".into(),
                    "ops::cargo_test::prepared::tests::prepared_child_fixture".into(),
                ],
                env: [
                    ("CARGO_PREPARED_FIXTURE".into(), "authorized".into()),
                    (
                        "CARGO_PREPARED_STARTED_MARKER".into(),
                        marker.to_str().unwrap().into(),
                    ),
                    ("RUST_TEST_THREADS".into(), threads.into()),
                ]
                .into_iter()
                .collect(),
                results: None,
            });
            executables.insert(
                executable,
                TestExecutionAuthorityEntry {
                    target: name.into(),
                    path,
                    sha256,
                    size,
                },
            );
        }
        let mut plan = PreparedTests {
            schema: wire::PLAN_SCHEMA.into(),
            session: "current".into(),
            host_os: std::env::consts::OS.into(),
            host_arch: std::env::consts::ARCH.into(),
            target_directory: root_path.to_str().unwrap().into(),
            no_fail_fast: true,
            tests,
        };
        let expected = plan
            .tests
            .iter()
            .map(|test| (test.executable.clone(), (test.sha256.clone(), test.size)))
            .collect();
        plan.validate("current", &expected).unwrap();
        let authority = TestExecutionAuthority {
            executables,
            prepared: Some(plan.clone()),
        };
        let mut context = GlobalContext::default().unwrap();
        context.set_env(
            [
                ("BUILD_SLOT_HELD".into(), "1".into()),
                ("CARGO_BUILD_JOBS".into(), "2".into()),
            ]
            .into_iter()
            .collect(),
        );
        let error = execute(&context, &authority, &plan).unwrap_err();
        assert!(error.to_string().contains("exceeding the admitted ceiling"));
        assert!(
            !marker.exists(),
            "a later invalid harness must prevent the earlier launch"
        );

        plan.tests[1].env.remove("RUST_TEST_THREADS");
        assert!(execute(&context, &authority, &plan).is_err());
        assert!(!marker.exists());
        plan.tests[1]
            .env
            .insert("RUST_TEST_THREADS".into(), "1".into());
        plan.tests[1].args.push("--test-threads=3".into());
        assert!(execute(&context, &authority, &plan).is_err());
        assert!(!marker.exists());
    }

    #[test]
    fn private_root_cancel_and_disconnect_stop_running_and_queued_harnesses() {
        use super::super::authenticated_lifecycle::{assert_child_stopped, image};
        use std::io::{Read as _, Write as _};
        use std::os::unix::net::UnixStream;
        use std::time::{Duration, Instant};

        for explicit_cancel in [true, false] {
            let root = tempfile::tempdir().unwrap();
            let root = root.path().canonicalize().unwrap();
            let (mut authority, executable, command) = image(&root, "wait");
            let first_entry = authority.executables.get(&executable).unwrap();
            let first = PreparedTest {
                target: "running".into(),
                executable: executable.to_str().unwrap().into(),
                sha256: first_entry.sha256.clone(),
                size: first_entry.size,
                cwd: root.to_str().unwrap().into(),
                args: command
                    .get_args()
                    .map(|arg| arg.to_str().unwrap().to_owned())
                    .collect(),
                env: command
                    .get_envs()
                    .iter()
                    .filter_map(|(key, value)| {
                        value
                            .as_ref()
                            .map(|value| (key.clone(), value.to_str().unwrap().to_owned()))
                    })
                    .collect(),
                results: None,
            };
            let queued_path = root.join("queued-image");
            fs::copy(&executable, &queued_path).unwrap();
            let (sha256, size) = exact_regular_test_executable_identity(&queued_path).unwrap();
            authority.executables.insert(
                queued_path.clone(),
                TestExecutionAuthorityEntry {
                    target: "queued".into(),
                    path: queued_path.to_str().unwrap().into(),
                    sha256: sha256.clone(),
                    size,
                },
            );
            let queued = PreparedTest {
                target: "queued".into(),
                executable: queued_path.to_str().unwrap().into(),
                sha256,
                size,
                cwd: root.to_str().unwrap().into(),
                args: vec![
                    "--exact".into(),
                    "ops::cargo_test::prepared::tests::prepared_child_fixture".into(),
                ],
                env: [
                    ("CARGO_PREPARED_FIXTURE".into(), "authorized".into()),
                    (
                        "CARGO_PREPARED_STARTED_MARKER".into(),
                        root.join("queued-started").to_str().unwrap().into(),
                    ),
                ]
                .into_iter()
                .collect(),
                results: None,
            };
            let plan = PreparedTests {
                schema: wire::PLAN_SCHEMA.into(),
                session: "private-control".into(),
                host_os: std::env::consts::OS.into(),
                host_arch: std::env::consts::ARCH.into(),
                target_directory: root.to_str().unwrap().into(),
                no_fail_fast: true,
                tests: vec![first, queued],
            };
            let expected = plan
                .tests
                .iter()
                .map(|test| (test.executable.clone(), (test.sha256.clone(), test.size)))
                .collect();
            plan.validate("private-control", &expected).unwrap();
            let (endpoint, mut controller) = UnixStream::pair().unwrap();
            controller
                .set_read_timeout(Some(Duration::from_secs(10)))
                .unwrap();
            let mut context = GlobalContext::default().unwrap();
            context.set_env(Default::default());
            context
                .install_root_control(
                    crate::context::root_control::RootControl::for_test(endpoint).unwrap(),
                )
                .unwrap();
            let pidfile = root.join("child-pid");
            let result = std::thread::scope(|threads| {
                let request = threads.spawn(|| {
                    let deadline = Instant::now() + Duration::from_secs(10);
                    while !pidfile.exists() && Instant::now() < deadline {
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    let started = pidfile.exists();
                    if explicit_cancel {
                        controller.write_all(b"C").unwrap();
                        let mut acknowledged = [0];
                        controller.read_exact(&mut acknowledged).unwrap();
                        assert_eq!(&acknowledged, b"A");
                    }
                    drop(controller);
                    started
                });
                let result = execute(&context, &authority, &plan);
                assert!(
                    request.join().unwrap(),
                    "private-control harness did not start"
                );
                result
            });
            assert!(
                result.is_err(),
                "private cancellation cannot become success"
            );
            assert!(
                !root.join("queued-started").exists(),
                "queued harness ran after cancellation"
            );
            assert_child_stopped(&pidfile);
        }
    }
}
