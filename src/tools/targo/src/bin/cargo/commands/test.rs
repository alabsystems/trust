#[path = "test/child_policy.rs"]
mod child_policy;

use crate::command_prelude::*;
use targo::ops;
use targo::util::CargoResult;

pub fn cli() -> Command {
    let command = subcommand("test")
        // Subcommand aliases are handled in `aliased_command()`.
        // .alias("t")
        .about("Execute all unit and integration tests and build examples of a local package")
        .arg(
            Arg::new("TESTNAME")
                .action(ArgAction::Set)
                .help("If specified, only run tests containing this string in their names"),
        )
        .arg(
            Arg::new("args")
                .value_name("ARGS")
                .help("Arguments for the test binary")
                .num_args(0..)
                .last(true),
        )
        .arg(flag("no-run", "Compile, but don't run tests"))
        .arg(
            Arg::new("resource-child-policy")
                .long("resource-child-policy")
                .hide(true)
                .num_args(1)
                .conflicts_with_all(["doc", "__retained-test-session"])
                .value_parser(clap::builder::ValueParser::new(child_policy::parse)),
        )
        .arg(
            flag(
                "__retained-test-session",
                "Private retained verified test session",
            )
            .hide(true)
            .requires("no-run"),
        )
        .arg(flag("no-fail-fast", "Run all tests regardless of failure"))
        // Trust: strengthen the resolved test inventory without narrowing it.
        .arg(
            Arg::new("require-test-bin")
                .long("require-test-bin")
                .value_name("NAME")
                .action(ArgAction::Append)
                .conflicts_with("no-run")
                .help("Require a selected native binary test harness to report passing tests"),
        )
        .arg_future_incompat_report()
        .arg_message_format()
        .arg(
            flag(
                "quiet",
                "Display one character per test instead of one line",
            )
            .short('q'),
        )
        .arg_package_spec(
            "Package to run tests for",
            "Test all packages in the workspace",
            "Exclude packages from the test",
        )
        .arg_targets_all(
            "Test only this package's library",
            "Test only the specified binary",
            "Test all binaries",
            "Test only the specified example",
            "Test all examples",
            "Test only the specified test target",
            "Test all targets that have `test = true` set",
            "Test only the specified bench target",
            "Test all targets that have `bench = true` set",
            "Test all targets (does not include doctests)",
        )
        .arg(
            flag("doc", "Test only this library's documentation")
                .help_heading(heading::TARGET_SELECTION),
        )
        .arg_features();
    // Trust: the native graph distinguishes failed compilation prerequisites
    // from failed test actions. Cargo compatibility retains upstream syntax.
    let command = if targo::is_targo_invocation() {
        // Trust: one invocation for several requests; only the branded
        // frontend has it (`targo::ops::test_plan`).
        command
            .mut_arg("resource-child-policy", |arg| arg.conflicts_with("plan"))
            .arg_parallel()
            .arg(
                opt(
                    "plan",
                    "Build and run the requests of a test plan file in one graph",
                )
                .value_name("FILE"),
            )
            .arg(
                multi_opt(
                    "request",
                    "ID",
                    "Narrow the plan to this request (default: every request)",
                )
                .requires("plan"),
            )
            // Trust: what changed, from which a plan run selects its
            // requests; with a plan, `-p` names members the change reaches.
            .arg(
                opt(
                    "changed-paths",
                    "Select the plan's requests from the changed paths in FILE (`-` for stdin), \
                     NUL- or newline-separated and relative to the workspace root",
                )
                .value_name("FILE")
                .requires("plan"),
            )
            // Trust: the change as git ranges, diffed by Targo itself.
            .arg(
                multi_opt(
                    "changed-range",
                    "RANGE",
                    "Select the plan's requests from the paths git says RANGE changed \
                     (`A..B`: the two trees; `A...B`: since the merge base)",
                )
                .requires("plan"),
            )
            .arg(
                opt(
                    "changed-pushed-refs",
                    "Select the plan's requests from the refs being pushed, as git gives them \
                     to a pre-push hook, in FILE (`-` for stdin)",
                )
                .value_name("FILE")
                .requires("plan"),
            )
            // Trust: a member or `[[workspace]]` the change reaches, by its
            // directory; an unknown one is refused.
            .arg(
                multi_opt(
                    "reached",
                    "DIR",
                    "Also test the plan member or `[[workspace]]` in DIR, from the workspace root",
                )
                .requires("plan"),
            )
            .arg(
                flag(
                    "whole-plan",
                    "Run every request of the plan, whatever changed",
                )
                .requires("plan"),
            )
            // Trust: what the plan selects for the change, as one JSON
            // line, and nothing built: for a caller that plans around the
            // lane and must not keep a copy of its rules.
            .arg(
                flag(
                    "select-only",
                    "Print the plan's selection for the change as one JSON record; build and run nothing",
                )
                .requires("plan")
                .conflicts_with_all(["no-run", "unit-graph", "run-after"]),
            )
            // Trust: the plan's one graph against its requests' own.
            .arg(
                flag(
                    "unit-graph-parity",
                    "Check that the plan's unit graph is the union of its requests' standalone graphs; build and run nothing",
                )
                .requires("plan")
                .conflicts_with_all(["no-run", "unit-graph", "run-after", "select-only"]),
            )
            // Trust: a caller that overlaps the build with work the tests
            // depend on holds the tests at a barrier file.
            .arg(
                opt(
                    "run-after",
                    "Build, and start no test executable until FILE says `run`",
                )
                .value_name("FILE")
                .requires("plan"),
            )
            .arg(
                opt(
                    "run-after-owner",
                    "The process that writes the --run-after file; the run stops once it is gone",
                )
                .value_name("PID")
                .requires("run-after"),
            )
    } else {
        command.arg_jobs().arg_unsupported_keep_going()
    };
    command
        .arg_release("Build artifacts in release mode, with optimizations")
        .arg_profile("Build artifacts with the specified profile")
        .arg_target_tuple("Build for the target tuple")
        .arg_target_dir()
        .arg_unit_graph()
        .arg_timings()
        .arg_manifest_path()
        .arg_ignore_rust_version()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer_with_invocation(
            "test",
            "test -- --help",
            "for test binary options",
        ))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    // Trust: a plan run's exit status says how it ended, and with JSON
    // messages its last record says the same (`ops::test_plan_outcome`):
    // 101 for red tests or a red build, 2 for a run that judged nothing,
    // 3 for one Targo stopped for time.
    // The path as every other record of the run spells it: from the
    // working directory, never as typed.
    let plan = args
        .value_of_path("plan", gctx)
        .map(|path| path.to_string_lossy().into_owned());
    let mut result = exec_tests(gctx, args);
    // Trust: a run Targo stopped (a signal, a bound) never exits 0
    // (`ops::test_plan_outcome::ended`).
    if plan.is_some() {
        result = ops::test_plan_outcome::ended(result);
    }
    let (Some(plan), Err(error)) = (plan, &result) else {
        return result;
    };
    // A run Targo stopped ends as the stop says, whatever error the stop
    // surfaced as. Otherwise an error is marked with how it ended, and an
    // unmarked one is red: 101 whatever status it was raised with, so that
    // a test executable that itself exits 2 or 3 is never read as a run
    // that judged nothing or ran out of time.
    let outcome = ops::test_plan_outcome::stopped()
        .map(|(outcome, _)| outcome)
        .or_else(|| {
            error
                .error
                .as_ref()
                .and_then(ops::test_plan_outcome::marked)
        })
        .unwrap_or(ops::test_plan_outcome::Outcome::Failed);
    let status = outcome.exit_status();
    let json = args
        ._values_of("message-format")
        .iter()
        .any(|format| format.split(',').any(|part| part.starts_with("json")));
    ops::test_plan_outcome::close(gctx, json, &plan, outcome, error.error.as_ref());
    let Err(error) = result else { unreachable!() };
    Err(CliError {
        exit_code: status,
        ..error
    })
}

pub(crate) enum NativeBudgetCheck {
    Allowed,
    ExistingBoundary,
}

/// Select the same root targets and runners as execution before accepting the
/// native argument boundary. Literal/no-cfg selection does not query a compiler;
/// matching cfg runners use the existing metadata borrower. No dependency
/// resolution, compilation or execution grant is constructed here.
pub(crate) fn native_budget_check(
    gctx: &GlobalContext,
    args: &ArgMatches,
) -> CargoResult<NativeBudgetCheck> {
    let words = args
        .get_one::<String>("TESTNAME")
        .into_iter()
        .chain(args.get_many::<String>("args").unwrap_or_default())
        .map(String::as_str)
        .collect::<Vec<_>>();
    let conflict = ops::validate_native_test_arguments(&words).err();
    if args.flag("no-run") || args.flag("doc") || args.value_of_path("plan", gctx).is_some() {
        return Ok(if conflict.is_some() {
            NativeBudgetCheck::ExistingBoundary
        } else {
            NativeBudgetCheck::Allowed
        });
    }
    let ws = args.workspace(gctx)?;
    let mut options =
        args.compile_options(gctx, UserIntent::Test, Some(&ws), ProfileChecking::Custom)?;
    configure_test_filter(args, &mut options)?;
    if ops::native_test_runner_scope(&ws, &options)? == ops::NativeTestRunnerScope::ExistingBoundary
    {
        return Ok(NativeBudgetCheck::ExistingBoundary);
    }
    let Some(conflict) = conflict else {
        return Ok(NativeBudgetCheck::Allowed);
    };
    let native_host = env!("RUST_HOST_TARGET");
    if options
        .build_config
        .requested_kinds
        .iter()
        .any(|kind| match kind {
            targo::compiler::CompileKind::Host => false,
            targo::compiler::CompileKind::Target(target) => {
                target.rustc_target().as_str() != native_host
            }
        })
    {
        return Ok(NativeBudgetCheck::ExistingBoundary);
    }
    match ops::native_test_argument_scope(&ws, &options)? {
        ops::NativeTestArgumentScope::Libtest => Err(conflict),
        ops::NativeTestArgumentScope::Other => Ok(NativeBudgetCheck::ExistingBoundary),
    }
}

fn configure_test_filter(args: &ArgMatches, options: &mut ops::CompileOptions) -> CargoResult<()> {
    if args.flag("doc") {
        anyhow::ensure!(
            !options.filter.is_specific(),
            "can't mix --doc with other target selecting options"
        );
        anyhow::ensure!(
            !args.flag("no-run"),
            "can't skip running doc tests with --no-run"
        );
        options.build_config.intent = UserIntent::Doctest;
        options.filter = ops::CompileFilter::lib_only();
    } else if args.get_one::<String>("TESTNAME").is_some() && !options.filter.is_specific() {
        // A named test excludes examples exactly as in actual execution.
        options.filter = ops::CompileFilter::all_test_targets();
    }
    Ok(())
}

fn exec_tests(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let child_supervision = args
        .get_one::<cargo_util::ChildSupervision>("resource-child-policy")
        .copied();
    // Trust: an authorized prepared plan executes without resolving or building again.
    // A new ordinary-only policy must refuse before that early execution path.
    if ops::try_run_prepared_tests(gctx, child_supervision)? {
        return Ok(());
    }
    // Trust: a plan owns package, feature and target selection; say so before
    // any of those flags is read.
    let plan = args.value_of_path("plan", gctx);
    // Trust: under a plan, a workspace or an invocation that cannot be read
    // judged no test.
    let unread = |error: anyhow::Error| match plan {
        Some(_) => ops::test_plan_outcome::cannot_judge(error),
        None => error,
    };
    // Trust: `mut` for the plan's feature scope below.
    let mut ws = args.workspace(gctx).map_err(unread)?;
    if plan.is_some() {
        refuse_plan_conflicts(args).map_err(|refusal| match refusal.error {
            Some(error) => CliError::new(
                ops::test_plan_outcome::cannot_judge(error),
                ops::test_plan_outcome::CANNOT_JUDGE,
            ),
            None => refusal,
        })?;
    }

    let mut compile_opts = args
        .compile_options(gctx, UserIntent::Test, Some(&ws), ProfileChecking::Custom)
        .map_err(unread)?;
    // Trust: whether a plan's selection performs any request of its own.
    let mut plan_performs = None;
    if let Some(plan) = plan {
        let only = args._values_of("request");
        let packages = args._values_of("package");
        let ranges = args._values_of("changed-range");
        let reached = args._values_of("reached");
        let run_after = args.value_of_path("run-after", gctx);
        let change = ops::test_plan::Change {
            paths: args.get_one::<String>("changed-paths").map(String::as_str),
            ranges: &ranges,
            pushed_refs: args
                .get_one::<String>("changed-pushed-refs")
                .map(String::as_str),
            packages: &packages,
            reached: &reached,
            whole: args.flag("whole-plan"),
            run_after: run_after.as_deref(),
            run_after_owner: args
                .get_one::<String>("run-after-owner")
                .map(String::as_str),
            select_only: args.flag("select-only"),
        };
        let performs = ops::test_plan::select(&mut ws, &mut compile_opts, &plan, &only, change)
            .map_err(|error| {
                // Trust: whatever refuses the selection judged nothing: a
                // changed path the plan does not account for, a range git cannot
                // diff, a reached directory the plan does not test, a plan that
                // does not fit the workspace. Told apart from a failed build or
                // test by its status.
                CliError::new(
                    ops::test_plan_outcome::cannot_judge(error),
                    ops::test_plan_outcome::CANNOT_JUDGE,
                )
            })?;
        // Trust: a listing is the selection and nothing after it.
        if args.flag("select-only") {
            return Ok(());
        }
        plan_performs = Some(performs);
    }

    let default_profile = gctx
        .build_config()?
        .profile
        .as_ref()
        .map(|p| p.as_ref())
        .unwrap_or_else(|| "test");
    compile_opts.build_config.requested_profile =
        args.get_profile_name(default_profile, ProfileChecking::Custom)?;

    // Trust: the parity of the plan's graph is a check of its own: no
    // phase, no build, no test.
    if args.flag("unit-graph-parity") {
        if plan_performs != Some(true) {
            return Err(CliError::new(
                ops::test_plan_outcome::cannot_judge(anyhow::format_err!(
                    "--unit-graph-parity: the selection performs no request, so there is no \
                     graph to compare; pass --whole-plan"
                )),
                ops::test_plan_outcome::CANNOT_JUDGE,
            ));
        }
        ops::test_plan_parity::check(&ws, &compile_opts)?;
        return Ok(());
    }

    // Trust: a plan's `[[tool]]` and `[[workspace]]` entries are built and
    // tested first, each under its own manifest. The tools' private copies
    // live until the plan's own tests have run.
    let _plan_tools = if let Some(performs) = plan_performs {
        let tools = ops::test_plan_phases::run(
            &ws,
            &mut compile_opts,
            args.flag("no-run"),
            args.flag("no-fail-fast"),
        )?;
        if !performs {
            // Trust: the selection performs no request; nothing more to build.
            ops::test_plan::idle(
                &ws,
                &compile_opts,
                args.flag("no-run"),
                args.flag("no-fail-fast"),
            )?;
            return Ok(());
        }
        Some(tools)
    } else {
        None
    };

    // `TESTNAME` is actually an argument of the test binary, but it's
    // important, so we explicitly mention it and reconfigure.
    let test_args = args.get_one::<String>("TESTNAME").into_iter();
    let test_args = test_args.chain(args.get_many::<String>("args").unwrap_or_default());
    let test_args = test_args.map(String::as_str).collect::<Vec<_>>();

    let no_run = args.flag("no-run");
    configure_test_filter(args, &mut compile_opts)?;

    let ops = ops::TestOptions {
        child_supervision,
        no_run,
        no_fail_fast: args.flag("no-fail-fast"),
        required_test_bins: args
            .get_many::<String>("require-test-bin")
            .into_iter()
            .flatten()
            .cloned()
            .collect(),
        compile_opts,
    };

    ops::run_tests(&ws, &ops, &test_args)
}

/// Trust: with `--plan` the plan names the packages, features, targets and
/// harness arguments of every request, so a flag that names any of them for
/// the whole invocation is refused rather than merged or ignored. `-p` is
/// read as selection instead: it names members whose requests run.
fn refuse_plan_conflicts(args: &ArgMatches) -> CliResult {
    const OWNED_BY_THE_PLAN: [(&str, &str); 20] = [
        ("features", "--features"),
        ("all-features", "--all-features"),
        ("no-default-features", "--no-default-features"),
        ("lib", "--lib"),
        ("bin", "--bin"),
        ("bins", "--bins"),
        ("example", "--example"),
        ("examples", "--examples"),
        ("test", "--test"),
        ("tests", "--tests"),
        ("bench", "--bench"),
        ("benches", "--benches"),
        ("all-targets", "--all-targets"),
        ("doc", "--doc"),
        ("TESTNAME", "a test name"),
        ("args", "arguments after `--`"),
        ("require-test-bin", "--require-test-bin"),
        ("exclude", "--exclude"),
        ("workspace", "--workspace"),
        ("all", "--all"),
        // `--package` is not here: with a plan it names the members a
        // change reaches (`targo::ops::test_plan_select`).
    ];
    if targo::trust_verified_targo() {
        return Err(anyhow::format_err!("--plan requires native unverified Targo").into());
    }
    for (id, spelling) in OWNED_BY_THE_PLAN {
        if args.value_source(id) == Some(clap::parser::ValueSource::CommandLine) {
            return Err(anyhow::format_err!(
                "--plan cannot be combined with {spelling}: the plan selects packages, \
                 features, targets and test arguments per request"
            )
            .into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod budget_tests {
    use super::*;

    fn fixture(config: &str) -> (tempfile::TempDir, GlobalContext) {
        let directory = tempfile::tempdir().unwrap();
        let cwd = directory.path().join("project");
        let home = directory.path().join("home");
        for path in [
            cwd.join("src"),
            cwd.join("tests"),
            cwd.join(".cargo"),
            home.clone(),
        ] {
            std::fs::create_dir_all(path).unwrap();
        }
        std::fs::write(cwd.join("Cargo.toml"),
            "[package]\nname='budget_scope'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[[test]]\nname='custom'\nharness=false\n[[test]]\nname='ordinary'\n").unwrap();
        std::fs::write(cwd.join("src/lib.rs"), "#[test] fn unit() {}\n").unwrap();
        std::fs::write(
            cwd.join("tests/ordinary.rs"),
            "#[test] fn integration() {}\n",
        )
        .unwrap();
        std::fs::write(cwd.join("tests/custom.rs"), "fn main() {}\n").unwrap();
        std::fs::write(cwd.join(".cargo/config.toml"), config).unwrap();
        let gctx = GlobalContext::new(cargo_util_terminal::Shell::new(), cwd, home);
        (directory, gctx)
    }

    fn parse(words: &[&str]) -> ArgMatches {
        cli()
            .try_get_matches_from(std::iter::once("test").chain(words.iter().copied()))
            .unwrap()
    }

    #[test]
    fn actual_test_selection_refuses_libtest_budget_but_preserves_custom_inputs() {
        let (_directory, gctx) = fixture("");
        for words in [
            vec!["--lib", "--", "--test-threads=1"],
            vec!["--test", "ord*", "--", "--test-threads", "1"],
        ] {
            let error = native_budget_check(&gctx, &parse(&words)).err().unwrap();
            assert!(error.is::<ops::NativeTestBudgetRefusal>(), "{error:#}");
        }
        assert!(matches!(
            native_budget_check(
                &gctx,
                &parse(&["--test", "custom", "--", "--test-threads=99"])
            )
            .unwrap(),
            NativeBudgetCheck::ExistingBoundary,
        ));
        assert!(matches!(
            native_budget_check(
                &gctx,
                &parse(&["--lib", "--", "--skip", "--test-threads=99"])
            )
            .unwrap(),
            NativeBudgetCheck::Allowed,
        ));
    }

    #[test]
    fn configured_runner_keeps_its_existing_argument_boundary() {
        let config = format!(
            "[target.{}]\nrunner='custom-runner'\n",
            env!("RUST_HOST_TARGET")
        );
        let (_directory, gctx) = fixture(&config);
        assert!(matches!(
            native_budget_check(&gctx, &parse(&["--lib", "--", "--test-threads=99"])).unwrap(),
            NativeBudgetCheck::ExistingBoundary,
        ));
        assert!(matches!(
            native_budget_check(&gctx, &parse(&["--lib"])).unwrap(),
            NativeBudgetCheck::ExistingBoundary,
        ));
        assert!(matches!(
            native_budget_check(&gctx, &parse(&["--lib", "--no-run"])).unwrap(),
            NativeBudgetCheck::Allowed,
        ));
        let foreign = if env!("RUST_HOST_TARGET") == "aarch64-apple-darwin" {
            "x86_64-unknown-linux-gnu"
        } else {
            "aarch64-apple-darwin"
        };
        let (_foreign_directory, foreign_gctx) =
            fixture(&format!("[target.{foreign}]\nrunner='foreign-runner'\n"));
        assert!(matches!(
            native_budget_check(&foreign_gctx, &parse(&["--lib"])).unwrap(),
            NativeBudgetCheck::Allowed,
        ));
        assert!(matches!(
            native_budget_check(&gctx, &parse(&["--lib", "--target", foreign])).unwrap(),
            NativeBudgetCheck::Allowed,
        ));
    }

    #[test]
    fn default_compile_only_examples_do_not_turn_custom_inputs_into_libtest_options() {
        let (directory, gctx) = fixture("");
        let cwd = directory.path().join("project");
        std::fs::write(cwd.join("Cargo.toml"),
            "[package]\nname='budget_scope'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[lib]\nharness=false\n[[test]]\nname='custom'\nharness=false\n").unwrap();
        std::fs::write(cwd.join("src/lib.rs"), "fn main() {}\n").unwrap();
        std::fs::remove_file(cwd.join("tests/ordinary.rs")).unwrap();
        std::fs::create_dir(cwd.join("examples")).unwrap();
        std::fs::write(cwd.join("examples/compile_only.rs"), "fn main() {}\n").unwrap();
        assert!(matches!(
            native_budget_check(&gctx, &parse(&["--", "--test-threads=99"])).unwrap(),
            NativeBudgetCheck::ExistingBoundary,
        ));
    }

    #[test]
    fn external_package_scope_is_unknown_without_dependency_resolution() {
        let (directory, gctx) = fixture("");
        let dependency = directory.path().join("dependency");
        std::fs::create_dir_all(dependency.join("src")).unwrap();
        std::fs::write(dependency.join("Cargo.toml"),
            "[package]\nname='external_scope'\nversion='0.0.0'\nedition='2024'\n[workspace]\n[lib]\nharness=false\n").unwrap();
        std::fs::write(dependency.join("src/lib.rs"), "fn main() {}\n").unwrap();
        let manifest = directory.path().join("project/Cargo.toml");
        let mut source = std::fs::read_to_string(&manifest).unwrap();
        source.push_str("[dependencies]\nexternal_scope={path='../dependency'}\n");
        std::fs::write(manifest, source).unwrap();
        assert!(matches!(
            native_budget_check(
                &gctx,
                &parse(&["-p", "external_scope", "--lib", "--", "--test-threads=99"])
            )
            .unwrap(),
            NativeBudgetCheck::ExistingBoundary,
        ));
    }
}
