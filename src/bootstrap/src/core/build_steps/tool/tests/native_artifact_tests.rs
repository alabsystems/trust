use super::*;

/// Trust: the Trust Cargo is built, restored and aliased as `targo` — never as
/// `cargo`. Until 2026-09-29 its package, its library and its one binary were
/// all named `cargo`, so every Trust build compiled `--crate-name cargo`; the
/// tool artifact in `stageN-tools-bin/` was a file called `cargo`; and sysroot
/// restoration copied whatever file carried that name to `bin/targo`. Nothing
/// tied the Trust name to the Trust package, so a stale upstream `cargo` in
/// that directory reached the sysroot as `targo` — one way to get the
/// "upstream cargo under the name targo" stage docs/BUILD_AND_INSTALL.md warns
/// about. Now the only file restoration will install as `targo` (or alias as
/// `cargo`) is the artifact the `targo` package builds.
#[test]
fn trust_cargo_is_built_restored_and_aliased_under_targo() {
    let manifest_path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tools/targo/Cargo.toml");
    let manifest: toml::Value = toml::from_str(
        &fs::read_to_string(&manifest_path)
            .unwrap_or_else(|error| panic!("read {}: {error}", manifest_path.display())),
    )
    .unwrap_or_else(|error| panic!("parse {}: {error}", manifest_path.display()));
    assert_eq!(
        manifest["package"]["name"].as_str(),
        Some("targo"),
        "the Trust Cargo package must be named `targo`, so no build compiles `--crate-name cargo`"
    );
    assert_eq!(
        manifest["lib"]["name"].as_str(),
        Some("targo"),
        "the Trust Cargo library crate must be named `targo`"
    );
    let bin_names: Vec<&str> = manifest["bin"]
        .as_array()
        .expect("the Trust Cargo manifest declares its binary explicitly")
        .iter()
        .map(|bin| bin["name"].as_str().expect("every [[bin]] has a name"))
        .collect();
    assert_eq!(bin_names, ["targo"], "the Trust Cargo package builds exactly one binary, `targo`");

    // Every tool selection that stages the frontend restores it from the
    // `targo` artifact; no restoration entry reads a `cargo`-named artifact.
    for tools in [
        None,
        Some(HashSet::from_iter(["targo".to_string()])),
        Some(HashSet::from_iter(["tippy".to_string()])),
        Some(tools_profile_default_tools()),
    ] {
        let bins = restored_sysroot_bins_for_tool_settings(true, tools.as_ref(), false, true);
        assert!(bins.contains(&("targo", "targo")), "{tools:?}: {bins:?}");
        assert!(
            bins.iter().all(|(source, _)| *source != "cargo"),
            "{tools:?}: a `cargo`-named tool artifact must never be restored: {bins:?}"
        );
    }

    // The `cargo` compatibility alias is a copy of the `targo` artifact, and
    // a `cargo`-named artifact has no alias to emit.
    assert_eq!(upstream_compat_bin_for_tool_source("targo"), Some("cargo"));
    assert_eq!(upstream_compat_bin_for_tool_source("cargo"), None);
}

/// Trust: `targo` is installed into a sysroot together with its `cargo` alias,
/// and a sysroot `bin/` that holds one without the other, or the two as
/// different bytes, is reported. From 0b37a090af (2026-11-10) the top stage's
/// `targo` was installed after the only pass that added the alias, so
/// `x.py build --stage 2` shipped `stage2/bin/targo` with no `cargo`; the
/// second directory below is that sysroot's shape.
#[test]
fn a_sysroot_targo_is_installed_and_checked_with_its_cargo_alias() {
    assert_eq!(sysroot_bin_names_for_tool_source("targo"), ["targo", "cargo"]);
    assert_eq!(sysroot_bin_names_for_tool_source("targo-trust"), ["targo-trust"]);
    assert_eq!(sysroot_bin_names_for_tool_source("trustd"), ["trustd"]);

    let context = crate::utils::tests::TestCtx::new();
    for host in ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin", "x86_64-pc-windows-msvc"] {
        let host = TargetSelection::from_user(host);
        let bindir = context.dir().join(host.triple.to_string()).join("bin");
        let targo = bindir.join(exe("targo", host));
        let cargo = bindir.join(exe("cargo", host));

        // Trust: an absent directory cannot establish a complete inspection.
        let problems = sysroot_compat_alias_problems(&bindir, host);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(problems[0].contains(&bindir.display().to_string()), "{problems:?}");
        fs::create_dir_all(&bindir).unwrap();
        fs::write(bindir.join(exe("trustc", host)), b"compiler").unwrap();
        assert_eq!(sysroot_compat_alias_problems(&bindir, host), Vec::<String>::new());

        // The 7cbb5e4327 stage2: `targo` alone.
        fs::write(&targo, b"the targo artifact").unwrap();
        let problems = sysroot_compat_alias_problems(&bindir, host);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(problems[0].contains("without its compatibility alias"), "{problems:?}");
        assert!(problems[0].contains(&cargo.display().to_string()), "{problems:?}");

        // What every install site now writes: each name from the one artifact.
        for name in sysroot_bin_names_for_tool_source("targo") {
            let destination = bindir.join(exe(name, host));
            if destination != targo {
                fs::hard_link(&targo, &destination)
                    .or_else(|_| fs::copy(&targo, &destination).map(drop))
                    .unwrap();
            }
        }
        assert_eq!(sysroot_compat_alias_problems(&bindir, host), Vec::<String>::new());

        // A copy on another filesystem is the same bytes without being the same file.
        fs::remove_file(&cargo).unwrap();
        fs::copy(&targo, &cargo).unwrap();
        assert_eq!(sysroot_compat_alias_problems(&bindir, host), Vec::<String>::new());

        // Another program under the alias name: same length, then another length.
        for other in [&b"the cargo artifact"[..], &b"stock cargo"[..]] {
            fs::write(&cargo, other).unwrap();
            let problems = sysroot_compat_alias_problems(&bindir, host);
            assert_eq!(problems.len(), 1, "{problems:?}");
            assert!(problems[0].contains("is not the same bytes"), "{problems:?}");
        }
    }
}

/// Trust: native directory failures and partial enumeration must never become
/// an empty successful validation. Fault injection uses the same inspector
/// with ordinary I/O errors, without assuming chmod can deny this test's user.
#[test]
fn sysroot_alias_inspection_refuses_unavailable_and_partial_directory_reads() {
    let context = crate::utils::tests::TestCtx::new();
    let host = TargetSelection::from_user("aarch64-apple-darwin");
    let bindir = context.dir().join("bin");
    assert!(!sysroot_compat_alias_problems(&bindir, host).is_empty());
    fs::write(&bindir, b"not a directory").unwrap();
    assert!(!sysroot_compat_alias_problems(&bindir, host).is_empty());
    fs::remove_file(&bindir).unwrap();
    fs::create_dir(&bindir).unwrap();
    fs::create_dir(bindir.join("support-files")).unwrap();
    assert!(sysroot_compat_alias_problems(&bindir, host).is_empty());

    let denied = Err::<std::iter::Empty<io::Result<PathBuf>>, _>(io::Error::from(
        io::ErrorKind::PermissionDenied,
    ));
    assert!(!inspect_sysroot_compat_aliases(&bindir, host, denied).is_empty());

    fs::write(bindir.join("targo"), b"same tool").unwrap();
    fs::write(bindir.join("cargo"), b"same tool").unwrap();
    assert!(sysroot_compat_alias_problems(&bindir, host).is_empty());
    let actual = fs::read_dir(&bindir).unwrap().map(|entry| entry.map(|entry| entry.path()));
    let partial =
        actual.chain(std::iter::once(Err(io::Error::from(io::ErrorKind::PermissionDenied))));
    assert!(!inspect_sysroot_compat_aliases(&bindir, host, Ok(partial)).is_empty());
}

/// Trust: only recognized tool names require a file, while a broken or
/// non-file recognized source cannot disappear from the alias checks.
#[test]
fn sysroot_alias_inspection_refuses_a_non_file_known_tool() {
    let context = crate::utils::tests::TestCtx::new();
    let host = TargetSelection::from_user("aarch64-apple-darwin");
    let bindir = context.dir().join("bin");
    fs::create_dir_all(bindir.join("targo")).unwrap();
    fs::write(bindir.join("cargo"), b"tool").unwrap();
    assert!(!sysroot_compat_alias_problems(&bindir, host).is_empty());
}

#[cfg(unix)]
#[test]
fn sysroot_alias_inspection_refuses_a_broken_known_tool() {
    let context = crate::utils::tests::TestCtx::new();
    let host = TargetSelection::from_user("aarch64-apple-darwin");
    let bindir = context.dir().join("bin");
    fs::create_dir(&bindir).unwrap();
    std::os::unix::fs::symlink("missing-tool", bindir.join("targo")).unwrap();
    fs::write(bindir.join("cargo"), b"tool").unwrap();
    assert!(!sysroot_compat_alias_problems(&bindir, host).is_empty());
}

#[test]
fn every_targo_build_site_shares_one_recipe_for_the_targo_artifact() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");
    let recipe =
        targo_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);

    // `ToolBuild::run` copies `cargo_out/<tool>` into the tools directory under
    // `<tool>`, so this is the file restoration installs as `bin/targo`.
    assert_eq!(recipe.tool, "targo");
    assert_eq!(recipe.path, "src/tools/targo");
    assert_eq!(recipe.mode, Mode::ToolTarget);
    assert_eq!(recipe.artifact_kind, ToolArtifactKind::Binary);
    assert!(recipe.cargo_args.is_empty(), "the recipe selects the package's only binary");
}

// Trust: the SDK qualification prebuild selects this library explicitly,
// without a bootstrap test that reassembles the compiler's standard library.
#[test]
fn explicit_run_make_support_build_keeps_the_seed_library_graph() {
    for stage in [1, 2] {
        for with_compiletest in [false, true] {
            let context = crate::utils::tests::TestCtx::new();
            let mut config =
                context.config("build").stage(stage).path("src/tools/run-make-support");
            if with_compiletest {
                config = config.path("src/tools/compiletest");
            }
            let build = crate::core::session::Session::new(config.create_config());
            let builder = Builder::new(&build);
            builder.execute_cli();
            let target = builder.host_target;
            let seed = Compiler::new(0, target);
            let recipe = ToolBuild {
                build_compiler: seed,
                output_compiler: Compiler::new(1, target),
                target,
                tool: "run_make_support",
                path: "src/tools/run-make-support",
                mode: Mode::ToolBootstrap,
                source_type: SourceType::InTree,
                extra_features: vec![],
                allow_features: "",
                cargo_args: vec![],
                artifact_kind: ToolArtifactKind::Library,
            };
            let cache = builder.step_cache();
            assert!(
                cache.contains::<RunMakeSupport>(),
                "the explicit source path must select its Step"
            );
            let output =
                cache.get(&recipe).expect("the selector must keep the actual seed library recipe");
            assert_eq!(output.build_compiler, seed);
            assert_eq!(
                output.tool_path,
                builder
                    .cargo_out(seed, Mode::ToolBootstrap, target)
                    .join("librun_make_support.rlib"),
            );
            assert_eq!(
                cache.inspect_all_steps_of_type::<ToolBuild, _>(|step, _| step.tool),
                if with_compiletest {
                    vec!["compiletest", "run_make_support"]
                } else {
                    vec!["run_make_support"]
                },
                "only the requested fixture tools may be built",
            );
            assert!(!cache.contains::<compile::Rustc>(), "no compiler emission is needed");
            assert!(!cache.contains::<compile::Std>(), "the seed already supplies native std");
            assert!(
                cache
                    .inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| step
                        .target_compiler
                        .stage)
                    .iter()
                    .all(|stage| *stage == 0),
                "no next-stage compiler may be assembled",
            );
            assert!(
                cache
                    .inspect_all_steps_of_type::<compile::Sysroot, _>(|step, _| step.compiler.stage)
                    .iter()
                    .all(|stage| *stage == 0),
                "the fixture prebuild must not reassemble the SDK sysroot",
            );
        }
    }
}

// Trust: select the public alias through the actual CLI graph, with SDK tools
// enabled. Both supported requested stages must keep this engineering target at
// compiler0; Bootstrap's global configuration guard still refuses stage0 builds.
#[test]
fn targo_build_tool_has_only_the_native_stage0_artifact_graph() {
    for stage in [1, 2] {
        let context = crate::utils::tests::TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", "build.extended=true", "--set", "rust.omit-git-hash=false"])
            .path("targo-build-tool")
            .create_config();
        let build = crate::core::session::Session::new(config);
        let builder = Builder::new(&build);
        assert!(!TargoBuildTool::is_default_step(&builder));
        builder.execute_cli();
        let target = builder.host_target;
        let cache = builder.step_cache();
        assert!(cache.contains::<TargoBuildTool>());
        assert!(!cache.contains::<Cargo>(), "the ordinary SDK Targo step must not run");
        assert!(!cache.contains::<compile::Rustc>(), "no compiler build is needed");
        assert!(!cache.contains::<compile::Std>(), "the seed already supplies native std");
        assert_eq!(
            cache.inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| {
                step.target_compiler.stage
            }),
            vec![0],
            "no next-stage compiler may be assembled",
        );
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Sysroot, _>(|step, _| step.compiler.stage)
                .iter()
                .all(|stage| *stage == 0),
            "no next-stage sysroot or default verifier closure may be assembled",
        );
        assert_eq!(
            cache.inspect_all_steps_of_type::<ToolBuild, _>(|step, result| {
                (
                    step.tool,
                    step.build_compiler.stage,
                    step.output_compiler.stage,
                    result.tool_path.clone(),
                )
            }),
            vec![(
                "targo",
                0,
                0,
                builder.tools_dir(Compiler::new(0, target), target).join(exe("targo", target))
            )],
            "exactly one tool artifact is built, outside any installed SDK",
        );
    }
}

// Trust: inspect the recipe the public target actually used, including Bootstrap's
// generated release and validated commit tuple, rather than caller-supplied CFG_*.
#[test]
fn targo_build_tool_uses_source_generated_release_and_identity() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .path("targo-build-tool")
        .args(&["--set", "rust.omit-git-hash=false", "--set", "rust.channel=trust"])
        .create_config();
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    builder.execute_cli();
    let producers = builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
        (step.tool, step.build_compiler.stage, step.output_compiler.stage)
    });
    assert_eq!(producers, vec![("targo", 0, 0)]);
    let compiler = Compiler::new(0, builder.host_target);
    let recipe = targo_tool_build_recipe(compiler, compiler, builder.host_target);
    assert!(builder.step_cache().get(&recipe).is_some());
    let cargo = prepare_tool_cargo(
        &builder,
        recipe.build_compiler,
        recipe.mode,
        recipe.target,
        Kind::Build,
        recipe.path,
        recipe.source_type,
        &recipe.extra_features,
    );
    let mut command = cargo.into_cmd();
    command.mark_as_executed();
    let env: std::collections::BTreeMap<_, _> = command
        .get_envs()
        .filter_map(|(key, value)| Some((key.to_str()?.to_owned(), value?.to_str()?.to_owned())))
        .collect();
    let compat = fs::read_to_string(builder.src.join("src/rust-compat-version")).unwrap();
    assert_eq!(env["CFG_RELEASE"], format!("{}-dev", compat.trim()));
    let identity = build.version_info();
    let hash = identity.sha().expect("the checkout must supply a source identity");
    assert_eq!(env["CFG_COMMIT_HASH"], hash);
    assert_eq!(env["CFG_SHORT_COMMIT_HASH"], identity.sha_short().unwrap());
    assert_eq!(env["CFG_COMMIT_DATE"], identity.commit_date().unwrap());
    assert_eq!(env["CFG_VER_HASH"], env["CFG_COMMIT_HASH"]);
    assert_eq!(env["CFG_RELEASE_CHANNEL"], builder.config.channel);
    let args = command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>().join(" ");
    assert!(args.contains("vendored-openssl"));
    assert!(args.contains("vendored-libgit2"));
}

// Trust: never let this native engineering target silently request a cross-host SDK.
#[test]
#[should_panic(expected = "targo-build-tool only supports the native build host")]
fn targo_build_tool_refuses_a_non_native_host() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context.config("build").stage(1).create_config();
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    let foreign = if builder.host_target.triple == "i686-unknown-haiku" {
        "i686-unknown-hurd-gnu"
    } else {
        "i686-unknown-haiku"
    };
    builder.ensure(TargoBuildTool { target: TargetSelection::from_user(foreign) });
}

// Trust: an engineering input still needs its real source identity. Do not allow
// this target to replace missing provenance with Targo's standalone fallback.
#[test]
#[should_panic(expected = "targo-build-tool requires source identity; do not omit git hash")]
fn targo_build_tool_refuses_omitted_source_identity() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .path("targo-build-tool")
        .args(&["--set", "rust.omit-git-hash=true"])
        .create_config();
    let build = crate::core::session::Session::new(config);
    Builder::new(&build).execute_cli();
}

// Trust: the cycle-breaking edge belongs only to the exact native producer.
#[test]
fn targo_build_tool_seed_edge_is_not_used_by_sdk_recipes() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let host = builder.host_target;
    let producer = targo_tool_build_recipe(Compiler::new(0, host), Compiler::new(0, host), host);
    assert_eq!(producer.cargo_input(&builder), CargoInput::Seed);
    for (build_stage, output_stage) in [(0, 1), (1, 2)] {
        let sdk = targo_tool_build_recipe(
            Compiler::new(build_stage, host),
            Compiler::new(output_stage, host),
            host,
        );
        assert_eq!(sdk.cargo_input(&builder), CargoInput::CurrentBuildTool);
    }
    let other_tool = ToolBuild { tool: "other", ..producer.clone() };
    assert_eq!(other_tool.cargo_input(&builder), CargoInput::CurrentBuildTool);
    let other_args = ToolBuild { cargo_args: vec!["--offline".to_owned()], ..producer.clone() };
    assert_eq!(other_args.cargo_input(&builder), CargoInput::CurrentBuildTool);
    for modified in [
        ToolBuild { artifact_kind: ToolArtifactKind::Library, ..producer.clone() },
        ToolBuild { source_type: SourceType::InTree, ..producer.clone() },
        ToolBuild { extra_features: vec!["changed".to_owned()], ..producer.clone() },
        ToolBuild { allow_features: "", ..producer.clone() },
        ToolBuild {
            build_compiler: Compiler::new(0, TargetSelection::from_user("wasm32-unknown-unknown")),
            ..producer.clone()
        },
        ToolBuild {
            output_compiler: Compiler::new(0, TargetSelection::from_user("wasm32-unknown-unknown")),
            ..producer.clone()
        },
        ToolBuild {
            target: TargetSelection::from_user("wasm32-unknown-unknown"),
            ..producer.clone()
        },
    ] {
        assert_eq!(modified.cargo_input(&builder), CargoInput::CurrentBuildTool);
    }
    let prerequisite = ToolBuild { mode: Mode::ToolBootstrap, ..producer };
    assert_eq!(prerequisite.cargo_input(&builder), CargoInput::Seed);
}

// Trust: exercise the real recipes and generated commands. The seed previously
// re-entered the same native-tool cache after current Cargo had written it and
// panicked while comparing a valid current build-script fingerprint.
#[test]
fn targo_seed_and_current_cache_domains_are_disjoint_and_stable() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let host = builder.host_target;
    let compiler = Compiler::new(0, host);
    let seed = targo_tool_build_recipe(compiler, compiler, host);
    let current = targo_tool_build_recipe(compiler, Compiler::new(1, host), host);
    let command_for = |recipe: &ToolBuild| {
        let input = recipe.cargo_input(&builder);
        let cargo = prepare_tool_cargo_with_input(
            &builder,
            recipe.build_compiler,
            recipe.mode,
            recipe.target,
            Kind::Build,
            recipe.path,
            recipe.source_type.clone(),
            &recipe.extra_features,
            input,
        );
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        command
    };
    let seed_command = command_for(&seed);
    let current_command = command_for(&current);
    let environment = |command: &BootstrapCommand, name: &str| {
        command
            .get_envs()
            .find(|(key, _)| *key == OsStr::new(name))
            .and_then(|(_, value)| value)
            .map(PathBuf::from)
            .unwrap()
    };
    let seed_dir = builder.out.join(host).join("bootstrap-seed-tools");
    let current_dir = builder.out.join(host).join("bootstrap-tools");
    assert_ne!(seed_dir, current_dir);
    for name in ["CARGO_TARGET_DIR", "CARGO_BUILD_BUILD_DIR"] {
        assert_eq!(environment(&seed_command, name), seed_dir);
        assert_eq!(environment(&current_command, name), current_dir);
        // Re-entering an unchanged recipe uses the same domain, not a new
        // directory per invocation or per rebuilt Cargo executable.
        assert_eq!(environment(&command_for(&seed), name), seed_dir);
        assert_eq!(environment(&command_for(&current), name), current_dir);
    }
    assert_eq!(seed_command.get_program(), build.initial_cargo.as_os_str());
    assert_ne!(current_command.get_program(), build.initial_cargo.as_os_str());
    assert_eq!(
        seed.mode,
        Mode::ToolTarget,
        "cache selection must not change flags or recipe identity"
    );
    assert_eq!(current.mode, Mode::ToolTarget);
    assert_eq!(
        builder.cargo_out(compiler, seed.cargo_input(&builder).cache_mode(seed.mode), host),
        seed_dir.join(host).join(builder.cargo_dir(seed.mode)),
        "the artifact reader must use the same root as its Cargo writer",
    );
    assert_eq!(
        builder.cargo_out(compiler, current.cargo_input(&builder).cache_mode(current.mode), host),
        current_dir.join(host).join(builder.cargo_dir(current.mode)),
    );
    // Other bootstrap prerequisites are seed-driven; compiler/std paths keep
    // their existing stage layout and selected producer.
    assert_eq!(builder.stage_out(compiler, Mode::ToolBootstrap), seed_dir);
    for mode in [Mode::Std, Mode::Rustc, Mode::Codegen, Mode::ToolStd, Mode::ToolRustcPrivate] {
        assert_eq!(CargoInput::for_mode(mode), CargoInput::CurrentBuildTool);
        assert_eq!(CargoInput::CurrentBuildTool.cache_mode(mode), mode);
    }
}

// Trust: local-rebuild consumers use their existing staged std; the producer
// itself still uses the actual snapshot so building std never needs itself.
#[test]
fn targo_build_tool_local_rebuild_seed_edge_uses_snapshot_std() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "build.local-rebuild=true"])
        .create_config();
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    let compiler = Compiler::new(0, builder.host_target);
    let recipe = targo_tool_build_recipe(compiler, compiler, builder.host_target);
    let cargo = prepare_tool_cargo_with_input(
        &builder,
        compiler,
        recipe.mode,
        recipe.target,
        Kind::Build,
        recipe.path,
        recipe.source_type.clone(),
        &recipe.extra_features,
        recipe.cargo_input(&builder),
    );
    assert_eq!(cargo.build_compiler_stage(), 0);
    let mut command = cargo.into_cmd();
    command.mark_as_executed();
    assert_eq!(command.get_program(), build.initial_cargo.as_os_str());
    assert_eq!(
        command
            .get_envs()
            .find(|(key, _)| *key == OsStr::new("RUSTC_SYSROOT"))
            .and_then(|(_, value)| value),
        Some(build.initial_sysroot.as_os_str())
    );
    let env_value = |command: &BootstrapCommand, name: &str| {
        command
            .get_envs()
            .find(|(key, _)| *key == OsStr::new(name))
            .and_then(|(_, value)| value)
            .map(|value| value.to_string_lossy().into_owned())
    };
    let flags = |command: &BootstrapCommand| {
        [
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTDOCFLAGS",
            "CARGO_ENCODED_RUSTDOCFLAGS",
            "RUSTC_HOST_FLAGS",
        ]
        .into_iter()
        .filter_map(|name| env_value(command, name))
        .collect::<Vec<_>>()
        .join("\x1f")
    };
    assert_eq!(env_value(&command, "RUSTC_STAGE").as_deref(), Some("0"));
    let seed_flags = flags(&command);
    assert!(seed_flags.contains("--cfg=bootstrap"));
    for staged_flag in ["-Zannotate-moves", "-Ztrust-verify=off", "-Cpanic=abort"] {
        assert!(
            !seed_flags.contains(staged_flag),
            "raw snapshot received {staged_flag}: {seed_flags}"
        );
    }
    assert!(!builder.step_cache().contains::<compile::Std>());
    assert!(!builder.step_cache().contains::<TargoBuildTool>());

    let sdk = prepare_tool_cargo(
        &builder,
        compiler,
        recipe.mode,
        recipe.target,
        Kind::Build,
        recipe.path,
        recipe.source_type.clone(),
        &recipe.extra_features,
    );
    assert_eq!(sdk.build_compiler_stage(), 1);
    let mut sdk_command = sdk.into_cmd();
    sdk_command.mark_as_executed();
    assert_eq!(env_value(&sdk_command, "RUSTC_STAGE").as_deref(), Some("1"));
    assert_eq!(
        env_value(&sdk_command, "RUSTC_SYSROOT"),
        Some(builder.sysroot(compiler).to_string_lossy().into_owned())
    );
    let sdk_flags = flags(&sdk_command);
    assert!(sdk_flags.contains("-Zannotate-moves"));
    assert!(sdk_flags.contains("-Ztrust-verify=off"));

    let prerequisite = prepare_tool_cargo(
        &builder,
        compiler,
        Mode::ToolBootstrap,
        recipe.target,
        Kind::Build,
        "src/bootstrap",
        SourceType::InTree,
        &[],
    );
    assert_eq!(prerequisite.build_compiler_stage(), 1);
    let mut prerequisite_command = prerequisite.into_cmd();
    prerequisite_command.mark_as_executed();
    assert_eq!(env_value(&prerequisite_command, "RUSTC_STAGE").as_deref(), Some("1"));
}

// Trust: a declared capability fixture exercises actual argv0 and the existing
// execution cache. It is not a Targo binary or production version/identity input.
#[cfg(unix)]
#[test]
fn targo_build_tool_alias_bytes_and_capabilities_keep_seed_and_argv0_separate() {
    use std::os::unix::fs::PermissionsExt;
    let temp = tempfile::TempDir::new().unwrap();
    let native = temp.path().join("targo");
    fs::write(&native, r#"#!/bin/sh
printf '%s %s\n' "${0##*/}" "$*" >> "${0%/*}/probes"
if [ "$1" = --help ]; then
    case "${0##*/}" in targo) printf '%s\n' --unverified ;; *) printf '%s\n' 'Cargo fixture help' ;; esac
    exit 0
fi
if [ "$1" = --unverified ]; then shift; fi
if [ "$1" = -Z ] && [ "$2" = help ]; then
    case "${0##*/}" in seed-cargo) printf '%s\n' '    -Z no-embed-metadata legacy' ;; *) printf '%s\n' '    -Z embed-metadata current' ;; esac
    exit 0
fi
exit 97
"#).unwrap();
    fs::set_permissions(&native, fs::Permissions::from_mode(0o755)).unwrap();
    let alias = copy_targo_build_tool_alias(
        &native,
        TargetSelection::from_user("x86_64-unknown-linux-gnu"),
        |src, dst| fs::hard_link(src, dst).unwrap(),
    );
    let seed = temp.path().join("seed-cargo");
    fs::hard_link(&native, &seed).unwrap();
    assert_eq!(fs::read(&native).unwrap(), fs::read(&alias).unwrap());
    let exec_ctx = crate::utils::exec::ExecutionContext::new(0, true);
    let old = CargoProgram::probe(&exec_ctx, seed.clone());
    assert_eq!(old.metadata_flag, "-Zno-embed-metadata");
    assert!(!old.unverified_lane);
    let current = CargoProgram::probe(&exec_ctx, alias.clone());
    assert_eq!(current.path, alias);
    assert_eq!(current.metadata_flag, "-Zembed-metadata=no");
    assert!(!current.unverified_lane);
    let branded = CargoProgram::probe(&exec_ctx, native.clone());
    assert!(branded.unverified_lane);
    assert_eq!(branded.metadata_flag, current.metadata_flag);
    for path in [seed, alias, native] {
        CargoProgram::probe(&exec_ctx, path);
    }
    let probes = fs::read_to_string(temp.path().join("probes")).unwrap();
    assert_eq!(probes.lines().count(), 6, "each immutable executable spelling is probed once");
    assert!(probes.contains("seed-cargo -Z help"));
    assert!(probes.contains("cargo -Z help"));
    assert!(probes.contains("targo --unverified -Z help"));
}

// Exercise the production CLI registry and real ToolBuild recipe. The old
// stage2-only assembly path advertised trustup but emitted none at stage1.
#[test]
fn trustup_default_and_explicit_paths_have_one_producer_per_stage() {
    for stage in [1, 2] {
        for paths in [&[][..], &["src/tools/trustup"][..]] {
            let config = crate::utils::tests::TestCtx::new()
                .config("build")
                .stage(stage)
                .paths(paths)
                .with_default_toml_config("profile = 'compiler'\n[build]\ntools = ['trustup']\n")
                .create_config();
            let build = crate::core::session::Session::new(config);
            let builder = Builder::new(&build);
            builder.execute_cli();
            let producers =
                builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
                    (step.tool == "trustup").then_some((
                        step.build_compiler.stage,
                        step.output_compiler.stage,
                        step.mode == Mode::ToolTarget,
                        step.path,
                        step.extra_features.clone(),
                        step.allow_features,
                    ))
                });
            let actual: Vec<_> = producers.into_iter().flatten().collect();
            assert_eq!(actual, [(stage - 1, stage, true, "src/tools/trustup", vec![], "")]);
        }
    }
}

#[test]
fn trustup_unselected_or_nonextended_default_does_not_build_it() {
    for selection in ["extended = true\ntools = ['targo']", "extended = false\ntools = ['trustup']"]
    {
        let config = crate::utils::tests::TestCtx::new()
            .config("build")
            .stage(1)
            .with_default_toml_config(&format!("profile = 'compiler'\n[build]\n{selection}\n"))
            .create_config();
        let build = crate::core::session::Session::new(config);
        let builder = Builder::new(&build);
        builder.execute_cli();
        let producers = builder
            .step_cache()
            .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| step.tool == "trustup");
        assert!(producers.into_iter().all(|selected| !selected));
    }
    assert!(!should_assemble_user_facing_tools(Kind::Build, 1));
}

#[test]
fn trustup_build_tool_has_only_the_native_artifact_graph() {
    for stage in [1, 2] {
        let context = crate::utils::tests::TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", "build.extended=true", "--set", "rust.omit-git-hash=false"])
            .path("trustup-build-tool")
            .create_config();
        let build = crate::core::session::Session::new(config);
        let builder = Builder::new(&build);
        assert!(!TrustupBuildTool::is_default_step(&builder));
        builder.execute_cli();
        let cache = builder.step_cache();
        assert!(cache.contains::<TrustupBuildTool>());
        assert!(!cache.contains::<Trustup>());
        assert!(!cache.contains::<compile::Rustc>());
        assert!(!cache.contains::<compile::Std>());
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| step
                    .target_compiler
                    .stage)
                .iter()
                .all(|stage| *stage == 0)
        );
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Sysroot, _>(|step, _| step.compiler.stage)
                .iter()
                .all(|stage| *stage == 0)
        );
        let host = builder.host_target;
        assert_eq!(
            cache.inspect_all_steps_of_type::<ToolBuild, _>(|step, _| (
                step.tool,
                step.build_compiler.stage,
                step.output_compiler.stage
            )),
            vec![("targo", 0, 0), ("trustup", 0, 0)]
        );
        let recipe =
            trustup_tool_build_recipe(Compiler::new(0, host), Compiler::new(0, host), host);
        assert_eq!(
            recipe.cargo_input(&builder),
            CargoInput::CurrentBuildToolSnapshotStd,
            "the seed-Cargo edge remains exclusive to the existing native Cargo producer"
        );
    }
}

// Trust: exercise the parsed CLI's actual Step graph, including the current
// native Cargo producer. A frontend artifact must not rebuild a target SDK.
#[test]
fn frontend_build_tool_does_not_assemble_or_modify_a_target_sdk() {
    for stage in [1, 2] {
        let context = crate::utils::tests::TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", "build.extended=true", "--set", "rust.omit-git-hash=false"])
            .path("targo-trust-build-tool")
            .create_config();
        let build = crate::core::session::Session::new(config);
        let builder = Builder::new(&build);
        assert!(!TCargoTrustBuildTool::is_default_step(&builder));
        builder.execute_cli();
        let cache = builder.step_cache();
        assert!(cache.contains::<TCargoTrustBuildTool>());
        assert!(!cache.contains::<TCargoTrust>());
        assert!(!cache.contains::<Trustd>());
        assert!(!cache.contains::<compile::Rustc>());
        assert!(!cache.contains::<compile::Std>());
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| step
                    .target_compiler
                    .stage)
                .iter()
                .all(|stage| *stage == 0)
        );
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Sysroot, _>(|step, _| step.compiler.stage)
                .iter()
                .all(|stage| *stage == 0)
        );
        assert_eq!(
            cache.inspect_all_steps_of_type::<ToolBuild, _>(|step, _| (
                step.tool,
                step.build_compiler.stage,
                step.output_compiler.stage,
            )),
            vec![("targo", 0, 0), ("targo-trust", 0, 0)],
        );
    }
}

#[test]
#[should_panic(expected = "targo-trust-build-tool only supports the native build host")]
fn frontend_build_tool_refuses_a_non_native_host() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let foreign = if builder.host_target.triple == "i686-unknown-haiku" {
        "i686-unknown-hurd-gnu"
    } else {
        "i686-unknown-haiku"
    };
    builder.ensure(TCargoTrustBuildTool { target: TargetSelection::from_user(foreign) });
}

#[test]
#[should_panic(expected = "targo-trust-build-tool requires source identity; do not omit git hash")]
fn frontend_build_tool_refuses_omitted_source_identity() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .path("targo-trust-build-tool")
        .args(&["--set", "rust.omit-git-hash=true"])
        .create_config();
    let build = crate::core::session::Session::new(config);
    Builder::new(&build).execute_cli();
}

#[test]
fn frontend_snapshot_std_role_is_exact_and_keeps_current_cargo() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let host = builder.host_target;
    let compiler = Compiler::new(0, host);
    let exact = targo_trust_tool_build_recipe(compiler, compiler, host);
    assert_eq!(exact.cargo_input(&builder), CargoInput::CurrentBuildToolSnapshotStd);
    assert_eq!(exact.cargo_input(&builder).cache_mode(Mode::ToolTarget), Mode::ToolTarget);
    assert_eq!(exact.extra_features, targo_trust_in_process_features());
    assert_eq!(exact.allow_features, CARGO_TRUST_ALLOW_FEATURES);
    for changed in [
        ToolBuild { output_compiler: Compiler::new(1, host), ..exact.clone() },
        ToolBuild { build_compiler: Compiler::new(1, host), ..exact.clone() },
        ToolBuild { tool: "other", ..exact.clone() },
        ToolBuild { path: "src/tools/other", ..exact.clone() },
        ToolBuild { source_type: SourceType::Submodule, ..exact.clone() },
        ToolBuild { extra_features: vec!["other".to_owned()], ..exact.clone() },
        ToolBuild { allow_features: "other", ..exact.clone() },
        ToolBuild { cargo_args: vec!["--offline".to_owned()], ..exact.clone() },
        ToolBuild { artifact_kind: ToolArtifactKind::Library, ..exact.clone() },
        ToolBuild { target: TargetSelection::from_user("wasm32-unknown-unknown"), ..exact.clone() },
    ] {
        assert_eq!(changed.cargo_input(&builder), CargoInput::CurrentBuildTool);
    }
    assert_eq!(
        targo_tool_build_recipe(compiler, compiler, host).cargo_input(&builder),
        CargoInput::Seed,
    );
}

#[test]
#[should_panic(expected = "trustup-build-tool only supports the native build host")]
fn trustup_build_tool_refuses_a_non_native_host() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let foreign = if builder.host_target.triple == "i686-unknown-haiku" {
        "i686-unknown-hurd-gnu"
    } else {
        "i686-unknown-haiku"
    };
    builder.ensure(TrustupBuildTool { target: TargetSelection::from_user(foreign) });
}

#[test]
#[should_panic(expected = "trustup-build-tool requires source identity; do not omit git hash")]
fn trustup_build_tool_refuses_omitted_source_identity() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .path("trustup-build-tool")
        .args(&["--set", "rust.omit-git-hash=true"])
        .create_config();
    let build = crate::core::session::Session::new(config);
    Builder::new(&build).execute_cli();
}

#[test]
fn trustup_snapshot_std_role_is_exact_and_keeps_current_cargo_cache() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let host = builder.host_target;
    let compiler = Compiler::new(0, host);
    let exact = trustup_tool_build_recipe(compiler, compiler, host);
    assert_eq!(exact.cargo_input(&builder), CargoInput::CurrentBuildToolSnapshotStd);
    assert_eq!(exact.cargo_input(&builder).cache_mode(Mode::ToolTarget), Mode::ToolTarget);
    for changed in [
        ToolBuild { output_compiler: Compiler::new(1, host), ..exact.clone() },
        ToolBuild { build_compiler: Compiler::new(1, host), ..exact.clone() },
        ToolBuild { tool: "other", ..exact.clone() },
        ToolBuild { path: "src/tools/other", ..exact.clone() },
        ToolBuild { source_type: SourceType::Submodule, ..exact.clone() },
        ToolBuild { extra_features: vec!["other".to_owned()], ..exact.clone() },
        ToolBuild { allow_features: "other", ..exact.clone() },
        ToolBuild { cargo_args: vec!["--offline".to_owned()], ..exact.clone() },
        ToolBuild { artifact_kind: ToolArtifactKind::Library, ..exact.clone() },
        ToolBuild { target: TargetSelection::from_user("wasm32-unknown-unknown"), ..exact.clone() },
    ] {
        assert_eq!(changed.cargo_input(&builder), CargoInput::CurrentBuildTool);
    }
    let targo = targo_tool_build_recipe(compiler, compiler, host);
    assert_eq!(targo.cargo_input(&builder), CargoInput::Seed);
    assert_eq!(targo.cargo_input(&builder).cache_mode(Mode::ToolTarget), Mode::ToolBootstrap);
}

#[test]
fn trustup_artifact_uses_current_cargo_and_real_snapshot_std_under_local_rebuild() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "build.local-rebuild=true"])
        .create_config();
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    let compiler = Compiler::new(0, builder.host_target);
    let recipe = trustup_tool_build_recipe(compiler, compiler, builder.host_target);
    let cargo = prepare_tool_cargo_with_input(
        &builder,
        compiler,
        recipe.mode,
        recipe.target,
        Kind::Build,
        recipe.path,
        recipe.source_type.clone(),
        &recipe.extra_features,
        recipe.cargo_input(&builder),
    );
    assert_eq!(cargo.build_compiler_stage(), 0);
    let mut command = cargo.into_cmd();
    command.mark_as_executed();
    assert_ne!(command.get_program(), build.initial_cargo.as_os_str());
    let value = |key: &str| {
        command
            .get_envs()
            .find(|(k, _)| *k == OsStr::new(key))
            .and_then(|(_, v)| v)
            .map(|v| v.to_string_lossy().into_owned())
    };
    assert_eq!(value("RUSTC_SYSROOT"), Some(build.initial_sysroot.to_string_lossy().into_owned()));
    assert_eq!(value("RUSTC_STAGE").as_deref(), Some("0"));
    let flags = ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_HOST_FLAGS"]
        .into_iter()
        .filter_map(value)
        .collect::<Vec<_>>()
        .join("\x1f");
    assert!(flags.contains("--sysroot"));
    assert!(flags.contains("--cfg=bootstrap"));
    for flag in ["-Zannotate-moves", "-Ztrust-verify=off", "-Cpanic=abort"] {
        assert!(!flags.contains(flag), "snapshot received staged flag {flag}: {flags}");
    }
    assert!(!builder.step_cache().contains::<compile::Std>());
}
