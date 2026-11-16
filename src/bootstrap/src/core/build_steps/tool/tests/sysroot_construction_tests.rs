//! Trust: exercise the actual Sysroot graph with dry-run disabled.
use super::*;

#[test]
fn non_dry_sysroot_does_not_construct_tools_before_its_compiler() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .with_default_toml_config(
            "[build]\nextended=true\ntools=['targo']\nlocal-rebuild=false\n\
             [rust]\nomit-git-hash=true\nlld=false\n",
        )
        .create_config();
    let mut session = crate::core::session::Session::new(config);
    let source = context.dir().join("source");
    fs::create_dir(&source).unwrap();
    session.config.src = source.clone();
    let snapshot = context.dir().join("snapshot");
    fs::create_dir(&snapshot).unwrap();
    session.initial_sysroot = snapshot.clone();
    session.config.set_dry_run(crate::core::config::DryRun::Disabled);
    let builder = Builder::new(&session);
    assert!(!builder.config.dry_run());
    assert!(!is_partial_stage1_source_build(
        builder.kind,
        1,
        builder.top_stage,
        builder.config.include_default_paths,
        &builder.paths,
    ));

    // Cache only unrelated completed prerequisites. The stage1 Sysroot and
    // final Targo ToolBuild remain uncached, so the old code reaches bind's
    // real recursive Sysroot request before it can dispatch a Cargo command.
    let seed = Compiler::new(0, builder.host_target);
    builder.step_cache().put(compile::Sysroot::new(seed), snapshot);
    builder
        .step_cache()
        .put(compile::StdLink::from_std(compile::Std::new(seed, seed.host), seed), ());
    let sentinel = context.dir().join("must-not-dispatch-cargo");
    builder.step_cache().put(
        TargoBuildTool::native(&builder),
        TargoBuildToolResult {
            artifact: ToolBuildResult {
                tool_path: sentinel.clone(),
                build_compiler: seed,
                artifacts: vec![],
            },
            cargo: CargoProgram {
                path: sentinel.clone(),
                unverified_lane: false,
                metadata_flag: "-Zembed-metadata=no",
            },
            native_path: sentinel.clone(),
        },
    );

    for stage in [1, 2] {
        let compiler = Compiler::new(stage, builder.host_target);
        let step = compile::Sysroot::new(compiler);
        assert!(builder.step_cache().get(&step).is_none());
        let root = builder.ensure(step.clone());
        assert_eq!(root, compile::local_sysroot_dir(&builder, compiler));
        assert_eq!(builder.step_cache().get(&step), Some(root.clone()));
        for relative in compile::sysroot_source_aliases(stage, false) {
            assert_eq!(fs::read_link(root.join(relative)).unwrap(), source);
        }
    }
    let built_tools = builder
        .step_cache()
        .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| step.output_compiler.stage);
    assert!(built_tools.is_empty(), "sysroot construction built final tools: {built_tools:?}");
    assert!(!sentinel.exists(), "the absent command is never materialized or dispatched");
}
