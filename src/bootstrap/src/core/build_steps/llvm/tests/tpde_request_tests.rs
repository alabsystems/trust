// Copyright 2026 Andrew Yates
use super::*;
use crate::core::session::Session;

// Pure selected request data. This never claims native Prepared observations.
fn planned(
    ctx: &TestCtx,
    change: impl FnOnce(&mut Config),
    lookup: &dyn Fn(&str) -> Option<OsString>,
) -> (CmakePlan, bool) {
    let mut config = ctx.config("build").stage(1).create_config();
    config.rust_remap_debuginfo = false;
    let mut session = Session::new(config);
    session.config.host_target = TargetSelection::from_user("aarch64-apple-darwin");
    session.config.ninja_in_file = true;
    session.config.lld_enabled = false;
    session.config.llvm_clang_cl = Some("/selected/compiler/clang-cl".into());
    change(&mut session.config);
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let output = tpde_output(&builder, target);
    let selected = in_tree_lld_requested(&builder.config, target)
        .then(|| source_lld_output_dir(&builder, target));
    let strip = builder.config.llvm_optimize && !builder.config.llvm_release_debuginfo;
    (
        tpde_cmake_plan(
            &builder,
            target,
            &output.tpde_root_dir,
            &ctx.dir().join("LLVM/lib/cmake/llvm"),
            &ctx.dir().join("LLVM"),
            selected.as_deref(),
            lookup,
            Vec::new,
        )
        .unwrap(),
        strip,
    )
}

fn defined<'a>(plan: &'a CmakePlan, name: &str) -> Option<&'a OsStr> {
    plan.operations.iter().rev().find_map(|operation| match operation {
        CmakeOperation::Define(key, value) | CmakeOperation::InputProgram(key, value)
            if key == name =>
        {
            Some(value.as_os_str())
        }
        _ => None,
    })
}

#[test]
fn actual_tpde_plan_changes_invalidate_unchanged_source_provider_and_plugin_status() {
    let ctx = TestCtx::new();
    let session = Session::new(ctx.config("build").stage(1).create_config());
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = completed_llvm_fixture(ctx.dir().join("completed LLVM"), target);
    let dependency = completed_llvm_dependency_key(&llvm, target).unwrap();
    let (base, strip) = planned(&ctx, |_| {}, &|_| None);
    let key = base.requested_key();
    let TpdeBuildStatus::ShouldBuild(info) = get_locally_built_tpde_build_status(
        &builder,
        target,
        reusable_cmake_inputs(Some("controlled source data"), Some(&dependency), Some(&key)),
        strip,
    ) else {
        panic!("fresh request");
    };
    begin_cmake_miss(&info.stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(info.output.plugin_path().parent().unwrap()).unwrap();
    fs::write(info.output.plugin_path(), b"owned status artifact, not a TPDE build").unwrap();
    record_tpde_completion(&info.stamp, &llvm, target, Some(&dependency)).unwrap();
    assert!(matches!(
        get_locally_built_tpde_build_status(
            &builder,
            target,
            reusable_cmake_inputs(Some("controlled source data"), Some(&dependency), Some(&key)),
            strip
        ),
        TpdeBuildStatus::AlreadyBuilt(_)
    ));
    for change in [
        (|c: &mut Config| c.llvm_cflags = Some("-DCHANGED_C".into())) as fn(&mut Config),
        |c| c.llvm_cxxflags = Some("-DCHANGED_CXX".into()),
        |c| c.llvm_ldflags = Some("-Wl,changed".into()),
        |c| c.llvm_clang_cl = Some("/another/compiler/clang-cl".into()),
        |c| c.llvm_assertions = !c.llvm_assertions,
        |c| c.llvm_optimize = !c.llvm_optimize,
    ] {
        let (changed, changed_strip) = planned(&ctx, change, &|_| None);
        let changed_key = changed.requested_key();
        assert_ne!(key, changed_key);
        assert!(matches!(
            get_locally_built_tpde_build_status(
                &builder,
                target,
                reusable_cmake_inputs(
                    Some("controlled source data"),
                    Some(&dependency),
                    Some(&changed_key)
                ),
                changed_strip
            ),
            TpdeBuildStatus::ShouldBuild(_)
        ));
    }
    let (changed, _) = planned(&ctx, |_| {}, &|name| {
        (name == "LDFLAGS_x86_64-unknown-linux-gnu").then(|| "selected-target-flags".into())
    });
    let changed_key = changed.requested_key();
    assert_ne!(key, changed_key);
    assert!(matches!(
        get_locally_built_tpde_build_status(
            &builder,
            target,
            reusable_cmake_inputs(
                Some("controlled source data"),
                Some(&dependency),
                Some(&changed_key)
            ),
            strip
        ),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    assert!(matches!(
        get_locally_built_tpde_build_status(
            &builder,
            target,
            reusable_cmake_inputs(Some("controlled source data"), Some(&dependency), Some(&key)),
            !strip
        ),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    assert_eq!(
        fs::read(info.output.plugin_path()).unwrap(),
        b"owned status artifact, not a TPDE build"
    );
}

#[test]
fn absent_prepared_request_never_authorizes_tpde_reuse_or_generation_or_completion() {
    let ctx = TestCtx::new();
    let session = Session::new(ctx.config("build").stage(1).create_config());
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = completed_llvm_fixture(ctx.dir().join("completed LLVM"), target);
    let dependency = completed_llvm_dependency_key(&llvm, target).unwrap();
    // Controlled status inputs, not fabricated native preparation receipts.
    let known = reusable_cmake_inputs(
        Some("controlled source data"),
        Some(dependency.as_str()),
        Some("controlled prepared request data"),
    );
    let TpdeBuildStatus::ShouldBuild(info) =
        get_locally_built_tpde_build_status(&builder, target, known, false)
    else {
        panic!("fresh request");
    };
    begin_cmake_miss(&info.stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(info.output.plugin_path().parent().unwrap()).unwrap();
    fs::write(info.output.plugin_path(), b"owned plugin fixture").unwrap();
    record_tpde_completion(&info.stamp, &llvm, target, Some(&dependency)).unwrap();
    assert!(matches!(
        get_locally_built_tpde_build_status(&builder, target, known, false),
        TpdeBuildStatus::AlreadyBuilt(_)
    ));
    let reusable =
        reusable_cmake_inputs(Some("controlled source data"), Some(dependency.as_str()), None);
    let TpdeBuildStatus::ShouldBuild(unknown) =
        get_locally_built_tpde_build_status(&builder, target, reusable, false)
    else {
        panic!("unknown request");
    };
    begin_cmake_miss(
        &unknown.stamp,
        if reusable.is_some() { CmakeGeneration::Known } else { CmakeGeneration::Unknown },
    )
    .unwrap();
    assert!(!cmake_generation_matches(&unknown.stamp));
    assert!(!info.output.plugin_path().exists());
    fs::create_dir_all(unknown.output.plugin_path().parent().unwrap()).unwrap();
    fs::write(unknown.output.plugin_path(), b"new unknown-build output").unwrap();
    record_tpde_completion(&unknown.stamp, &llvm, target, reusable.map(|inputs| inputs.dependency))
        .unwrap();
    assert!(!unknown.stamp.path().exists());
}

#[test]
fn false_ninja_still_keeps_the_actual_requested_compiler_launcher() {
    let ctx = TestCtx::new();
    let (plan, _) = planned(
        &ctx,
        |c| {
            c.ninja_in_file = false;
            c.ccache = Some("requested-launcher".into());
        },
        &|_| None,
    );
    assert!(
        !plan.operations.iter().any(|operation| matches!(operation, CmakeOperation::Generator(_)))
    );
    assert_eq!(defined(&plan, "CMAKE_C_COMPILER_LAUNCHER"), Some(OsStr::new("requested-launcher")));
    assert!(
        matches!(plan.operations.last(), Some(CmakeOperation::BuildTarget(target)) if target == "tpde-plugin")
    );
}

#[test]
fn linker_request_planning_is_lazy_and_does_not_construct_a_linker() {
    let ctx = TestCtx::new();
    let mut session = Session::new(ctx.config("build").stage(1).create_config());
    session.config.llvm_clang_cl = Some("/selected/compiler/clang-cl".into());
    session.config.lld_enabled = true;
    session.config.llvm_use_linker = None;
    session.config.ninja_in_file = true;
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let selected = source_lld_output_dir(&builder, target);
    let before = builder.step_cache().executed_steps().len();
    let llvm_root = ctx.dir().join("LLVM");
    let prior = ctx.dir().join("prior runtime path");
    let plan = tpde_cmake_plan(
        &builder,
        target,
        &ctx.dir().join("tpde"),
        &llvm_root.join("lib/cmake/llvm"),
        &llvm_root,
        Some(&selected),
        &|_| None,
        || vec![prior.clone()],
    )
    .unwrap();
    assert_eq!(
        builder.step_cache().executed_steps().len(),
        before,
        "only the pure planning interval is observed"
    );
    assert!(
        defined(&plan, "CMAKE_MODULE_LINKER_FLAGS")
            .unwrap()
            .to_string_lossy()
            .contains(&format!("'-B{}'", selected.join("bin").display()))
    );
    let paths = plan
        .operations
        .iter()
        .find_map(|operation| match operation {
            CmakeOperation::Env(name, value) if name == helpers::dylib_path_var() => Some(value),
            _ => None,
        })
        .unwrap();
    assert_eq!(env::split_paths(paths).collect::<Vec<_>>(), vec![llvm_root.join("lib"), prior]);
    let own = plan
        .operations
        .iter()
        .position(|operation| {
            matches!(operation,
        CmakeOperation::Define(name, _) | CmakeOperation::InputProgram(name, _) if name == "LLVM_DIR")
        })
        .unwrap();
    let linker_env = plan
        .operations
        .iter()
        .position(|operation| {
            matches!(operation,
        CmakeOperation::Env(name, _) if name == helpers::dylib_path_var())
        })
        .unwrap();
    let common = plan
        .operations
        .iter()
        .position(|operation| {
            matches!(operation,
        CmakeOperation::Define(name, _) | CmakeOperation::InputProgram(name, _) if name == "CMAKE_INSTALL_MESSAGE")
        })
        .unwrap();
    assert!(own < linker_env && linker_env < common);
    let mut static_flags = LdFlags::default();
    assert!(
        requested_lld_settings(
            &builder.config,
            target,
            Some(&selected),
            &llvm_root,
            false,
            || panic!("static linker must not read runtime paths"),
            &mut static_flags
        )
        .unwrap()
        .is_none()
    );
    assert!(static_flags.module.to_string_lossy().contains("-fuse-ld=lld"));
    assert!(verify_requested_lld(&selected, &selected).is_ok());
    assert!(verify_requested_lld(&selected, &ctx.dir().join("different LLD")).is_err());
    let mut flags = LdFlags::default();
    requested_lld_settings(
        &builder.config,
        TargetSelection::from_user("aarch64-apple-darwin"),
        None,
        &llvm_root,
        true,
        || panic!("Apple must not read runtime paths"),
        &mut flags,
    )
    .unwrap();
    assert!(flags.module.is_empty());
    let mut config = ctx.config("build").create_config();
    config.lld_enabled = false;
    config.llvm_thin_lto = true;
    requested_lld_settings(
        &config,
        target,
        None,
        &llvm_root,
        true,
        || panic!("fallback must not read runtime paths"),
        &mut flags,
    )
    .unwrap();
    assert!(flags.module.to_string_lossy().contains("-fuse-ld=lld"));
}
