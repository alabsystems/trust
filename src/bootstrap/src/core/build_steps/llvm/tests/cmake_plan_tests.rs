// Copyright 2026 Andrew Yates
use super::*;
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

fn resolved(
    ctx: &TestCtx,
    change: impl FnOnce(&mut Config),
    target: TargetSelection,
    environment: &dyn Fn(&str) -> Option<OsString>,
) -> CmakePlan {
    let mut config = ctx.config("build").create_config();
    config.rust_remap_debuginfo = false;
    // This is a selected cross-host planning fixture, not physical target work.
    config.host_target = TargetSelection::from_user("aarch64-apple-darwin");
    config.ninja_in_file = true;
    config.llvm_clang_cl = Some("/selected compiler/clang-cl".into());
    let mut session = Session::new(config);
    // These controls vary selected request data, not tool availability. In
    // particular a launcher value is never executed by this pure plan fixture.
    change(&mut session.config);
    let builder = Builder::new(&session);
    resolve_cmake_plan(
        &builder,
        target,
        CommonCmakeOptions { ninja: true, use_compiler_launcher: true },
        LdFlags::default(),
        CcFlags::default(),
        &[],
        environment,
    )
    .unwrap()
}

fn definition<'a>(plan: &'a CmakePlan, name: &str) -> &'a OsStr {
    plan.operations
        .iter()
        .rev()
        .find_map(|operation| match operation {
            CmakeOperation::Define(key, value) | CmakeOperation::InputProgram(key, value)
                if key == name =>
            {
                Some(value.as_os_str())
            }
            _ => None,
        })
        .unwrap()
}

#[test]
fn resolved_flags_paths_and_target_environment_change_the_requested_key() {
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let base = resolved(&ctx, |_| {}, target, &|_| None);
    for configure in [
        (|c: &mut Config| c.llvm_cflags = Some("-DCHANGED_C".into())) as fn(&mut Config),
        |c| c.llvm_cxxflags = Some("-DCHANGED_CXX".into()),
        |c| c.llvm_ldflags = Some("-Wl,changed".into()),
        |c| c.llvm_clang_cl = Some("/another compiler/clang-cl".into()),
        |c| c.ccache = Some("another-launcher".into()),
    ] {
        let changed = resolved(&ctx, configure, target, &|_| None);
        assert_ne!(base.requested_key(), changed.requested_key());
    }
    let vars = [
        (format!("LDFLAGS_{}", target.triple), "target-dash"),
        (format!("LDFLAGS_{}", target.triple.replace('-', "_")), "target-underscore"),
        ("TARGET_LDFLAGS".into(), "target-kind"),
        ("LDFLAGS".into(), "fallback"),
    ];
    for start in 0..vars.len() {
        let environment = |key: &str| {
            vars[start..]
                .iter()
                .find_map(|(name, value)| (name == key).then(|| OsString::from(*value)))
        };
        let plan = resolved(&ctx, |_| {}, target, &environment);
        assert!(
            definition(&plan, "CMAKE_MODULE_LINKER_FLAGS")
                .to_string_lossy()
                .contains(vars[start].1)
        );
        assert_ne!(base.requested_key(), plan.requested_key());
    }
    // Changing an overridden lower-priority variable cannot change the actual request.
    let left = resolved(&ctx, |_| {}, target, &|key| {
        if key == vars[0].0.as_str() {
            Some("selected".into())
        } else if key == "LDFLAGS" {
            Some("old".into())
        } else {
            None
        }
    });
    let right = resolved(&ctx, |_| {}, target, &|key| {
        if key == vars[0].0.as_str() {
            Some("selected".into())
        } else if key == "LDFLAGS" {
            Some("new".into())
        } else {
            None
        }
    });
    assert_eq!(left.requested_key(), right.requested_key());
}

#[test]
fn requested_operation_order_is_preserved_but_execution_share_is_not_configuration() {
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let mut plan = resolved(&ctx, |_| {}, target, &|_| None);
    let original = plan.requested_key();
    plan.parallel_build(1).quiet_build().parallel_build(8);
    assert_eq!(plan.requested_key(), original);
    plan.define("CMAKE_C_FLAGS", "owner override").define("CMAKE_C_FLAGS", "final owner override");
    assert_eq!(definition(&plan, "CMAKE_C_FLAGS"), OsStr::new("final owner override"));
    let writes: Vec<_> = plan
        .operations
        .iter()
        .filter_map(|operation| match operation {
            CmakeOperation::Define(name, value) | CmakeOperation::InputProgram(name, value)
                if name == "CMAKE_C_FLAGS" =>
            {
                Some(value.as_os_str())
            }
            _ => None,
        })
        .collect();
    assert!(writes.len() >= 3);
    assert_eq!(
        writes[writes.len() - 2..],
        [OsStr::new("owner override"), OsStr::new("final owner override")]
    );
    assert_ne!(plan.requested_key(), original);
}

#[test]
fn platform_selection_retains_apple_overrides_and_msvc_early_return() {
    let ctx = TestCtx::new();
    let apple = TargetSelection::from_user("aarch64-apple-ios");
    let plan = resolved(&ctx, |_| {}, apple, &|_| None);
    assert_eq!(definition(&plan, "CMAKE_SYSTEM_NAME"), OsStr::new("Darwin"));
    assert_eq!(definition(&plan, "CMAKE_OSX_SYSROOT"), OsStr::new("/"));
    assert_eq!(definition(&plan, "CMAKE_OSX_ARCHITECTURES"), OsStr::new("arm64"));
    let mut config = ctx.config("build").create_config();
    config.rust_remap_debuginfo = false;
    let session = Session::new(config);
    let builder = Builder::new(&session);
    let msvc = TargetSelection::from_user("x86_64-pc-windows-msvc");
    let plan = resolve_cmake_plan(
        &builder,
        msvc,
        CommonCmakeOptions { ninja: false, use_compiler_launcher: true },
        LdFlags::default(),
        CcFlags::default(),
        &[],
        &|_| None,
    )
    .unwrap();
    assert!(!plan.operations.iter().any(
        |operation| matches!(operation, CmakeOperation::Define(key, _) | CmakeOperation::InputProgram(key, _) if key == "CMAKE_C_COMPILER")
    ));
    assert!(plan.operations.iter().any(|operation| matches!(operation, CmakeOperation::Env(key, value) if key == "DESTDIR" && value.is_empty())));
}

#[test]
fn configured_ninja_selection_does_not_require_a_build_tool_on_cache_hit() {
    let ctx = TestCtx::new();
    let mut config = ctx.config("build").create_config();
    config.ninja_in_file = true;
    let session = Session::new(config);
    assert!(
        session.selected_ninja_with(|| panic!("configured choice must not query availability"))
    );
    let mut config = ctx.config("build").create_config();
    config.ninja_in_file = false;
    config.host_target = TargetSelection::from_user("x86_64-pc-windows-msvc");
    let session = Session::new(config);
    assert!(!session.selected_ninja_with(|| false));
    assert!(session.selected_ninja_with(|| true));
}

// This may query a real compiler family; only the bounded manual lane calls it.
#[cfg(unix)]
fn assert_selected_tool_suppression(session: &mut Session) {
    let target = session.config.host_target;
    // Build a real cc-rs Tool description; do not execute a compilation with
    // these synthetic requested flags or claim target/compiler readiness.
    let tool = cc::Build::new()
        .target(&target.triple)
        .host(&target.triple)
        .opt_level(0)
        .debug(false)
        .no_default_flags(true)
        .flag("-mmacosx-version-min=10.0")
        .flag("-DKEEP_SELECTED_FLAG")
        .get_compiler();
    let original_cc = session.cc.insert(target, tool.clone());
    let original_cxx = session.cxx.insert(target, tool);
    {
        let builder = Builder::new(&session);
        let ordinary = resolve_cmake_plan(
            &builder,
            target,
            CommonCmakeOptions { ninja: false, use_compiler_launcher: false },
            LdFlags::default(),
            CcFlags::default(),
            &[],
            &|_| None,
        )
        .unwrap();
        let filtered = resolve_cmake_plan(
            &builder,
            target,
            CommonCmakeOptions { ninja: false, use_compiler_launcher: false },
            LdFlags::default(),
            CcFlags::default(),
            &["-mmacosx-version-min="],
            &|_| None,
        )
        .unwrap();
        for key in ["CMAKE_C_FLAGS", "CMAKE_CXX_FLAGS", "CMAKE_ASM_FLAGS"] {
            assert!(definition(&ordinary, key).to_string_lossy().contains("-mmacosx-version-min="));
            assert!(
                !definition(&filtered, key).to_string_lossy().contains("-mmacosx-version-min=")
            );
            assert!(definition(&filtered, key).to_string_lossy().contains("-DKEEP_SELECTED_FLAG"));
        }
        assert_ne!(ordinary.requested_key(), filtered.requested_key());
    }
    session.cxx.remove(&target);
    {
        let builder = Builder::new(&session);
        assert!(
            resolve_cmake_plan(
                &builder,
                target,
                CommonCmakeOptions { ninja: false, use_compiler_launcher: false },
                LdFlags::default(),
                CcFlags::default(),
                &[],
                &|_| None
            )
            .is_none()
        );
    }
    match original_cc {
        Some(tool) => {
            session.cc.insert(target, tool);
        }
        None => {
            session.cc.remove(&target);
        }
    }
    match original_cxx {
        Some(tool) => {
            session.cxx.insert(target, tool);
        }
        None => {
            session.cxx.remove(&target);
        }
    }
}

#[test]
fn unresolved_selected_tool_data_cannot_create_a_requested_plan() {
    let ctx = TestCtx::new();
    let mut config = ctx.config("build").create_config();
    config.rust_remap_debuginfo = false;
    let mut session = Session::new(config);
    let target = session.config.host_target;
    session.config.set_dry_run(crate::core::config::DryRun::Disabled);
    session.cc.clear();
    session.cxx.clear();
    let builder = Builder::new(&session);
    assert!(
        enzyme_cmake_plan(
            &builder,
            target,
            &ctx.dir().join("out"),
            &ctx.dir().join("llvm"),
            &|_| None
        )
        .is_none()
    );
}

#[test]
fn enzyme_uses_its_resolved_plan_for_profile_flags_paths_and_cache_decision() {
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let apple = TargetSelection::from_user("aarch64-apple-darwin");
    let out = ctx.dir().join("enzyme output");
    let llvm = ctx.dir().join("selected llvm/lib/cmake/llvm");
    fs::create_dir_all(&out).unwrap();
    let library = out.join("owned library.so");
    fs::write(&library, b"synthetic library, not LLVM construction").unwrap();
    let request = |configure: fn(&mut Config),
                   target,
                   output: &Path,
                   llvm_dir: &Path,
                   environment: &dyn Fn(&str) -> Option<OsString>| {
        let mut config = ctx.config("build").create_config();
        config.rust_remap_debuginfo = false;
        config.ninja_in_file = true;
        config.llvm_clang_cl = Some("/selected/compiler".into());
        config.llvm_optimize = true;
        config.llvm_release_debuginfo = false;
        config.llvm_thin_lto = false;
        configure(&mut config);
        let session = Session::new(config);
        let builder = Builder::new(&session);
        enzyme_cmake_plan(&builder, target, output, llvm_dir, environment).unwrap()
    };
    let original = request(|_| {}, target, &out, &llvm, &|_| None);
    let stamp =
        enzyme_stamp(&out, "sources", Some("recorded dependency"), &original.requested_key());
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    fs::write(&library, b"synthetic library, not LLVM construction").unwrap();
    stamp.write().unwrap();
    assert!(cached_enzyme(&stamp, &library, Some("recorded dependency")).is_some());
    for (configure, expected_profile, expected_linker) in [
        (
            (|c: &mut Config| c.llvm_release_debuginfo = true) as fn(&mut Config),
            "RelWithDebInfo",
            false,
        ),
        (|c| c.llvm_optimize = false, "Debug", false),
        (|c| c.llvm_thin_lto = true, "Release", true),
        (|c| c.llvm_cflags = Some("-DNEW_REQUEST".into()), "Release", false),
        (|c| c.llvm_clang_cl = Some("/changed/compiler".into()), "Release", false),
    ] {
        let plan = request(configure, target, &out, &llvm, &|_| None);
        assert!(plan.operations.iter().any(|operation| matches!(operation, CmakeOperation::Profile(value) if value == expected_profile)));
        assert_eq!(
            definition(&plan, "CMAKE_MODULE_LINKER_FLAGS")
                .to_string_lossy()
                .contains("-fuse-ld=lld"),
            expected_linker
        );
        let changed =
            enzyme_stamp(&out, "sources", Some("recorded dependency"), &plan.requested_key());
        assert!(cached_enzyme(&changed, &library, Some("recorded dependency")).is_none());
    }
    let changed_env =
        request(|_| {}, target, &out, &llvm, &|key| (key == "LDFLAGS").then(|| "-Wl,new".into()));
    assert_ne!(changed_env.requested_key(), original.requested_key());
    let changed_llvm = request(|_| {}, target, &out, &ctx.dir().join("another llvm"), &|_| None);
    assert_ne!(changed_llvm.requested_key(), original.requested_key());
    let mut changed_source = request(|_| {}, target, &out, &llvm, &|_| None);
    changed_source.source(ctx.dir().join("another source"));
    assert_ne!(changed_source.requested_key(), original.requested_key());
    let changed_out = request(|_| {}, target, &ctx.dir().join("another output"), &llvm, &|_| None);
    assert_ne!(changed_out.requested_key(), original.requested_key());
    let apple_default = request(|_| {}, apple, &out, &llvm, &|_| None);
    let apple_thin = request(|c| c.llvm_thin_lto = true, apple, &out, &llvm, &|_| None);
    assert_eq!(
        apple_default.requested_key(),
        apple_thin.requested_key(),
        "Apple's own linker choice is unchanged"
    );
}

#[cfg(unix)]
#[test]
fn requested_key_preserves_non_utf8_values_instead_of_lossy_display() {
    use std::os::unix::ffi::OsStringExt;
    let mut left = CmakePlan::default();
    let mut right = CmakePlan::default();
    let left_value = OsString::from_vec(vec![b'a', 0xff]);
    let right_value = OsString::from_vec(vec![b'a', 0xfe]);
    assert_eq!(left_value.to_string_lossy(), right_value.to_string_lossy());
    left.env("FLAGS", left_value);
    right.env("FLAGS", right_value);
    assert_ne!(left.requested_key(), right.requested_key());
}

// This invokes real managed CMake; the separate maintained owned-process lane
// supplies the 60-second hang detector and authentic inherited transport.
#[cfg(unix)]
#[test]
#[ignore = "run only under maintained owned-process CMake qualification lane"]
fn real_cmake_none_project_observes_the_same_ordered_plan() {
    let ctx = TestCtx::new();
    let mut config = ctx
        .config("build")
        .stage(1)
        .path("library/std")
        .args(&["--set", "rust.trust-source-identity=false"])
        .create_config_with_fixed_budget(Some(1));
    config.set_dry_run(crate::core::config::DryRun::Disabled);
    config.rust_remap_debuginfo = false;
    config.ninja_in_file = true;
    config.llvm_cflags = Some("-DPLAN_C=1".into());
    config.llvm_cxxflags = Some("-DPLAN_CXX=2".into());
    config.llvm_ldflags = Some("-Wl,plan-request".into());
    assert_eq!(
        crate::utils::trust_preparation::PreparationScope::for_config(&config),
        crate::utils::trust_preparation::PreparationScope::RequestSources
    );
    let mut session = Session::new(config);
    assert_selected_tool_suppression(&mut session);
    let builder = Builder::new(&session);
    let project = ctx.dir().join("project");
    let output = ctx.dir().join("output");
    fs::create_dir_all(&project).unwrap();
    fs::write(project.join("CMakeLists.txt"), r#"cmake_minimum_required(VERSION 3.20)
project(BootstrapPlan NONE)
file(WRITE "${CMAKE_BINARY_DIR}/observed.txt"
 "c=${CMAKE_C_FLAGS}\ncxx=${CMAKE_CXX_FLAGS}\nasm=${CMAKE_ASM_FLAGS}\nmodule=${CMAKE_MODULE_LINKER_FLAGS}\nprofile=${CMAKE_BUILD_TYPE}\nduplicate=${PLAN_DUPLICATE}\nenvironment=$ENV{TRUST_CMAKE_PLAN_OBSERVE}\ncommand=${CMAKE_COMMAND}\nversion=${CMAKE_VERSION}\ntpde_assertions=${TPDE_ENABLE_ASSERTIONS}\n")
add_custom_target(observe COMMAND "${CMAKE_COMMAND}" -E touch "${CMAKE_BINARY_DIR}/built.marker")
"#).unwrap();
    let mut plan = enzyme_cmake_plan(
        &builder,
        builder.host_target,
        &output,
        &ctx.dir().join("unused LLVM directory in NONE project"),
        &|_| None,
    )
    .unwrap();
    plan.define("PLAN_DUPLICATE", "first").define("PLAN_DUPLICATE", "last");
    plan.env("TRUST_CMAKE_PLAN_OBSERVE", "first").env("TRUST_CMAKE_PLAN_OBSERVE", "last");
    plan.source(&project);
    let request = plan.requested_key();
    let mut cmake = plan.new_config();
    cmake.build_target("observe");
    let prepared = cmake.try_prepare().expect("managed CMake input preparation");
    let first_inputs =
        prepared.cache_inputs().expect("native explicit Ninja must remain reusable").to_vec();
    let mut quiet = cmake.clone();
    quiet.build_arg("--quiet");
    let quiet_prepared = quiet.try_prepare().expect("quiet preparation");
    assert_eq!(quiet_prepared.cache_inputs(), Some(first_inputs.as_slice()));
    drop(quiet_prepared);
    drop(quiet);
    // Later caller mutations must invalidate the request key, but must not
    // reselect or change the first snapshot consumed below.
    cmake.define("PLAN_DUPLICATE", "changed-after-preparation");
    cmake.env("TRUST_CMAKE_PLAN_OBSERVE", "changed-after-preparation");
    let changed = cmake.try_prepare().expect("changed input preparation");
    assert_ne!(
        changed.cache_inputs().expect("changed native request remains reusable"),
        first_inputs.as_slice()
    );
    drop(changed);
    prepared.build();
    let observed = fs::read_to_string(output.join("build/observed.txt")).unwrap();
    for (label, key) in [
        ("c", "CMAKE_C_FLAGS"),
        ("cxx", "CMAKE_CXX_FLAGS"),
        ("asm", "CMAKE_ASM_FLAGS"),
        ("module", "CMAKE_MODULE_LINKER_FLAGS"),
    ] {
        assert!(observed.lines().any(|line| line == format!("{label}={}", definition(&plan, key).to_str().unwrap())), "{observed}");
    }
    assert!(observed.contains("duplicate=last\n"), "{observed}");
    assert!(observed.contains("environment=last\n"), "{observed}");
    assert!(
        observed
            .lines()
            .any(|line| line == format!("profile={}", get_llvm_profile(&builder.config))),
        "{observed}"
    );
    assert!(output.join("build/built.marker").is_file(), "the selected build target must execute");
    let command = observed.lines().find_map(|line| line.strip_prefix("command=")).unwrap();
    let selected = env::var_os("CMAKE").expect("qualification lane must select managed CMake");
    assert_eq!(
        fs::canonicalize(command).unwrap(),
        fs::canonicalize(selected).unwrap(),
        "the actual CMake program must match the selected managed tool"
    );
    assert_eq!(plan.requested_key(), request);
    // The original mutable builder remains usable after isolated preparation,
    // including repeated builds and later ordered overrides.
    for value in ["changed-after-preparation", "changed-again"] {
        cmake.define("PLAN_DUPLICATE", value).env("TRUST_CMAKE_PLAN_OBSERVE", value);
        fs::remove_file(output.join("build/built.marker")).unwrap();
        cmake.always_configure(true).build();
        let observed = fs::read_to_string(output.join("build/observed.txt")).unwrap();
        assert!(observed.contains(&format!("duplicate={value}\n")), "{observed}");
        assert!(observed.contains(&format!("environment={value}\n")), "{observed}");
        assert!(output.join("build/built.marker").is_file());
    }

    // This ignored case runs alone in the maintained --exact/--test-threads=1
    // actor. The default concurrent suite never changes process cwd.
    struct RestoreCwd(PathBuf);
    impl Drop for RestoreCwd {
        fn drop(&mut self) {
            env::set_current_dir(&self.0).expect("restore the isolated actor cwd");
        }
    }
    let prepare_at = ctx.dir().join("prepare-cwd");
    let execute_at = ctx.dir().join("execute-cwd");
    fs::create_dir_all(&prepare_at).unwrap();
    fs::create_dir_all(&execute_at).unwrap();
    let restore = RestoreCwd(env::current_dir().unwrap());
    env::set_current_dir(&prepare_at).unwrap();
    let mut relative = cmake.clone();
    relative.out_dir("relative-output");
    let relative_prepared = relative.try_prepare().expect("relative output preparation");
    assert!(relative_prepared.cache_inputs().is_some());
    env::set_current_dir(&execute_at).unwrap();
    let returned = relative_prepared.build();
    drop(restore);
    assert!(returned.is_absolute());
    let expected = prepare_at.join("relative-output");
    assert_eq!(fs::canonicalize(&returned).unwrap(), fs::canonicalize(&expected).unwrap());
    let observed = fs::read_to_string(expected.join("build/observed.txt")).unwrap();
    assert!(observed.contains("duplicate=changed-again\n"), "{observed}");
    assert!(observed.contains("environment=changed-again\n"), "{observed}");
    assert!(expected.join("build/built.marker").is_file());
    assert!(!execute_at.join("relative-output").exists());

    // Retain the actual Ninja/cache/output evidence even if the diagnostic is
    // red. This directory is owned by this one maintained manual invocation.
    let retained = tempfile::Builder::new().prefix("cmake-generation-").tempdir().unwrap().keep();
    println!("retained CMake generation evidence: {}", retained.display());
    let source = retained.join("source");
    let out = retained.join("output");
    fs::create_dir_all(&source).unwrap();
    fs::write(
        source.join("CMakeLists.txt"),
        r#"cmake_minimum_required(VERSION 3.20)
project(RetainedGeneration NONE)
set(INPUT "${CMAKE_CURRENT_SOURCE_DIR}/input.txt")
set(PAYLOAD "${CMAKE_BINARY_DIR}/payload.txt")
file(WRITE "${CMAKE_BINARY_DIR}/request-observed.txt" "${OWNER_REQUEST}")
add_custom_command(OUTPUT "${PAYLOAD}"
 COMMAND "${CMAKE_COMMAND}" -E copy "${INPUT}" "${PAYLOAD}"
 DEPENDS "${INPUT}"
 VERBATIM)
add_custom_target(copy-output DEPENDS "${PAYLOAD}")
"#,
    )
    .unwrap();
    let input = source.join("input.txt");
    let old_bytes = b"first\n";
    let new_bytes = b"other\n";
    assert_eq!(old_bytes.len(), new_bytes.len());
    fs::write(&input, old_bytes).unwrap();
    let mut retained_plan = enzyme_cmake_plan(
        &builder,
        builder.host_target,
        &out,
        &ctx.dir().join("unused LLVM directory in retained NONE project"),
        &|_| None,
    )
    .unwrap();
    retained_plan.source(&source).define("OWNER_REQUEST", "first");
    let first_key = retained_plan.requested_key();
    let mut first_config = retained_plan.new_config();
    first_config.build_target("copy-output");
    let first = first_config.try_prepare().expect("initial retained generation preparation");
    let first_inputs =
        first.cache_inputs().expect("initial native request must be reusable").to_vec();
    let first_source = observe_cmake_sources(&source, &out).unwrap().unwrap();
    let first_stamp = BuildStamp::new(&out)
        .with_prefix("controlled-request")
        .add_stamp(&first_key)
        .add_stamp(&first_source);
    begin_cmake_miss(&first_stamp, CmakeGeneration::Known).unwrap();
    first.build();
    let payload = out.join("build/payload.txt");
    let old_payload = fs::read(&payload).unwrap();
    assert_eq!(old_payload, old_bytes);
    assert!(own_source_unchanged(
        Some(&first_source),
        observe_cmake_sources(&source, &out).unwrap().as_deref()
    ));
    first_stamp.write().unwrap();
    assert!(first_stamp.is_up_to_date());
    fs::copy(first_stamp.path(), retained.join("first-completion.stamp")).unwrap();
    fs::copy(&payload, retained.join("first-payload.txt")).unwrap();
    let modified = fs::metadata(&input).unwrap().modified().unwrap();
    fs::copy(out.join("build/build.ninja"), retained.join("first-build.ninja")).unwrap();
    fs::copy(out.join("build/CMakeCache.txt"), retained.join("first-CMakeCache.txt")).unwrap();

    // Only Rust changes the input; reconfiguration cannot write it back.
    fs::write(&input, new_bytes).unwrap();
    crate::utils::helpers::set_file_times(&input, fs::FileTimes::new().set_modified(modified))
        .unwrap();
    assert_eq!(fs::read(&input).unwrap(), new_bytes);
    assert_eq!(fs::metadata(&input).unwrap().modified().unwrap(), modified);
    retained_plan.define("OWNER_REQUEST", "other");
    let second_key = retained_plan.requested_key();
    assert_ne!(first_key, second_key);
    let mut second_config = retained_plan.new_config();
    second_config.build_target("copy-output");
    let second = second_config.try_prepare().expect("changed retained generation preparation");
    assert_ne!(
        second.cache_inputs().expect("changed native request remains reusable"),
        first_inputs.as_slice()
    );
    let second_source = observe_cmake_sources(&source, &out).unwrap().unwrap();
    assert_ne!(
        first_source, second_source,
        "actual source bytes must change identity despite preserved mtime"
    );
    let second_stamp = BuildStamp::new(&out)
        .with_prefix("controlled-request")
        .add_stamp(&second_key)
        .add_stamp(&second_source);
    assert!(!second_stamp.is_up_to_date(), "the actual request completion must miss");
    println!(
        "retained generation before rebuild: first_key={first_key} second_key={second_key} input_mtime={modified:?} old_payload={old_payload:?} new_input={new_bytes:?}"
    );
    begin_cmake_miss(&second_stamp, CmakeGeneration::Known).unwrap();
    second.build();
    assert!(own_source_unchanged(
        Some(&second_source),
        observe_cmake_sources(&source, &out).unwrap().as_deref()
    ));
    let observed_request = fs::read_to_string(out.join("build/request-observed.txt")).unwrap();
    let actual = fs::read(&payload).unwrap();
    let after_modified = fs::metadata(&input).unwrap().modified().unwrap();
    println!(
        "retained generation facts: first_key={first_key} second_key={second_key} input_mtime={modified:?} restored_mtime={after_modified:?} old_payload={old_payload:?} new_input={new_bytes:?} actual_payload={actual:?} configured_request={observed_request:?}"
    );
    assert_eq!(observed_request, "other", "the second actual CMake configuration must run");
    assert_eq!(after_modified, modified);
    assert_eq!(
        actual, new_bytes,
        "a request-key miss must not complete with the previous generated payload"
    );

    // Exercise the actual TPDE plan and preparation on a host NONE project.
    // Requested LLVM/LLD paths are data here, not a claim that TPDE or LLVM was built.
    let tpde_out = ctx.dir().join("tpde-plan-NONE");
    let requested_lld = in_tree_lld_requested(&builder.config, builder.host_target)
        .then(|| source_lld_output_dir(&builder, builder.host_target));
    let mut tpde_plan = tpde_cmake_plan(
        &builder,
        builder.host_target,
        &tpde_out,
        &ctx.dir().join("unused LLVM cmake path"),
        &ctx.dir().join("unused LLVM root"),
        requested_lld.as_deref(),
        &|_| None,
        helpers::dylib_path,
    )
    .unwrap();
    tpde_plan.source(&project).build_target("observe");
    tpde_plan.define("PLAN_DUPLICATE", "tpde").env("TRUST_CMAKE_PLAN_OBSERVE", "tpde");
    let tpde_config = tpde_plan.new_config();
    let tpde_prepared = tpde_config.try_prepare().expect("actual host TPDE plan preparation");
    assert!(
        prepared_cmake_request(b"tpde-prepared-cmake:v1", &tpde_plan, &tpde_prepared).is_some()
    );
    tpde_prepared.build();
    let tpde_observed = fs::read_to_string(tpde_out.join("build/observed.txt")).unwrap();
    for (label, key) in [
        ("c", "CMAKE_C_FLAGS"),
        ("cxx", "CMAKE_CXX_FLAGS"),
        ("module", "CMAKE_MODULE_LINKER_FLAGS"),
        ("tpde_assertions", "TPDE_ENABLE_ASSERTIONS"),
    ] {
        assert!(
            tpde_observed
                .lines()
                .any(|line| line
                    == format!("{label}={}", definition(&tpde_plan, key).to_str().unwrap())),
            "{tpde_observed}"
        );
    }
    assert!(tpde_observed.contains("environment=tpde\n"), "{tpde_observed}");
    assert!(tpde_out.join("build/built.marker").is_file());

    // Two independent NONE targets exercise the same ordered set lifecycle as
    // Sanitizers, without inventing a compiler-rt build or an LLVM provider.
    let set_source = ctx.dir().join("sanitizer-set-NONE-source");
    let set_output = ctx.dir().join("sanitizer-set-NONE-output");
    fs::create_dir(&set_source).unwrap();
    fs::create_dir(&set_output).unwrap();
    fs::write(set_output.join("old-generation"), b"must be cleared once").unwrap();
    fs::write(set_source.join("first.input"), b"independent first runtime").unwrap();
    fs::write(set_source.join("second.input"), b"independent second runtime").unwrap();
    fs::write(set_source.join("CMakeLists.txt"), r#"cmake_minimum_required(VERSION 3.20)
project(SanitizerSet NONE)
foreach(name first second)
  add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/${name}.a"
    COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_CURRENT_SOURCE_DIR}/${name}.input" "${CMAKE_BINARY_DIR}/${name}.a"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${name}.input" VERBATIM)
  add_custom_target(build-${name} DEPENDS "${CMAKE_BINARY_DIR}/${name}.a")
endforeach()
"#).unwrap();
    let selected = ["first", "second"]
        .into_iter()
        .map(|name| SanitizerRuntime {
            cmake_target: format!("build-{name}"),
            path: set_output.join("build").join(format!("{name}.a")),
            name: format!("{name}.a"),
        })
        .collect::<Vec<_>>();
    let set_plan = sanitizer_cmake_plan(
        &builder,
        builder.host_target,
        &set_source,
        &set_output,
        &ctx.dir().join("unused LLVM config request"),
        &|_| None,
    )
    .unwrap();
    let targets = prepare_cmake_targets(&set_plan, &selected);
    let request = sanitizer_request_key(&selected, &targets)
        .expect("both actual native requests must be reusable");
    let source = observe_cmake_sources(&set_source, &set_output).unwrap().unwrap();
    let eligible =
        reusable_cmake_inputs(Some(&source), Some("controlled NONE provider data"), Some(&request));
    let stamp = sanitizer_stamp(&set_output, eligible);
    build_cmake_target_set(&stamp, CmakeGeneration::Known, targets).unwrap();
    assert!(!set_output.join("old-generation").exists());
    assert_eq!(fs::read(&selected[0].path).unwrap(), b"independent first runtime");
    assert_eq!(fs::read(&selected[1].path).unwrap(), b"independent second runtime");
    assert!(sanitizer_artifacts_exist(&selected));
    assert!(
        !stamp.path().exists(),
        "all target builds still do not constitute provider completion"
    );
    assert!(cmake_generation_matches(&stamp));
    complete_with_unchanged_cmake_source(&set_source, &set_output, Some(&source), || stamp.write())
        .unwrap();
    assert!(cached_sanitizers(&stamp, &selected, eligible));
    fs::remove_file(&selected[1].path).unwrap();
    assert!(
        !cached_sanitizers(&stamp, &selected, eligible),
        "an incomplete target set never reuses completion"
    );

    // The real install copies three files through the actual offload lifecycle.
    // Paths/mode below are requested fixture data, not a fabricated LLVM provider.
    let install_source = ctx.dir().join("offload-install-NONE-source");
    let install_output = ctx.dir().join("offload-install-NONE-output");
    let offload = omp_offload_output(&install_output);
    fs::create_dir_all(install_source.join("lib")).unwrap();
    for (index, path) in offload.offload.iter().enumerate() {
        fs::write(
            install_source.join("lib").join(path.file_name().unwrap()),
            format!("controlled installed library {index}"),
        )
        .unwrap();
    }
    fs::write(install_source.join("CMakeLists.txt"), r#"cmake_minimum_required(VERSION 3.20)
project(OffloadInstall NONE)
file(WRITE "${CMAKE_BINARY_DIR}/observed.txt" "c=${CMAKE_C_COMPILER}\ncxx=${CMAKE_CXX_COMPILER}\nruntimes=${LLVM_ENABLE_RUNTIMES}\n")
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/lib/" DESTINATION lib)
"#).unwrap();
    let clang = OffloadClang {
        clang: builder.cc(builder.host_target),
        clangxx: builder.cxx(builder.host_target).unwrap(),
        cmake_dir: None,
    };
    let queried_library = query_offload_cxx_library(&builder, builder.host_target)
        .expect("actual configured CXX metadata query");
    let install_requested_lld = in_tree_lld_requested(&builder.config, builder.host_target)
        .then(|| source_lld_output_dir(&builder, builder.host_target));
    let mut install_plan = omp_offload_cmake_plan(
        &builder,
        builder.host_target,
        &install_output,
        OffloadLlvmRequest {
            root: &ctx.dir().join("unused LLVM request root"),
            cmake: &ctx.dir().join("unused LLVM request cmake"),
            link_shared: false,
        },
        &clang,
        queried_library.as_deref(),
        install_requested_lld.as_deref(),
        &|_| None,
        Vec::new,
    )
    .unwrap();
    install_plan.source(&install_source);
    let mut install_config = install_plan.new_config();
    let install_prepared =
        install_config.try_prepare().expect("actual offload install preparation");
    let request =
        prepared_cmake_request(b"omp-offload-prepared:v1", &install_plan, &install_prepared)
            .expect("actual offload prepared inputs");
    let source = observe_cmake_sources(&install_source, &install_output).unwrap().unwrap();
    let inputs =
        reusable_cmake_inputs(Some(&source), Some("controlled NONE provider data"), Some(&request));
    let stamp = omp_offload_stamp(&install_output, inputs);
    build_omp_offload_install(
        &stamp,
        CmakeGeneration::Known,
        &mut install_config,
        Some(install_prepared),
        &offload,
    )
    .unwrap();
    for (index, path) in offload.offload.iter().enumerate() {
        assert_eq!(
            fs::read(path).unwrap(),
            format!("controlled installed library {index}").as_bytes()
        );
    }
    let observed = fs::read_to_string(install_output.join("build/observed.txt")).unwrap();
    assert!(observed.contains(&format!("c={}\n", clang.clang.display())), "{observed}");
    assert!(observed.contains(&format!("cxx={}\n", clang.clangxx.display())), "{observed}");
    assert!(observed.contains("runtimes=openmp;offload\n"), "{observed}");
    assert!(!stamp.path().exists(), "successful install is not selected provider completion");
    complete_with_unchanged_cmake_source(&install_source, &install_output, Some(&source), || {
        stamp.write()
    })
    .unwrap();
    assert!(cached_omp_offload(&stamp, &offload, inputs));
    fs::remove_file(&offload.offload[2]).unwrap();
    assert!(!cached_omp_offload(&stamp, &offload, inputs));
}
