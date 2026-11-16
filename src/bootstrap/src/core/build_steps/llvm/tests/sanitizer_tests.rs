// Copyright 2026 Andrew Yates
// Controlled files/request data do not claim a compiler-rt or LLVM build.
use super::*;
use crate::utils::tests::TestCtx;

fn runtimes(output: &Path) -> Vec<SanitizerRuntime> {
    ["first", "second"]
        .into_iter()
        .map(|name| SanitizerRuntime {
            cmake_target: format!("build-{name}"),
            path: output.join(format!("{name}.a")),
            name: format!("{name}.a"),
        })
        .collect()
}

fn request_rows(source: &Path, requests: &[Option<&str>]) -> Vec<CmakeTargetBuild> {
    // Aggregate-input fixtures, not fabricated native Prepared observations.
    requests
        .iter()
        .map(|request| CmakeTargetBuild {
            config: cmake::Config::new(source),
            prepared: None,
            request: request.map(str::to_owned),
        })
        .collect()
}

#[test]
fn sanitizer_source_stamp_distinguishes_staged_bytes_and_sibling_cmake_inputs() {
    use crate::utils::trust_repo_cache::git;
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("llvm-project");
    let output = temp.path().join("sanitizers");
    fs::create_dir_all(source.join("compiler-rt")).unwrap();
    fs::create_dir(source.join("cmake")).unwrap();
    let input = source.join("compiler-rt/input");
    fs::write(&input, b"first").unwrap();
    fs::write(source.join("cmake/shared.cmake"), b"module A").unwrap();
    git(&source, &["init", "-q"]).unwrap();
    git(&source, &["add", "."]).unwrap();
    git(
        &source,
        &[
            "-c",
            "user.name=Source fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "fixture",
        ],
    )
    .unwrap();
    fs::write(&input, b"stageA").unwrap();
    git(&source, &["add", "."]).unwrap();
    let diff_a = git(&source, &["diff", "."]).unwrap();
    let status_a =
        git(&source, &["status", ".", "--porcelain", "-z", "--untracked-files=normal"]).unwrap();
    let head_a = git(&source, &["rev-parse", "HEAD"]).unwrap();
    let source_a = observe_cmake_sources(&source, &output).unwrap().unwrap();
    let rows = request_rows(&source, &[Some("first request"), Some("second request")]);
    let runtimes = runtimes(&output);
    let request = sanitizer_request_key(&runtimes, &rows).unwrap();
    let eligible = reusable_cmake_inputs(Some(&source_a), Some("provider data"), Some(&request));
    let stamp_a = sanitizer_stamp(&output, eligible);
    begin_cmake_miss(&stamp_a, CmakeGeneration::Known).unwrap();
    for runtime in &runtimes {
        fs::write(&runtime.path, b"controlled runtime").unwrap();
    }
    stamp_a.write().unwrap();
    assert!(cached_sanitizers(&stamp_a, &runtimes, eligible));
    fs::write(&input, b"stageB").unwrap();
    git(&source, &["add", "."]).unwrap();
    assert!(diff_a.is_empty());
    assert_eq!(diff_a, git(&source, &["diff", "."]).unwrap());
    assert_eq!(
        status_a,
        git(&source, &["status", ".", "--porcelain", "-z", "--untracked-files=normal"]).unwrap()
    );
    assert_eq!(head_a, git(&source, &["rev-parse", "HEAD"]).unwrap());
    let source_b = observe_cmake_sources(&source, &output).unwrap().unwrap();
    assert_ne!(
        source_a, source_b,
        "the old diff/status/revision inputs collide but actual bytes differ"
    );
    let changed = reusable_cmake_inputs(Some(&source_b), Some("provider data"), Some(&request));
    let stamp_b = sanitizer_stamp(&output, changed);
    assert!(!cached_sanitizers(&stamp_b, &runtimes, changed));
    assert!(!cmake_generation_matches(&stamp_b));
    fs::write(source.join("cmake/shared.cmake"), b"module B").unwrap();
    assert_ne!(
        source_b,
        observe_cmake_sources(&source, &output).unwrap().unwrap(),
        "compiler-rt's sibling CMake is an own-source input"
    );
}

#[test]
fn ordered_sanitizer_request_set_keeps_duplicates_paths_names_and_unknowns() {
    let temp = tempfile::tempdir().unwrap();
    let selected = runtimes(temp.path());
    let rows = || request_rows(temp.path(), &[Some("request A"), Some("request B")]);
    let key = sanitizer_request_key(&selected, &rows()).unwrap();
    let mut reordered = selected.clone();
    reordered.swap(0, 1);
    let mut reordered_rows = rows();
    reordered_rows.swap(0, 1);
    assert_ne!(key, sanitizer_request_key(&reordered, &reordered_rows).unwrap());
    for change in [
        (|r: &mut SanitizerRuntime| r.cmake_target.push_str("-other")) as fn(&mut SanitizerRuntime),
        |r| r.path = r.path.with_extension("changed"),
        |r| r.name.push_str("-other"),
    ] {
        let mut changed = selected.clone();
        change(&mut changed[1]);
        assert_ne!(key, sanitizer_request_key(&changed, &rows()).unwrap());
    }
    let mut duplicate = selected.clone();
    duplicate.push(selected[0].clone());
    assert_ne!(
        key,
        sanitizer_request_key(
            &duplicate,
            &request_rows(temp.path(), &[Some("request A"), Some("request B"), Some("request A")])
        )
        .unwrap()
    );
    assert!(
        sanitizer_request_key(&selected, &request_rows(temp.path(), &[Some("request A"), None]))
            .is_none()
    );
    assert!(
        sanitizer_request_key(&selected, &request_rows(temp.path(), &[Some("request A")]))
            .is_none()
    );
    assert!(sanitizer_request_key(&[], &[]).is_none());
}

#[test]
fn sanitizer_completion_requires_every_output_and_the_same_host_provider() {
    let ctx = TestCtx::new();
    let host = TargetSelection::from_user("aarch64-apple-darwin");
    let cross = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    for (name, llvm) in [
        (
            "local-static",
            super::enzyme_tests::local_llvm(ctx.dir().join("local-static"), false, host),
        ),
        (
            "local-shared",
            super::enzyme_tests::local_llvm(ctx.dir().join("local-shared"), true, host),
        ),
        ("ci", super::enzyme_tests::ci_llvm(ctx.dir().join("ci"), false)),
    ] {
        let output = ctx.dir().join(format!("sanitizers-{name}"));
        let before = recorded_llvm_dependency_key(&llvm, host).unwrap();
        assert_ne!(Some(&before), recorded_llvm_dependency_key(&llvm, cross).as_ref());
        let eligible =
            reusable_cmake_inputs(Some("source data"), Some(&before), Some("request data"));
        let stamp = sanitizer_stamp(&output, eligible);
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        let selected = runtimes(&output);
        fs::write(&selected[0].path, b"first runtime").unwrap();
        record_sanitizer_completion(&stamp, &selected, &llvm, host, eligible).unwrap();
        assert!(!stamp.path().exists(), "a partial target set never completes");
        fs::create_dir(&selected[1].path).unwrap();
        record_sanitizer_completion(&stamp, &selected, &llvm, host, eligible).unwrap();
        assert!(!stamp.path().exists());
        fs::remove_dir(&selected[1].path).unwrap();
        fs::write(&selected[1].path, b"second runtime").unwrap();
        record_sanitizer_completion(&stamp, &selected, &llvm, host, eligible).unwrap();
        assert!(cached_sanitizers(&stamp, &selected, eligible));
        fs::remove_file(&selected[1].path).unwrap();
        assert!(
            !cached_sanitizers(&stamp, &selected, eligible),
            "a missing previously completed runtime denies the hit"
        );
        fs::write(&selected[1].path, b"restored second runtime").unwrap();
        assert!(cached_sanitizers(&stamp, &selected, eligible));
        assert!(!cached_sanitizers(&stamp, &selected, None));
        #[cfg(unix)]
        {
            let actual = output.join("second-actual.a");
            fs::rename(&selected[1].path, &actual).unwrap();
            std::os::unix::fs::symlink(&actual, &selected[1].path).unwrap();
            assert!(
                cached_sanitizers(&stamp, &selected, eligible),
                "a supported regular-file alias remains usable"
            );
        }
        stamp.remove().unwrap();
        record_sanitizer_completion(&stamp, &selected, &llvm, host, None).unwrap();
        assert!(
            !stamp.path().exists(),
            "unknown request cannot publish even with existing membership"
        );
        record_sanitizer_completion(&stamp, &selected, &llvm, cross, eligible).unwrap();
        assert!(!stamp.path().exists());
        fs::write(llvm.root_dir().join(".llvm-stamp"), b"changed completion").unwrap();
        record_sanitizer_completion(&stamp, &selected, &llvm, host, eligible).unwrap();
        assert!(!stamp.path().exists());
        let mut external = llvm.clone();
        external.kind = LlvmKind::External;
        assert!(recorded_llvm_dependency_key(&external, host).is_none());
        record_sanitizer_completion(&stamp, &selected, &external, host, None).unwrap();
        assert!(!stamp.path().exists());
    }
}

#[test]
fn sanitizer_plan_binds_actual_flags_target_and_darwin_launcher_policy() {
    let ctx = TestCtx::new();
    let plan = |target: TargetSelection, change: fn(&mut Config)| {
        let mut config = ctx.config("build").stage(1).create_config();
        config.rust_remap_debuginfo = false;
        let mut session = crate::core::session::Session::new(config);
        session.config.llvm_clang_cl = Some("/selected/compiler/clang-cl".into());
        session.config.ccache = Some("selected-launcher".into());
        change(&mut session.config);
        let builder = Builder::new(&session);
        sanitizer_cmake_plan(
            &builder,
            target,
            &ctx.dir().join("compiler-rt"),
            &ctx.dir().join("output"),
            &ctx.dir().join("LLVM/bin/llvm-config"),
            &|_| None,
        )
        .unwrap()
    };
    let linux = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let baseline = plan(linux, |_| {});
    for change in [
        (|c: &mut Config| c.llvm_cflags = Some("-DCHANGED_C".into())) as fn(&mut Config),
        |c| c.llvm_cxxflags = Some("-DCHANGED_CXX".into()),
        |c| c.llvm_ldflags = Some("-Wl,changed".into()),
    ] {
        assert_ne!(baseline.requested_key(), plan(linux, change).requested_key());
    }
    let darwin = plan(TargetSelection::from_user("aarch64-apple-darwin"), |_| {});
    assert_ne!(baseline.requested_key(), darwin.requested_key());
    let launcher = |p: &CmakePlan| {
        p.operations.iter().any(|op| matches!(op, CmakeOperation::Define(name, _) | CmakeOperation::InputProgram(name, _) if name == "CMAKE_C_COMPILER_LAUNCHER"))
    };
    assert!(launcher(&baseline));
    assert!(!launcher(&darwin));
    let ohos = plan(TargetSelection::from_user("aarch64-unknown-linux-ohos"), |_| {});
    assert!(ohos.operations.iter().any(|op| matches!(op, CmakeOperation::Define(name, value) | CmakeOperation::InputProgram(name, value) if name == "COMPILER_RT_USE_BUILTINS_LIBRARY" && value == "ON")));
}
