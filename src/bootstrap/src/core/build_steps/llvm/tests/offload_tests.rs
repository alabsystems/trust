// Copyright 2026 Andrew Yates
// These are selected request/record fixtures, never an actual offload provider build.
use super::*;
use crate::utils::tests::TestCtx;

#[test]
fn offload_hit_and_completion_require_each_regular_library() {
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let host = TargetSelection::from_user("aarch64-apple-darwin");
    for (name, llvm) in [
        ("local", super::enzyme_tests::local_llvm(ctx.dir().join("local LLVM"), false, target)),
        ("ci", super::enzyme_tests::ci_llvm(ctx.dir().join("CI LLVM"), true)),
    ] {
        let root = ctx.dir().join(name);
        let output = omp_offload_output(&root);
        let dependency = recorded_llvm_dependency_key(&llvm, target).unwrap();
        assert_ne!(Some(&dependency), recorded_llvm_dependency_key(&llvm, host).as_ref());
        let inputs =
            reusable_cmake_inputs(Some("source data"), Some(&dependency), Some("request data"));
        let stamp = omp_offload_stamp(&root, inputs);
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        fs::create_dir(&output.lib_dir).unwrap();
        for path in &output.offload {
            fs::write(path, b"controlled artifact").unwrap();
        }
        record_omp_offload_completion(&stamp, &output, &llvm, target, inputs).unwrap();
        assert!(cached_omp_offload(&stamp, &output, inputs));
        for path in &output.offload {
            fs::remove_file(path).unwrap();
            assert!(!cached_omp_offload(&stamp, &output, inputs));
            stamp.remove().unwrap();
            record_omp_offload_completion(&stamp, &output, &llvm, target, inputs).unwrap();
            assert!(!stamp.path().exists());
            fs::create_dir(path).unwrap();
            assert!(!cached_omp_offload(&stamp, &output, inputs));
            record_omp_offload_completion(&stamp, &output, &llvm, target, inputs).unwrap();
            assert!(!stamp.path().exists());
            fs::remove_dir(path).unwrap();
            #[cfg(unix)]
            {
                std::os::unix::fs::symlink(root.join("absent"), path).unwrap();
                assert!(!cached_omp_offload(&stamp, &output, inputs));
                record_omp_offload_completion(&stamp, &output, &llvm, target, inputs).unwrap();
                assert!(!stamp.path().exists());
                fs::remove_file(path).unwrap();
            }
            fs::write(path, b"restored artifact").unwrap();
            record_omp_offload_completion(&stamp, &output, &llvm, target, inputs).unwrap();
            assert!(cached_omp_offload(&stamp, &output, inputs));
            #[cfg(unix)]
            {
                let actual = path.with_extension("owned-actual");
                fs::rename(path, &actual).unwrap();
                std::os::unix::fs::symlink(&actual, path).unwrap();
                assert!(
                    cached_omp_offload(&stamp, &output, inputs),
                    "regular-file aliases remain supported"
                );
            }
        }
        assert!(!cached_omp_offload(&stamp, &output, None));
        stamp.remove().unwrap();
        record_omp_offload_completion(&stamp, &output, &llvm, target, None).unwrap();
        assert!(!stamp.path().exists());
        record_omp_offload_completion(&stamp, &output, &llvm, host, inputs).unwrap();
        assert!(!stamp.path().exists(), "the actual selected target provider is required");
        fs::write(llvm.root_dir().join(".llvm-stamp"), b"changed provider").unwrap();
        record_omp_offload_completion(&stamp, &output, &llvm, target, inputs).unwrap();
        assert!(!stamp.path().exists());
    }
}

#[test]
fn offload_full_source_observation_covers_each_actual_sibling() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("llvm-project");
    let root = temp.path().join("output");
    for name in ["runtimes", "openmp", "offload", "cmake"] {
        fs::create_dir_all(source.join(name)).unwrap();
        fs::write(source.join(name).join("CMakeLists.txt"), b"first source").unwrap();
    }
    let baseline = observe_cmake_sources(&source, &root).unwrap().unwrap();
    let inputs =
        reusable_cmake_inputs(Some(&baseline), Some("provider data"), Some("request data"));
    let stamp = omp_offload_stamp(&root, inputs);
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let output = omp_offload_output(&root);
    fs::create_dir(&output.lib_dir).unwrap();
    for path in &output.offload {
        fs::write(path, b"controlled artifact").unwrap();
    }
    stamp.write().unwrap();
    assert!(cached_omp_offload(&stamp, &output, inputs));
    for name in ["runtimes", "openmp", "offload", "cmake"] {
        let file = source.join(name).join("CMakeLists.txt");
        fs::write(&file, b"other source").unwrap();
        let changed = observe_cmake_sources(&source, &root).unwrap().unwrap();
        assert_ne!(baseline, changed);
        let inputs =
            reusable_cmake_inputs(Some(&changed), Some("provider data"), Some("request data"));
        let changed_stamp = omp_offload_stamp(&root, inputs);
        assert!(!cached_omp_offload(&changed_stamp, &output, inputs));
        assert!(!cmake_generation_matches(&changed_stamp));
        fs::write(file, b"first source").unwrap();
        assert_eq!(baseline, observe_cmake_sources(&source, &root).unwrap().unwrap());
    }
}

#[test]
fn cxx_library_query_decoder_distinguishes_observed_absence_and_unavailability() {
    use crate::utils::exec::{CommandOutput, OutputMode};
    let observed = |bytes: &[u8]| {
        CommandOutput::from_output(
            std::process::Output {
                status: std::process::ExitStatus::default(),
                stdout: bytes.to_vec(),
                stderr: Vec::new(),
            },
            OutputMode::Capture,
            OutputMode::Print,
        )
    };
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("selected CXX library/libstdc++.so");
    assert_eq!(
        decode_offload_cxx_library(&observed(format!("{}\n", path.display()).as_bytes())).unwrap(),
        path.parent().map(Path::to_owned)
    );
    for bytes in [b"libstdc++.so".as_slice(), b"\n".as_slice()] {
        assert!(decode_offload_cxx_library(&observed(bytes)).unwrap().is_none());
    }
    assert!(matches!(
        decode_offload_cxx_library(&observed(&[0xff])),
        Err(OffloadCxxQueryUnavailable::CommandFailure(_))
    ));
    assert!(matches!(
        decode_offload_cxx_library(&observed(b"/invalid\0/libstdc++.so")),
        Err(OffloadCxxQueryUnavailable::CommandFailure(_))
    ));
    assert!(matches!(
        decode_offload_cxx_library(&CommandOutput::not_finished(
            OutputMode::Capture,
            OutputMode::Print
        )),
        Err(OffloadCxxQueryUnavailable::CommandFailure(_))
    ));
    #[cfg(unix)]
    let failure = {
        use std::os::unix::process::ExitStatusExt;
        std::process::ExitStatus::from_raw(1 << 8)
    };
    #[cfg(windows)]
    let failure = {
        use std::os::windows::process::ExitStatusExt;
        std::process::ExitStatus::from_raw(1)
    };
    #[cfg(any(unix, windows))]
    {
        let failed = CommandOutput::from_output(
            std::process::Output {
                status: failure,
                stdout: path.as_os_str().as_encoded_bytes().to_vec(),
                stderr: Vec::new(),
            },
            OutputMode::Capture,
            OutputMode::Print,
        );
        assert!(
            matches!(
                decode_offload_cxx_library(&failed),
                Err(OffloadCxxQueryUnavailable::CommandFailure(_))
            ),
            "failed output never manufactures a directory"
        );
    }
}

#[test]
fn offload_clang_and_lld_selection_preserve_actual_provider_branches() {
    let ctx = TestCtx::new();
    let mut session =
        crate::core::session::Session::new(ctx.config("build").stage(1).create_config());
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = super::enzyme_tests::ci_llvm(ctx.dir().join("LLVM"), true);
    let source_lld = {
        let builder = Builder::new(&session);
        source_lld_output_dir(&builder, target)
    };
    {
        let builder = Builder::new(&session);
        assert_eq!(requested_lld_output_dir(&builder, &llvm, target), source_lld);
    }
    fs::create_dir_all(llvm.root_dir().join("bin")).unwrap();
    fs::write(llvm.root_dir().join("bin/lld"), b"metadata-only entry, never executed").unwrap();
    assert_eq!(ci_lld_output_dir(&llvm, target).as_deref(), Some(llvm.root_dir()));
    {
        let builder = Builder::new(&session);
        assert_eq!(requested_lld_output_dir(&builder, &llvm, target), llvm.root_dir());
    }
    let mut local = llvm.clone();
    local.kind = LlvmKind::BuiltLocally;
    assert!(ci_lld_output_dir(&local, target).is_none());
    let mut external = llvm.clone();
    external.kind = LlvmKind::External;
    assert!(ci_lld_output_dir(&external, target).is_none());
    session.config.llvm_clang = true;
    assert!(selected_offload_clang(&session.config, &llvm, target).is_none());
    fs::write(llvm.root_dir().join("bin/clang"), b"metadata-only entry, never executed").unwrap();
    assert_eq!(
        selected_offload_clang(&session.config, &llvm, target).unwrap().clang,
        llvm.root_dir().join("bin/clang")
    );
    let prefix = ctx.dir().join("external clang prefix");
    fs::create_dir_all(prefix.join("bin")).unwrap();
    fs::write(prefix.join("bin/clang"), b"metadata-only entry, never executed").unwrap();
    session.config.llvm_clang = false;
    session.config.offload_clang_dir = Some(prefix.join("lib/cmake/clang"));
    let selected = selected_offload_clang(&session.config, &llvm, target).unwrap();
    assert_eq!(selected.clang, prefix.join("bin/clang"));
    assert_eq!(selected.clangxx, prefix.join("bin/clang++"));
    assert_eq!(selected.cmake_dir, session.config.offload_clang_dir);
}

#[test]
fn offload_plan_keeps_common_then_clang_overrides_and_actual_request_inputs() {
    let ctx = TestCtx::new();
    let mut config = ctx.config("build").stage(1).create_config();
    config.rust_remap_debuginfo = false;
    let mut session = crate::core::session::Session::new(config);
    session.config.host_target = TargetSelection::from_user("aarch64-apple-darwin");
    session.config.ninja_in_file = true;
    session.config.llvm_clang_cl = Some("/selected/common/compiler".into());
    session.config.lld_enabled = false;
    session.config.llvm_cflags = Some("-DSELECTED_C".into());
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = super::enzyme_tests::local_llvm(ctx.dir().join("LLVM"), true, target);
    let clang = OffloadClang {
        clang: ctx.dir().join("clang"),
        clangxx: ctx.dir().join("clang++"),
        cmake_dir: Some(ctx.dir().join("ClangConfig")),
    };
    let plan = omp_offload_cmake_plan(
        &builder,
        target,
        &ctx.dir().join("output"),
        OffloadLlvmRequest {
            root: llvm.root_dir(),
            cmake: &llvm.cmake_dir(),
            link_shared: llvm.link_shared(),
        },
        &clang,
        Some(&ctx.dir().join("selected CXX lib")),
        None,
        &|_| None,
        Vec::new,
    )
    .unwrap();
    let definitions = plan
        .operations
        .iter()
        .filter_map(|op| match op {
            CmakeOperation::Define(k, v) | CmakeOperation::InputProgram(k, v)
                if k == "CMAKE_C_COMPILER" =>
            {
                Some(v)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(definitions.len() >= 2);
    assert_ne!(definitions[0], *definitions.last().unwrap());
    assert_eq!(definitions.last().unwrap().as_os_str(), clang.clang.as_os_str());
    assert!(
        matches!(plan.operations.last(), Some(CmakeOperation::BuildTarget(name)) if name == "install")
    );
    let changed_library = omp_offload_cmake_plan(
        &builder,
        target,
        &ctx.dir().join("output"),
        OffloadLlvmRequest {
            root: llvm.root_dir(),
            cmake: &llvm.cmake_dir(),
            link_shared: llvm.link_shared(),
        },
        &clang,
        Some(&ctx.dir().join("different CXX lib")),
        None,
        &|_| None,
        Vec::new,
    )
    .unwrap();
    assert_ne!(
        plan.requested_key(),
        changed_library.requested_key(),
        "same clang with changed queried library path must invalidate"
    );
    let changed = OffloadClang { clang: ctx.dir().join("other clang"), ..clang };
    let changed_plan = omp_offload_cmake_plan(
        &builder,
        target,
        &ctx.dir().join("output"),
        OffloadLlvmRequest {
            root: llvm.root_dir(),
            cmake: &llvm.cmake_dir(),
            link_shared: llvm.link_shared(),
        },
        &changed,
        None,
        None,
        &|_| None,
        Vec::new,
    )
    .unwrap();
    assert_ne!(plan.requested_key(), changed_plan.requested_key());
}
