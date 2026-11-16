// Copyright 2026 Andrew Yates
// File-backed owner controls; no LLVM/provider construction is implied.
use super::enzyme_tests::recorded_source_recipe;
use super::*;
use crate::utils::trust_repo_cache::{cleanup_input_namespaces, git};

fn recorded_lld_recipe() -> SourceRecipeKey {
    SourceRecipeKey { dependency: "d".repeat(64), ..recorded_source_recipe(false) }
}

fn observed(source: &Path, anchor: &Path, output: &Path) -> OwnSourceGeneration {
    OwnSourceGeneration {
        source: source.to_owned(),
        anchor: anchor.to_owned(),
        output: output.to_owned(),
        observed: observe_cmake_sources(source, output).unwrap(),
    }
}

fn commit(source: &Path) {
    git(source, &["add", "."]).unwrap();
    git(
        source,
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
}

#[test]
fn indexed_source_changes_collide_in_old_git_inputs_but_miss_the_owned_generation() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let anchor = temp.path().join("owned");
    let output = anchor.join("llvm");
    fs::create_dir(&source).unwrap();
    git(&source, &["init", "-q"]).unwrap();
    let input = source.join("input");
    fs::write(&input, b"base\n").unwrap();
    commit(&source);
    let head = git(&source, &["rev-parse", "HEAD"]).unwrap();
    fs::write(&input, b"first\n").unwrap();
    git(&source, &["add", "input"]).unwrap();
    let old_inputs = || {
        (
            git(&source, &["diff", "."]).unwrap(),
            git(&source, &["status", ".", "--porcelain", "-z", "--untracked-files=normal"])
                .unwrap(),
            git(&source, &["rev-parse", "HEAD"]).unwrap(),
        )
    };
    let first_old = old_inputs();
    assert!(first_old.0.is_empty());
    assert!(!first_old.1.is_empty());
    assert_eq!(first_old.2, head);
    let first = observed(&source, &anchor, &output);
    let stamp = first.stamp("llvm", "fixture-target", Some(&recorded_source_recipe(false)));
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let artifact = output.join("bin/llvm-config");
    fs::create_dir_all(artifact.parent().unwrap()).unwrap();
    fs::write(&artifact, b"fixture artifact").unwrap();
    fixture_install_manifest(&output, &[&artifact]);
    assert!(first.complete(&stamp, || true).unwrap());
    assert!(
        first.cache_matches("llvm", &stamp, &artifact),
        "a real matching completion must first hit"
    );
    fs::write(&input, b"other\n").unwrap();
    git(&source, &["add", "input"]).unwrap();
    assert_eq!(first_old, old_inputs(), "all old smart-hash Git inputs collide");
    let second = observed(&source, &anchor, &output);
    assert_ne!(first.observed, second.observed);
    assert_ne!(
        stamp.stamp(),
        second.stamp("llvm", "fixture-target", Some(&recorded_source_recipe(false))).stamp()
    );
    assert!(!second.cache_matches(
        "llvm",
        &second.stamp("llvm", "fixture-target", Some(&recorded_source_recipe(false))),
        &artifact
    ));
    assert!(!first.unchanged());
}

#[test]
fn completion_and_generation_both_matter_and_unknown_projection_does_not_memoize_source() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let anchor = temp.path().join("owned");
    let output = anchor.join("lld");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("input"), b"first").unwrap();
    let projection = OwnSourceGeneration {
        source: source.clone(),
        anchor: anchor.clone(),
        output: output.clone(),
        observed: None,
    };
    let first = observed(&source, &anchor, &output);
    let stamp = first.stamp("lld", "fixture-target", Some(&recorded_lld_recipe()));
    fs::create_dir_all(&output).unwrap();
    let artifact = output.join("lld");
    fs::write(&artifact, b"fixture artifact").unwrap();
    stamp.write().unwrap();
    assert!(
        !first.cache_matches("lld", &stamp, &artifact),
        "legacy completion without generation is not reusable"
    );
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    assert!(!first.cache_matches("lld", &stamp, &artifact), "membership is not completion");
    fs::write(&artifact, b"fixture artifact").unwrap();
    fixture_install_manifest(&output, &[&artifact]);
    assert!(installed_outputs::publish(&stamp).unwrap());
    stamp.write().unwrap();
    assert!(first.cache_matches("lld", &stamp, &artifact));
    fs::remove_file(&artifact).unwrap();
    assert!(!first.cache_matches("lld", &stamp, &artifact));
    fs::create_dir(&artifact).unwrap();
    assert!(!first.cache_matches("lld", &stamp, &artifact));
    fs::remove_dir(&artifact).unwrap();
    fs::write(&artifact, b"fixture artifact").unwrap();
    assert!(first.cache_matches("lld", &stamp, &artifact));
    assert!(!projection.cache_matches(
        "lld",
        &projection.stamp("lld", "fixture-target", Some(&recorded_lld_recipe())),
        &artifact
    ));
    assert!(!projection.unchanged());
    stamp.remove().unwrap();
    assert!(!projection.complete(&stamp, || true).unwrap());
    assert!(!stamp.path().exists(), "unknown source cannot write completion");
    assert!(first.complete(&stamp, || true).unwrap());
    fs::write(source.join("input"), b"other").unwrap();
    let actual = observed(&source, &anchor, &output);
    stamp.remove().unwrap();
    assert!(!first.complete(&stamp, || true).unwrap());
    assert!(!stamp.path().exists(), "changed source cannot write completion");
    assert_ne!(
        first.observed, actual.observed,
        "an earlier projection cannot cache the next observation"
    );
    assert!(!actual.cache_matches(
        "lld",
        &actual.stamp("lld", "fixture-target", Some(&recorded_lld_recipe())),
        &artifact
    ));
}

#[test]
fn actual_dry_owner_projection_does_not_memoize_the_next_source_observation() {
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;
    let ctx = TestCtx::new();
    let config = ctx.config("build").stage(1).create_config_with_fixed_budget(Some(1));
    assert!(config.dry_run());
    let mut session = Session::new(config);
    let temp = tempfile::tempdir().unwrap();
    // Initialize the ordinary session first; only the read-only owner query is
    // redirected to these deliberately absent, independently owned paths.
    session.config.src = temp.path().join("fixture-source");
    session.config.out = temp.path().join("fixture-output");
    {
        let builder = Builder::new(&session);
        let LlvmBuildStatus::ShouldBuild(info) =
            get_locally_built_llvm_build_status(&builder, builder.host_target)
        else {
            panic!("an absent fixture cannot have a completed LLVM");
        };
        assert!(info.source_generation.observed.is_none());
        assert!(!session.config.out.exists());
        assert!(!session.config.src.exists());
    }
    let source = session.config.src.join("src/llvm-project");
    fs::create_dir_all(&source).unwrap();
    fs::write(source.join("input"), b"actual current bytes").unwrap();
    session.config.set_dry_run(crate::core::config::DryRun::Disabled);
    // This control observes the real source branch without launching pre-cache
    // compiler/CMake probes; selected C/C++ request data is deliberately absent.
    session.cc.clear();
    session.cxx.clear();
    session.config.llvm_clang_cl = None;
    {
        let builder = Builder::new(&session);
        let LlvmBuildStatus::ShouldBuild(info) =
            get_locally_built_llvm_build_status(&builder, builder.host_target)
        else {
            panic!("observation alone cannot establish completed LLVM");
        };
        assert!(info.source_generation.observed.is_some());
        assert!(matches!(info.recipe, SourceRecipeResolution::Unavailable(_)));
        assert!(!session.config.out.exists(), "status observation does not write output");
    }
}

#[test]
fn selected_tools_and_provider_inputs_inside_output_refuse_without_mutating_sentinels() {
    let temp = tempfile::tempdir().unwrap();
    let anchor = temp.path().join("owned");
    let output = anchor.join("llvm");
    fs::create_dir_all(output.join("bin")).unwrap();
    let compiler = output.join("bin/compiler");
    let provider = output.join("lib/cmake/llvm");
    fs::write(&compiler, b"selected compiler must survive").unwrap();
    fs::create_dir_all(&provider).unwrap();
    let completion = output.join(".llvm-stamp");
    fs::write(&completion, b"existing completion").unwrap();
    for input in [&compiler, &provider, &anchor] {
        assert!(cleanup_input_namespaces(&anchor, &output, &[input.to_path_buf()]).is_err());
        assert_eq!(fs::read(&completion).unwrap(), b"existing completion");
        assert_eq!(fs::read(&compiler).unwrap(), b"selected compiler must survive");
    }
    #[cfg(unix)]
    {
        let alias = temp.path().join("compiler-alias");
        std::os::unix::fs::symlink(&compiler, &alias).unwrap();
        assert!(cleanup_input_namespaces(&anchor, &output, &[alias]).is_err());
        let dangling = temp.path().join("opaque-tool");
        std::os::unix::fs::symlink(temp.path().join("missing-tool"), &dangling).unwrap();
        assert!(cleanup_input_namespaces(&anchor, &output, &[dangling]).is_err());
        let outside = temp.path().join("outside-output");
        fs::create_dir(&outside).unwrap();
        fs::write(outside.join("sentinel"), b"foreign output").unwrap();
        let linked_output = anchor.join("reuse");
        std::os::unix::fs::symlink(&outside, &linked_output).unwrap();
        assert!(cleanup_input_namespaces(&anchor, &linked_output, &[]).is_err());
        let inside = anchor.join("retained-output");
        fs::create_dir(&inside).unwrap();
        let inside_alias = anchor.join("inside-reuse");
        std::os::unix::fs::symlink(&inside, &inside_alias).unwrap();
        let proof = cleanup_input_namespaces(&anchor, &inside_alias, &[]).unwrap();
        assert!(proof.linked, "existing linked output cannot authorize destructive reset");
        proof.recheck().unwrap();
        assert_eq!(fs::read(outside.join("sentinel")).unwrap(), b"foreign output");
        assert_eq!(fs::read(&completion).unwrap(), b"existing completion");
    }
}

#[test]
fn local_dependency_evidence_accepts_current_source_completion_without_legacy_provenance() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("tarball-source");
    let output = temp.path().join("owned/llvm");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("input"), b"first").unwrap();
    let target = TargetSelection::from_user("aarch64-unknown-linux-gnu");
    let llvm = LlvmOutput {
        llvm_config: output.join("bin/llvm-config"),
        link_shared: true,
        llvm_root_dir: output.clone(),
        kind: LlvmKind::BuiltLocally,
    };
    let write_completion = || {
        let owner = observed(&source, temp.path(), &output);
        let stamp = owner.stamp("llvm", &target.triple, Some(&recorded_source_recipe(true)));
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        fs::create_dir_all(output.join("build")).unwrap();
        fs::write(output.join("build/CMakeCache.txt"), b"actual recorded configuration").unwrap();
        let artifact = output.join("bin/llvm-config");
        fs::create_dir_all(artifact.parent().unwrap()).unwrap();
        fs::write(&artifact, b"recorded output").unwrap();
        fixture_install_manifest(&output, &[&artifact]);
        assert!(owner.complete(&stamp, || true).unwrap());
        stamp
    };
    let stamp = write_completion();
    assert!(!output.join(".trust-llvm-sources").exists());
    let first =
        recorded_llvm_dependency_key(&llvm, target).expect("current tarball completion evidence");
    fs::write(source.join("input"), b"other").unwrap();
    let changed = write_completion();
    assert_ne!(stamp.stamp(), changed.stamp());
    assert_ne!(first, recorded_llvm_dependency_key(&llvm, target).unwrap());
    // A legacy Built record must not rescue a malformed new-domain stamp.
    let record = output.join(".trust-llvm-sources");
    fs::write(&record, format!("tree {}\norigin built\n", "a".repeat(40))).unwrap();
    for invalid in [
        changed.stamp().replace("working-source/v2", "working-source/v9"),
        changed
            .stamp()
            .replace(observed(&source, temp.path(), &output).observed.as_ref().unwrap(), "unknown"),
        changed.stamp().replace(&format!("target {}", target.triple), "target wrong-target"),
    ] {
        fs::write(changed.path(), invalid).unwrap();
        assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
    }
}

#[test]
fn dependency_classification_cannot_reuse_a_replaced_current_stamp_snapshot() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("llvm");
    fs::create_dir_all(root.join("build")).unwrap();
    let target = TargetSelection::from_user("aarch64-unknown-linux-gnu");
    fs::write(root.join("build/CMakeCache.txt"), b"recorded configuration").unwrap();
    super::enzyme_tests::write_local_completion(&root, target, &"a".repeat(64), true);
    let stamp = BuildStamp::new(&root).with_prefix("llvm");
    let llvm = LlvmOutput {
        llvm_config: root.join("bin/llvm-config"),
        link_shared: true,
        llvm_root_dir: root.clone(),
        kind: LlvmKind::BuiltLocally,
    };
    assert!(
        recorded_llvm_dependency_key(&llvm, target).is_some(),
        "current completion precondition must actually admit"
    );
    let mut called = false;
    let result = recorded_llvm_dependency_key_with_hook(&llvm, target, || {
        called = true;
        fs::write(
            stamp.path(),
            b"trust.llvm-working-source/v1\nmalformed replacement of a different size\n",
        )
        .unwrap();
    });
    assert!(called, "classification hook must be reached from valid evidence");
    assert!(result.is_none(), "a changed completion snapshot cannot supply a dependency key");
}

#[cfg(unix)]
#[test]
#[ignore = "run only under maintained owned-process CMake qualification lane"]
fn real_same_request_source_change_rebuilds_preserved_mtime_payload() {
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;
    let ctx = TestCtx::new();
    let evidence = tempfile::Builder::new()
        .prefix("llvm-source-only-")
        .suffix(".noindex")
        .tempdir()
        .unwrap()
        .keep();
    println!("retained source-only CMake evidence: {}", evidence.display());
    let source = evidence.join("source");
    let output = evidence.join("output");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("CMakeLists.txt"), r#"cmake_minimum_required(VERSION 3.20)
project(SourceOnly NONE)
add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/payload.txt"
 COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_CURRENT_SOURCE_DIR}/input.txt" "${CMAKE_BINARY_DIR}/payload.txt"
 DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/input.txt" VERBATIM)
add_custom_target(copy-output ALL DEPENDS "${CMAKE_BINARY_DIR}/payload.txt")
install(FILES "${CMAKE_BINARY_DIR}/payload.txt" DESTINATION lib)
"#).unwrap();
    let input = source.join("input.txt");
    fs::write(&input, b"first\n").unwrap();
    let mut config = ctx
        .config("build")
        .stage(1)
        .path("library/std")
        .args(&["--set", "rust.trust-source-identity=false"])
        .create_config_with_fixed_budget(Some(1));
    config.set_dry_run(crate::core::config::DryRun::Disabled);
    config.ninja_in_file = true;
    assert_eq!(
        crate::utils::trust_preparation::PreparationScope::for_config(&config),
        crate::utils::trust_preparation::PreparationScope::RequestSources
    );
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(builder.config.is_host_target(builder.host_target));
    let target_native = builder.host_target.to_string();
    let prepare = || {
        let mut recipe = llvm_cmake_config(
            &builder,
            builder.host_target,
            LlvmCmakeRequest {
                source: &source,
                output: &output,
                target_native: &target_native,
                link_shared: false,
            },
        )
        .config;
        recipe.build_target("install");
        prepare_owned_source_build(&builder, &mut recipe).unwrap()
    };
    let first = prepare();
    let request = first.cache_inputs().expect("real native request must be known").to_vec();
    assert!(
        first.cleanup_inputs().is_some(),
        "the ordinary lane must establish cleanup namespace data"
    );
    let before = observed(&source, &evidence, &output);
    let first_stamp =
        before.stamp("llvm", &target_native, Some(&source_recipe_key(&first, &[], false).unwrap()));
    // Use an actual resolved Prepared value with explicitly unavailable cleanup
    // evidence; refusal must precede deleting either existing file.
    fs::create_dir_all(&output).unwrap();
    let sentinel = output.join("keep-on-refusal");
    fs::write(&sentinel, b"untouched").unwrap();
    fs::write(first_stamp.path(), b"old completion").unwrap();
    let mut opaque_recipe = llvm_cmake_config(
        &builder,
        builder.host_target,
        LlvmCmakeRequest {
            source: &source,
            output: &output,
            target_native: &target_native,
            link_shared: false,
        },
    )
    .config;
    opaque_recipe.build_target("copy-output").opaque_cleanup_inputs();
    let opaque = prepare_owned_source_build(&builder, &mut opaque_recipe).unwrap();
    assert!(opaque.cleanup_inputs().is_none());
    assert!(before.begin(&first_stamp, &opaque, CmakeGeneration::Known, &[]).is_err());
    assert_eq!(fs::read(&sentinel).unwrap(), b"untouched");
    assert_eq!(fs::read(first_stamp.path()).unwrap(), b"old completion");
    drop(opaque);
    before.begin(&first_stamp, &first, CmakeGeneration::Known, &[]).unwrap();
    first.build();
    let payload = output.join("build/payload.txt");
    assert_eq!(fs::read(&payload).unwrap(), b"first\n");
    assert!(before.complete(&first_stamp, || true).unwrap());
    assert!(before.cache_matches("llvm", &first_stamp, &payload));
    let modified = fs::metadata(&input).unwrap().modified().unwrap();
    fs::write(&input, b"other\n").unwrap();
    crate::utils::helpers::set_file_times(&input, fs::FileTimes::new().set_modified(modified))
        .unwrap();
    assert_eq!(fs::metadata(&input).unwrap().modified().unwrap(), modified);
    let second = prepare();
    assert_eq!(
        second.cache_inputs().unwrap(),
        request.as_slice(),
        "only source content, not the prepared request, changes"
    );
    let after = observed(&source, &evidence, &output);
    let second_stamp =
        after.stamp("llvm", &target_native, Some(&source_recipe_key(&second, &[], false).unwrap()));
    assert_ne!(first_stamp.stamp(), second_stamp.stamp());
    assert!(!after.cache_matches("llvm", &second_stamp, &payload));
    after.begin(&second_stamp, &second, CmakeGeneration::Known, &[]).unwrap();
    second.build();
    assert_eq!(
        fs::read(&payload).unwrap(),
        b"other\n",
        "source-only miss must not retain the old Ninja payload"
    );
    assert_eq!(fs::metadata(&input).unwrap().modified().unwrap(), modified);
    assert!(after.complete(&second_stamp, || true).unwrap());
    assert!(after.cache_matches("llvm", &second_stamp, &payload));
}

#[cfg(unix)]
#[test]
fn matching_linked_generation_is_read_only_and_changed_linked_source_refuses_replacement() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let anchor = temp.path().join("owned");
    let output = anchor.join("llvm");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("input"), b"first").unwrap();
    let original = observed(&source, &anchor, &output);
    let stamp = original.stamp("llvm", "fixture-target", Some(&recorded_source_recipe(false)));
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let artifact = output.join("llvm-config");
    fs::write(&artifact, b"regular fixture output").unwrap();
    fixture_install_manifest(&output, &[&artifact]);
    assert!(original.complete(&stamp, || true).unwrap());
    let alias = anchor.join("reuse");
    std::os::unix::fs::symlink(&output, &alias).unwrap();
    let linked = OwnSourceGeneration { output: alias.clone(), ..original };
    let linked_stamp = linked.stamp("llvm", "fixture-target", Some(&recorded_source_recipe(false)));
    assert!(linked.cache_matches("llvm", &linked_stamp, &alias.join("llvm-config")));
    let completion = fs::read(stamp.path()).unwrap();
    fs::write(source.join("input"), b"other").unwrap();
    assert!(!linked.unchanged());
    assert!(linked.refuse_linked_miss().is_err());
    assert_eq!(fs::read(stamp.path()).unwrap(), completion);
    assert_eq!(fs::read(&artifact).unwrap(), b"regular fixture output");
}

#[test]
fn explicit_linker_requires_an_absolute_bound_program_and_keeps_other_opaque_flags_refused() {
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;
    let ctx = TestCtx::new();
    let mut config =
        ctx.config("build").stage(1).path("library/std").create_config_with_fixed_budget(Some(1));
    config.ninja_in_file = true;
    config.llvm_use_linker = Some("lld".into());
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(validate_owned_source_build(&builder).is_err());

    let mut config =
        ctx.config("build").stage(1).path("library/std").create_config_with_fixed_budget(Some(1));
    config.ninja_in_file = true;
    config.llvm_use_linker =
        Some(std::env::current_dir().unwrap().join("selected-linker").display().to_string());
    let session = Session::new(config);
    let builder = Builder::new(&session);
    // This is namespace eligibility only; Prepared must still resolve the actual program.
    assert!(validate_owned_source_build(&builder).is_ok());

    let mut config =
        ctx.config("build").stage(1).path("library/std").create_config_with_fixed_budget(Some(1));
    config.ninja_in_file = true;
    config.llvm_use_linker =
        Some(std::env::current_dir().unwrap().join("selected-linker").display().to_string());
    config.llvm_ldflags = Some("-L/untracked".into());
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(validate_owned_source_build(&builder).is_err());
}

#[test]
fn darwin_lld_runtime_is_exactly_the_selected_sdk_stub() {
    let root = tempfile::tempdir().unwrap();
    let sdk = root.path().join("SDK");
    assert!(darwin_cxx_runtime(Path::new("SDK")).is_err());
    assert!(darwin_cxx_runtime(&sdk).is_err());
    fs::create_dir_all(sdk.join("usr/lib")).unwrap();
    let runtime = sdk.join("usr/lib/libc++.tbd");
    fs::create_dir(&runtime).unwrap();
    assert!(darwin_cxx_runtime(&sdk).is_err());
    fs::remove_dir(&runtime).unwrap();
    fs::write(&runtime, b"selected SDK stub fixture").unwrap();
    assert_eq!(darwin_cxx_runtime(&sdk).unwrap(), runtime);
}

#[test]
fn darwin_lld_runtime_binding_preserves_explicit_static_cpp_policy() {
    assert!(uses_darwin_platform_cxx_runtime("aarch64-apple-darwin", false));
    assert!(!uses_darwin_platform_cxx_runtime("aarch64-apple-darwin", true));
    assert!(!uses_darwin_platform_cxx_runtime("x86_64-unknown-linux-gnu", false));
}
