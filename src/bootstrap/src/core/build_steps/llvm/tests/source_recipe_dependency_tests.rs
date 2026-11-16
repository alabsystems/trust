// Cache-observation DATA controls, not provider or SourceReady construction.
use super::*;

#[test]
fn observed_dependency_drift_is_final_even_after_the_original_digest_returns() {
    let output = LlvmOutput {
        llvm_config: PathBuf::from("/fixture/bin/llvm-config"),
        llvm_root_dir: PathBuf::from("/fixture"),
        link_shared: false,
        kind: super::super::LlvmKind::External,
    };
    let mut selected = SelectedLlvmDependency::observe(
        output,
        TargetSelection::from_user("aarch64-unknown-linux-gnu"),
    );
    assert!(selected.observed.is_none(), "an unprepared external selection stays unknown");
    // The comparison consumes cache DATA only, no native completion/owner.
    let original = "a".repeat(64);
    selected.observed = Some(original.clone());
    assert!(selected.matches_observation(Some(&original)));
    assert!(!selected.matches_observation(Some(&"b".repeat(64))));
    assert!(!selected.matches_observation(Some(&original)));
}

#[test]
fn an_unreadable_dependency_observation_cannot_recover_cache_eligibility() {
    let output = LlvmOutput {
        llvm_config: PathBuf::from("/fixture/bin/llvm-config"),
        llvm_root_dir: PathBuf::from("/fixture"),
        link_shared: false,
        kind: super::super::LlvmKind::External,
    };
    let mut selected = SelectedLlvmDependency::observe(
        output,
        TargetSelection::from_user("aarch64-unknown-linux-gnu"),
    );
    selected.observed = Some("a".repeat(64));
    assert!(!selected.matches_observation(None));
    assert!(!selected.matches_observation(Some(&"a".repeat(64))));
}

#[cfg(target_os = "macos")]
#[test]
#[ignore = "run only under maintained owned-process native input observation lane"]
fn real_prepared_external_request_observes_selected_native_inputs_without_building() {
    use crate::utils::trust_repo_tools;

    // This is an explicit test input path, never a provider/SourceReady grant.
    // The configured real tool and every declared input are observed below.
    let llvm_config = PathBuf::from(
        std::env::var_os("BOOTSTRAP_TEST_EXTERNAL_LLVM_CONFIG")
            .expect("owning native observation requires its actual configured llvm-config"),
    );
    assert!(llvm_config.is_absolute());
    let prefix = llvm_config.parent().and_then(Path::parent).unwrap().to_owned();
    let version = trust_repo_tools::query(&llvm_config, &["--version"]).unwrap();
    assert!(!version.is_empty());
    let world = tempfile::tempdir().unwrap();
    let source = world.path().join("source");
    let output = world.path().join("output");
    fs::create_dir(&source).unwrap();
    fs::write(
        source.join("CMakeLists.txt"),
        "cmake_minimum_required(VERSION 3.20)\nproject(CacheInputObservation NONE)\n",
    )
    .unwrap();
    let host = format!("{}-apple-darwin", std::env::consts::ARCH);
    let target = TargetSelection::from_user(&host);
    let llvm = LlvmOutput {
        llvm_config,
        llvm_root_dir: prefix,
        link_shared: false,
        kind: super::super::LlvmKind::External,
    };
    let selected = SelectedLlvmDependency::observe(llvm.clone(), target);
    assert!(selected.observed.is_none(), "the unprepared provider alone stays unknown");
    let mut config = cmake::Config::new(&source);
    config
        .out_dir(&output)
        .host(&host)
        .target(&host)
        .profile("Release")
        .generator("Ninja")
        .define_input_path("LLVM_DIR", llvm.cmake_dir())
        .define_input_path("LLVM_CMAKE_DIR", llvm.cmake_dir());
    let started = std::time::Instant::now();
    let recipe = ResolvedSourceRecipe::from_config(config, None, vec![selected], false).unwrap();
    let key = recipe.key.as_ref().expect("actual prepared external inputs must be observed");
    assert!(full_source_digest(&key.dependency));
    assert!(
        recipe.dependencies[0].unchanged(),
        "the same original inputs must survive the bookend"
    );
    println!(
        "observed real selected LLVM {version}; cache dependency {}; elapsed {:?}",
        key.dependency,
        started.elapsed()
    );
    // No Prepared::build, generation/completion publication, CMake configure,
    // LLVM/LLD compilation, SourceReady, Seed or SDK validation occurs here.
    assert!(!output.join("bin/lld").exists());
}
