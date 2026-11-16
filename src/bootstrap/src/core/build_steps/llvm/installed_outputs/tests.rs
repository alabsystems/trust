// Copyright 2026 Andrew Yates
// Owned filesystem controls; no LLVM, SDK or provider readiness is inferred.
use super::*;

fn fixture() -> (tempfile::TempDir, PathBuf, BuildStamp) {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap().join("output");
    fs::create_dir_all(root.join("build")).unwrap();
    fs::create_dir_all(root.join("lib")).unwrap();
    fs::write(root.join("lib/one"), b"one").unwrap();
    fs::write(root.join("lib/two"), b"two").unwrap();
    let stamp = BuildStamp::new(&root).with_prefix("llvm").add_stamp("completion DATA");
    (temp, root, stamp)
}
fn manifest(root: &Path, paths: &[&str]) {
    fs::create_dir_all(root.join("build")).unwrap();
    let rows = paths.iter().map(|p| root.join(p).to_str().unwrap().to_owned()).collect::<Vec<_>>();
    // Actual CMake's generated install list need not have a final newline.
    fs::write(root.join("build/install_manifest.txt"), rows.join("\n")).unwrap();
}
#[test]
fn actual_membership_is_deduplicated_and_every_installed_output_is_required() {
    let (_temp, root, stamp) = fixture();
    manifest(&root, &["lib/one", "lib/two", "lib/one"]);
    let before = observe(&root, stamp.stamp()).unwrap();
    assert!(matches(&root, stamp.stamp()).is_none(), "legacy/unobserved is not complete");
    assert!(publish(&stamp).unwrap());
    assert_eq!(matches(&root, stamp.stamp()), Some(before.clone()));
    manifest(&root, &["lib/two", "lib/one"]);
    assert_eq!(matches(&root, stamp.stamp()), Some(before));
    assert!(matches(&root, "different completion").is_none());
    fs::remove_file(root.join("lib/two")).unwrap();
    assert!(matches(&root, stamp.stamp()).is_none());
    fs::create_dir(root.join("lib/two")).unwrap();
    assert!(matches(&root, stamp.stamp()).is_none());
    fs::remove_dir(root.join("lib/two")).unwrap();
    fs::write(root.join("lib/two"), b"restored bytes are not authenticated").unwrap();
    assert!(matches(&root, stamp.stamp()).is_some());
    manifest(&root, &["lib/one"]);
    assert!(
        matches(&root, stamp.stamp()).is_none(),
        "a truncated valid prefix is not the recorded set"
    );
}
#[test]
fn malformed_and_unowned_manifests_never_publish() {
    let (_temp, root, stamp) = fixture();
    for bytes in [
        vec![],
        b"relative\n".to_vec(),
        b"/outside/unowned\n".to_vec(),
        format!("{}/lib/../lib/one", root.display()).into_bytes(),
        format!("{}/lib/one\0", root.display()).into_bytes(),
        vec![b'x'; MAX_MANIFEST as usize + 1],
        vec![0xff],
    ] {
        fs::write(root.join("build/install_manifest.txt"), bytes).unwrap();
        assert!(!publish(&stamp).unwrap());
        assert!(!root.join(RECORD).exists());
    }
    fs::write(root.join("build/install_manifest.txt"), format!("{}/lib/one\r\n", root.display()))
        .unwrap();
    assert!(
        observe(&root, stamp.stamp()).is_none(),
        "a raw carriage return is part of the filename, not silently stripped"
    );
    #[cfg(unix)]
    {
        fs::write(root.join("lib/one\r"), b"literal carriage-return member").unwrap();
        assert!(observe(&root, stamp.stamp()).is_some());
    }
    manifest(&root, &["lib/one", "lib/two"]);
    assert!(publish(&stamp).unwrap());
    fs::write(root.join(RECORD), b"malformed").unwrap();
    assert!(matches(&root, stamp.stamp()).is_none());
}
#[cfg(unix)]
#[test]
fn internal_aliases_work_but_outside_routes_and_cycles_do_not() {
    use std::os::unix::fs::symlink;
    let (temp, root, stamp) = fixture();
    fs::create_dir(root.join("lib/nested")).unwrap();
    for target in [".", ".."] {
        let alias = root.join("lib/nested/dir-alias");
        symlink(target, &alias).unwrap();
        manifest(&root, &["lib/nested/dir-alias"]);
        assert!(
            observe(&root, stamp.stamp()).is_none(),
            "directory alias {target} is not an installed file"
        );
        fs::remove_file(&alias).unwrap();
    }
    for suffix in ["/", "/."] {
        // Include the ordinary duplicate first: dedup must not discard this
        // unusable spelling of the same normalized membership.
        fs::write(
            root.join("build/install_manifest.txt"),
            format!("{0}/lib/one\n{0}/lib/one{suffix}", root.display()),
        )
        .unwrap();
        assert!(observe(&root, stamp.stamp()).is_none());
        let alias = root.join("lib/alias");
        symlink(format!("one{suffix}"), &alias).unwrap();
        manifest(&root, &["lib/alias"]);
        assert!(observe(&root, stamp.stamp()).is_none());
        fs::remove_file(alias).unwrap();
    }
    fs::write(root.join("lib/nested/realfile"), b"ordinary member").unwrap();
    symlink("nested/", root.join("lib/dir-alias")).unwrap();
    manifest(&root, &["lib/dir-alias/realfile"]);
    assert!(observe(&root, stamp.stamp()).is_some(), "valid directory aliases retain their child");
    symlink("one", root.join("lib/alias")).unwrap();
    manifest(&root, &["lib/alias", "lib/two"]);
    assert!(publish(&stamp).unwrap());
    fs::remove_file(root.join("lib/alias")).unwrap();
    symlink(temp.path().join("never-probe-outside"), root.join("lib/alias")).unwrap();
    assert!(matches(&root, stamp.stamp()).is_none());
    fs::remove_file(root.join("lib/alias")).unwrap();
    symlink("alias", root.join("lib/alias")).unwrap();
    assert!(observe(&root, stamp.stamp()).is_none());
    fs::remove_file(root.join("lib/alias")).unwrap();
    symlink("../../outside", root.join("lib/alias")).unwrap();
    assert!(observe(&root, stamp.stamp()).is_none());
}

#[cfg(unix)]
#[test]
#[ignore = "run only under the maintained owned-process CMake qualification lane"]
fn real_none_install_requires_both_actual_manifest_members() {
    use crate::core::build_steps::llvm::{
        CmakeGeneration, LlvmCmakeRequest, OwnSourceGeneration, llvm_cmake_config,
        observe_cmake_sources, prepare_owned_source_build, source_recipe_key,
    };
    use crate::core::builder::Builder;
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;
    let ctx = TestCtx::new();
    let evidence = tempfile::Builder::new()
        .prefix("installed-output-")
        .suffix(".noindex")
        .tempdir()
        .unwrap()
        .keep();
    println!("retained installed-output CMake evidence: {}", evidence.display());
    let source = evidence.join("source");
    let output = evidence.join("output");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("one"), b"one").unwrap();
    fs::write(source.join("two"), b"two").unwrap();
    fs::write(
        source.join("CMakeLists.txt"),
        r#"cmake_minimum_required(VERSION 3.20)
project(InstalledOutputs NONE)
install(FILES one two DESTINATION lib)
"#,
    )
    .unwrap();
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
    let target = builder.host_target.to_string();
    let mut config = llvm_cmake_config(
        &builder,
        builder.host_target,
        LlvmCmakeRequest {
            source: &source,
            output: &output,
            target_native: &target,
            link_shared: false,
        },
    )
    .config;
    let prepared = prepare_owned_source_build(&builder, &mut config).unwrap();
    let recipe = source_recipe_key(&prepared, &[], false).unwrap();
    let owner = OwnSourceGeneration {
        source: source.clone(),
        anchor: evidence.clone(),
        output: output.clone(),
        observed: observe_cmake_sources(&source, &output).unwrap(),
    };
    let stamp = owner.stamp("llvm", &target, Some(&recipe));
    owner.begin(&stamp, &prepared, CmakeGeneration::Known, &[]).unwrap();
    prepared.build();
    assert_eq!(fs::read(output.join("lib/one")).unwrap(), b"one");
    assert_eq!(fs::read(output.join("lib/two")).unwrap(), b"two");
    assert!(owner.complete(&stamp, || true).unwrap());
    assert!(owner.cache_matches("llvm", &stamp, &output.join("lib/one")));
    assert!(matches(&output, stamp.stamp()).is_some(), "provider's installed observation exists");
    fs::remove_file(output.join("lib/two")).unwrap();
    assert!(!owner.cache_matches("llvm", &stamp, &output.join("lib/one")));
    assert!(
        matches(&output, stamp.stamp()).is_none(),
        "provider key cannot observe complete installed outputs"
    );
    assert!(stamp.path().is_file(), "a read-only miss does not remove completion");
    // No invented manifest or provider/Ready is used in this genuine case.
}

#[test]
fn lld_missing_install_does_not_revoke_a_separate_recorded_llvm_install() {
    use crate::core::build_steps::llvm::*;
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let target = crate::core::config::TargetSelection::from_user("aarch64-unknown-linux-gnu");
    // Recorded-file DATA using the same reader fixtures; not an executed provider.
    let llvm = enzyme_tests::local_llvm(root.join("llvm"), false, target);
    let provider_key = recorded_llvm_dependency_key(&llvm, target).unwrap();
    let source = root.join("source");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("input"), b"source fixture").unwrap();
    let output = root.join("lld");
    let owner = OwnSourceGeneration {
        source: source.clone(),
        anchor: root.clone(),
        output: output.clone(),
        observed: observe_cmake_sources(&source, &output).unwrap(),
    };
    let recipe = SourceRecipeKey {
        dependency: provider_key.clone(),
        ..enzyme_tests::recorded_source_recipe(false)
    };
    let stamp = owner.stamp("lld", &target.triple, Some(&recipe));
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(output.join("bin")).unwrap();
    fs::write(output.join("bin/lld"), b"lld DATA").unwrap();
    fs::write(output.join("bin/other-installed-tool"), b"tool DATA").unwrap();
    manifest(&output, &["bin/lld", "bin/other-installed-tool"]);
    assert!(owner.complete(&stamp, || true).unwrap());
    assert!(owner.cache_matches("lld", &stamp, &output.join("bin/lld")));
    fs::remove_file(output.join("bin/other-installed-tool")).unwrap();
    assert!(!owner.cache_matches("lld", &stamp, &output.join("bin/lld")));
    assert_eq!(recorded_llvm_dependency_key(&llvm, target), Some(provider_key));
    assert!(stamp.path().exists(), "missing outputs do not authorize deletion");
}
