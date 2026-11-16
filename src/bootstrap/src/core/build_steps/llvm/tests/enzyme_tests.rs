// Andrew Yates
use super::*;
use crate::utils::tests::TestCtx;

fn selected_request(ctx: &TestCtx, out: &Path) -> String {
    let mut config = ctx.config("build").create_config();
    config.rust_remap_debuginfo = false;
    let session = crate::core::session::Session::new(config);
    let builder = Builder::new(&session);
    enzyme_cmake_plan(
        &builder,
        builder.host_target,
        out,
        &ctx.dir().join("selected llvm/lib/cmake/llvm"),
        &|_| None,
    )
    .unwrap()
    .requested_key()
}

// Owned recorded-file fixtures, not a claim that LLVM was built or downloaded.
pub(super) fn local_llvm(root: PathBuf, shared: bool, target: TargetSelection) -> LlvmOutput {
    fs::create_dir_all(root.join("build")).unwrap();
    fs::write(root.join("build/CMakeCache.txt"), b"CMAKE_BUILD_TYPE:STRING=Release\n").unwrap();
    write_local_completion(&root, target, &"a".repeat(64), shared);
    LlvmOutput {
        llvm_config: root.join("bin/llvm-config"),
        llvm_root_dir: root,
        link_shared: shared,
        kind: LlvmKind::BuiltLocally,
    }
}

// Strict recorded DATA for reader controls; no build or provider readiness is fabricated.
pub(super) fn write_local_completion(
    root: &Path,
    target: TargetSelection,
    source: &str,
    shared: bool,
) {
    let data = OwnSourceGeneration {
        source: root.join("unexecuted-source-fixture"),
        anchor: root.parent().unwrap().to_owned(),
        output: root.to_owned(),
        observed: Some(source.to_owned()),
    };
    let stamp = data.stamp("llvm", &target.triple, Some(&recorded_source_recipe(shared)));
    cmake_generation_record(&stamp).unwrap().write().unwrap();
    let artifact = root.join("bin/llvm-config");
    fs::create_dir_all(artifact.parent().unwrap()).unwrap();
    fs::write(&artifact, b"recorded fixture output").unwrap();
    let secondary = root.join("lib/recorded-secondary");
    fs::create_dir_all(secondary.parent().unwrap()).unwrap();
    fs::write(&secondary, b"recorded secondary output").unwrap();
    fixture_install_manifest(root, &[&artifact, &secondary]);
    assert!(installed_outputs::publish(&stamp).unwrap());
    stamp.write().unwrap();
    order_local(root);
}

// Request-shaped recorded DATA, not a claim that native preparation executed.
pub(super) fn recorded_source_recipe(shared: bool) -> SourceRecipeKey {
    SourceRecipeKey { request: "c".repeat(64), dependency: "none".to_owned(), link_shared: shared }
}

fn ordered_time(path: &Path, seconds: u64) {
    crate::utils::helpers::set_file_times(
        path,
        fs::FileTimes::new()
            .set_modified(std::time::UNIX_EPOCH + std::time::Duration::from_secs(seconds)),
    )
    .unwrap();
}

fn order_local(root: &Path) {
    ordered_time(&root.join("build/CMakeCache.txt"), 10);
    ordered_time(&root.join(".llvm-stamp"), 20);
    ordered_time(&root.join(".cmake-generation-stamp"), 15);
}

pub(super) fn ci_llvm(root: PathBuf, shared: bool) -> LlvmOutput {
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join(LLVM_CI_LINK_TYPE_PATH), if shared { "dynamic" } else { "static" })
        .unwrap();
    fs::write(
        root.join(".llvm-stamp"),
        format!("{}false{}", "a".repeat(40), crate::core::download::CI_LLVM_COMPLETION_RECIPE),
    )
    .unwrap();
    ordered_time(&root.join(LLVM_CI_LINK_TYPE_PATH), 10);
    ordered_time(&root.join(".llvm-stamp"), 20);
    LlvmOutput {
        llvm_config: root.join("bin/llvm-config"),
        llvm_root_dir: root,
        link_shared: shared,
        kind: LlvmKind::DownloadedFromCi,
    }
}

#[test]
fn enzyme_completion_tracks_local_and_ci_provider_changes_and_unknowns() {
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let out = ctx.dir().join("enzyme");
    fs::create_dir_all(&out).unwrap();
    let dylib = out.join("libEnzyme-22.so");
    fs::write(&dylib, b"owned synthetic library").unwrap();
    let request = selected_request(&ctx, &out);
    for shared in [false, true] {
        let llvm = local_llvm(ctx.dir().join(format!("local-{shared}")), shared, target);
        let before = recorded_llvm_dependency_key(&llvm, target).unwrap();
        let secondary = llvm.root_dir().join("lib/recorded-secondary");
        let completion_before = fs::read(llvm.root_dir().join(".llvm-stamp")).unwrap();
        let generation_before = fs::read(llvm.root_dir().join(".cmake-generation-stamp")).unwrap();
        fs::remove_file(&secondary).unwrap();
        assert!(llvm.llvm_config().is_file());
        assert!(llvm.root_dir().join("build/CMakeCache.txt").is_file());
        assert_eq!(fs::read(llvm.root_dir().join(".llvm-stamp")).unwrap(), completion_before);
        assert_eq!(
            fs::read(llvm.root_dir().join(".cmake-generation-stamp")).unwrap(),
            generation_before
        );
        assert!(
            recorded_llvm_dependency_key(&llvm, target).is_none(),
            "missing secondary install denies the actual local provider reader"
        );
        fs::write(&secondary, b"restored secondary output").unwrap();
        assert_eq!(recorded_llvm_dependency_key(&llvm, target), Some(before.clone()));
        let mut other_selection = llvm.clone();
        other_selection.link_shared = !shared;
        assert!(
            recorded_llvm_dependency_key(&other_selection, target).is_none(),
            "desired mode must match completed mode"
        );
        let stamp = enzyme_stamp(&out, "same enzyme sources", Some(&before), &request);
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        fs::write(&dylib, b"owned synthetic library").unwrap();
        record_enzyme_completion(&stamp, &dylib, &llvm, target, Some(&before)).unwrap();
        assert!(cached_enzyme(&stamp, &dylib, Some(&before)).is_some());
        let ordinary = fs::read(llvm.root_dir().join(".llvm-stamp")).unwrap();
        write_local_completion(llvm.root_dir(), target, &"b".repeat(64), shared);
        let changed = recorded_llvm_dependency_key(&llvm, target).unwrap();
        assert_ne!(before, changed);
        assert_ne!(fs::read(llvm.root_dir().join(".llvm-stamp")).unwrap(), ordinary);
        assert!(
            cached_enzyme(
                &enzyme_stamp(&out, "same enzyme sources", Some(&changed), &request),
                &dylib,
                Some(&changed)
            )
            .is_none()
        );
        stamp.remove().unwrap();
        record_enzyme_completion(&stamp, &dylib, &llvm, target, Some(&before)).unwrap();
        assert!(!stamp.path().exists());
        fs::write(llvm.root_dir().join("build/CMakeCache.txt"), b"CMAKE_BUILD_TYPE:STRING=Debug\n")
            .unwrap();
        order_local(llvm.root_dir());
        assert_ne!(recorded_llvm_dependency_key(&llvm, target).unwrap(), changed);
        fs::write(
            llvm.root_dir().join(".llvm-stamp"),
            b"legacy completion without source evidence",
        )
        .unwrap();
        fs::write(
            llvm.root_dir().join(".trust-llvm-sources"),
            format!("tree {}\norigin adopted\n", "b".repeat(40)),
        )
        .unwrap();
        assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
        record_enzyme_completion(&stamp, &dylib, &llvm, target, Some(&changed)).unwrap();
        assert!(!stamp.path().exists());
    }
    for shared in [false, true] {
        let llvm = ci_llvm(ctx.dir().join(format!("ci-{shared}")), shared);
        let before = recorded_llvm_dependency_key(&llvm, target).unwrap();
        let stamp = enzyme_stamp(&out, "same enzyme sources", Some(&before), &request);
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        fs::write(&dylib, b"owned synthetic library").unwrap();
        record_enzyme_completion(&stamp, &dylib, &llvm, target, Some(&before)).unwrap();
        assert!(cached_enzyme(&stamp, &dylib, Some(&before)).is_some());
        fs::write(
            llvm.root_dir().join(".llvm-stamp"),
            format!("{}true{}", "b".repeat(40), crate::core::download::CI_LLVM_COMPLETION_RECIPE),
        )
        .unwrap();
        ordered_time(&llvm.root_dir().join(".llvm-stamp"), 20);
        let changed = recorded_llvm_dependency_key(&llvm, target).unwrap();
        assert_ne!(before, changed);
        assert!(
            cached_enzyme(
                &enzyme_stamp(&out, "same enzyme sources", Some(&changed), &request),
                &dylib,
                Some(&changed)
            )
            .is_none()
        );
        stamp.remove().unwrap();
        record_enzyme_completion(&stamp, &dylib, &llvm, target, Some(&before)).unwrap();
        assert!(!stamp.path().exists());
    }
    let mut external = local_llvm(ctx.dir().join("external"), true, target);
    external.kind = LlvmKind::External;
    assert!(recorded_llvm_dependency_key(&external, target).is_none());
    let unknown = enzyme_stamp(&out, "sources", None, &request);
    unknown.write().unwrap();
    assert!(cached_enzyme(&unknown, &dylib, None).is_none());
    unknown.remove().unwrap();
    record_enzyme_completion(&unknown, &dylib, &external, target, None).unwrap();
    assert!(!unknown.path().exists());
}

#[test]
fn enzyme_ci_dependency_refuses_legacy_malformed_and_incomplete_completion() {
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = ci_llvm(ctx.dir().join("ci"), true);
    let stamp = llvm.root_dir().join(".llvm-stamp");
    let link = llvm.root_dir().join(LLVM_CI_LINK_TYPE_PATH);
    let valid = fs::read(&stamp).unwrap();
    let baseline = recorded_llvm_dependency_key(&llvm, target).unwrap();
    for prefix in [
        format!("{}false", "a".repeat(40)),
        format!("{}true", "a".repeat(40)),
        format!("{}false", "b".repeat(40)),
    ] {
        fs::write(&stamp, format!("{prefix}{}", crate::core::download::CI_LLVM_COMPLETION_RECIPE))
            .unwrap();
        ordered_time(&stamp, 20);
        let key = recorded_llvm_dependency_key(&llvm, target).unwrap();
        assert_eq!(key == baseline, prefix == format!("{}false", "a".repeat(40)));
    }
    fs::write(
        &stamp,
        format!("{}false{}", "a".repeat(64), crate::core::download::CI_LLVM_COMPLETION_RECIPE),
    )
    .unwrap();
    ordered_time(&stamp, 20);
    assert!(recorded_llvm_dependency_key(&llvm, target).is_some());
    for bytes in [
        format!("{}false", "a".repeat(40)).into_bytes(),
        b"bad".to_vec(),
        format!("{}false{}", "A".repeat(40), crate::core::download::CI_LLVM_COMPLETION_RECIPE)
            .into_bytes(),
        vec![b'x'; 64 * 1024 + 1],
    ] {
        fs::write(&stamp, bytes).unwrap();
        ordered_time(&stamp, 20);
        assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
    }
    fs::write(&stamp, &valid).unwrap();
    ordered_time(&stamp, 20);
    assert!(recorded_llvm_dependency_key(&llvm, target).is_some());
    for bytes in [b"static".as_slice(), b"dynamic\n", b"unknown", b"dynamic-and-extra"] {
        fs::write(&link, bytes).unwrap();
        ordered_time(&link, 10);
        assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
    }
    fs::write(&link, "dynamic").unwrap();
    ordered_time(&link, 30);
    assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
    ordered_time(&link, 10);
    for path in [&stamp, &link] {
        assert!(recorded_llvm_dependency_key(&llvm, target).is_some());
        let saved = fs::read(path).unwrap();
        fs::remove_file(path).unwrap();
        assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
        fs::create_dir(path).unwrap();
        assert!(recorded_llvm_dependency_key(&llvm, target).is_none());
        fs::remove_dir(path).unwrap();
        fs::write(path, saved).unwrap();
        ordered_time(path, if path == &stamp { 20 } else { 10 });
        assert!(recorded_llvm_dependency_key(&llvm, target).is_some());
    }
    let out = ctx.dir().join("enzyme");
    fs::create_dir_all(&out).unwrap();
    let dylib = out.join("library.so");
    fs::write(&dylib, b"owned library").unwrap();
    let request = selected_request(&ctx, &out);
    let completion = enzyme_stamp(&out, "sources", Some(&baseline), &request);
    record_enzyme_completion(&completion, &dylib, &llvm, target, None).unwrap();
    assert!(!completion.path().exists(), "unknown before build cannot be upgraded after it");
    fs::remove_file(&stamp).unwrap();
    record_enzyme_completion(&completion, &dylib, &llvm, target, Some(&baseline)).unwrap();
    assert!(!completion.path().exists(), "unknown after build cannot authorize reuse");
}

#[test]
fn enzyme_completion_requires_the_selected_library_and_matching_stamp() {
    let ctx = TestCtx::new();
    let out = ctx.dir().join("enzyme");
    let lib = out.join("lib");
    let selected = lib.join("libEnzyme-22.so");
    let next_major = lib.join("libEnzyme-23.so");
    let stamp = BuildStamp::new(&out).with_prefix("enzyme").add_stamp("selected sources");
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(&lib).unwrap();

    fs::write(&selected, b"owned synthetic library").unwrap();
    assert!(
        cached_enzyme(&stamp, &selected, Some("fixture dependency")).is_none(),
        "an artifact alone is not completion"
    );
    stamp.write().unwrap();
    assert_eq!(
        cached_enzyme(&stamp, &selected, Some("fixture dependency")).unwrap().enzyme_path(),
        selected
    );
    assert!(
        cached_enzyme(&stamp, &next_major, Some("fixture dependency")).is_none(),
        "an older major's file is not the selected output"
    );

    fs::remove_file(&selected).unwrap();
    assert!(
        cached_enzyme(&stamp, &selected, Some("fixture dependency")).is_none(),
        "a matching stamp cannot replace a missing artifact"
    );
    fs::create_dir(&selected).unwrap();
    assert!(
        cached_enzyme(&stamp, &selected, Some("fixture dependency")).is_none(),
        "a directory is not a library"
    );
    fs::remove_dir(&selected).unwrap();
    fs::write(&selected, b"restored owned synthetic library").unwrap();
    assert_eq!(
        cached_enzyme(&stamp, &selected, Some("fixture dependency")).unwrap().enzyme_path(),
        selected
    );

    let changed = BuildStamp::new(&out).with_prefix("enzyme").add_stamp("changed sources");
    assert!(
        cached_enzyme(&changed, &selected, Some("fixture dependency")).is_none(),
        "existing output cannot satisfy another completion stamp"
    );
    stamp.remove().unwrap();
    assert!(cached_enzyme(&stamp, &selected, Some("fixture dependency")).is_none());
}

#[cfg(unix)]
#[test]
fn enzyme_completion_keeps_regular_library_aliases_but_not_dangling_ones() {
    let ctx = TestCtx::new();
    let out = ctx.dir().join("enzyme");
    fs::create_dir_all(&out).unwrap();
    let artifact = out.join("actual library.so");
    let selected = out.join("libEnzyme-22.so");
    let stamp = BuildStamp::new(&out).with_prefix("enzyme").add_stamp("selected sources");
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    fs::write(&artifact, b"owned synthetic library").unwrap();
    std::os::unix::fs::symlink(&artifact, &selected).unwrap();
    stamp.write().unwrap();
    assert_eq!(
        cached_enzyme(&stamp, &selected, Some("fixture dependency")).unwrap().enzyme_path(),
        selected
    );
    fs::remove_file(&artifact).unwrap();
    assert!(cached_enzyme(&stamp, &selected, Some("fixture dependency")).is_none());
}
