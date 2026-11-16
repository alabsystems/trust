// Andrew Yates
// Trust: synthetic provider facts exercise the actual owner, not tool availability.
use super::*;
use crate::utils::tests::TestCtx;

#[test]
fn tpde_owner_rejects_every_unsupported_provider_before_output_effects() {
    for kind in [LlvmKind::BuiltLocally, LlvmKind::DownloadedFromCi, LlvmKind::External] {
        for link_shared in [false, true] {
            let ctx = TestCtx::new();
            let session =
                crate::core::session::Session::new(ctx.config("build").stage(1).create_config());
            let builder = Builder::new(&session);
            let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
            let root = ctx.dir().join("selected llvm");
            builder.step_cache().put(
                Llvm { target },
                LlvmOutput {
                    llvm_config: root.join("bin/llvm-config"),
                    link_shared,
                    llvm_root_dir: root,
                    kind,
                },
            );
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                builder.ensure(Tpde { target })
            }));
            assert_eq!(result.is_ok(), kind == LlvmKind::BuiltLocally && link_shared);
            assert!(!tpde_output_dir(&builder, target).exists());
            assert!(!builder.step_cache().contains::<crate::core::build_steps::compile::Rustc>());
        }
    }
}

#[test]
fn tpde_planning_preserves_existing_stamps_and_creates_no_output() {
    for existing in [false, true] {
        let ctx = TestCtx::new();
        let session =
            crate::core::session::Session::new(ctx.config("build").stage(1).create_config());
        let builder = Builder::new(&session);
        let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
        let root = ctx.dir().join("selected llvm");
        builder.step_cache().put(
            Llvm { target },
            LlvmOutput {
                llvm_config: root.join("bin/llvm-config"),
                link_shared: true,
                llvm_root_dir: root,
                kind: LlvmKind::BuiltLocally,
            },
        );
        let out = tpde_output_dir(&builder, target);
        let stamp = BuildStamp::new(&out).with_prefix("tpde");
        let sentinel = out.join("build/CMakeCache.txt");
        if existing {
            fs::create_dir_all(sentinel.parent().unwrap()).unwrap();
            fs::write(stamp.path(), b"existing TPDE stamp").unwrap();
            fs::write(&sentinel, b"existing selected provider cache").unwrap();
        }
        let output = builder.ensure(Tpde { target });
        assert_eq!(output.plugin_path(), out.join("build/tpde-llvm/tpde-plugin.so"));
        if existing {
            assert_eq!(fs::read(stamp.path()).unwrap(), b"existing TPDE stamp");
            assert_eq!(fs::read(&sentinel).unwrap(), b"existing selected provider cache");
            assert_eq!(fs::read_dir(&out).unwrap().count(), 2);
        } else {
            assert!(!out.exists());
        }
    }
}

#[test]
fn direct_tpde_planning_retains_only_its_selected_lld_dependency() {
    for (target_name, enabled, explicit_linker, expected) in [
        ("x86_64-unknown-linux-gnu", true, false, true),
        ("x86_64-unknown-linux-gnu", false, false, false),
        ("x86_64-unknown-linux-gnu", true, true, false),
        ("aarch64-apple-darwin", true, false, false),
        ("x86_64-pc-windows-msvc", true, false, false),
    ] {
        let ctx = TestCtx::new();
        let mut config = ctx
            .config("build")
            .stage(1)
            .args(&["--set", &format!("rust.lld={enabled}")])
            .create_config();
        if explicit_linker {
            config.llvm_use_linker = Some("fixture-explicit-linker".into());
        }
        let session = crate::core::session::Session::new(config);
        let builder = Builder::new(&session);
        let target = TargetSelection::from_user(target_name);
        let root = ctx.dir().join("selected llvm");
        builder.step_cache().put(
            Llvm { target },
            LlvmOutput {
                llvm_config: root.join("bin/llvm-config"),
                link_shared: true,
                llvm_root_dir: root,
                kind: LlvmKind::BuiltLocally,
            },
        );
        builder.ensure(Tpde { target });
        let steps = builder.step_cache().executed_steps();
        let lld: Vec<_> = steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                (step.step.downcast_ref::<Lld>() == Some(&Lld { target })).then_some(index)
            })
            .collect();
        assert_eq!(lld.len(), usize::from(expected));
        if expected {
            let tpde = steps
                .iter()
                .position(|step| step.step.downcast_ref::<Tpde>() == Some(&Tpde { target }))
                .unwrap();
            assert!(lld[0] < tpde);
        }
        assert!(!tpde_output_dir(&builder, target).exists());
    }
}

// Trust: use the real status-produced stamp; do not manufacture its source hash or reset its memo.
#[test]
fn tpde_cache_requires_the_execution_recipe_and_a_regular_plugin() {
    let ctx = TestCtx::new();
    let session = crate::core::session::Session::new(ctx.config("build").stage(1).create_config());
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = completed_llvm_fixture(ctx.dir().join("completed llvm"), target);
    let dependency = completed_llvm_dependency_key(&llvm, target).unwrap();
    let TpdeBuildStatus::ShouldBuild(info) =
        recorded_fixture_status(&builder, target, Some(&dependency))
    else {
        panic!("a fresh owned output cannot be cached");
    };
    let plugin = info.output.plugin_path();
    begin_cmake_miss(&info.stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(plugin.parent().unwrap()).unwrap();
    fs::write(plugin, b"synthetic cached plugin").unwrap();
    info.stamp.write().unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&dependency)),
        TpdeBuildStatus::AlreadyBuilt(_)
    ));

    fs::remove_file(plugin).unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&dependency)),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    fs::create_dir(plugin).unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&dependency)),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    fs::remove_dir(plugin).unwrap();
    #[cfg(unix)]
    {
        let other = ctx.dir().join("another cached file");
        fs::write(&other, b"another owned artifact").unwrap();
        std::os::unix::fs::symlink(&other, plugin).unwrap();
        assert!(matches!(
            recorded_fixture_status(&builder, target, Some(&dependency)),
            TpdeBuildStatus::ShouldBuild(_)
        ));
        fs::remove_file(plugin).unwrap();
    }

    fs::write(plugin, b"synthetic cached plugin").unwrap();
    // A legacy completion lacking the current recipe/request fields is not reusable.
    let legacy = info.stamp.stamp().split_once(TPDE_BUILD_RECIPE).unwrap().0;
    fs::write(info.stamp.path(), legacy).unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&dependency)),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    assert_eq!(fs::read(plugin).unwrap(), b"synthetic cached plugin");
    info.stamp.write().unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&dependency)),
        TpdeBuildStatus::AlreadyBuilt(_)
    ));
}

// Trust: these are owned file fixtures, not claims that LLVM was actually built.
fn completed_llvm_fixture(root: PathBuf, target: TargetSelection) -> LlvmOutput {
    super::enzyme_tests::local_llvm(root, true, target)
}

fn order_llvm_completion(root: &Path) {
    use crate::utils::helpers::set_file_times;
    for (name, seconds) in
        [("build/CMakeCache.txt", 10), (".cmake-generation-stamp", 15), (".llvm-stamp", 20)]
    {
        set_file_times(
            &root.join(name),
            fs::FileTimes::new()
                .set_modified(std::time::UNIX_EPOCH + std::time::Duration::from_secs(seconds)),
        )
        .unwrap();
    }
}

#[test]
fn tpde_cache_tracks_recorded_llvm_changes_and_never_reuses_unknown_evidence() {
    let ctx = TestCtx::new();
    let session = crate::core::session::Session::new(ctx.config("build").stage(1).create_config());
    let builder = Builder::new(&session);
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = completed_llvm_fixture(ctx.dir().join("completed llvm"), target);
    let key_a = completed_llvm_dependency_key(&llvm, target).unwrap();
    assert_eq!(completed_llvm_dependency_key(&llvm, target).as_ref(), Some(&key_a));
    assert!(
        completed_llvm_dependency_key(
            &llvm,
            TargetSelection::from_user("aarch64-unknown-linux-gnu")
        )
        .is_none()
    );
    let other = completed_llvm_fixture(ctx.dir().join("other completed llvm"), target);
    assert_ne!(completed_llvm_dependency_key(&other, target).unwrap(), key_a);
    let TpdeBuildStatus::ShouldBuild(info) =
        recorded_fixture_status(&builder, target, Some(&key_a))
    else {
        panic!("fresh TPDE output");
    };
    begin_cmake_miss(&info.stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(info.output.plugin_path().parent().unwrap()).unwrap();
    fs::write(info.output.plugin_path(), b"synthetic plugin").unwrap();
    record_tpde_completion(&info.stamp, &llvm, target, Some(&key_a)).unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&key_a)),
        TpdeBuildStatus::AlreadyBuilt(_)
    ));

    let ordinary = fs::read(llvm.root_dir().join(".llvm-stamp")).unwrap();
    super::enzyme_tests::write_local_completion(llvm.root_dir(), target, &"b".repeat(64), true);
    let key_b = completed_llvm_dependency_key(&llvm, target).unwrap();
    assert_ne!(key_a, key_b);
    assert_ne!(fs::read(llvm.root_dir().join(".llvm-stamp")).unwrap(), ordinary);
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&key_b)),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    info.stamp.remove().unwrap();
    record_tpde_completion(&info.stamp, &llvm, target, Some(&key_a)).unwrap();
    assert!(!info.stamp.path().exists(), "changed post-build observations cannot record reuse");
    record_tpde_completion(&info.stamp, &llvm, target, None).unwrap();
    assert!(!info.stamp.path().exists(), "unknown pre-build evidence cannot be upgraded later");

    fs::write(
        llvm.root_dir().join("build/CMakeCache.txt"),
        b"CMAKE_BUILD_TYPE:STRING=Debug\nLLVM_LINK_LLVM_DYLIB:BOOL=ON\n",
    )
    .unwrap();
    order_llvm_completion(llvm.root_dir());
    let key_c = completed_llvm_dependency_key(&llvm, target).unwrap();
    assert_ne!(key_b, key_c);
    let TpdeBuildStatus::ShouldBuild(current) =
        recorded_fixture_status(&builder, target, Some(&key_c))
    else {
        panic!("new dependency requires TPDE build");
    };
    let suffix = format!("\nllvm-dependency:{key_c}");
    let unbound = current.stamp.stamp().strip_suffix(&suffix).unwrap();
    fs::write(current.stamp.path(), unbound).unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&key_c)),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    begin_cmake_miss(&current.stamp, CmakeGeneration::Known).unwrap();
    fs::create_dir_all(current.output.plugin_path().parent().unwrap()).unwrap();
    fs::write(current.output.plugin_path(), b"synthetic plugin").unwrap();
    record_tpde_completion(&current.stamp, &llvm, target, Some(&key_c)).unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, Some(&key_c)),
        TpdeBuildStatus::AlreadyBuilt(_)
    ));
    assert!(matches!(
        recorded_fixture_status(&builder, target, None),
        TpdeBuildStatus::ShouldBuild(_)
    ));
    current.stamp.remove().unwrap();
    fs::write(llvm.root_dir().join(".llvm-stamp"), b"legacy completion without source evidence")
        .unwrap();
    fs::write(
        llvm.root_dir().join(".trust-llvm-sources"),
        format!("tree {}\norigin adopted\n", "b".repeat(40)),
    )
    .unwrap();
    assert!(completed_llvm_dependency_key(&llvm, target).is_none());
    record_tpde_completion(&current.stamp, &llvm, target, Some(&key_c)).unwrap();
    assert!(!current.stamp.path().exists(), "unknown post-build evidence cannot record reuse");
    record_tpde_completion(&current.stamp, &llvm, target, None).unwrap();
    assert!(
        !current.stamp.path().exists(),
        "two unknown observations are not a completion identity"
    );
    let TpdeBuildStatus::ShouldBuild(unbound) = recorded_fixture_status(&builder, target, None)
    else {
        panic!("unknown dependency cannot be cached");
    };
    unbound.stamp.write().unwrap();
    assert!(matches!(
        recorded_fixture_status(&builder, target, None),
        TpdeBuildStatus::ShouldBuild(_)
    ));
}

#[test]
fn llvm_dependency_evidence_stays_unknown_for_weaker_or_incomplete_files() {
    use crate::utils::helpers::set_file_times;
    let ctx = TestCtx::new();
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let llvm = completed_llvm_fixture(ctx.dir().join("completed llvm"), target);
    let completion = llvm.root_dir().join(".llvm-stamp");
    let completed = fs::read(&completion).unwrap();
    assert!(completed_llvm_dependency_key(&llvm, target).is_some());
    for origin in ["built", "adopted", "header"] {
        fs::write(&completion, b"legacy completion").unwrap();
        fs::write(
            llvm.root_dir().join(".trust-llvm-sources"),
            format!("tree {}\norigin {origin}\ncommit {}\n", "a".repeat(40), "b".repeat(40)),
        )
        .unwrap();
        assert!(completed_llvm_dependency_key(&llvm, target).is_none());
    }
    fs::write(&completion, completed).unwrap();
    let record = llvm.root_dir().join(".cmake-generation-stamp");
    let original = fs::read(&record).unwrap();
    for bad in [b"not membership".as_slice(), b"legacy record is not membership"] {
        fs::write(&record, bad).unwrap();
        assert!(completed_llvm_dependency_key(&llvm, target).is_none());
    }
    fs::write(&record, &original).unwrap();
    order_llvm_completion(llvm.root_dir());
    let cache = llvm.root_dir().join("build/CMakeCache.txt");
    let cache_bytes = fs::read(&cache).unwrap();
    set_file_times(
        &cache,
        fs::FileTimes::new()
            .set_modified(std::time::UNIX_EPOCH + std::time::Duration::from_secs(40)),
    )
    .unwrap();
    assert!(completed_llvm_dependency_key(&llvm, target).is_none());
    order_llvm_completion(llvm.root_dir());
    assert!(completed_llvm_dependency_key(&llvm, target).is_some());
    for (path, limit) in [
        (record.clone(), 16 * 1024),
        (cache.clone(), 4 * 1024 * 1024),
        (llvm.root_dir().join(".llvm-stamp"), 64 * 1024),
    ] {
        assert!(completed_llvm_dependency_key(&llvm, target).is_some());
        let saved = fs::read(&path).unwrap();
        fs::remove_file(&path).unwrap();
        assert!(completed_llvm_dependency_key(&llvm, target).is_none());
        fs::create_dir(&path).unwrap();
        assert!(completed_llvm_dependency_key(&llvm, target).is_none());
        fs::remove_dir(&path).unwrap();
        let oversized = if path == record {
            let mut bytes = saved.clone();
            bytes.extend_from_slice(b"\n#");
            bytes.resize(limit + 1, b'x');
            bytes
        } else {
            vec![b'x'; limit + 1]
        };
        fs::write(&path, oversized).unwrap();
        order_llvm_completion(llvm.root_dir());
        assert!(completed_llvm_dependency_key(&llvm, target).is_none());
        fs::write(&path, saved).unwrap();
        order_llvm_completion(llvm.root_dir());
        assert!(completed_llvm_dependency_key(&llvm, target).is_some());
    }
    fs::write(&cache, cache_bytes).unwrap();
    order_llvm_completion(llvm.root_dir());
    assert!(completed_llvm_dependency_key(&llvm, target).is_some());
    let mut unsupported = llvm.clone();
    unsupported.kind = LlvmKind::External;
    assert!(completed_llvm_dependency_key(&unsupported, target).is_none());
    unsupported.kind = LlvmKind::DownloadedFromCi;
    assert!(completed_llvm_dependency_key(&unsupported, target).is_none());
    unsupported.kind = LlvmKind::BuiltLocally;
    unsupported.link_shared = false;
    assert!(completed_llvm_dependency_key(&unsupported, target).is_none());
}

// Old provider/artifact controls use explicit request data, not native preparation evidence.
fn recorded_fixture_status(
    builder: &Builder<'_>,
    target: TargetSelection,
    dependency: Option<&str>,
) -> TpdeBuildStatus {
    get_locally_built_tpde_build_status(
        builder,
        target,
        reusable_cmake_inputs(
            Some("controlled source data"),
            dependency,
            Some("controlled prepared request data"),
        ),
        builder.config.llvm_optimize && !builder.config.llvm_release_debuginfo,
    )
}

#[path = "tpde_request_tests.rs"]
mod request_tests;
