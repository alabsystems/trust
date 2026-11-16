use super::*;

// Trust: the public and compiler dependency populations must both survive,
// without competing for a direct import of std's helper crate.
#[test]
fn compiler_helpers_sharing_std_names_are_dependency_only() {
    let temp = tempfile::TempDir::new().unwrap();
    let dst = temp.path();
    let std = ["libhashbrown-aaaa.rlib", "libhashbrown-aaaa.rmeta", "liblibc-aaaa.rmeta"];
    let compiler = [
        "libhashbrown-bbbb.rmeta",
        "libhashbrown-cccc.rmeta",
        "liblibc-bbbb.rmeta",
        "librustc_middle-bbbb.rmeta",
        "libcompiler_only-bbbb.rmeta",
    ];
    for name in std.iter().chain(&compiler).chain(["libhashbrown-stale.rmeta"].iter()) {
        fs::write(dst.join(name), name.as_bytes()).unwrap();
    }
    let entries = |names: &[&str]| {
        names.iter().map(|name| (PathBuf::from(name), DependencyType::Target)).collect::<Vec<_>>()
    };
    separate_compiler_std_dependencies(dst, &entries(&std), &entries(&compiler));
    for name in std {
        assert_eq!(fs::read(dst.join(name)).unwrap(), name.as_bytes());
    }
    for name in &compiler[..3] {
        assert!(!dst.join(name).exists(), "compiler helper must not compete with a direct import");
        assert_eq!(fs::read(dst.join("rustc-dependencies").join(name)).unwrap(), name.as_bytes());
    }
    for name in &compiler[3..] {
        assert_eq!(fs::read(dst.join(name)).unwrap(), name.as_bytes(), "private roots stay public");
    }
    assert!(!dst.join("libhashbrown-stale.rmeta").exists());
    assert!(!dst.join("rustc-dependencies/libhashbrown-stale.rmeta").exists());
}

#[test]
fn identical_std_and_compiler_helpers_need_no_second_copy() {
    let temp = tempfile::TempDir::new().unwrap();
    let name = "libhashbrown-aaaa.rmeta";
    fs::write(temp.path().join(name), b"same exact artifact").unwrap();
    let entries = [(PathBuf::from(name), DependencyType::Target)];
    separate_compiler_std_dependencies(temp.path(), &entries, &entries);
    assert_eq!(fs::read(temp.path().join(name)).unwrap(), b"same exact artifact");
    assert!(!temp.path().join("rustc-dependencies").exists());
}

// Trust: Assemble and the explicit development component can install the same
// compiler producer twice. Its old private copy and the new public copy may be
// hardlinks to one inode, for which POSIX rename alone is a successful no-op.
#[test]
fn compiler_helpers_reinstallation_keeps_only_the_private_link() {
    let temp = tempfile::TempDir::new().unwrap();
    let dst = temp.path().join("sysroot");
    fs::create_dir(&dst).unwrap();
    let std_name = "libhashbrown-aaaa.rmeta";
    let compiler_name = "libhashbrown-bbbb.rmeta";
    let producer = temp.path().join(compiler_name);
    fs::write(&producer, b"current compiler helper").unwrap();
    fs::write(dst.join(std_name), b"public standard helper").unwrap();
    let std = [(PathBuf::from(std_name), DependencyType::Target)];
    let compiler = [(PathBuf::from(compiler_name), DependencyType::Target)];
    let private = dst.join("rustc-dependencies").join(compiler_name);

    for _ in 0..3 {
        fs::hard_link(&producer, dst.join(compiler_name)).unwrap();
        separate_compiler_std_dependencies(&dst, &std, &compiler);
        assert!(!dst.join(compiler_name).exists(), "compiler helper must be dependency-only");
        assert_eq!(fs::read(&private).unwrap(), b"current compiler helper");
        assert_eq!(fs::read(&producer).unwrap(), b"current compiler helper");
        assert_eq!(fs::read(dst.join(std_name)).unwrap(), b"public standard helper");
    }
}

#[test]
fn compiler_helpers_reinstallation_replaces_stale_private_metadata() {
    let temp = tempfile::TempDir::new().unwrap();
    let dst = temp.path().join("sysroot");
    let private = dst.join("rustc-dependencies");
    fs::create_dir_all(&private).unwrap();
    let std_name = "libhashbrown-aaaa.rmeta";
    let compiler_name = "libhashbrown-bbbb.rmeta";
    let producer = temp.path().join(compiler_name);
    fs::write(&producer, b"current compiler helper").unwrap();
    fs::write(private.join(compiler_name), b"previous compiler helper").unwrap();
    fs::write(dst.join(std_name), b"public standard helper").unwrap();
    fs::hard_link(&producer, dst.join(compiler_name)).unwrap();
    let std = [(PathBuf::from(std_name), DependencyType::Target)];
    let compiler = [(PathBuf::from(compiler_name), DependencyType::Target)];

    separate_compiler_std_dependencies(&dst, &std, &compiler);
    assert!(!dst.join(compiler_name).exists(), "compiler helper must be dependency-only");
    assert_eq!(fs::read(private.join(compiler_name)).unwrap(), b"current compiler helper");
    assert_eq!(fs::read(&producer).unwrap(), b"current compiler helper");
    assert_eq!(fs::read(dst.join(std_name)).unwrap(), b"public standard helper");
}

#[test]
fn public_prune_removes_the_previous_local_compiler_helper_directory() {
    let temp = tempfile::TempDir::new().unwrap();
    let private = temp.path().join("rustc-dependencies");
    fs::create_dir(&private).unwrap();
    fs::write(private.join("libhashbrown-old.rmeta"), b"previous local compiler").unwrap();
    fs::write(temp.path().join("libhashbrown-new.rlib"), b"std rlib").unwrap();
    fs::write(temp.path().join("libhashbrown-new.rmeta"), b"std metadata").unwrap();
    prune_public_sysroot_compiler_artifacts(temp.path());
    assert!(!private.exists(), "dist/test must not retain a previous local compiler closure");
    assert_eq!(fs::read(temp.path().join("libhashbrown-new.rmeta")).unwrap(), b"std metadata");
}

// Trust: a configured stage0 SDK is an input, not an internal build artifact.
#[cfg(unix)]
mod initial_sysroot_custody {
    use std::collections::BTreeMap;
    use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};

    use super::*;
    use crate::core::config::DryRun;
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;

    #[derive(Debug, PartialEq, Eq)]
    struct InputEntry {
        physical: (u64, u64, u32, u64, u64, i64, i64, i64, i64),
        bytes: Vec<u8>,
        alias: Option<PathBuf>,
    }

    fn snapshot(root: &Path) -> BTreeMap<PathBuf, InputEntry> {
        fn visit(root: &Path, path: &Path, entries: &mut BTreeMap<PathBuf, InputEntry>) {
            let m = fs::symlink_metadata(path).unwrap();
            entries.insert(
                path.strip_prefix(root).unwrap().to_owned(),
                InputEntry {
                    physical: (
                        m.dev(),
                        m.ino(),
                        m.mode(),
                        m.nlink(),
                        m.len(),
                        m.mtime(),
                        m.mtime_nsec(),
                        m.ctime(),
                        m.ctime_nsec(),
                    ),
                    bytes: if m.is_file() { fs::read(path).unwrap() } else { Vec::new() },
                    alias: m.file_type().is_symlink().then(|| fs::read_link(path).unwrap()),
                },
            );
            if m.is_dir() {
                for entry in fs::read_dir(path).unwrap() {
                    visit(root, &entry.unwrap().path(), entries);
                }
            }
        }
        let mut entries = BTreeMap::new();
        visit(root, root, &mut entries);
        entries
    }

    fn fixture(ctx: &TestCtx) -> Session {
        let mut session = Session::new(ctx.config("build").create_config());
        session.config.set_dry_run(DryRun::Disabled);
        // Trust: a real stage-0 Sysroot asks for the LLVM build status, which hashes
        // `<src>/src/llvm-project` (llvm.rs OwnSourceGeneration). Give that walk this
        // fixture's own empty tree: a unit test never hashes this checkout's sources.
        session.config.src = ctx.dir().join("fixture source");
        fs::create_dir_all(session.config.src.join("src/llvm-project")).unwrap();
        let sdk = ctx.dir().join("external initial SDK");
        let lib = sdk.join("lib/rustlib").join(session.host_target).join("lib");
        fs::create_dir_all(&lib).unwrap();
        for (name, bytes) in [
            ("libstd-fixture.rlib", b"snapshot std".as_slice()),
            ("librustc_std_workspace_core-fixture.rlib", b"std shim"),
            ("librustc_ast-fixture.rmeta", b"private metadata"),
        ] {
            fs::write(lib.join(name), bytes).unwrap();
        }
        fs::set_permissions(lib.join("libstd-fixture.rlib"), fs::Permissions::from_mode(0o640))
            .unwrap();
        symlink("libstd-fixture.rlib", lib.join("libstd-alias.rlib")).unwrap();
        fs::write(sdk.join("lib/librustc_driver-fixture.dylib"), b"private runtime").unwrap();
        let outside = ctx.dir().join("unrelated source");
        fs::create_dir(&outside).unwrap();
        fs::write(outside.join("marker"), b"must stay outside sysroot").unwrap();
        symlink(&outside, sdk.join("lib/rustlib/src")).unwrap();
        symlink(&outside, sdk.join("lib/rustlib/rustc-src")).unwrap();
        // Session creation probes the genuine test compiler; only the installer reads this SDK.
        session.initial_rustc = sdk.join("bin/trustc");
        session.config.external_rustc = Some(session.initial_rustc.clone());
        session.initial_sysroot = sdk;
        session
    }

    fn install(builder: &Builder<'_>) -> PathBuf {
        let compiler = Compiler::new(0, builder.host_target);
        StdLink::from_std(Std::new(compiler, compiler.host), compiler).run(builder);
        local_sysroot_dir(builder, compiler)
    }

    #[test]
    fn external_sdk_is_unchanged_across_install_and_reassembly() {
        let ctx = TestCtx::new();
        let session = fixture(&ctx);
        let original = snapshot(&session.initial_sysroot);
        let outside = snapshot(&ctx.dir().join("unrelated source"));
        let builder = Builder::new(&session);
        let relative = Path::new("lib/rustlib").join(builder.host_target).join("lib");
        let source = session.initial_sysroot.join(&relative).join("libstd-fixture.rlib");
        for _ in 0..2 {
            let destination = install(&builder);
            assert_eq!(snapshot(&session.initial_sysroot), original, "external SDK custody");
            assert_eq!(snapshot(&ctx.dir().join("unrelated source")), outside);
            let std = destination.join(&relative).join("libstd-fixture.rlib");
            assert_ne!(fs::metadata(&std).unwrap().ino(), fs::metadata(&source).unwrap().ino());
            assert_eq!(fs::read(&std).unwrap(), b"snapshot std");
            assert_eq!(fs::metadata(&std).unwrap().mode() & 0o777, 0o640);
            assert_eq!(
                fs::read(destination.join(&relative).join("libstd-alias.rlib")).unwrap(),
                b"snapshot std"
            );
            assert_eq!(
                fs::read(
                    destination.join(&relative).join("librustc_std_workspace_core-fixture.rlib")
                )
                .unwrap(),
                b"std shim"
            );
            assert!(!destination.join(&relative).join("librustc_ast-fixture.rmeta").exists());
            assert!(!destination.join("lib/librustc_driver-fixture.dylib").exists());
            assert!(!destination.join("lib/rustlib/src/marker").exists());
            assert!(!destination.join("lib/rustlib/rustc-src/marker").exists());
            fs::write(&std, b"owned destination edit").unwrap();
            assert_eq!(
                snapshot(&session.initial_sysroot),
                original,
                "destination must be isolated"
            );
        }
    }

    #[test]
    fn legacy_sdk_link_detaches_once_then_preserves_the_input() {
        let ctx = TestCtx::new();
        let session = fixture(&ctx);
        let builder = Builder::new(&session);
        let relative = Path::new("lib/rustlib").join(builder.host_target).join("lib");
        let source = session.initial_sysroot.join(&relative).join("libstd-fixture.rlib");
        let original_links = fs::metadata(&source).unwrap().nlink();
        let destination = builder.sysroot(Compiler::new(0, builder.host_target));
        fs::create_dir_all(destination.join(&relative)).unwrap();
        fs::hard_link(&source, destination.join(&relative).join("libstd-fixture.rlib")).unwrap();
        assert_eq!(fs::metadata(&source).unwrap().nlink(), original_links + 1);
        install(&builder);
        assert_eq!(
            fs::metadata(&source).unwrap().nlink(),
            original_links,
            "retire old shared inode"
        );
        let detached = snapshot(&session.initial_sysroot);
        install(&builder);
        assert_eq!(snapshot(&session.initial_sysroot), detached);
    }

    #[test]
    fn configured_compiler_in_stage0_bin_still_has_external_input_custody() {
        let ctx = TestCtx::new();
        let mut session = fixture(&ctx);
        // An explicitly configured compiler can use the legacy bin spelling while its
        // sysroot query reports an external SDK. The declaration, not that spelling,
        // determines whether the whole legacy downloaded toolchain can be linked.
        let legacy = session.out.join(session.host_target).join("stage0");
        fs::create_dir_all(legacy.join("bin")).unwrap();
        session.initial_rustc = legacy.join("bin/trustc");
        session.config.external_rustc = Some(session.initial_rustc.clone());
        fs::write(&session.initial_rustc, b"owned compiler path fixture").unwrap();
        symlink(session.initial_sysroot.join("lib"), legacy.join("lib")).unwrap();
        for name in ["src", "rustc-src"] {
            fs::remove_file(session.initial_sysroot.join("lib/rustlib").join(name)).unwrap();
        }
        let original = snapshot(&session.initial_sysroot);
        let destination = install(&Builder::new(&session));
        assert_eq!(snapshot(&session.initial_sysroot), original, "explicit external SDK");
        assert!(!destination.join("lib/librustc_driver-fixture.dylib").exists());
    }

    #[test]
    fn downloaded_stage0_keeps_its_owned_toolchain_links() {
        let ctx = TestCtx::new();
        let mut session = fixture(&ctx);
        for name in ["src", "rustc-src"] {
            fs::remove_file(session.initial_sysroot.join("lib/rustlib").join(name)).unwrap();
        }
        let stage0 = session.out.join(session.host_target).join("stage0");
        fs::create_dir_all(stage0.parent().unwrap()).unwrap();
        fs::rename(&session.initial_sysroot, &stage0).unwrap();
        session.initial_sysroot = stage0.clone();
        session.initial_rustc = stage0.join("bin/trustc");
        session.config.external_rustc = None;
        fs::create_dir(stage0.join("bin")).unwrap();
        fs::write(&session.initial_rustc, b"owned downloaded compiler").unwrap();
        let builder = Builder::new(&session);
        let destination = install(&builder);
        for relative in [Path::new("bin/trustc"), Path::new("lib/librustc_driver-fixture.dylib")] {
            let source = fs::metadata(stage0.join(relative)).unwrap();
            let installed = fs::metadata(destination.join(relative)).unwrap();
            assert_eq!((source.dev(), source.ino()), (installed.dev(), installed.ino()));
            assert_eq!(source.nlink(), 2, "downloaded build-owned artifacts still hard-link");
            assert_eq!(
                fs::read(stage0.join(relative)).unwrap(),
                fs::read(destination.join(relative)).unwrap()
            );
        }
    }

    #[test]
    fn internal_filtered_artifacts_keep_the_hard_link_fast_path() {
        let ctx = TestCtx::new();
        let session = fixture(&ctx);
        let source = ctx.dir().join("internal build output");
        let destination = ctx.dir().join("internal sysroot");
        fs::create_dir_all(source.join("nested")).unwrap();
        fs::create_dir(&destination).unwrap();
        fs::write(source.join("nested/libbuilt.rlib"), b"built here").unwrap();
        session.cp_link_filtered(&source, &destination, &|_| true);
        let artifact = fs::metadata(source.join("nested/libbuilt.rlib")).unwrap();
        let installed = fs::metadata(destination.join("nested/libbuilt.rlib")).unwrap();
        assert_eq!((artifact.dev(), artifact.ino()), (installed.dev(), installed.ino()));
        assert_eq!(artifact.nlink(), 2, "control must exercise real hard links");
        assert_eq!(fs::read(destination.join("nested/libbuilt.rlib")).unwrap(), b"built here");
    }
}

// Trust: identical rendered std rows can be distinct cache keys. Cross-host
// assembly needs target runtime std and build-host std before compiling rustc,
// then its own (possibly uplifted) target std without an implicit StdLink.
#[test]
fn cross_host_assembly_retains_std_dependencies_and_link_policies() {
    for (stage, explicit_frontend) in [(2, false), (2, true), (3, false), (3, true)] {
        for full_bootstrap in [false, true] {
            let context = crate::utils::tests::TestCtx::new();
            let target = TargetSelection::from_user("i686-unknown-haiku");
            let config = context
                .config("build")
                .stage(stage)
                .hosts(&[&target.triple])
                .args(&["--set", &format!("build.full-bootstrap={full_bootstrap}")]);
            let config = if explicit_frontend {
                config.args(&[
                    "--set",
                    "build.extended=true",
                    "--set",
                    "build.tools=['targo-trust']",
                ])
            } else {
                config.args(&["--set", "build.extended=false"])
            };
            let session = crate::core::session::Session::new(config.create_config());
            let builder = Builder::new(&session);
            let build_compiler = Compiler::new(stage - 1, builder.host_target);
            let target_compiler = Compiler::new(stage, target);
            builder.ensure(Assemble { target_compiler });

            // The host assembly's unlinked key must not hide Rustc's linked
            // host dependency, even though their rendered metadata is equal.
            for std in [
                Std::new(build_compiler, build_compiler.host).without_sysroot_link(),
                Std::new(build_compiler, build_compiler.host),
                Std::new(build_compiler, target),
                Std::new(target_compiler, target).without_sysroot_link(),
            ] {
                let stamp =
                    builder.step_cache().get(&std).expect("required std cache key is absent");
                let std_compiler = if !full_bootstrap && std.build_compiler.stage > 1 {
                    Compiler::new(1, builder.host_target)
                } else {
                    std.build_compiler
                };
                assert_eq!(
                    stamp.expect("required std stamp is absent").path(),
                    build_stamp::libstd_stamp(&builder, std_compiler, std.target).path(),
                    "stage {stage}, full_bootstrap={full_bootstrap}, explicit_frontend={explicit_frontend}, {std:?}",
                );
            }

            let runtime_std_compiler = if !full_bootstrap {
                Compiler::new(1, builder.host_target)
            } else {
                build_compiler
            };
            for std_target in [build_compiler.host, target] {
                assert!(
                    builder
                        .step_cache()
                        .get(&StdLink::from_std(
                            Std::new(build_compiler, std_target),
                            runtime_std_compiler,
                        ))
                        .is_some(),
                    "rustc must receive linked host and target std before assembly",
                );
            }
            assert!(
                builder
                    .step_cache()
                    .get(&StdLink::from_std(
                        Std::new(target_compiler, target),
                        if full_bootstrap {
                            Compiler::new(stage, builder.host_target)
                        } else {
                            runtime_std_compiler
                        },
                    ))
                    .is_none(),
                "Assemble owns installation of its selected target std stamp",
            );

            let steps = builder.step_cache().executed_steps();
            let positions = |step: crate::core::builder::StepMetadata| {
                steps
                    .iter()
                    .enumerate()
                    .filter_map(|(index, executed)| {
                        (executed.metadata.as_ref() == Some(&step)).then_some(index)
                    })
                    .collect::<Vec<_>>()
            };
            let rustc = positions(Step::metadata(&Rustc::new(build_compiler, target)).unwrap());
            assert_eq!(rustc.len(), 1, "cross-host rustc must be compiled exactly once");
            for prerequisite in [
                Step::metadata(&llvm::Llvm { target }).unwrap(),
                Step::metadata(&Std::new(build_compiler, target)).unwrap(),
                Step::metadata(&Std::new(build_compiler, build_compiler.host)).unwrap(),
            ] {
                let dependencies = positions(prerequisite);
                assert!(!dependencies.is_empty(), "rustc prerequisite is absent");
                assert!(dependencies.iter().all(|index| *index < rustc[0]));
            }
            let assembled_std =
                positions(Step::metadata(&Std::new(target_compiler, target)).unwrap());
            assert_eq!(assembled_std.len(), 1, "assembled compiler needs its target std");
            assert!(rustc[0] < assembled_std[0]);
        }
    }
}

// Trust: the legacy path is the exact failure from `x check --stage 1 compiler`.
#[test]
fn cargo_hashed_artifact_paths_cover_both_layouts() {
    let root = Path::new("stage1-rustc/target/release");
    assert!(is_precise_cargo_artifact(&root.join("deps/liblibc-df6d82f3e61a1c17.rmeta"), root));
    assert!(is_precise_cargo_artifact(&root.join("build/libc/hash/out/liblibc-hash.rmeta"), root));
    for alias in
        ["liblibc.rmeta", "deps-other/liblibc-hash.rmeta", "build-other/liblibc-hash.rmeta"]
    {
        assert!(!is_precise_cargo_artifact(&root.join(alias), root));
    }
    assert!(!is_precise_cargo_artifact(
        Path::new("other-target/release/deps/liblibc-hash.rmeta"),
        root
    ));
}

#[test]
fn cargo_top_level_aliases_resolve_in_either_layout_and_mixed_caches() {
    for directories in
        [vec!["deps"], vec!["build/example/hash/out"], vec!["deps", "build/example/hash/out"]]
    {
        let temp = tempfile::TempDir::new().unwrap();
        let top_level = temp.path().join("libexample.rlib");
        fs::write(&top_level, b"current artifact").unwrap();
        let mut expected = Vec::new();
        for directory in directories {
            let directory = temp.path().join(directory);
            fs::create_dir_all(&directory).unwrap();
            let matching = directory.join("libexample-current.rlib");
            fs::write(&matching, b"current artifact").unwrap();
            expected.push(matching);
            // Equal length is not enough to select an old artifact.
            fs::write(directory.join("libexample-stale.rlib"), b"outdated content").unwrap();
        }
        let candidates = cargo_artifact_candidates(temp.path());
        let refs = candidates.iter().collect::<Vec<_>>();
        let selected = resolve_top_level_artifact(&top_level, "libexample", "rlib", 16, &refs);
        assert!(expected.iter().any(|path| path == selected));
        assert_eq!(fs::read(selected).unwrap(), b"current artifact");
    }
}

#[test]
#[should_panic(expected = "no deps output matched top-level artifact bytes")]
fn cargo_top_level_alias_rejects_same_length_wrong_bytes_across_layouts() {
    let temp = tempfile::TempDir::new().unwrap();
    let top_level = temp.path().join("libexample.rmeta");
    fs::write(&top_level, b"current artifact").unwrap();
    for directory in ["deps", "build/example/hash/out"] {
        let directory = temp.path().join(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("libexample-stale.rmeta"), b"outdated content").unwrap();
    }
    let candidates = cargo_artifact_candidates(temp.path());
    let refs = candidates.iter().collect::<Vec<_>>();
    resolve_top_level_artifact(&top_level, "libexample", "rmeta", 16, &refs);
}

#[test]
#[should_panic(expected = "no output generated")]
fn cargo_top_level_alias_rejects_missing_hashed_artifacts() {
    let temp = tempfile::TempDir::new().unwrap();
    let top_level = temp.path().join("libexample.rmeta");
    fs::write(&top_level, b"current artifact").unwrap();
    let candidates = cargo_artifact_candidates(temp.path());
    assert!(candidates.is_empty());
    resolve_top_level_artifact(&top_level, "libexample", "rmeta", 16, &[]);
}

#[test]
fn private_sysroot_identity_uses_the_full_compiler_commit() {
    let version = "rustc 1.99.0-nightly (012345678 2026-07-19)\n\
binary: rustc\n\
commit-hash: 0123456789abcdef0123456789abcdef01234567\n\
host: aarch64-apple-darwin\n";

    assert_eq!(
        rustc_commit_hash_from_verbose_version(version),
        Some("0123456789abcdef0123456789abcdef01234567")
    );
    assert_eq!(rustc_commit_hash_from_verbose_version("commit-hash: \n"), None);
    assert_eq!(rustc_commit_hash_from_verbose_version("release: nightly\n"), None);

    let stamp_path = Path::new("build/aarch64-apple-darwin/stage1-rustc/.librustc.stamp");
    let first = rustc_private_sysroot_key_from_entries(
        stamp_path,
        Some("0123456789abcdef0123456789abcdef01234567"),
        Vec::new(),
        None,
        None,
    );
    let repeated = rustc_private_sysroot_key_from_entries(
        stamp_path,
        Some("0123456789abcdef0123456789abcdef01234567"),
        Vec::new(),
        None,
        None,
    );
    let second = rustc_private_sysroot_key_from_entries(
        stamp_path,
        Some("fedcba9876543210fedcba9876543210fedcba98"),
        Vec::new(),
        None,
        None,
    );

    assert_eq!(first, repeated, "the same compiler identity must reuse its private sysroot");
    assert_ne!(first, second, "a different compiler commit must select a different sysroot");
}

#[test]
fn private_sysroot_identity_tracks_in_place_runtime_dylib_rebuilds() {
    let temp = tempfile::TempDir::new().unwrap();
    let runtime = temp.path().join("librustc_driver-same-disambiguator.so");
    fs::write(&runtime, b"runtime-generation-one").unwrap();

    let first_runtime_identity = rustc_private_runtime_dylib_identity(vec![runtime.clone()]);
    let first_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        vec![(runtime.clone(), DependencyType::Target)],
        Some(&first_runtime_identity),
        None,
    );

    // Keep the path, stamp entry, commit, and byte length fixed. Only the
    // runtime's actual content changes, matching an in-place stage rebuild.
    fs::write(&runtime, b"runtime-generation-two").unwrap();
    let second_runtime_identity = rustc_private_runtime_dylib_identity(vec![runtime.clone()]);
    let second_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        vec![(runtime, DependencyType::Target)],
        Some(&second_runtime_identity),
        None,
    );

    assert_ne!(first_runtime_identity, second_runtime_identity);
    assert_ne!(
        first_sysroot_identity, second_sysroot_identity,
        "changed runtime bytes must change Cargo's private-sysroot search path"
    );
}

// Trust: reproduce the std cache hole with a fixed launcher and an in-place
// driver replacement whose path, length and mtime all stay unchanged.
#[test]
fn std_cache_tracks_runtime_bytes_behind_a_fixed_launcher() {
    let temp = tempfile::TempDir::new().unwrap();
    let launcher = temp.path().join("rustc");
    let runtime = temp.path().join("librustc_driver.so");
    let output = temp.path().join("std");
    fs::write(&launcher, b"unchanged launcher").unwrap();
    fs::write(&runtime, b"runtime-generation-one").unwrap();
    let before = fs::metadata(&runtime).unwrap();
    let identity = std_compiler_runtime_files_identity(launcher.clone(), vec![runtime.clone()]);
    assert!(build_stamp::clear_if_identity_changed(&output, &identity).unwrap());
    fs::write(output.join("core.rmeta"), b"old runtime metadata").unwrap();
    fs::write(output.join(".rustc_info.json"), b"old cached version").unwrap();

    fs::write(&runtime, b"runtime-generation-two").unwrap();
    fs::File::options()
        .write(true)
        .open(&runtime)
        .unwrap()
        .set_times(fs::FileTimes::new().set_modified(before.modified().unwrap()))
        .unwrap();
    assert_eq!(fs::metadata(&runtime).unwrap().len(), before.len());
    assert_eq!(fs::metadata(&runtime).unwrap().modified().unwrap(), before.modified().unwrap());
    let changed = std_compiler_runtime_files_identity(launcher, vec![runtime]);
    assert_ne!(identity, changed);
    assert!(build_stamp::clear_if_identity_changed(&output, &changed).unwrap());
    assert!(!output.join("core.rmeta").exists());
    assert!(!output.join(".rustc_info.json").exists());
    fs::write(output.join("core.rmeta"), b"new runtime metadata").unwrap();
    assert!(!build_stamp::clear_if_identity_changed(&output, &changed).unwrap());
    assert!(output.join("core.rmeta").exists());
}

#[test]
fn std_cache_static_compiler_tracks_launcher_bytes() {
    let temp = tempfile::TempDir::new().unwrap();
    let launcher = temp.path().join("rustc");
    fs::write(&launcher, b"compiler-one").unwrap();
    let first = std_compiler_runtime_files_identity(launcher.clone(), Vec::new());
    assert_eq!(first, std_compiler_runtime_files_identity(launcher.clone(), Vec::new()));
    fs::write(&launcher, b"compiler-two").unwrap();
    assert_ne!(first, std_compiler_runtime_files_identity(launcher, Vec::new()));
}

#[test]
fn private_sysroot_identity_tracks_in_place_copied_std_rebuilds() {
    let temp = tempfile::TempDir::new().unwrap();
    let std_artifact = temp.path().join("libcore-same-disambiguator.rlib");
    fs::write(&std_artifact, b"copied-std-generation-one").unwrap();

    let first_std_identity = rustc_private_copied_std_identity(vec![std_artifact.clone()]);
    let first_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        Vec::new(),
        None,
        Some(&first_std_identity),
    );

    fs::write(&std_artifact, b"copied-std-generation-two").unwrap();
    let second_std_identity = rustc_private_copied_std_identity(vec![std_artifact]);
    let second_sysroot_identity = rustc_private_sysroot_key_from_entries(
        Path::new("build/host/stage1-rustc/.librustc.stamp"),
        Some("unchanged-compiler-commit"),
        Vec::new(),
        None,
        Some(&second_std_identity),
    );

    assert_ne!(first_std_identity, second_std_identity);
    assert_ne!(
        first_sysroot_identity, second_sysroot_identity,
        "changed copied std bytes must select a fresh nested-driver sysroot"
    );
}

#[test]
fn narrow_trust_cg_self_host_boundary_is_stage_and_backend_exact() {
    assert!(!staged_narrow_trust_cg_cannot_self_host(0, false, &CodegenBackendKind::TrustCg,));
    assert!(staged_narrow_trust_cg_cannot_self_host(0, true, &CodegenBackendKind::TrustCg,));
    assert!(staged_narrow_trust_cg_cannot_self_host(1, false, &CodegenBackendKind::TrustCg,));
    assert!(staged_narrow_trust_cg_cannot_self_host(2, false, &CodegenBackendKind::TrustCg,));
    assert!(!staged_narrow_trust_cg_cannot_self_host(2, false, &CodegenBackendKind::Llvm,));
    // The trust-ir → trust-cg plugin is the SELF-HOST lane: a staged compiler
    // whose default backend is `trust-ir-cg` may build std and the next stage.
    assert!(!staged_narrow_trust_cg_cannot_self_host(1, false, &CodegenBackendKind::TrustIrCg,));
    assert!(!staged_narrow_trust_cg_cannot_self_host(2, false, &CodegenBackendKind::TrustIrCg,));

    let error = narrow_trust_cg_self_host_error("the standard library");
    assert!(error.contains("External scalar-register functions"));
    assert!(error.contains("codegen-backends = [\"llvm\", \"trust-cg\"]"));
    assert!(error.contains("LLVM first"));
}

#[test]
fn trust_channel_takes_the_nightly_compiler_defaults() {
    // PERF-SEP26-DEFAULTS: upstream gates Polonius-next and the next trait
    // solver on nightly/dev; the `trust` channel must stay in that set or
    // Trust builds silently revert to the pre-1.101 defaults.
    for channel in ["nightly", "dev", "trust"] {
        assert!(channel_takes_nightly_defaults(channel), "{channel}");
    }
    for channel in ["stable", "beta", "auto-detect", ""] {
        assert!(!channel_takes_nightly_defaults(channel), "{channel}");
    }
}

#[test]
fn trust_cg_builtin_selector_considers_every_configured_host() {
    let all_disabled =
        [vec![CodegenBackendKind::Llvm], vec![CodegenBackendKind::Custom("other".into())]];
    assert!(!trust_cg_builtin_enabled_for_any_host(all_disabled.iter().map(Vec::as_slice)));
    assert!(!trust_cg_builtin_enabled_for_host(&all_disabled[0]));
    assert!(!trust_cg_builtin_enabled_for_host(&all_disabled[1]));

    let cross_host_only = [
        vec![CodegenBackendKind::Llvm],
        vec![CodegenBackendKind::TrustCg, CodegenBackendKind::Llvm],
    ];
    assert!(trust_cg_builtin_enabled_for_any_host(cross_host_only.iter().map(Vec::as_slice)));
    assert!(
        !trust_cg_builtin_enabled_for_host(&cross_host_only[0]),
        "a globally registered selector must still skip a host where trust-cg is disabled"
    );
    assert!(trust_cg_builtin_enabled_for_host(&cross_host_only[1]));
}

#[test]
fn installing_an_rlib_prunes_metadata_left_by_an_earlier_build() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    // Neither is recorded as installed by this run, so both are leftovers.
    fs::write(sysroot.join("libfoo-old.rmeta"), b"stale metadata").unwrap();
    fs::write(sysroot.join("libfoo-new.rmeta"), b"active metadata").unwrap();

    let active_rlib =
        RustArtifact { crate_name: "foo", stem: "libfoo-new", kind: RustArtifactKind::Rlib };
    prune_superseded_sysroot_artifacts(sysroot, active_rlib);

    assert!(sysroot.join("libfoo-new.rmeta").exists(), "the active stem's own metadata must stay");
    assert!(!sysroot.join("libfoo-old.rmeta").exists(), "a superseded stem must be pruned");
}

/// Regression test for a sysroot that built successfully and could not be used.
///
/// `lib/rustlib/<target>/lib` is filled from TWO stamps — std's and rustc's —
/// and they legitimately carry the same external crates at different versions
/// (`hashbrown`, `libc`, `object`, `memchr`, `gimli`, `miniz_oxide`, ...).
/// Pruning by crate NAME made whichever population was copied second delete the
/// other's artifacts. Measured on a clean stage2 (2026-08-30), 12 artifacts
/// across 9 crate names went missing and `extern crate rustc_public;` — with no
/// other code at all — failed with E0460 `found possibly newer version of crate
/// hashbrown which rustc_public depends on`, i.e. every out-of-tree
/// `rustc_private` consumer, including this repo's own `trust-mir-extract`.
#[test]
fn two_versions_of_one_external_crate_survive_the_same_build() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();

    // std's copy lands first and is recorded, exactly as add_to_sysroot does.
    fs::write(sysroot.join("libhashbrown-aaaa.rmeta"), b"std's metadata").unwrap();
    record_sysroot_install(sysroot, "libhashbrown-aaaa.rmeta");

    // rustc's copy of the same crate at a different version follows.
    let rustc_copy = RustArtifact {
        crate_name: "hashbrown",
        stem: "libhashbrown-bbbb",
        kind: RustArtifactKind::Rlib,
    };
    prune_superseded_sysroot_artifacts(sysroot, rustc_copy);

    assert!(
        sysroot.join("libhashbrown-aaaa.rmeta").exists(),
        "the other population's artifact is not stale — deleting it is the E0460 bug"
    );
}

#[test]
fn a_rustc_private_crate_still_admits_only_one_version() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    // Even recorded-this-run, rustc_* crates are single-version by construction,
    // so a different hash under the same name is unambiguously a leftover.
    fs::write(sysroot.join("librustc_middle-old.rmeta"), b"leftover").unwrap();
    record_sysroot_install(sysroot, "librustc_middle-old.rmeta");

    let active = RustArtifact {
        crate_name: "rustc_middle",
        stem: "librustc_middle-new",
        kind: RustArtifactKind::Rmeta,
    };
    prune_superseded_sysroot_artifacts(sysroot, active);

    assert!(!sysroot.join("librustc_middle-old.rmeta").exists());
}

#[test]
fn public_sysroot_prune_removes_private_and_metadata_only_artifacts() {
    let temp = tempfile::TempDir::new().unwrap();
    let sysroot = temp.path();
    fs::write(sysroot.join("librustc_middle-111.rlib"), b"private rlib").unwrap();
    fs::write(sysroot.join("librustc_middle-111.rmeta"), b"private metadata").unwrap();
    fs::write(sysroot.join("libserde-222.rmeta"), b"metadata-only dep").unwrap();
    fs::write(sysroot.join("libserde_derive-333.so"), b"private proc macro").unwrap();
    fs::write(sysroot.join("libhashbrown-444.rlib"), b"public unstable dep").unwrap();
    fs::write(sysroot.join("libhashbrown-444.rmeta"), b"public unstable metadata").unwrap();
    fs::write(sysroot.join("libstd-555.so"), b"public std dylib").unwrap();
    fs::write(sysroot.join("libstd-555.rmeta"), b"public std metadata").unwrap();

    prune_public_sysroot_compiler_artifacts(sysroot);

    assert!(!sysroot.join("librustc_middle-111.rlib").exists());
    assert!(!sysroot.join("librustc_middle-111.rmeta").exists());
    assert!(!sysroot.join("libserde-222.rmeta").exists());
    assert!(!sysroot.join("libserde_derive-333.so").exists());
    assert!(sysroot.join("libhashbrown-444.rlib").exists());
    assert!(sysroot.join("libhashbrown-444.rmeta").exists());
    assert!(sysroot.join("libstd-555.so").exists());
    assert!(sysroot.join("libstd-555.rmeta").exists());
}

#[test]
fn local_compiler_runtime_artifacts_are_target_dylibs_or_debug_info() {
    assert!(is_local_compiler_runtime_artifact(
        Path::new("librustc_driver-1234.dylib"),
        DependencyType::Target,
    ));
    assert!(is_local_compiler_runtime_artifact(
        Path::new("rustc_driver.pdb"),
        DependencyType::Target,
    ));
    assert!(!is_local_compiler_runtime_artifact(
        Path::new("libproc_macro_helper-1234.dylib"),
        DependencyType::Host,
    ));
    assert!(!is_local_compiler_runtime_artifact(
        Path::new("librustc_driver-1234.rmeta"),
        DependencyType::Target,
    ));
}

#[test]
fn local_compiler_runtime_artifacts_skip_missing_entries() {
    let temp = tempfile::TempDir::new().unwrap();
    let existing_runtime = temp.path().join("librustc_driver-1234.dylib");
    let missing_runtime = temp.path().join("libunrelated-1234.dylib");
    fs::write(&existing_runtime, b"runtime").unwrap();

    assert_eq!(
        existing_local_compiler_runtime_artifacts(vec![
            (existing_runtime.clone(), DependencyType::Target),
            (missing_runtime, DependencyType::Target),
        ]),
        vec![existing_runtime]
    );
}

#[cfg(unix)]
#[test]
fn local_compiler_runtime_artifacts_accept_non_utf8_filenames() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let filename = OsStr::from_bytes(b"librustc_driver-\xFF.dylib");
    assert!(is_local_compiler_runtime_artifact(Path::new(filename), DependencyType::Target));
}

#[test]
fn assembled_compiler_driver_detection_excludes_codegen_plugins() {
    assert!(is_rustc_driver_runtime_artifact(Path::new("librustc_driver-1234.dylib")));
    assert!(is_rustc_driver_runtime_artifact(Path::new("rustc_driver-1234.dll")));
    assert!(!is_rustc_driver_runtime_artifact(Path::new("librustc_codegen_trust_cg-1234.dylib")));
    assert!(!is_rustc_driver_runtime_artifact(Path::new("librustc_driver-1234.rmeta")));
}

#[test]
fn compiler_runtime_restore_prunes_every_stale_driver_generation() {
    let temp = tempfile::TempDir::new().unwrap();
    let old = temp.path().join("librustc_driver-old.dylib");
    let older = temp.path().join("librustc_driver-older.dylib");
    let backend = temp.path().join("librustc_codegen_trust_cg-current.dylib");
    fs::write(&old, b"old driver").unwrap();
    fs::write(&older, b"older driver").unwrap();
    fs::write(&backend, b"current backend").unwrap();

    prune_rustc_driver_runtime_artifacts(temp.path()).unwrap();

    assert!(!old.exists());
    assert!(!older.exists());
    assert!(backend.exists(), "codegen backends are not driver generations");
}

/// SILENT-WRONG-BEHAVIOUR REGRESSION. `TRUST_STD_ENCODE_MIR` used to disable on
/// the exact string `0` and silently ignore every other value, so
/// `TRUST_STD_ENCODE_MIR=false` left `-Zalways-encode-mir` ON while reading like
/// an opt-out. That switch decides whether std is lowerable at all.
#[test]
fn trust_std_encode_mir_refuses_unrecognized_values() {
    // Default and the two accepted values are unchanged.
    assert_eq!(trust_std_encode_mir_enabled(None), Ok(true));
    assert_eq!(trust_std_encode_mir_enabled(Some(OsStr::new("1"))), Ok(true));
    assert_eq!(trust_std_encode_mir_enabled(Some(OsStr::new("0"))), Ok(false));

    // Everything a person might reach for meaning "off" is now a hard error
    // naming the accepted set, rather than a silent ON.
    for value in ["false", "no", "off", "n", "", "00", "1 ", "true", "yes"] {
        let error = trust_std_encode_mir_enabled(Some(OsStr::new(value)))
            .expect_err(&format!("{value:?} was silently accepted"));
        assert!(error.contains(TRUST_STD_ENCODE_MIR_ENV), "{error}");
        assert!(error.contains('`') && error.contains("`1`") && error.contains("`0`"), "{error}");
    }
}

/// Trust: the Trust rustflags of a `Mode::Std` unit, for every (build compiler stage,
/// `rust.trust-ir-metadata`, `TRUST_STD_ENCODE_MIR`) the helper can be handed.
///
/// The option-off rows are the regression half: they are exactly what a `Mode::Std`
/// unit received before the option existed, at every stage, so a default build's units
/// keep their flags and therefore their cargo unit ids.
#[test]
fn trust_std_rustflags_per_stage_option_and_encode_mir_setting() {
    const ENCODE: &str = "-Zalways-encode-mir";
    const LOWER: &str = "-Ztrust-ir-lower=on";
    const NO_FLIP: &str = "-Ztrust-ir-flip=no";
    const TEMPLATES: &str = "-Ztrust-ir-lower-templates";
    // The constants the helper is built from are these literal flags, in this order.
    assert_eq!(TRUST_STD_ENCODE_MIR_FLAG, ENCODE);
    assert_eq!(TRUST_STD_IR_METADATA_FLAGS, [LOWER, NO_FLIP, TEMPLATES]);

    let unset: Option<&OsStr> = None;
    let one = Some(OsStr::new("1"));
    let zero = Some(OsStr::new("0"));

    // Option off: only the encode-MIR gate decides, whatever the stage.
    for stage in [0, 1, 2, 3] {
        assert_eq!(trust_std_rustflags(stage, false, unset), Ok(vec![ENCODE]), "stage {stage}");
        assert_eq!(trust_std_rustflags(stage, false, one), Ok(vec![ENCODE]), "stage {stage}");
        assert_eq!(trust_std_rustflags(stage, false, zero), Ok(vec![]), "stage {stage}");
    }

    // Option on, stage 0: the seed compiles the unit, so no producer flag.
    assert_eq!(trust_std_rustflags(0, true, unset), Ok(vec![ENCODE]));
    assert_eq!(trust_std_rustflags(0, true, one), Ok(vec![ENCODE]));
    assert_eq!(trust_std_rustflags(0, true, zero), Ok(vec![]));

    // Option on, stage >= 1: the producer flags follow the encode-MIR flag, in a fixed
    // order, and do not depend on the encode-MIR opt-out.
    for stage in [1, 2, 3] {
        assert_eq!(
            trust_std_rustflags(stage, true, unset),
            Ok(vec![ENCODE, LOWER, NO_FLIP, TEMPLATES]),
            "stage {stage}"
        );
        assert_eq!(
            trust_std_rustflags(stage, true, one),
            Ok(vec![ENCODE, LOWER, NO_FLIP, TEMPLATES]),
            "stage {stage}"
        );
        assert_eq!(
            trust_std_rustflags(stage, true, zero),
            Ok(vec![LOWER, NO_FLIP, TEMPLATES]),
            "stage {stage}"
        );
    }

    // An unrecognized `TRUST_STD_ENCODE_MIR` is still refused, with the option on or
    // off: the option must not turn the refusal into a silent default.
    for stage in [0, 1] {
        for option in [false, true] {
            let error = trust_std_rustflags(stage, option, Some(OsStr::new("false")))
                .expect_err("an unrecognized value was accepted");
            assert!(error.contains(TRUST_STD_ENCODE_MIR_ENV), "{error}");
        }
    }
}

/// Trust: `rust.trust-ir-metadata` reaches a real `Mode::Std` cargo through the one
/// helper, and is off unless `bootstrap.toml` sets it.
///
/// It reads the command bootstrap would run, so it also shows that the producer flags
/// do not displace `-Ztrust-verify=off` (still there, once) and do not trip the
/// self-proof refusal, which would panic in `into_cmd`.
#[test]
fn trust_ir_metadata_option_reaches_a_std_cargo_through_the_helper() {
    use crate::utils::tests::TestCtx;

    let encode_mir = std::env::var_os(TRUST_STD_ENCODE_MIR_ENV);
    for (toml, option) in [
        ("", false),
        ("[rust]\ntrust-ir-metadata = false\n", false),
        ("[rust]\ntrust-ir-metadata = true\n", true),
    ] {
        for stage in [0, 1, 2] {
            let context = TestCtx::new();
            let config =
                context.config("build").stage(2).with_default_toml_config(toml).create_config();
            assert_eq!(config.trust_ir_metadata, option, "{toml:?}");
            let build = crate::core::session::Session::new(config);
            let builder = Builder::new(&build);
            let target = builder.config.host_target;
            let mut cargo = Cargo::new(
                &builder,
                Compiler::new(stage, target),
                Mode::Std,
                SourceType::InTree,
                target,
                Kind::Build,
            );
            let effective_stage = cargo.build_compiler_stage();
            apply_trust_std_rustflags(&builder, &mut cargo);
            let mut command = cargo.into_cmd();
            command.mark_as_executed(); // Inspect the command without running Cargo.
            let rustflags = ["CARGO_ENCODED_RUSTFLAGS", "RUSTFLAGS"]
                .into_iter()
                .find_map(|name| {
                    command
                        .get_envs()
                        .find(|(key, _)| *key == OsStr::new(name))
                        .and_then(|(_, value)| value)
                })
                .expect("a std cargo always has rustflags")
                .to_str()
                .unwrap()
                .to_string();
            let flags = rustflags.split(['\u{1f}', ' ']).collect::<Vec<_>>();
            let count = |flag: &str| flags.iter().filter(|seen| **seen == flag).count();

            let expected =
                trust_std_rustflags(effective_stage, option, encode_mir.as_deref()).unwrap();
            let producer = option && effective_stage >= 1;
            assert_eq!(
                expected.contains(&TRUST_STD_IR_METADATA_FLAGS[0]),
                producer,
                "{toml:?} stage {stage}"
            );
            for flag in [TRUST_STD_ENCODE_MIR_FLAG].into_iter().chain(TRUST_STD_IR_METADATA_FLAGS) {
                assert_eq!(
                    count(flag),
                    usize::from(expected.contains(&flag)),
                    "{toml:?} stage {stage}: {flag} in {flags:?}"
                );
            }
            // No other spelling of a producer option rides along.
            assert_eq!(
                flags
                    .iter()
                    .filter(|flag| flag.contains("trust-ir-lower") || flag.contains("trust-ir-flip"))
                    .count(),
                if producer { 3 } else { 0 },
                "{toml:?} stage {stage}: {flags:?}"
            );
            assert_eq!(
                count("-Ztrust-verify=off"),
                usize::from(effective_stage >= 1),
                "{toml:?} stage {stage}: the producer flags must not displace the off-switch \
                 in {flags:?}"
            );
        }
    }
}

/// Trust: every non-test bootstrap source under `src/bootstrap/src`, with its path
/// relative to that directory.
fn bootstrap_non_test_sources() -> Vec<(String, String)> {
    fn walk(dir: &Path, root: &Path, sources: &mut Vec<(String, String)>) {
        let mut entries =
            fs::read_dir(dir).unwrap().map(|entry| entry.unwrap().path()).collect::<Vec<_>>();
        entries.sort();
        for path in entries {
            let name = path.file_name().unwrap().to_str().unwrap();
            if path.is_dir() {
                if name != "tests" {
                    walk(&path, root, sources);
                }
            } else if name.ends_with(".rs") && name != "tests.rs" {
                let relative = path.strip_prefix(root).unwrap().to_str().unwrap().to_string();
                sources.push((relative, fs::read_to_string(&path).unwrap()));
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    walk(&root, &root, &mut sources);
    assert!(sources.len() > 50, "walked only {} sources; the walk broke", sources.len());
    sources
}

/// Trust: the two `Mode::Std` lanes that share one target directory take their Trust
/// rustflags from ONE helper, and nothing else spells the producer flags.
///
/// A source scan, because the property is about call sites: a flag that only one lane
/// adds forks `core` into two units with one `-Cmetadata` (the `StableCrateId`
/// collision `apply_trust_std_rustflags` documents), and the pure-function test above
/// cannot see who calls the function.
#[test]
fn both_std_lanes_take_their_trust_rustflags_from_the_one_helper() {
    const COMPILE: &str = "core/build_steps/compile.rs";
    const TEST: &str = "core/build_steps/test.rs";
    let sources = bootstrap_non_test_sources();

    // Calls of `name(` outside comments: not its `fn name(` definition, and not a
    // longer identifier that ends in `name`.
    let calls = |name: &str| {
        let call = format!("{name}(");
        sources
            .iter()
            .filter_map(|(path, text)| {
                let count = text
                    .lines()
                    .filter(|line| !line.trim_start().starts_with("//"))
                    .flat_map(|line| line.match_indices(&call).map(move |(at, _)| &line[..at]))
                    .filter(|before| {
                        !before.ends_with("fn ")
                            && !before.ends_with(|c: char| c.is_alphanumeric() || c == '_')
                    })
                    .count();
                (count != 0).then(|| (path.as_str(), count))
            })
            .collect::<Vec<_>>()
    };

    // The helper: called once from the build lane and once from the test lane.
    assert_eq!(calls("apply_trust_std_rustflags"), vec![(COMPILE, 1), (TEST, 1)]);
    // The flag list: computed only inside the helper.
    assert_eq!(calls("trust_std_rustflags"), vec![(COMPILE, 1)]);
    let (_, compile) = sources.iter().find(|(path, _)| path == COMPILE).unwrap();
    let helper = compile
        .split_once("pub fn apply_trust_std_rustflags(")
        .and_then(|(_, rest)| rest.split_once("\n}\n"))
        .map(|(body, _)| body)
        .expect("apply_trust_std_rustflags moved or was renamed");
    assert!(helper.contains("trust_std_rustflags("), "{helper}");
    assert!(helper.contains("cargo.build_compiler_stage()"), "{helper}");
    assert!(helper.contains("builder.config.trust_ir_metadata"), "{helper}");

    // Each lane's call follows that lane's `std_cargo` call: the same cargo, the same
    // branch.
    for path in [COMPILE, TEST] {
        let (_, text) = sources.iter().find(|(source, _)| source == path).unwrap();
        let (before, _) = text
            .split_once("apply_trust_std_rustflags(builder, &mut cargo);")
            .unwrap_or_else(|| panic!("{path} does not hand the helper its builder and cargo"));
        // The test lane names the helper through its module.
        let before = before.strip_suffix("compile::").unwrap_or(before);
        let (_, since_std_cargo) = before
            .rsplit_once("std_cargo(builder, target, &mut cargo, ")
            .unwrap_or_else(|| panic!("{path}: no `std_cargo` call precedes the helper"));
        let mut between = since_std_cargo.lines();
        assert!(between.next().is_some_and(|rest| rest.ends_with(");")), "{path}");
        for line in between {
            let line = line.trim();
            assert!(
                line.is_empty() || line.starts_with("//"),
                "{path}: code between `std_cargo` and the helper call: {line:?}"
            );
        }
    }

    // The replaced helper is gone, and neither the option nor either producer flag is
    // spelled anywhere a second lane could pick it up from.
    for (path, text) in &sources {
        assert!(!text.contains("apply_trust_std_encode_mir"), "{path} names the old helper");
        for needle in ["-Ztrust-ir-lower", "-Ztrust-ir-flip", "TRUST_STD_IR_METADATA_FLAGS"] {
            let expected = match (path.as_str(), needle) {
                // The lowering and template flags share the first prefix.
                (COMPILE, "-Ztrust-ir-lower") => 2,
                (COMPILE, "-Ztrust-ir-flip") => 1,
                // Its definition and its one use, in `trust_std_rustflags`.
                (COMPILE, "TRUST_STD_IR_METADATA_FLAGS") => 2,
                _ => 0,
            };
            let code = text
                .lines()
                .filter(|line| !line.trim_start().starts_with("//"))
                .map(|line| line.matches(needle).count())
                .sum::<usize>();
            assert_eq!(code, expected, "{path}: `{needle}` outside comments");
        }
        // One reader of the option, the helper. (The TOML module's one use is the
        // `download-rustc` compatibility check of the unresolved `Option`.)
        let reads = text.matches(".trust_ir_metadata").count();
        let expected = usize::from(path == COMPILE || path == "core/config/toml/rust.rs");
        assert_eq!(reads, expected, "{path}: reads of the option");
    }
}

/// Trust: the proc-macro exclusion in `restore_local_compiler_runtime_artifacts`
/// must test what a file IS, not what it is named.
///
/// The name-based half cannot work across compiler generations — the libdir it
/// copies from belongs to the build compiler, whose `-Cextra-filename` differs —
/// and a proc-macro dylib that slips into the compiler's public libdir is then
/// substituted by dyld for the one rustc asked for, because that libdir is on
/// `DYLD_LIBRARY_PATH` and dyld matches it by leaf name.
mod proc_macro_dylib_detection {
    use super::super::dylib_declares_proc_macro;

    fn sym(hex: &str) -> Vec<u8> {
        format!("....__rustc_proc_macro_decls_{hex}__....").into_bytes()
    }

    /// The common case: a StableCrateId with a non-zero top nibble.
    #[test]
    fn sixteen_digits_is_a_proc_macro() {
        assert!(dylib_declares_proc_macro(&sym("63c75b4b32cf02ec")));
    }

    /// `{:08x}` is a MINIMUM width, so a hash with a zero top nibble renders
    /// SHORTER. Requiring exactly 16 missed a random ~1-in-16 of all proc-macro
    /// dylibs — measured, 58 of 1,921 in this tree, `displaydoc` among them — which
    /// re-opened the very bug the predicate exists to close.
    #[test]
    fn short_hashes_are_proc_macros_too() {
        assert!(dylib_declares_proc_macro(&sym("d5931bb43dafb43")), "15 digits");
        assert!(dylib_declares_proc_macro(&sym("0fffffffffffff")), "14 digits");
        assert!(dylib_declares_proc_macro(&sym("abcdef12")), "8 digits, the minimum");
        assert!(dylib_declares_proc_macro(&sym("00000000")), "a zero hash still formats to 8");
    }

    /// THE DANGEROUS DIRECTION. `librustc_driver` carries this prefix once, from the
    /// format string that mints the symbol — and the `{:08x}` placeholder is not
    /// stored as text. The two `&str` pieces sit in the constant pool with exactly
    /// eight bytes of filler between them, then the literal `__`. This is the real
    /// payload, read out of a 690 MB `librustc_driver` at offset 395826980. A false
    /// positive here drops the driver from the assembled compiler's libdir and
    /// yields a compiler that cannot start.
    #[test]
    fn the_real_librustc_driver_constant_pool_payload_is_not_a_proc_macro() {
        let mut bytes = b"__rustc_proc_macro_decls_".to_vec();
        bytes.extend_from_slice(&[0xc3, 0x20, 0x00, 0x00, 0x69, 0x08, 0x00, 0x02]);
        bytes.extend_from_slice(b"__");
        assert!(!dylib_declares_proc_macro(&bytes));
    }

    /// The literal format string, in case it is ever stored as text.
    #[test]
    fn the_format_string_is_not_a_proc_macro() {
        assert!(!dylib_declares_proc_macro(b"....__rustc_proc_macro_decls_{:08x}__...."));
    }

    /// Below the generator's floor: `{:08x}` can never emit fewer than 8 digits, so
    /// a shorter run is something else that happens to share the prefix.
    #[test]
    fn fewer_than_eight_digits_is_not_a_proc_macro() {
        assert!(!dylib_declares_proc_macro(&sym("abc")));
        assert!(!dylib_declares_proc_macro(&sym("abcdef1")), "7 digits");
        assert!(!dylib_declares_proc_macro(b"__rustc_proc_macro_decls_"));
    }

    /// A u64 cannot exceed 16 hex digits, so a longer run is not this symbol. The
    /// bound is what keeps an unbounded scan off the driver's eight-byte gap.
    #[test]
    fn more_than_sixteen_digits_is_not_a_proc_macro() {
        assert!(!dylib_declares_proc_macro(&sym("0123456789abcdef0")));
    }

    /// `{:08x}` never emits uppercase, so accepting `A-F` would widen the
    /// false-positive surface (UUIDs, hex dumps) for no gain.
    #[test]
    fn uppercase_hex_is_not_a_proc_macro() {
        assert!(!dylib_declares_proc_macro(&sym("63C75B4B32CF02EC")));
    }

    #[test]
    fn an_ordinary_dylib_is_not_a_proc_macro() {
        assert!(!dylib_declares_proc_macro(b"just some bytes, libstd-1234.dylib"));
    }

    // Trust: an invalid match may overlap the next prefix by its final underscore.
    // Non-overlapping substring iteration would miss the valid second declaration.
    #[test]
    fn overlapping_prefixes_keep_the_later_valid_declaration() {
        let prefix = b"__rustc_proc_macro_decls_";
        let mut bytes = prefix.to_vec();
        bytes.extend_from_slice(&prefix[1..]);
        bytes.extend_from_slice(b"abcdef12__");
        assert!(dylib_declares_proc_macro(&bytes));
    }

    // Trust: accept the generator's entire width range, including a declaration
    // ending exactly at EOF; require both terminator bytes at every width.
    #[test]
    fn generated_widths_and_exact_buffer_boundaries() {
        let prefix = b"__rustc_proc_macro_decls_";
        let hex = b"0123456789abcdef";
        for width in 0..=hex.len() {
            let mut bytes = prefix.to_vec();
            bytes.extend_from_slice(&hex[..width]);
            assert!(!dylib_declares_proc_macro(&bytes), "unterminated {width} digits");
            bytes.push(b'_');
            assert!(!dylib_declares_proc_macro(&bytes), "one terminator, {width} digits");
            bytes.push(b'_');
            assert_eq!(dylib_declares_proc_macro(&bytes), width >= 8, "{width} digits");
        }
        for end in 0..prefix.len() {
            assert!(!dylib_declares_proc_macro(&prefix[..end]));
        }
        for leading in [b"r".as_slice(), b"_r", b"rr"] {
            assert!(!dylib_declares_proc_macro(leading));
        }
    }

    // Trust: a malformed earlier candidate must not terminate the whole search.
    #[test]
    fn rejected_candidates_do_not_hide_later_declarations() {
        let mut bytes = b"rr".to_vec();
        bytes.extend_from_slice(&sym("0123456789abcdef0"));
        bytes.extend_from_slice(&sym("01234567A"));
        bytes.extend_from_slice(b"\x00\xff");
        bytes.extend_from_slice(&sym("0123456789abcdef"));
        assert!(dylib_declares_proc_macro(&bytes));
    }

    // Trust: retain the actual former scan as a differential/performance control,
    // not a timing assertion whose result depends on load from other builders.
    fn previous_window_scan(bytes: &[u8]) -> bool {
        const NEEDLE: &[u8] = b"__rustc_proc_macro_decls_";
        bytes.windows(NEEDLE.len()).enumerate().any(|(i, window)| {
            if window != NEEDLE {
                return false;
            }
            let rest = &bytes[i + NEEDLE.len()..];
            let digits = rest
                .iter()
                .take(17)
                .take_while(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
                .count();
            (8..=16).contains(&digits) && rest[digits..].starts_with(b"__")
        })
    }

    fn compare_large_buffer(label: &str, bytes: &[u8], expected: bool) {
        let start = std::time::Instant::now();
        let previous = previous_window_scan(std::hint::black_box(bytes));
        let previous_time = start.elapsed();
        let start = std::time::Instant::now();
        let current = dylib_declares_proc_macro(std::hint::black_box(bytes));
        let current_time = start.elapsed();
        assert_eq!(previous, expected, "previous scan: {label}");
        assert_eq!(current, expected, "candidate scan: {label}");
        eprintln!(
            "proc-macro scan {label}: {} bytes, previous={previous_time:?}, current={current_time:?}",
            bytes.len()
        );
    }

    #[test]
    fn large_binary_buffers_keep_negative_and_end_of_buffer_verdicts() {
        let mut bytes = vec![0; 8 * 1024 * 1024];
        // Sparse binary separators and one complete but invalid declaration.
        for offset in (0..bytes.len()).step_by(4096) {
            bytes[offset] = b'_';
        }
        let invalid = sym("0123456789abcdef0");
        bytes[4096..4096 + invalid.len()].copy_from_slice(&invalid);
        compare_large_buffer("sparse negative", &bytes, false);

        bytes.extend_from_slice(b"__rustc_proc_macro_decls_abcdef12__");
        compare_large_buffer("declaration at EOF", &bytes, true);

        // Keep the declaration starting at the final two underscores of a dense run.
        let mut dense = vec![b'_'; 256 * 1024];
        dense.extend_from_slice(b"rustc_proc_macro_decls_abcdef12__");
        compare_large_buffer("dense overlapping prefix", &dense, true);
    }
}

/// Trust (E0464, 2026-09-14): the stage0-sysroot rustc-private filter asks what a file
/// IS, by crate name, not what its path or file name looks like.
mod rustc_private_artifact_detection {
    use std::path::Path;

    use super::super::is_rustc_private_artifact;

    #[test]
    fn rustc_private_crates_are_matched_in_every_spelling() {
        // unix rlib/rmeta/dylib, and the Windows dylib, which carries NO `lib` prefix.
        assert!(is_rustc_private_artifact(Path::new("librustc_abi-1f34233.rmeta")));
        assert!(is_rustc_private_artifact(Path::new("librustc_driver-903b2fc.dylib")));
        assert!(is_rustc_private_artifact(Path::new("rustc_driver-903b2fc.dll")));
        assert!(is_rustc_private_artifact(Path::new("librustc_middle-abc123.rlib")));
    }

    /// The std-side shims begin with `rustc_` but belong to the standard library half a
    /// rustc-private tool genuinely needs. Dropping them would break the very tools this
    /// filter exists to unblock.
    #[test]
    fn std_workspace_shims_are_not_rustc_private() {
        assert!(!is_rustc_private_artifact(Path::new("librustc_std_workspace_core-fa68890.rlib")));
        assert!(!is_rustc_private_artifact(Path::new("librustc_std_workspace_alloc-e902d9f.rlib")));
        assert!(!is_rustc_private_artifact(Path::new("librustc_std_workspace_std-1234567.rlib")));
    }

    /// The standard library depends on several `rustc_*` crates. Dropping one does not
    /// fail tidily: shipping this filter with only the `rustc_std_workspace_` exception
    /// fixed the E0464 (0 occurrences) and introduced 2571 `E0463: can't find crate for
    /// 'rustc_demangle' which 'std' depends on`. Re-derive the list with
    /// `grep -hoE '^rustc[-_][a-z_-]+' library/*/Cargo.toml | sort -u`.
    #[test]
    fn std_side_rustc_crates_are_kept() {
        assert!(!is_rustc_private_artifact(Path::new("librustc_demangle-abc123.rlib")));
        // `proc_macro` depends on this one. The first probe missed it because the build
        // stopped at `rustc_demangle` and never reached `proc-macro2`.
        assert!(!is_rustc_private_artifact(Path::new("librustc_literal_escaper-abc.rlib")));
    }

    /// The manifest derivation is a SUPERSET of what the sysroot must carry, and the
    /// difference is not cosmetic. `rustc_apfloat` is declared by
    /// `library/compiler-builtins` AND linked by `src/tools/miri` as rustc-private;
    /// exempting it left miri seeing two generations and reproduced the exact E0464 this
    /// filter removes. Measured: dropping all three manifest-named crates produced
    /// missing-crate errors for `rustc_demangle` only.
    #[test]
    fn dual_use_rustc_crates_are_still_filtered() {
        assert!(is_rustc_private_artifact(Path::new("librustc_apfloat-abc123.rlib")));
    }

    #[test]
    fn ordinary_std_artifacts_are_kept() {
        assert!(!is_rustc_private_artifact(Path::new("libstd-65d90f8.rlib")));
        assert!(!is_rustc_private_artifact(Path::new("libcore-23eb100.rmeta")));
        assert!(!is_rustc_private_artifact(Path::new("liballoc-df0bdd0.rlib")));
        assert!(!is_rustc_private_artifact(Path::new("libproc_macro-abc.rlib")));
    }

    /// A DIRECTORY named after a rustc crate must not be dropped by a path-substring
    /// test — the filter is applied to every entry of the tree walk, directories
    /// included, and dropping one would silently truncate the copy.
    #[test]
    fn a_directory_named_like_a_rustc_crate_is_not_an_artifact() {
        assert!(!is_rustc_private_artifact(Path::new("rustc_foo")));
        assert!(!is_rustc_private_artifact(Path::new("src/rust")));
    }
}

// Trust (2026-10-01): trust-cg-verify, linked into the driver, admits only the
// `ay` whose bytes its build script recorded, and a compiler that hosts it names
// its OWN sysroot's `bin/ay`. The compiler crates compiled with the stage-N
// compiler are assembled into stage N+1's sysroot, so that is the sysroot every
// compiler-crate cargo invocation must name — check and build alike, so they
// share one build-script record. Naming the build compiler's (stage N) made a
// stage2 compiler refuse its own stage2/bin/ay and admit only stage1's.
#[test]
fn compiler_crates_record_the_ay_of_the_sysroot_they_are_assembled_in() {
    for (kind, stage) in [("check", 1), ("build", 1), ("build", 2)] {
        let context = crate::utils::tests::TestCtx::new();
        let build =
            crate::core::session::Session::new(context.config(kind).stage(stage).create_config());
        let builder = Builder::new(&build);
        let target = builder.config.host_target;
        let build_compiler = Compiler::new(stage - 1, target);
        let mut cargo = Cargo::new(
            &builder,
            build_compiler,
            Mode::Rustc,
            SourceType::InTree,
            target,
            builder.kind,
        );
        // `rustc_cargo` calls exactly this; the rest of it needs an LLVM.
        name_ay_record_host_sysroot(&builder, &mut cargo, target, &build_compiler);
        let mut command = cargo.into_cmd();
        command.mark_as_executed(); // Inspect the command without running Cargo.
        let named = command
            .get_envs()
            .find(|(key, _)| *key == AY_RECORD_HOST_SYSROOT_ENV)
            .and_then(|(_, value)| value)
            .map(PathBuf::from);
        let assembled = builder.out.join(target).join(format!("stage{stage}"));
        assert_eq!(
            named.as_ref(),
            Some(&assembled),
            "`{kind}` with the stage{} compiler must name the stage{stage} sysroot",
            stage - 1,
        );
        assert_eq!(local_sysroot_dir(&builder, Compiler::new(stage, target)), assembled);
    }
}

// Trust (2026-10-14, D8 of the first seed mint): a rustc-private tool's private sysroot, and with
// it the `-L` path in the tool's RUSTFLAGS, cargo's metadata hash and the tool's bytes, is named by
// the runtime the tool loads. `x build`'s rustc-dev top-up adds the compiler's proc-macro dylibs to
// the target libdir and `x dist`'s assembly prunes them; with that directory in the identity, one
// tool had two private sysroots, and the dist archives shipped other bytes than the local stage2
// sysroot held (the trustc archive's trustdoc `rustdoc_tool_binary-d5fcedeae07813d1`, stage2's
// `-b5f5cd69dceb9db7`; the two sysroots' 920 files were identical, only their names differed).
#[test]
fn a_tool_runtime_identity_ignores_the_rustc_dev_dylibs_dist_prunes() {
    let ctx = crate::utils::tests::TestCtx::new();
    let build = crate::core::session::Session::new(ctx.config("build").stage(2).create_config());
    let builder = Builder::new(&build);
    let host = builder.config.host_target;
    let compiler = Compiler::new(2, host);
    let dylib = |stem: &str| format!("lib{stem}.{}", std::env::consts::DLL_EXTENSION);
    let libdir = builder.rustc_libdir(compiler);
    let target_libdir = builder.sysroot_target_libdir(compiler, host);
    for dir in [&libdir, &target_libdir] {
        fs::create_dir_all(dir).unwrap();
        fs::write(dir.join(dylib("rustc_driver-0123")), b"driver").unwrap();
        fs::write(dir.join(dylib("std-4567")), b"std").unwrap();
    }
    // `x build` tops the target libdir up with rustc-dev, proc-macro dylibs included ...
    let proc_macro = target_libdir.join(dylib("serde_derive-89ab"));
    fs::write(&proc_macro, b"proc macro").unwrap();
    let local_build = rustc_private_tool_runtime_identity(&builder, compiler);
    // ... and `x dist` assembles the same compiler with them pruned.
    fs::remove_file(&proc_macro).unwrap();
    let dist = rustc_private_tool_runtime_identity(&builder, compiler);
    assert_eq!(
        local_build, dist,
        "one compiler runtime must name one private sysroot under `x build` and `x dist`"
    );
    // A runtime replaced in place still names a fresh one.
    fs::write(libdir.join(dylib("rustc_driver-0123")), b"rebuilt driver").unwrap();
    assert_ne!(rustc_private_tool_runtime_identity(&builder, compiler), dist);
}

// Trust: exercise the actual Builder-selected host/runtime paths. Target std
// outputs must not feed back into their own compiler freshness identity.
#[test]
fn std_cache_identity_uses_host_runtime_and_excludes_target_outputs() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(2).create_config());
    let builder = Builder::new(&build);
    let host = builder.config.host_target;
    let compiler = Compiler::new(2, host);
    let launcher = builder.rustc(compiler);
    fs::create_dir_all(launcher.parent().unwrap()).unwrap();
    fs::write(&launcher, b"launcher").unwrap();
    let runtime_dir = builder.rustc_libdir(compiler);
    let target_dir = builder.sysroot_target_libdir(compiler, host);
    fs::create_dir_all(&runtime_dir).unwrap();
    fs::create_dir_all(&target_dir).unwrap();
    let library = format!("librustc_driver-test.{}", std::env::consts::DLL_EXTENSION);
    let runtime = runtime_dir.join(&library);
    fs::write(&runtime, b"host driver").unwrap();
    let first = std_compiler_runtime_identity(&builder, compiler);
    fs::write(target_dir.join(&library), b"new target std output").unwrap();
    assert_eq!(first, std_compiler_runtime_identity(&builder, compiler));
    fs::write(&runtime, b"new host driver").unwrap();
    assert_ne!(first, std_compiler_runtime_identity(&builder, compiler));
    fs::remove_file(runtime).unwrap();
    assert_eq!(
        std_compiler_runtime_identity(&builder, compiler),
        std_compiler_runtime_files_identity(launcher, Vec::new()),
        "a static compiler needs no host dylib, and must still exclude target outputs",
    );
}

// Trust: selecting an AST/parser test does not require an unrelated native LLVM
// build. Driver/back-end and whole-compiler routes retain that prerequisite.
#[test]
fn llvm_prerequisite_follows_the_selected_compiler_dependency_graph() {
    let context = crate::utils::tests::TestCtx::new();
    let build = crate::core::session::Session::new(context.config("test").create_config());
    let builder = Builder::new(&build);
    for selected in ["rustc_expand", "rustc_parse", "rustc_ast"] {
        assert!(!compiler_crates_need_llvm(&builder, &[selected.to_owned()]));
    }
    for selected in ["rustc_llvm", "rustc_codegen_llvm", "rustc_driver_impl", "rustc-main"] {
        assert!(compiler_crates_need_llvm(&builder, &[selected.to_owned()]));
    }
    assert!(compiler_crates_need_llvm(&builder, &[]));
    assert!(compiler_crates_need_llvm(
        &builder,
        &["rustc_expand".to_owned(), "rustc_llvm".to_owned()],
    ));
}

#[test]
#[should_panic(expected = "metadata missing for unknown-compiler-crate")]
fn unknown_compiler_metadata_cannot_waive_the_llvm_prerequisite() {
    let context = crate::utils::tests::TestCtx::new();
    let build = crate::core::session::Session::new(context.config("test").create_config());
    let builder = Builder::new(&build);
    compiler_crates_need_llvm(&builder, &["unknown-compiler-crate".to_owned()]);
}

#[test]
fn target_only_llvm_prerequisite_survives_disabled_host_backends() {
    let context = crate::utils::tests::TestCtx::new();
    let mut config = context.config("test").create_config();
    config.rust_codegen_backends = vec![CodegenBackendKind::TrustCg];
    for host in &config.hosts {
        config.target_config.entry(*host).or_default().codegen_backends =
            Some(vec![CodegenBackendKind::TrustCg]);
    }
    let target = TargetSelection::from_user("wasm32-unknown-unknown");
    config.target_config.entry(target).or_default().codegen_backends =
        Some(vec![CodegenBackendKind::Llvm]);
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    assert!(builder.config.llvm_enabled(target));
    assert!(builder.config.hosts.iter().all(|host| !builder.config.llvm_enabled(*host)));
    assert!(compiler_crates_need_llvm(&builder, &["rustc_driver_impl".to_owned()]));
    assert!(!compiler_crates_need_llvm(&builder, &["rustc_expand".to_owned()]));
}

// Trust: these exercise actual Builder step ordering in dry-run mode, not
// provider readiness, a Ninja probe, or compilation of the selected tools.
#[test]
fn assembly_selects_lld_before_recursive_compiler_artifacts() {
    for (stage, cross_host) in [(1, false), (2, false), (1, true)] {
        let ctx = crate::utils::tests::TestCtx::new();
        let config = ctx.config("build").stage(stage).args(&["--set", "rust.lld=true"]);
        let config = if cross_host { config.hosts(&["i686-unknown-haiku"]) } else { config };
        let session = crate::core::session::Session::new(config.create_config());
        let builder = Builder::new(&session);
        let target = if cross_host {
            TargetSelection::from_user("i686-unknown-haiku")
        } else {
            builder.host_target
        };
        builder.ensure(Assemble { target_compiler: Compiler::new(stage, target) });
        let steps = builder.step_cache().executed_steps();

        let lld = completed_step_positions(&steps, &llvm::Lld { target });
        assert_eq!(lld.len(), 1, "the later wrapper must reuse the selected provider");
        assert!(builder.step_cache().get(&llvm::Lld { target }).is_some());
        for producer_stage in 0..stage {
            let compiler = Compiler::new(producer_stage, builder.host_target);
            let key = Rustc::new(compiler, target);
            let rustc = completed_step_positions(&steps, &key);
            assert!(!rustc.is_empty(), "control must include compiler artifact work");
            assert!(rustc.iter().all(|index| lld[0] < *index));
            let metadata = Step::metadata(&key).unwrap();
            assert!(rustc.iter().all(|index| steps[*index].metadata.as_ref() == Some(&metadata)));
        }
        if stage == 2 {
            let key = Assemble { target_compiler: Compiler::new(1, target) };
            assert!(builder.step_cache().get(&key).is_some());
            let previous = completed_step_positions(&steps, &key);
            assert_eq!(previous.len(), 1, "control must recursively assemble stage1");
            assert!(lld[0] < previous[0], "LLD precedes recursive compiler assembly");
        }
    }
}

#[test]
fn assembly_fast_returns_and_disabled_lld_do_not_select_a_provider() {
    for (stage, lld_enabled, downloaded) in [(0, true, false), (2, false, false), (2, true, true)] {
        let ctx = crate::utils::tests::TestCtx::new();
        let mut config = ctx
            .config("build")
            // Trust: the valid invocation can request the stage0 Assemble key.
            .stage(2)
            .args(&["--set", &format!("rust.lld={lld_enabled}")])
            .create_config();
        if downloaded {
            // Select the existing CI fast path without downloading in this dry run.
            config.download_rustc_commit = Some("fixture-ci-compiler".into());
        }
        let session = crate::core::session::Session::new(config);
        let builder = Builder::new(&session);
        assert_eq!(builder.download_rustc(), downloaded);
        let target = builder.host_target;
        let selected = Compiler::new(stage, target);
        assert_eq!(builder.ensure(Assemble { target_compiler: selected }), selected);
        assert!(builder.step_cache().get(&llvm::Lld { target }).is_none());
        if stage == 0 || downloaded {
            assert!(!builder.step_cache().contains::<Rustc>());
        } else {
            assert!(
                builder.step_cache().contains::<Rustc>(),
                "disabled LLD still builds its compiler"
            );
        }
    }
}

fn completed_step_positions<S: Step>(
    steps: &[crate::utils::cache::ExecutedStep],
    expected: &S,
) -> Vec<usize> {
    steps
        .iter()
        .enumerate()
        .filter_map(|(index, record)| {
            (record.step.downcast_ref::<S>() == Some(expected)).then_some(index)
        })
        .collect()
}

// Trust: selected Linux graph keys/order only, with no physical Linux or tool probe.
#[test]
fn assembly_selects_tpde_before_recursive_compiler_artifacts() {
    for (stage, cross_host) in [(1, false), (2, false), (1, true)] {
        let ctx = crate::utils::tests::TestCtx::new();
        let target_name =
            if cross_host { "aarch64-unknown-linux-gnu" } else { "x86_64-unknown-linux-gnu" };
        let config = ctx
            .config("build")
            .stage(stage)
            .hosts(&[target_name])
            .args(&[
                "--build",
                "x86_64-unknown-linux-gnu",
                "--set",
                "llvm.tpde=true",
                "--set",
                "llvm.link-shared=true",
                "--set",
                "rust.lld=false",
            ])
            .create_config();
        let session = crate::core::session::Session::new(config);
        let builder = Builder::new(&session);
        let target = TargetSelection::from_user(target_name);
        builder.ensure(Assemble { target_compiler: Compiler::new(stage, target) });
        let steps = builder.step_cache().executed_steps();
        let tpde = completed_step_positions(&steps, &llvm::Tpde { target });
        assert_eq!(tpde.len(), 1, "late installation must reuse the selected TPDE provider");
        let producer = Compiler::new(stage - 1, builder.host_target);
        let rustc = completed_step_positions(&steps, &Rustc::new(producer, target));
        assert_eq!(rustc.len(), 1, "control must include actual compiler artifact work");
        assert!(tpde[0] < rustc[0]);
        if stage == 2 {
            let previous =
                completed_step_positions(&steps, &Assemble { target_compiler: producer });
            assert_eq!(previous.len(), 1);
            assert!(tpde[0] < previous[0]);
        }
    }
}

#[test]
fn assembly_tpde_fast_returns_disabled_and_non_linux_do_not_select_a_provider() {
    for (stage, enabled, linux, downloaded) in [
        (0, true, true, false),
        (1, false, true, false),
        (1, true, false, false),
        (2, true, true, true),
    ] {
        let ctx = crate::utils::tests::TestCtx::new();
        let target_name = if linux { "x86_64-unknown-linux-gnu" } else { "i686-unknown-haiku" };
        let mut config = ctx
            .config("build")
            .stage(2)
            .hosts(&[target_name])
            .args(&[
                "--build",
                "x86_64-unknown-linux-gnu",
                "--set",
                &format!("llvm.tpde={enabled}"),
                "--set",
                "llvm.link-shared=true",
                "--set",
                "rust.lld=false",
            ])
            .create_config();
        if downloaded {
            config.download_rustc_commit = Some("fixture-ci-compiler".into());
        }
        let session = crate::core::session::Session::new(config);
        let builder = Builder::new(&session);
        assert_eq!(builder.download_rustc(), downloaded);
        let target = TargetSelection::from_user(target_name);
        builder.ensure(Assemble { target_compiler: Compiler::new(stage, target) });
        if stage == 0 || downloaded || !enabled {
            assert!(!builder.step_cache().contains::<llvm::Tpde>());
        }
        // Trust: a non-Linux wrapper can need a separate native Linux compiler.
        assert!(builder.step_cache().get(&llvm::Tpde { target }).is_none());
        if stage == 0 || downloaded {
            assert!(!builder.step_cache().contains::<Rustc>());
        } else {
            assert!(builder.step_cache().contains::<Rustc>());
        }
    }
}
