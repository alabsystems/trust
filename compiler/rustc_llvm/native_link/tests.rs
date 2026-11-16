use super::*;

fn file(root: &Path, name: &str) -> PathBuf {
    let path = root.join(name);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, b"fixture").unwrap();
    path
}

#[test]
fn static_search_exposes_only_exact_archives_and_never_reuses_stale_siblings() {
    let root = tempfile::tempdir().unwrap();
    let provider = root.path().join("provider");
    let output = root.path().join("output");
    std::fs::create_dir(&output).unwrap();
    let libraries = selected_libraries(
        [file(&provider, "libLLVMCore.a"), file(&provider, "libPolly.a")],
        "aarch64-apple-darwin",
        false,
    )
    .unwrap();
    for name in ["libc++.dylib", "libc++abi.a", "libunwind.dylib"] {
        file(&provider, name);
    }
    let first = isolate_static_search(&libraries, &output).unwrap();
    assert!(first.replaces(&provider));
    assert!(first.replaces(&provider.join(".")));
    assert!(!first.replaces(&output));
    assert!(!first.replaces(&root.path().join("absent")));
    let actual: BTreeSet<_> = std::fs::read_dir(&first.directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect();
    assert_eq!(actual, ["libLLVMCore.a", "libPolly.a"].map(Into::into).into_iter().collect());
    for library in libraries.values() {
        assert_eq!(
            std::fs::read(&library.path).unwrap(),
            std::fs::read(first.directory.join(library.path.file_name().unwrap())).unwrap()
        );
    }
    file(&first.directory, "libc++.dylib");
    let second = isolate_static_search(&libraries, &output).unwrap();
    assert_ne!(first.directory, second.directory);
    assert!(!second.directory.join("libc++.dylib").exists());
}

#[test]
fn static_search_refuses_empty_dynamic_missing_and_colliding_inputs() {
    let root = tempfile::tempdir().unwrap();
    assert!(isolate_static_search(&BTreeMap::new(), root.path()).is_err());
    let a = file(root.path(), "a/libLLVM.a");
    let mut libraries = selected_libraries([a.clone()], "aarch64-apple-darwin", false).unwrap();
    libraries.get_mut("LLVM").unwrap().kind = LinkKind::Dynamic;
    assert!(isolate_static_search(&libraries, root.path()).is_err());
    libraries.get_mut("LLVM").unwrap().kind = LinkKind::Static;
    let b = file(root.path(), "b/libLLVM.a");
    libraries.insert(
        "Other".to_owned(),
        NativeLibrary { name: "Other".to_owned(), path: b.clone(), kind: LinkKind::Static },
    );
    assert!(isolate_static_search(&libraries, root.path()).is_err());
    assert_eq!(std::fs::read(&a).unwrap(), b"fixture");
    assert_eq!(std::fs::read(&b).unwrap(), b"fixture");
    libraries.remove("Other");
    std::fs::remove_file(&a).unwrap();
    assert!(isolate_static_search(&libraries, root.path()).is_err());
    std::fs::create_dir(&a).unwrap();
    assert!(isolate_static_search(&libraries, root.path()).is_err());
}

#[cfg(unix)]
#[test]
fn static_search_replaces_both_declared_file_alias_and_physical_archive_directories() {
    let root = tempfile::tempdir().unwrap();
    let source = file(root.path(), "physical/libLLVMCore.a");
    let declared = root.path().join("declared");
    std::fs::create_dir(&declared).unwrap();
    let alias = declared.join("libLLVMCore.a");
    std::os::unix::fs::symlink(&source, &alias).unwrap();
    let libraries = selected_libraries([alias], "aarch64-apple-darwin", false).unwrap();
    let isolated = isolate_static_search(&libraries, root.path()).unwrap();
    assert!(isolated.replaces(&declared));
    assert!(isolated.replaces(source.parent().unwrap()));
    assert_eq!(std::fs::read(isolated.directory.join("libLLVMCore.a")).unwrap(), b"fixture");
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "requires explicit TRUST_TEST_LLVM_CONFIG for installed LLVM/LLD and private C++ runtime"]
fn static_search_executes_cpp_without_private_runtime_shadowing() {
    use std::os::unix::fs::symlink;
    let config = std::env::var_os("TRUST_TEST_LLVM_CONFIG").expect("explicit LLVM input required");
    let query = |arg: &str| {
        let output = Command::new(&config).arg(arg).output().unwrap();
        assert!(output.status.success());
        PathBuf::from(String::from_utf8(output.stdout).unwrap().trim())
    };
    let bin = query("--bindir");
    let lib = query("--libdir");
    let sdk = Command::new("/usr/bin/xcrun").arg("--show-sdk-path").output().unwrap();
    assert!(sdk.status.success());
    let sdk = String::from_utf8(sdk.stdout).unwrap();
    let root = tempfile::tempdir().unwrap();
    let provider = root.path().join("provider");
    let output = root.path().join("output");
    std::fs::create_dir(&provider).unwrap();
    std::fs::create_dir(&output).unwrap();
    let source = root.path().join("main.cpp");
    std::fs::write(&source, "int main(int argc, char**) { int* p = new int(argc); int v = *p; delete p; return v - argc; }\n").unwrap();
    let bitcode = root.path().join("main.bc");
    let compile = Command::new(bin.join("clang++"))
        .args(["-target", "arm64-apple-macos11", "-isysroot", sdk.trim(), "-flto", "-O0", "-c"])
        .arg(&source)
        .arg("-o")
        .arg(&bitcode)
        .output()
        .unwrap();
    assert!(compile.status.success(), "{}", String::from_utf8_lossy(&compile.stderr));
    let archive = provider.join("libLLVMProbe.a");
    assert!(
        Command::new(bin.join("llvm-ar"))
            .arg("rcs")
            .arg(&archive)
            .arg(&bitcode)
            .status()
            .unwrap()
            .success()
    );
    for name in ["libc++.dylib", "libc++abi.dylib", "libunwind.dylib"] {
        assert!(lib.join(name).is_file(), "fixture requires private runtime {name}");
        symlink(lib.join(name), provider.join(name)).unwrap();
    }
    let libraries = selected_libraries([archive], "aarch64-apple-darwin", false).unwrap();
    let isolated = isolate_static_search(&libraries, &output).unwrap();
    for (directory, succeeds) in [(&provider, false), (&isolated.directory, true)] {
        let executable = root.path().join(if succeeds { "isolated" } else { "shadowed" });
        let link = Command::new(bin.join("lld"))
            .args([
                "-flavor",
                "darwin",
                "-arch",
                "arm64",
                "-platform_version",
                "macos",
                "11.0",
                "11.0",
                "-syslibroot",
                sdk.trim(),
                "-dead_strip",
                "-L",
            ])
            .arg(directory)
            .args(["-lLLVMProbe", "-lc++", "-lSystem", "-o"])
            .arg(&executable)
            .output()
            .unwrap();
        assert_eq!(link.status.success(), succeeds, "{}", String::from_utf8_lossy(&link.stderr));
        if succeeds {
            assert!(Command::new(&executable).status().unwrap().success());
            let loads = Command::new("/usr/bin/otool").arg("-L").arg(&executable).output().unwrap();
            assert!(loads.status.success());
            let loads = String::from_utf8(loads.stdout).unwrap();
            assert!(loads.contains("/usr/lib/libc++.1.dylib"), "{loads}");
            assert!(!loads.contains("@rpath/libc++"), "{loads}");
        } else {
            assert!(String::from_utf8_lossy(&link.stderr).contains("undefined symbol"));
        }
    }
}

#[test]
fn bare_polly_names_are_classified_by_the_selected_archives() {
    let root = tempfile::tempdir().unwrap();
    let libraries = selected_libraries(
        [file(root.path(), "libPolly.a"), file(root.path(), "libPollyISL.a")],
        "aarch64-apple-darwin",
        false,
    )
    .unwrap();
    assert_eq!(libraries["Polly"].kind, LinkKind::Static);
    assert_eq!(libraries["PollyISL"].kind, LinkKind::Static);
    assert_eq!(libraries["Polly"].kind.rustc_name(), "static");
    let polly =
        selected_library("-lPolly", &libraries, "aarch64-apple-darwin", false).unwrap().unwrap();
    assert_eq!(polly.kind, LinkKind::Static);
    assert!(selected_library("-lUnknown", &libraries, "aarch64-apple-darwin", false).is_err());
    assert!(selected_library("-lz3", &libraries, "aarch64-apple-darwin", false).unwrap().is_none());
    assert!(
        selected_library("-lLLVMLineEditor", &libraries, "aarch64-apple-darwin", false)
            .unwrap()
            .is_none()
    );
    let wrong_path = file(root.path(), "other/libPolly.a");
    assert!(
        selected_library(wrong_path.to_str().unwrap(), &libraries, "aarch64-apple-darwin", false)
            .is_err()
    );
}

#[test]
fn windows_import_libraries_follow_the_selected_mode() {
    let root = tempfile::tempdir().unwrap();
    let msvc = file(root.path(), "LLVM.lib");
    assert_eq!(
        library_file(&msvc, "x86_64-pc-windows-msvc", true).unwrap().kind,
        LinkKind::Dynamic
    );
    assert_eq!(
        library_file(&msvc, "x86_64-pc-windows-msvc", false).unwrap().kind,
        LinkKind::Static
    );
    let gnu = file(root.path(), "libLLVM.dll.a");
    assert_eq!(library_file(&gnu, "x86_64-pc-windows-gnu", true).unwrap().kind, LinkKind::Dynamic);
    assert!(library_file(&gnu, "x86_64-pc-windows-gnu", false).is_err());
}

#[test]
fn crossed_builds_never_consume_a_host_file_inventory() {
    let root = tempfile::tempdir().unwrap();
    let host_archive = file(root.path(), "host/libPolly.a");
    assert!(!root.path().join("target/libPolly.a").exists());
    let crossed = native_inventory(
        || panic!("a host --libfiles query must never run for the target"),
        "aarch64-apple-darwin",
        false,
        true,
    )
    .unwrap();
    assert!(crossed.is_none());
    let shared = native_inventory(
        || panic!("shared LLVM retains its existing platform import policy"),
        "x86_64-pc-windows-msvc",
        true,
        false,
    )
    .unwrap();
    assert!(shared.is_none());
    let native = native_inventory(|| vec![host_archive], "aarch64-apple-darwin", false, false)
        .unwrap()
        .unwrap();
    assert_eq!(native["Polly"].kind, LinkKind::Static);
}

#[test]
fn versioned_shared_files_keep_their_linker_names() {
    let root = tempfile::tempdir().unwrap();
    let elf = file(root.path(), "libLLVM.so.23.1");
    assert_eq!(library_file(&elf, "x86_64-unknown-linux-gnu", true).unwrap().name, "LLVM");
    let darwin = file(root.path(), "libLLVM-23.dylib");
    assert_eq!(library_file(&darwin, "aarch64-apple-darwin", true).unwrap().name, "LLVM-23");
    assert!(library_file(&darwin, "aarch64-apple-darwin", false).is_err());
}

#[test]
fn missing_unknown_and_ambiguous_files_refuse() {
    let root = tempfile::tempdir().unwrap();
    assert!(library_file(&root.path().join("libPolly.a"), "aarch64-apple-darwin", false).is_err());
    assert!(
        library_file(&file(root.path(), "Polly.unknown"), "aarch64-apple-darwin", false).is_err()
    );
    let first = file(root.path(), "one/libPolly.a");
    let second = file(root.path(), "two/libPolly.a");
    assert!(selected_libraries([first, second], "aarch64-apple-darwin", false).is_err());
}

#[test]
fn static_system_archive_is_bound_to_provider_metadata_and_whole_paths() {
    let root = tempfile::tempdir().unwrap();
    let libdir = root.path().join("provider with spaces/lib");
    let archive = file(&libdir, "libzstd.a");
    #[cfg(unix)]
    let libdir = {
        let alias = root.path().join("declared provider alias");
        std::os::unix::fs::symlink(&libdir, &alias).unwrap();
        alias
    };
    let metadata = file(&libdir.join("pkgconfig"), "libzstd.pc");
    let provider = file(root.path(), "pkg-config");
    let resolve = |quoted| {
        static_zstd_with(&provider, "aarch64-apple-darwin", |args| {
            Ok(match args[0] {
                "--variable=libdir" => libdir.display().to_string(),
                "--path" => metadata.display().to_string(),
                "--modversion" => "1.5.7".to_owned(),
                "--libs-only-L" => {
                    if quoted {
                        format!("-L'{}'", libdir.display())
                    } else {
                        format!("-L{}", libdir.display())
                    }
                }
                "--libs-only-l" => "-lzstd".to_owned(),
                "--libs-only-other" => String::new(),
                _ => panic!("unexpected query: {args:?}"),
            })
        })
    };
    let resolved = resolve(false).unwrap();
    assert_eq!(resolve(true).unwrap().library.path, resolved.library.path);
    assert_eq!(resolved.library.path, archive.canonicalize().unwrap());
    assert_eq!(resolved.library.kind, LinkKind::Static);
    assert_eq!(resolved.metadata, metadata.canonicalize().unwrap());
    assert_eq!(resolved.provider, provider);
    assert_eq!(resolved.version, "1.5.7");
    #[cfg(unix)]
    assert!(resolved.watch_paths.contains(&root.path().to_owned()));
}

#[test]
fn additional_system_dependencies_and_missing_selection_refuse() {
    let root = tempfile::tempdir().unwrap();
    for flags in [vec!["-lzstd", "-lother"], vec!["-lzstd", "-pthread"], vec![]] {
        let flags = flags.into_iter().map(str::to_owned).collect::<Vec<_>>();
        assert!(validate_zstd_flags(&flags, root.path()).is_err());
    }
}

#[test]
fn static_provider_refuses_missing_metadata_or_archive_and_relative_libdir() {
    let root = tempfile::tempdir().unwrap();
    let libdir = root.path().join("lib");
    let archive = file(&libdir, "libzstd.a");
    let metadata = file(&libdir.join("pkgconfig"), "libzstd.pc");
    let provider = file(root.path(), "pkg-config");
    let query = |args: &[&str]| {
        Ok(match args {
            ["--variable=libdir", "libzstd"] => libdir.display().to_string(),
            ["--path", "libzstd"] => metadata.display().to_string(),
            ["--modversion", "libzstd"] => "1.5.7".to_owned(),
            ["--libs-only-l", "--static", "libzstd"] => "-lzstd".to_owned(),
            ["--libs-only-L" | "--libs-only-other", "--static", "libzstd"] => String::new(),
            _ => panic!("unexpected query: {args:?}"),
        })
    };
    std::fs::remove_file(&archive).unwrap();
    assert!(static_zstd_with(&provider, "aarch64-apple-darwin", query).is_err());
    file(&libdir, "libzstd.a");
    std::fs::remove_file(&metadata).unwrap();
    assert!(static_zstd_with(&provider, "aarch64-apple-darwin", query).is_err());
    assert!(
        static_zstd_with(&provider, "aarch64-apple-darwin", |_| Ok("relative".into())).is_err()
    );
}

#[test]
fn relocated_system_zstd_uses_provider_without_missing_path_cache_churn() {
    let root = tempfile::tempdir().unwrap();
    let absent = root.path().join("missing/lib/libzstd.a");
    let token = absent.to_str().unwrap();
    let selected = system_zstd_input(["-lm", token]).unwrap();
    assert_eq!(selected.provider_tokens, [token.to_owned()].into_iter().collect());
    assert!(selected.watch_paths.contains(&root.path().to_owned()));
    assert!(selected.watch_paths.iter().all(|path| path.exists()));
    assert!(!selected.watch_paths.contains(&absent));
    file(absent.parent().unwrap(), "libzstd.a");
    let selected = system_zstd_input([token]).unwrap();
    assert!(
        selected.provider_tokens.is_empty(),
        "an existing LLVM-selected archive stays selected"
    );
    assert!(selected.watch_paths.contains(&absent));
    assert_eq!(
        system_zstd_input(["-lzstd"]).unwrap().provider_tokens,
        ["-lzstd".to_owned()].into_iter().collect()
    );
    assert!(
        system_zstd_input(["relative/libzstd.a", "-lzstd-other"])
            .unwrap()
            .provider_tokens
            .is_empty()
    );
}

#[cfg(unix)]
#[test]
fn malformed_system_zstd_is_not_reinterpreted_as_relocation() {
    use std::os::unix::fs::symlink;
    let root = tempfile::tempdir().unwrap();
    let archive = root.path().join("libzstd.a");
    std::fs::create_dir(&archive).unwrap();
    assert!(system_zstd_input([archive.to_str().unwrap()]).is_err());
    std::fs::remove_dir(&archive).unwrap();
    symlink(root.path().join("absent"), &archive).unwrap();
    assert!(system_zstd_input([archive.to_str().unwrap()]).is_err());
    std::fs::remove_file(&archive).unwrap();
    let broken = root.path().join("broken");
    symlink(root.path().join("absent"), &broken).unwrap();
    let inside = broken.join("libzstd.a");
    assert!(system_zstd_input([inside.to_str().unwrap()]).is_err());
}

#[test]
fn whole_path_zstd_queries_still_refuse_other_native_dependencies() {
    let root = tempfile::tempdir().unwrap();
    let libdir = root.path().join("library with spaces");
    file(&libdir, "libzstd.a");
    let metadata = file(&libdir.join("pkgconfig"), "libzstd.pc");
    let provider = file(root.path(), "pkg-config");
    let good_search = format!("-L{}", libdir.display());
    let other_search = format!("-L{}", root.path().display());
    for (libraries, other, search) in [
        ("-lzstd -llz4", "", good_search.as_str()),
        ("-lzstd", "-pthread", good_search.as_str()),
        ("-lzstd", "", other_search.as_str()),
    ] {
        assert!(
            static_zstd_with(&provider, "aarch64-apple-darwin", |args| {
                Ok(match args[0] {
                    "--variable=libdir" => libdir.display().to_string(),
                    "--path" => metadata.display().to_string(),
                    "--modversion" => "1.5.7".to_owned(),
                    "--libs-only-l" => libraries.to_owned(),
                    "--libs-only-other" => other.to_owned(),
                    "--libs-only-L" => search.to_owned(),
                    _ => panic!("unexpected query: {args:?}"),
                })
            })
            .is_err()
        );
    }
}

#[test]
fn declared_metadata_directory_refuses_fallback_and_relative_inputs() {
    let root = tempfile::tempdir().unwrap();
    let selected = root.path().join("selected with spaces");
    let other = root.path().join("implicit fallback");
    std::fs::create_dir(&selected).unwrap();
    std::fs::create_dir(&other).unwrap();
    let metadata = file(&selected, "libzstd.pc");
    assert!(validate_metadata_directory(&metadata, &selected).is_ok());
    assert!(validate_metadata_directory(&metadata, &other).is_err());
    assert!(
        static_zstd_in(Path::new("unused"), "aarch64-apple-darwin", Path::new("relative")).is_err()
    );
    assert!(
        static_zstd_in(Path::new("unused"), "aarch64-apple-darwin", &root.path().join("missing"))
            .is_err()
    );
}

#[test]
fn metadata_query_requires_the_exact_raw_selected_filename() {
    let root = tempfile::tempdir().unwrap();
    let libdir = root.path().join("provider with spaces/lib");
    file(&libdir, "libzstd.a");
    let metadata = file(&libdir.join("pkgconfig"), "libzstd.pc");
    let other = file(metadata.parent().unwrap(), "other.pc");
    let provider = file(root.path(), "pkg-config");
    for response in [
        other.display().to_string(),
        metadata.display().to_string().replace(' ', "\\ "),
        "relative/libzstd.pc".into(),
    ] {
        assert!(
            static_zstd_with(&provider, "aarch64-apple-darwin", |args| {
                Ok(match args[0] {
                    "--variable=libdir" => libdir.display().to_string(),
                    "--path" => response.clone(),
                    _ => panic!("invalid metadata must refuse before later queries: {args:?}"),
                })
            })
            .is_err()
        );
    }
}

#[cfg(target_os = "macos")]
#[test]
#[ignore = "requires explicitly bound actual native zstd package/provider"]
fn actual_declared_zstd_provider_preserves_whole_metadata_paths() {
    let provider = PathBuf::from(
        std::env::var_os("TRUST_LLVM_ZSTD_QUALIFICATION_PROVIDER")
            .expect("explicit provider required"),
    );
    let directory = PathBuf::from(
        std::env::var_os("TRUST_LLVM_ZSTD_QUALIFICATION_DIRECTORY")
            .expect("explicit metadata directory required"),
    );
    assert!(provider.is_absolute());
    assert!(directory.is_absolute());
    let target = format!("{}-apple-darwin", std::env::consts::ARCH);
    let selected = static_zstd_in(&provider, &target, &directory).unwrap();
    assert_eq!(selected.metadata.parent(), Some(directory.canonicalize().unwrap().as_path()));
    assert_eq!(selected.library.kind, LinkKind::Static);
    assert_eq!(selected.library.name, "zstd");
    assert_eq!(selected.metadata.file_name().unwrap(), "libzstd.pc");
    assert!(static_zstd_in(&provider, &target, &directory.join("missing")).is_err());
}
