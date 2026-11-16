use super::*;

#[test]
fn selected_zstd_headers_require_an_absolute_complete_directory() {
    let temp = tempfile::tempdir().unwrap();
    let selected = temp.path().canonicalize().unwrap().join("headers with spaces");
    assert!(include_directory("relative/include").is_err());
    assert!(include_directory("/headers\nother").is_err());
    assert!(include_directory(selected.to_str().unwrap()).is_err());
    fs::create_dir(&selected).unwrap();
    assert!(include_directory(selected.to_str().unwrap()).is_err());
    fs::write(selected.join("zstd.h"), b"selected header").unwrap();
    assert_eq!(include_directory(selected.to_str().unwrap()).unwrap(), selected);
}

#[cfg(unix)]
#[test]
fn selected_zstd_headers_preserve_the_declared_alias_namespace() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let physical = root.join("physical headers");
    let declared = root.join("package header alias");
    fs::create_dir(&physical).unwrap();
    fs::write(physical.join("zstd.h"), b"selected header").unwrap();
    std::os::unix::fs::symlink(&physical, &declared).unwrap();
    assert_eq!(include_directory(declared.to_str().unwrap()).unwrap(), declared);
    fs::remove_file(physical.join("zstd.h")).unwrap();
    assert!(include_directory(declared.to_str().unwrap()).is_err());
}

#[cfg(unix)]
fn pkgconf_fixture(root: &Path, retarget: bool) -> (PathBuf, PathBuf, PathBuf) {
    use std::os::unix::fs::PermissionsExt;

    let package = root.join("selected package with spaces");
    let metadata_directory = package.join("lib/pkgconfig");
    let library_directory = package.join("lib");
    let include = package.join("include");
    fs::create_dir_all(&metadata_directory).unwrap();
    fs::create_dir_all(&include).unwrap();
    fs::write(metadata_directory.join("libzstd.pc"), b"selected package metadata").unwrap();
    fs::write(library_directory.join("libzstd.a"), b"selected archive fixture").unwrap();
    fs::write(include.join("zstd.h"), b"selected header fixture").unwrap();
    let original = root.join("original pkgconf");
    let alternate = root.join("alternate pkgconf");
    let alias = root.join("declared pkgconf alias");
    let quote = |path: &Path| shlex::try_quote(path.to_str().unwrap()).unwrap().into_owned();
    let body = |retarget: &str| {
        format!(
            "#!/bin/sh\ncase \"$2\" in\n\
             --variable=libdir) printf '%s\\n' {};;\n\
             --path) printf '%s\\n' {};;\n\
             --modversion) printf '%s\\n' 1.5.7;;\n\
             --libs-only-l) printf '%s\\n' -lzstd;;\n\
             --libs-only-other) printf '\\n';;\n\
             --libs-only-L) printf '%s\\n' {};;\n\
             --variable=includedir) {retarget} printf '%s\\n' {};;\n\
             *) exit 9;;\nesac\n",
            quote(&library_directory),
            quote(&metadata_directory.join("libzstd.pc")),
            shlex::try_quote(&format!("-L{}", library_directory.display())).unwrap(),
            quote(&include),
        )
    };
    fs::write(&alternate, body("")).unwrap();
    let change = if retarget {
        format!("rm -f {}; ln -s {} {};", quote(&alias), quote(&alternate), quote(&alias))
    } else {
        String::new()
    };
    fs::write(&original, body(&change)).unwrap();
    for path in [&original, &alternate] {
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }
    std::os::unix::fs::symlink(&original, &alias).unwrap();
    (alias, metadata_directory, alternate)
}

#[cfg(unix)]
#[test]
fn actual_declared_zstd_helper_accepts_a_stable_tool_alias() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let (provider, metadata, _) = pkgconf_fixture(&root, false);
    let mut config = cmake::Config::new(root.join("source"));
    bind_declared(&mut config, &provider, "aarch64-apple-darwin", &metadata).unwrap();
}

#[cfg(unix)]
#[test]
fn actual_declared_zstd_helper_refuses_original_tool_alias_retarget() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let (provider, metadata, alternate) = pkgconf_fixture(&root, true);
    let mut config = cmake::Config::new(root.join("source"));
    let error =
        bind_declared(&mut config, &provider, "aarch64-apple-darwin", &metadata).unwrap_err();
    assert!(error.contains("changed while resolving its headers"), "{error}");
    assert_eq!(provider.canonicalize().unwrap(), alternate);
}
