use super::*;
use crate::utils::llvm_native_link::{LinkKind, NativeLibrary};

#[test]
fn native_static_darwin_closure_does_not_change_other_link_modes_or_hosts() {
    let host = "aarch64-apple-darwin";
    assert!(applies(host, host, true, false));
    assert!(!applies(host, host, true, true));
    assert!(!applies(host, host, false, false));
    assert!(!applies("x86_64-apple-darwin", host, true, false));
    assert!(!applies("x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu", true, false));
}

#[test]
fn private_tool_search_exposes_only_the_selected_static_archives() {
    let root = tempfile::tempdir().unwrap();
    let provider = root.path().join("LLVM with spaces");
    fs::create_dir(&provider).unwrap();
    let archive = provider.join("libLLVMCore.a");
    fs::write(&archive, b"selected archive").unwrap();
    fs::write(provider.join("libc++.1.dylib"), b"unselected private runtime").unwrap();
    fs::write(provider.join("libUnselected.a"), b"unselected archive").unwrap();
    let quoted = shlex::try_quote(archive.to_str().unwrap()).unwrap();
    let search =
        isolated_tool_search(&quoted, "aarch64-apple-darwin", &root.path().join("out")).unwrap();
    assert_eq!(fs::read(search.join("libLLVMCore.a")).unwrap(), b"selected archive");
    assert_eq!(fs::read_dir(&search).unwrap().count(), 1);
    assert!(!search.join("libc++.1.dylib").exists());
    assert!(!search.join("libUnselected.a").exists());
    assert_eq!(fs::read(&archive).unwrap(), b"selected archive");
}

#[test]
fn private_tool_search_refuses_unproved_native_inventory() {
    let root = tempfile::tempdir().unwrap();
    let shared = root.path().join("libLLVM.dylib");
    fs::write(&shared, b"shared inventory is not static").unwrap();
    for files in [
        "".to_owned(),
        "relative.a".to_owned(),
        "'unterminated".to_owned(),
        shlex::try_quote(shared.to_str().unwrap()).unwrap().into_owned(),
        shlex::try_quote(root.path().join("libMissing.a").to_str().unwrap()).unwrap().into_owned(),
    ] {
        assert!(
            isolated_tool_search(&files, "aarch64-apple-darwin", &root.path().join("out")).is_err()
        );
    }
}

#[test]
fn private_tool_search_reuses_exact_contents_and_changes_key_with_the_selected_bytes() {
    let root = tempfile::tempdir().unwrap();
    let archive = root.path().join("libLLVMCore.a");
    fs::write(&archive, b"first selected bytes").unwrap();
    let files = shlex::try_quote(archive.to_str().unwrap()).unwrap();
    let output = root.path().join("out");
    let first = isolated_tool_search(&files, "aarch64-apple-darwin", &output).unwrap();
    let same = isolated_tool_search(&files, "aarch64-apple-darwin", &output).unwrap();
    assert_eq!(first, same);
    fs::write(&archive, b"new selected bytes").unwrap();
    let next = isolated_tool_search(&files, "aarch64-apple-darwin", &output).unwrap();
    assert_ne!(first, next);
    assert_eq!(fs::read(next.join("libLLVMCore.a")).unwrap(), b"new selected bytes");
}

#[test]
fn private_tool_search_never_reuses_an_extra_runtime_or_an_indirect_cache() {
    let root = tempfile::tempdir().unwrap();
    let archive = root.path().join("libLLVMCore.a");
    fs::write(&archive, b"selected archive").unwrap();
    let files = shlex::try_quote(archive.to_str().unwrap()).unwrap();
    let output = root.path().join("out");
    let search = isolated_tool_search(&files, "aarch64-apple-darwin", &output).unwrap();
    fs::write(search.join("libc++.1.dylib"), b"unselected runtime").unwrap();
    assert!(isolated_tool_search(&files, "aarch64-apple-darwin", &output).is_err());
    fs::remove_file(search.join("libc++.1.dylib")).unwrap();
    #[cfg(unix)]
    {
        let retained = root.path().join("retained-search");
        fs::rename(&search, &retained).unwrap();
        std::os::unix::fs::symlink(&retained, &search).unwrap();
        assert!(isolated_tool_search(&files, "aarch64-apple-darwin", &output).is_err());
        fs::remove_file(&search).unwrap();
        fs::rename(&retained, &search).unwrap();
        fs::remove_file(search.join("libLLVMCore.a")).unwrap();
        std::os::unix::fs::symlink(&archive, search.join("libLLVMCore.a")).unwrap();
        assert!(isolated_tool_search(&files, "aarch64-apple-darwin", &output).is_err());
    }
}

#[test]
fn development_archive_preserves_source_and_binds_exact_provider_bytes() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().join("libzstd.a");
    let metadata = root.path().join("libzstd.pc");
    let provider = root.path().join("pkg-config");
    fs::write(&source, b"selected static archive").unwrap();
    fs::write(&metadata, b"selected metadata").unwrap();
    fs::write(&provider, b"selected provider").unwrap();
    let input = StaticZstd {
        library: NativeLibrary {
            name: "zstd".into(),
            path: source.clone(),
            kind: LinkKind::Static,
        },
        metadata,
        provider,
        version: "1.5.7".into(),
        watch_paths: vec![],
    };
    let destination = root.path().join("sdk/lib/rustlib/target/lib");
    fs::create_dir_all(&destination).unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(&source, destination.join("libzstd.a")).unwrap();
    stage_static_zstd(&input, &destination).unwrap();
    assert_eq!(fs::read(&source).unwrap(), b"selected static archive");
    assert!(!fs::symlink_metadata(destination.join("libzstd.a")).unwrap().file_type().is_symlink());
    assert_eq!(fs::read(destination.join("libzstd.a")).unwrap(), fs::read(&source).unwrap());
    let receipt: serde_json::Value =
        serde_json::from_slice(&fs::read(destination.join("trust-llvm-native-dev.json")).unwrap())
            .unwrap();
    assert_eq!(receipt["kind"], "static");
    assert_eq!(receipt["sha256"], format!("{:x}", Sha256::digest(b"selected static archive")));
    assert_eq!(
        receipt["pkg_config_metadata_sha256"],
        format!("{:x}", Sha256::digest(b"selected metadata"))
    );
    assert_eq!(
        receipt["pkg_config_provider_sha256"],
        format!("{:x}", Sha256::digest(b"selected provider"))
    );
}
