use std::fs;

#[cfg(target_os = "macos")]
fn macho(dependency: Option<&std::path::Path>) -> Vec<u8> {
    let name = dependency.map(|path| path.to_str().unwrap().as_bytes());
    let command_size = name.map_or(0, |name| (24 + name.len() + 1 + 7) & !7);
    let mut bytes = Vec::new();
    for word in
        [0xfeedfacfu32, 0x0100000c, 0, 6, u32::from(name.is_some()), command_size as u32, 0, 0]
    {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    if let Some(name) = name {
        for word in [0xcu32, command_size as u32, 24, 0, 0, 0] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        bytes.extend_from_slice(name);
        bytes.resize(32 + command_size, 0);
    }
    bytes
}

#[test]
fn installation_identity_includes_headers_beside_the_tool_binaries() {
    let root = tempfile::tempdir().unwrap();
    fs::create_dir_all(root.path().join("include/llvm")).unwrap();
    let header = root.path().join("include/llvm/config.h");
    fs::write(&header, "first").unwrap();
    let before = super::installation_digest(root.path()).unwrap();
    fs::write(&header, "other").unwrap();
    assert_ne!(before, super::installation_digest(root.path()).unwrap());
}

#[cfg(unix)]
#[test]
fn installation_absence_does_not_make_a_required_tool_or_loader_available() {
    let root = tempfile::tempdir().unwrap();
    fs::create_dir(root.path().join("bin")).unwrap();
    let link = root.path().join("bin/optional-helper");
    std::os::unix::fs::symlink("../absent/helper", &link).unwrap();
    let before = super::installation_digest(root.path()).unwrap();
    assert_eq!(before, super::installation_digest(root.path()).unwrap());
    let error = super::tool_digest(&link).unwrap_err();
    assert!(error.contains(link.to_str().unwrap()), "required tool lost its path: {error}");
    assert!(super::loader_closure([link.clone()]).is_err());
    fs::create_dir(root.path().join("absent")).unwrap();
    fs::write(root.path().join("absent/helper"), b"now available").unwrap();
    assert_ne!(before, super::installation_digest(root.path()).unwrap());
    assert!(super::tool_digest(&link).is_ok());
}

#[cfg(target_os = "macos")]
#[test]
fn tool_identity_follows_external_loader_library_bytes() {
    // Static Mach-O fixtures, never executed: one library load command is
    // enough for the system object reader to expose the external edge.
    let root = tempfile::tempdir().unwrap();
    let dependency = root.path().join("external.dylib");
    let tool = root.path().join("tool");
    fs::write(&dependency, macho(None)).unwrap();
    fs::write(&tool, macho(Some(&dependency))).unwrap();
    let before = super::tool_digest(&tool).unwrap();
    let mut changed = macho(None);
    changed.extend_from_slice(b"changed library bytes");
    fs::write(&dependency, changed).unwrap();
    assert_ne!(before, super::tool_digest(&tool).unwrap());
}

#[cfg(target_os = "macos")]
#[test]
fn selected_host_tool_keeps_foreign_namespace_bytes_and_required_loader_refusals() {
    let root = tempfile::tempdir().unwrap();
    let external = tempfile::tempdir().unwrap();
    fs::create_dir(root.path().join("bin")).unwrap();
    fs::create_dir(root.path().join("lib")).unwrap();
    let tool = root.path().join("bin/clang");
    let support = root.path().join("lib/foreign-support.dylib");
    fs::write(&tool, macho(None)).unwrap();
    fs::write(&support, macho(Some(std::path::Path::new("@rpath/Missing.framework/Missing"))))
        .unwrap();
    assert!(super::installation_digest(root.path()).unwrap_err().contains("Missing.framework"));
    let before = super::selected_tool_installation_digest(root.path(), &tool).unwrap();
    let mut changed = fs::read(&support).unwrap();
    changed.extend_from_slice(b"foreign support bytes still matter");
    fs::write(&support, changed).unwrap();
    assert_ne!(before, super::selected_tool_installation_digest(root.path(), &tool).unwrap());
    let dependency = external.path().join("required.dylib");
    fs::write(&dependency, macho(None)).unwrap();
    fs::write(&tool, macho(Some(&dependency))).unwrap();
    let before = super::selected_tool_installation_digest(root.path(), &tool).unwrap();
    let mut changed = macho(None);
    changed.extend_from_slice(b"required loader bytes");
    fs::write(&dependency, changed).unwrap();
    assert_ne!(before, super::selected_tool_installation_digest(root.path(), &tool).unwrap());
    fs::remove_file(&dependency).unwrap();
    assert!(super::selected_tool_installation_digest(root.path(), &tool).is_err());
    fs::remove_file(&tool).unwrap();
    assert!(super::selected_tool_installation_digest(root.path(), &tool).is_err());

    // Supply explicitly before counting the installed-tool subcontrol.
    if let Some(tool) = std::env::var_os("TRUST_NATIVE_REPO_CLANG_CONTROL") {
        let tool = std::path::Path::new(&tool);
        let installation = tool.parent().and_then(std::path::Path::parent).unwrap();
        let identity = super::selected_tool_installation_digest(installation, tool).unwrap();
        assert!(!identity.is_empty());
        println!(
            "actual selected clang installation and required loader control executed: {}; SHA256 {}",
            tool.display(),
            identity
        );
    }
}
