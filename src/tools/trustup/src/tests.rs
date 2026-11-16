use std::time::{SystemTime, UNIX_EPOCH};

use super::*;

fn scratch_root(tag: &str) -> PathBuf {
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let root = env::temp_dir().join(format!("trustup-{tag}-{}-{nonce}", std::process::id()));
    fs::create_dir_all(root.join("bin")).unwrap();
    for required in REQUIRED_TOOLS {
        write_tool(&root.join("bin").join(exe_name(required)));
    }
    root
}

fn write_tool(path: &Path) {
    fs::write(path, b"fixture").unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }
}

/// The whole point of the relaxation: a real Trust stage2 sysroot ships `rustc`
/// and `cargo` as extra links onto `trustc`/`targo`, and `rustdoc` is an alias of
/// `trustdoc`. Refusing those aliases makes trustup unable to select the
/// complete toolchain it exists to select.
#[cfg(unix)]
#[test]
fn toolchain_admission_accepts_same_inode_rustup_aliases() {
    let root = scratch_root("same-inode-aliases");
    let bin = root.join("bin");

    fs::hard_link(bin.join(exe_name("trustc")), bin.join(exe_name("rustc"))).unwrap();
    std::os::unix::fs::symlink(bin.join(exe_name("targo")), bin.join(exe_name("cargo"))).unwrap();
    write_tool(&bin.join(exe_name("trustdoc")));
    fs::hard_link(bin.join(exe_name("trustdoc")), bin.join(exe_name("rustdoc"))).unwrap();

    validate_toolchain_root(&root).expect("same-artifact rustup aliases must be admitted");

    fs::remove_file(bin.join(exe_name("rustdoc"))).unwrap();
    std::os::unix::fs::symlink(exe_name("trustdoc"), bin.join(exe_name("rustdoc"))).unwrap();
    validate_toolchain_root(&root).expect("confined relative rustdoc alias must be admitted");

    fs::remove_dir_all(root).unwrap();
}

/// The relaxation admits *aliases*, not spellings. An unrelated executable that
/// merely happens to be named `rustc` is still a foreign toolchain, and equal
/// bytes are not equal identity.
#[cfg(unix)]
#[test]
fn toolchain_admission_still_rejects_unlinked_and_dangling_stock_names() {
    let root = scratch_root("unlinked-stock-names");
    let bin = root.join("bin");

    // Byte-identical to `trustc`, but a separate inode.
    let rustc = bin.join(exe_name("rustc"));
    fs::write(&rustc, b"fixture").unwrap();
    let error = validate_toolchain_root(&root).expect_err("unlinked `rustc` was admitted");
    assert!(error.contains("rustc"), "unexpected admission error: {error}");
    fs::remove_file(&rustc).unwrap();

    // A dangling symlink is invisible to `Path::exists`, so it must not become
    // a way to park a stock name in a Trust root unchecked.
    std::os::unix::fs::symlink(bin.join(exe_name("nonexistent")), &rustc).unwrap();
    let error = validate_toolchain_root(&root).expect_err("dangling `rustc` link was admitted");
    assert!(error.contains("rustc"), "unexpected admission error: {error}");
    fs::remove_file(&rustc).unwrap();

    // `cargo` may only alias Targo, never some other canonical Trust binary.
    fs::hard_link(bin.join(exe_name("targo-trust")), bin.join(exe_name("cargo"))).unwrap();
    let error = validate_toolchain_root(&root).expect_err("`cargo -> targo-trust` was admitted");
    assert!(error.contains("cargo"), "unexpected admission error: {error}");

    fs::remove_dir_all(root).unwrap();
}

/// Other inherited names remain forbidden, and an allowed name must still
/// refer to its own canonical tool rather than an arbitrary same-inode sibling.
#[cfg(unix)]
#[test]
fn toolchain_admission_never_admits_aliases_trust_does_not_materialize() {
    let root = scratch_root("non-materialized-aliases");
    let bin = root.join("bin");

    for (inherited, canonical) in
        [("rustdoc", "trustc"), ("rustfmt", "trustc"), ("rust-analyzer", "trustc")]
    {
        let path = bin.join(exe_name(inherited));
        fs::hard_link(bin.join(exe_name(canonical)), &path).unwrap();
        let error = validate_toolchain_root(&root)
            .expect_err("a non-materialized inherited name was admitted");
        assert!(error.contains(inherited), "unexpected admission error: {error}");
        fs::remove_file(&path).unwrap();
    }

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn toolchain_admission_rejects_every_retired_tippy_leaf() {
    let root = scratch_root("tippy-surface");
    let bin = root.join("bin");
    assert!(validate_toolchain_root(&root).is_ok());

    for retired in
        ["cargo-clippy", "clippy-driver", "targo-clippy", "trust-clippy", "trust-clippy-driver"]
    {
        let path = bin.join(exe_name(retired));
        fs::write(&path, b"fixture").unwrap();
        let error = validate_toolchain_root(&root).expect_err("retired Tippy leaf was admitted");
        assert!(error.contains(retired), "unexpected admission error: {error}");
        fs::remove_file(path).unwrap();
    }

    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn rustdoc_admission_rejects_distinct_missing_and_dangling_targets() {
    let root = scratch_root("rustdoc-targets");
    let bin = root.join("bin");
    let alias = bin.join(exe_name("rustdoc"));
    let canonical = bin.join(exe_name("trustdoc"));
    write_tool(&canonical);
    write_tool(&alias); // Equal bytes are not the same artifact.
    assert!(validate_toolchain_root(&root).unwrap_err().contains("rustdoc"));
    fs::remove_file(&alias).unwrap();

    std::os::unix::fs::symlink(exe_name("missing"), &alias).unwrap();
    assert!(validate_toolchain_root(&root).unwrap_err().contains("rustdoc"));
    fs::remove_file(&alias).unwrap();

    fs::hard_link(&canonical, &alias).unwrap();
    fs::remove_file(&canonical).unwrap();
    assert!(validate_toolchain_root(&root).unwrap_err().contains("rustdoc"));
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn rustdoc_alias_cannot_escape_through_an_external_link_of_the_same_inode() {
    let root = scratch_root("rustdoc-escape");
    let external = scratch_root("rustdoc-external");
    let canonical = root.join("bin/trustdoc");
    let outside = external.join("bin/trustdoc");
    write_tool(&canonical);
    fs::hard_link(&canonical, &outside).unwrap();
    let alias = root.join("bin/rustdoc");
    std::os::unix::fs::symlink(&outside, &alias).unwrap();

    assert!(same_artifact(&alias, &canonical), "fixture must defeat inode-only admission");
    assert!(validate_toolchain_root(&root).unwrap_err().contains("rustdoc"));
    fs::remove_dir_all(root).unwrap();
    fs::remove_dir_all(external).unwrap();
}

#[cfg(unix)]
#[test]
fn rustdoc_canonical_leaf_cannot_redirect_outside_the_root() {
    let root = scratch_root("rustdoc-canonical-link");
    let external = scratch_root("rustdoc-canonical-external");
    let canonical = root.join("bin/trustdoc");
    let outside = external.join("bin/trustdoc");
    write_tool(&outside);
    std::os::unix::fs::symlink(&outside, &canonical).unwrap();
    let alias = root.join("bin/rustdoc");
    std::os::unix::fs::symlink("trustdoc", &alias).unwrap();

    assert!(same_artifact(&alias, &canonical), "fixture must defeat inode-only admission");
    assert!(validate_toolchain_root(&root).unwrap_err().contains("rustdoc"));
    fs::remove_dir_all(root).unwrap();
    fs::remove_dir_all(external).unwrap();
}

#[cfg(unix)]
#[test]
fn non_executable_canonical_tools_cannot_authenticate_an_alias() {
    use std::os::unix::fs::PermissionsExt;
    let root = scratch_root("non-executable-canonical");
    let bin = root.join("bin");
    let canonical = bin.join("trustdoc");
    write_tool(&canonical);
    fs::hard_link(&canonical, bin.join("rustdoc")).unwrap();
    fs::set_permissions(&canonical, fs::Permissions::from_mode(0o644)).unwrap();
    assert!(validate_toolchain_root(&root).unwrap_err().contains("rustdoc"));

    fs::remove_file(bin.join("rustdoc")).unwrap();
    fs::set_permissions(bin.join("targo"), fs::Permissions::from_mode(0o644)).unwrap();
    assert!(validate_toolchain_root(&root).unwrap_err().contains("targo"));
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn root_registration_links_are_allowed_but_bin_directory_links_are_not() {
    let root = scratch_root("directory-links");
    let registered = root.with_extension("registered");
    std::os::unix::fs::symlink(&root, &registered).unwrap();
    validate_toolchain_root(&registered).expect("Trustup's own root links remain valid");

    fs::rename(root.join("bin"), root.join("other-bin")).unwrap();
    std::os::unix::fs::symlink("other-bin", root.join("bin")).unwrap();
    assert!(validate_toolchain_root(&registered).unwrap_err().contains("bin directory"));
    fs::remove_file(registered).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn retired_tcargo_cannot_authenticate_cargo_or_remain_in_the_surface() {
    let root = scratch_root("retired-tcargo");
    let bin = root.join("bin");
    let retired = bin.join("tcargo");
    write_tool(&retired);
    fs::hard_link(&retired, bin.join("cargo")).unwrap();
    assert!(validate_toolchain_root(&root).unwrap_err().contains("cargo"));

    fs::remove_file(bin.join("cargo")).unwrap();
    fs::remove_file(&retired).unwrap();
    fs::hard_link(bin.join("targo"), bin.join("cargo")).unwrap();
    fs::hard_link(bin.join("targo"), &retired).unwrap();
    assert!(validate_toolchain_root(&root).unwrap_err().contains("tcargo"));
    fs::remove_dir_all(root).unwrap();
}
