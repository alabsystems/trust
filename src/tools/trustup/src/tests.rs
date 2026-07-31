use std::time::{SystemTime, UNIX_EPOCH};

use super::*;

fn scratch_root(tag: &str) -> PathBuf {
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let root = env::temp_dir().join(format!("trustup-{tag}-{}-{nonce}", std::process::id()));
    fs::create_dir_all(root.join("bin")).unwrap();
    for required in REQUIRED_TOOLS {
        fs::write(root.join("bin").join(exe_name(required)), b"fixture").unwrap();
    }
    root
}

/// The whole point of the relaxation: a real Trust stage2 sysroot ships `rustc`
/// and `cargo` as extra links onto `trustc`/`targo` because rustup will not
/// register a toolchain without them. Refusing to link such a root made trustup
/// unable to select the toolchain it exists to select.
#[cfg(unix)]
#[test]
fn toolchain_admission_accepts_same_inode_rustup_aliases() {
    let root = scratch_root("same-inode-aliases");
    let bin = root.join("bin");

    fs::hard_link(bin.join(exe_name("trustc")), bin.join(exe_name("rustc"))).unwrap();
    std::os::unix::fs::symlink(bin.join(exe_name("targo")), bin.join(exe_name("cargo"))).unwrap();

    validate_toolchain_root(&root).expect("same-artifact rustup aliases must be admitted");

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

/// Every inherited name outside the two rustup-required spellings is rejected
/// unconditionally — being a genuine same-inode alias does not rescue it.
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
        let error =
            validate_toolchain_root(&root).expect_err("retired Tippy leaf was admitted");
        assert!(error.contains(retired), "unexpected admission error: {error}");
        fs::remove_file(path).unwrap();
    }

    fs::remove_dir_all(root).unwrap();
}
