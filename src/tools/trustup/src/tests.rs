use std::time::{SystemTime, UNIX_EPOCH};

use super::*;

#[test]
fn toolchain_admission_rejects_every_retired_tippy_leaf() {
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let root =
        env::temp_dir().join(format!("trustup-tippy-surface-{}-{nonce}", std::process::id()));
    let bin = root.join("bin");
    fs::create_dir_all(&bin).unwrap();
    for required in REQUIRED_TOOLS {
        fs::write(bin.join(exe_name(required)), b"fixture").unwrap();
    }
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
