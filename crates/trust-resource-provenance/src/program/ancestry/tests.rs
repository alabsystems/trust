use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

/// Own build output is a checked private ancestor, unlike world-writable /tmp.
fn scratch() -> tempfile::TempDir {
    let base = std::env::current_exe().unwrap().parent().unwrap().canonicalize().unwrap();
    tempfile::Builder::new().prefix("held-ancestry-").suffix(".noindex").tempdir_in(base).unwrap()
}

/// `root/<name>0/<name>1/...` with each mode set and read back.
fn chain(root: &Path, name: &str, modes: &[u32]) -> Vec<PathBuf> {
    let mut path = root.to_owned();
    let mut created = Vec::new();
    for (index, &mode) in modes.iter().enumerate() {
        path.push(format!("{name}{index}"));
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
        assert_eq!(fs::metadata(&path).unwrap().mode() & 0o7777, mode, "{}", path.display());
        created.push(path.clone());
    }
    created
}

#[test]
fn the_mask_is_the_one_owned_refuses() {
    assert_eq!(HELD_FORBIDDEN_MODE, 0o7022);
}

#[test]
fn an_owner_only_chain_passes_the_same_walk_held_inputs_take() {
    let scratch = scratch();
    let dirs = chain(scratch.path(), "private", &[0o755, 0o700, 0o750]);
    check_directory_ancestry(&dirs[2], deadline()).unwrap();
    directory(&dirs[2], deadline()).unwrap();
    HeldDirectoryInput::open(&dirs[2], deadline()).unwrap();
}

#[test]
fn the_first_writable_or_special_directory_is_reported_with_owner_and_mode() {
    let scratch = scratch();
    // SAFETY: geteuid only reads this process's effective account.
    let uid = unsafe { libc::geteuid() };
    for (name, mode) in [
        ("shared", 0o1777),
        ("group", 0o775),
        ("world", 0o757),
        ("setgid", 0o2755),
        ("sticky", 0o1755),
    ] {
        let dirs = chain(scratch.path(), name, &[0o755, mode, 0o700]);
        let refusal = check_directory_ancestry(&dirs[2], deadline()).unwrap_err();
        assert_eq!(refusal.directory, dirs[1], "{name}");
        assert_eq!(refusal.uid, Some(uid), "{name}");
        assert_eq!(refusal.mode.map(|mode| mode & 0o7777), Some(mode), "{name}");
        let message = "native input has unsupported kind or writable/special mode";
        assert_eq!(refusal.error.to_string(), message, "{name}");
        // The capture paths refuse with the very same error.
        assert_eq!(directory(&dirs[2], deadline()).unwrap_err().to_string(), message);
        assert!(HeldDirectoryInput::open(&dirs[2], deadline()).is_err(), "{name}");
    }
    let dirs = chain(scratch.path(), "first", &[0o775, 0o1777]);
    assert_eq!(check_directory_ancestry(&dirs[1], deadline()).unwrap_err().directory, dirs[0]);
}

#[test]
fn a_symlink_component_and_noncanonical_syntax_are_refused_where_they_occur() {
    let scratch = scratch();
    let dirs = chain(scratch.path(), "private", &[0o700]);
    let link = scratch.path().join("link");
    std::os::unix::fs::symlink(&dirs[0], &link).unwrap();
    let refusal = check_directory_ancestry(&link, deadline()).unwrap_err();
    assert_eq!(refusal.directory, link);
    assert_eq!((refusal.uid, refusal.mode), (None, None));
    assert!(directory(&link, deadline()).is_err());

    let relative = Path::new("relative/path");
    let refusal = check_directory_ancestry(relative, deadline()).unwrap_err();
    assert_eq!(refusal.directory, relative);
    let dotted = dirs[0].join("..").join("private0");
    assert_eq!(check_directory_ancestry(&dotted, deadline()).unwrap_err().directory, dotted);
}
