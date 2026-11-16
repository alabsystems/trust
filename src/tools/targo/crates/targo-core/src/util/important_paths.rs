use crate::util::errors::CargoResult;
use cargo_util::paths;
use std::path::{Path, PathBuf};

/// Finds the root manifest.
///
/// Trust: the authenticated Targo frontend prefers `Targo.toml`, with
/// `Cargo.toml` as a fallback. The Cargo compatibility frontend retains
/// upstream discovery and diagnostics, including ignoring `Targo.toml`.
pub fn find_root_manifest_for_wd(cwd: &Path) -> CargoResult<PathBuf> {
    find_root_manifest_for_frontend(cwd, crate::is_targo_invocation())
}

// Trust: keep selection independently testable without changing the process's
// authenticated frontend identity (a unit-test executable has neither name).
fn find_root_manifest_for_frontend(cwd: &Path, targo: bool) -> CargoResult<PathBuf> {
    let valid_manifest_file_names: &[&str] = if targo {
        &["Targo.toml", "Cargo.toml"]
    } else {
        &["Cargo.toml"]
    };
    let invalid_cargo_toml_file_name = "cargo.toml";
    let mut invalid_cargo_toml_path_exists = false;

    for current in paths::ancestors(cwd, None) {
        for &name in valid_manifest_file_names {
            let manifest = current.join(name);
            if manifest.exists() {
                return Ok(manifest);
            }
        }
        if current.join(invalid_cargo_toml_file_name).exists() {
            invalid_cargo_toml_path_exists = true;
        }
    }

    if !targo {
        if invalid_cargo_toml_path_exists {
            anyhow::bail!(
                "could not find `Cargo.toml` in `{}` or any parent directory, but found cargo.toml please try to rename it to Cargo.toml",
                cwd.display()
            )
        } else {
            anyhow::bail!(
                "could not find `Cargo.toml` in `{}` or any parent directory",
                cwd.display()
            )
        }
    } else if invalid_cargo_toml_path_exists {
        anyhow::bail!(
            "could not find `Targo.toml` or `Cargo.toml` in `{}` or any parent directory, but found `cargo.toml`; rename it to `Targo.toml` (native) or `Cargo.toml` (compatibility)",
            cwd.display()
        )
    } else {
        anyhow::bail!(
            "could not find `Targo.toml` or `Cargo.toml` in `{}` or any parent directory",
            cwd.display()
        )
    }
}

// Trust: pins the search order — nearest directory first, then the native
// spelling within a directory. Getting that backwards would silently retarget
// a workspace whose members carry `Cargo.toml`.
#[cfg(test)]
mod tests {
    use super::find_root_manifest_for_frontend;
    use std::fs;

    #[test]
    fn native_manifest_wins_over_compatibility_manifest_in_the_same_directory() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("Cargo.toml"), "[package]\nname='compat'\n").unwrap();
        fs::write(root.path().join("Targo.toml"), "[package]\nname='native'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_frontend(root.path(), true).unwrap(),
            root.path().join("Targo.toml")
        );
    }

    #[test]
    fn compatibility_manifest_remains_a_supported_fallback() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("Cargo.toml"), "[package]\nname='compat'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_frontend(root.path(), true).unwrap(),
            root.path().join("Cargo.toml")
        );
    }

    #[test]
    fn nearest_manifest_wins_before_dialect_preference() {
        let root = tempfile::tempdir().unwrap();
        let child = root.path().join("child");
        let nested = child.join("nested");
        fs::create_dir_all(&nested).unwrap();
        fs::write(root.path().join("Targo.toml"), "[workspace]\n").unwrap();
        fs::write(child.join("Cargo.toml"), "[package]\nname='child'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_frontend(&nested, true).unwrap(),
            child.join("Cargo.toml")
        );
    }

    #[test]
    fn cargo_ignores_native_manifest_in_the_same_directory() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("Cargo.toml"), "[package]\nname='compat'\n").unwrap();
        fs::write(root.path().join("Targo.toml"), "[package]\nname='native'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_frontend(root.path(), false).unwrap(),
            root.path().join("Cargo.toml")
        );
    }

    #[test]
    fn cargo_skips_a_nearer_native_manifest() {
        let root = tempfile::tempdir().unwrap();
        let child = root.path().join("child");
        let nested = child.join("nested");
        fs::create_dir_all(&nested).unwrap();
        fs::write(root.path().join("Cargo.toml"), "[workspace]\n").unwrap();
        fs::write(child.join("Targo.toml"), "[package]\nname='native'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_frontend(&nested, false).unwrap(),
            root.path().join("Cargo.toml")
        );
    }

    #[test]
    fn cargo_missing_manifest_keeps_upstream_diagnostic_even_with_native_manifest() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("Targo.toml"), "[package]\nname='native'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_frontend(root.path(), false)
                .unwrap_err()
                .to_string(),
            format!(
                "could not find `Cargo.toml` in `{}` or any parent directory",
                root.path().display()
            )
        );
    }

    #[test]
    fn native_missing_manifest_keeps_both_supported_names() {
        let root = tempfile::tempdir().unwrap();
        assert_eq!(
            find_root_manifest_for_frontend(root.path(), true)
                .unwrap_err()
                .to_string(),
            format!(
                "could not find `Targo.toml` or `Cargo.toml` in `{}` or any parent directory",
                root.path().display()
            )
        );
    }

    // Trust: like the inherited integration control, this needs a
    // case-sensitive filesystem so `cargo.toml` is not also `Cargo.toml`.
    #[cfg(target_os = "linux")]
    #[test]
    fn cargo_lowercase_manifest_keeps_upstream_rename_diagnostic() {
        let root = tempfile::tempdir().unwrap();
        fs::write(
            root.path().join("cargo.toml"),
            "[package]\nname='lowercase'\n",
        )
        .unwrap();
        assert_eq!(
            find_root_manifest_for_frontend(root.path(), false)
                .unwrap_err()
                .to_string(),
            format!(
                "could not find `Cargo.toml` in `{}` or any parent directory, but found cargo.toml please try to rename it to Cargo.toml",
                root.path().display()
            )
        );
    }
}

/// Returns the path to the `file` in `pwd`, if it exists.
pub fn find_project_manifest_exact(pwd: &Path, file: &str) -> CargoResult<PathBuf> {
    let manifest = pwd.join(file);

    if manifest.exists() {
        Ok(manifest)
    } else {
        anyhow::bail!("Could not find `{}` in `{}`", file, pwd.display())
    }
}
