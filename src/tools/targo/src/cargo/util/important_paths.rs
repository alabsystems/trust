use crate::util::errors::CargoResult;
use cargo_util::paths;
use std::path::{Path, PathBuf};

/// Finds the root manifest.
///
/// Trust: the canonical name is `Targo.toml`, searched first so a project can
/// be Trust-native without carrying Cargo's filename. `Cargo.toml` remains a
/// fallback because every crates.io dependency and every stock-Rust project
/// ships one, and drop-in compatibility requires discovering those unchanged.
pub fn find_root_manifest_for_wd(cwd: &Path) -> CargoResult<PathBuf> {
    let valid_manifest_file_names = ["Targo.toml", "Cargo.toml"];
    let invalid_cargo_toml_file_name = "cargo.toml";
    let mut invalid_cargo_toml_path_exists = false;

    for current in paths::ancestors(cwd, None) {
        for name in valid_manifest_file_names {
            let manifest = current.join(name);
            if manifest.exists() {
                return Ok(manifest);
            }
        }
        if current.join(invalid_cargo_toml_file_name).exists() {
            invalid_cargo_toml_path_exists = true;
        }
    }

    if invalid_cargo_toml_path_exists {
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
    use super::find_root_manifest_for_wd;
    use std::fs;

    #[test]
    fn native_manifest_wins_over_compatibility_manifest_in_the_same_directory() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("Cargo.toml"), "[package]\nname='compat'\n").unwrap();
        fs::write(root.path().join("Targo.toml"), "[package]\nname='native'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_wd(root.path()).unwrap(),
            root.path().join("Targo.toml")
        );
    }

    #[test]
    fn compatibility_manifest_remains_a_supported_fallback() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("Cargo.toml"), "[package]\nname='compat'\n").unwrap();

        assert_eq!(
            find_root_manifest_for_wd(root.path()).unwrap(),
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
            find_root_manifest_for_wd(&nested).unwrap(),
            child.join("Cargo.toml")
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
