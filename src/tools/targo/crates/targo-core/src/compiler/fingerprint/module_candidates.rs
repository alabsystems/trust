//! Trust: ordinary Rust module resolution also observes the other candidate's
//! absence. Compiler dep-info lists files read, so retain these precise path
//! observations beside that read-set rather than scanning the whole package.
use std::path::{Path, PathBuf};

/// Rust's default module locations are `name.rs` and `name/mod.rs`. Raw path
/// spelling is deliberate: canonicalizing an absent path or a symlink would
/// discard the namespace whose later change must invalidate the artifact.
pub(super) fn alternate(source: &Path) -> Option<PathBuf> {
    if source.extension()? != "rs" {
        return None;
    }
    if source.file_name()? == "mod.rs" {
        let directory = source.parent()?;
        let mut name = directory.file_name()?.to_os_string();
        name.push(".rs");
        Some(directory.with_file_name(name))
    } else {
        Some(source.with_extension("").join("mod.rs"))
    }
}

/// Match rustc's `FileLoader::file_exists`, including directories and followed
/// symlinks. An unreadable observation cannot establish freshness; it does not
/// turn an otherwise successful compilation into a build failure.
pub(super) fn observe(path: &Path) -> Option<bool> {
    path.try_exists().ok()
}

#[cfg(test)]
pub(super) fn unchanged(path: &Path, previous: Option<bool>) -> bool {
    previous.is_some() && observe(path) == previous
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_rust_module_layouts_track_the_opposite_raw_location() {
        assert_eq!(
            alternate(Path::new("src/foo.rs")),
            Some("src/foo/mod.rs".into())
        );
        assert_eq!(
            alternate(Path::new("src/foo/mod.rs")),
            Some("src/foo.rs".into())
        );
        assert_eq!(
            alternate(Path::new("src/foo.bar/mod.rs")),
            Some("src/foo.bar.rs".into())
        );
        assert!(alternate(Path::new("src/not-rust.txt")).is_none());
    }

    #[test]
    fn a_competing_module_with_previously_absent_parent_invalidates_once() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("implementation/mod.rs");
        let absent = observe(&path);
        assert_eq!(absent, Some(false));
        assert!(unchanged(&path, absent));
        // Merely creating an empty directory does not change Rust resolution.
        std::fs::create_dir(path.parent().unwrap()).unwrap();
        assert!(unchanged(&path, absent));
        std::fs::write(&path, "pub fn value() -> u32 { 43 }\n").unwrap();
        assert!(!unchanged(&path, absent));
        let present = observe(&path);
        assert!(
            unchanged(&path, present),
            "explicit #[path] users may legitimately have both candidates"
        );
        std::fs::remove_file(&path).unwrap();
        assert!(!unchanged(&path, present));
        assert!(
            !unchanged(&path, None),
            "unavailable evidence never authorizes fresh"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_dangling_competing_symlink_becoming_valid_invalidates() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("candidate.rs");
        let target = root.path().join("target.rs");
        std::os::unix::fs::symlink(&target, &path).unwrap();
        let previous = observe(&path);
        assert_eq!(previous, Some(false));
        std::fs::write(&target, "pub fn value() -> u32 { 43 }\n").unwrap();
        assert!(!unchanged(&path, previous));
    }
}
