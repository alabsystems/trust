// Trust: `Cow`/`Path`/`PathBuf` serve `path_under_root` below.
use std::borrow::Cow;
use std::path::{Path, PathBuf};

use ignore::gitignore;

use crate::config::{FileName, IgnoreList};

pub(crate) struct IgnorePathSet {
    ignore_set: gitignore::Gitignore,
    // Trust: the canonical form of the matcher's root (the directory holding
    // rustfmt.toml), so an absolute path that reaches that directory through
    // a symlink (macOS `/tmp` -> `/private/tmp`) still relates to it.
    canonical_root: Option<PathBuf>,
}

impl IgnorePathSet {
    pub(crate) fn from_ignore_list(ignore_list: &IgnoreList) -> Result<Self, ignore::Error> {
        let mut ignore_builder = gitignore::GitignoreBuilder::new(ignore_list.rustfmt_toml_path());

        for ignore_path in ignore_list {
            ignore_builder.add_line(None, ignore_path.to_str().unwrap())?;
        }

        // Trust: see `canonical_root`.
        let ignore_set = ignore_builder.build()?;
        let canonical_root = ignore_set.path().canonicalize().ok();
        Ok(IgnorePathSet {
            ignore_set,
            canonical_root,
        })
    }

    pub(crate) fn is_match(&self, file_name: &FileName) -> bool {
        match file_name {
            FileName::Stdin => false,
            FileName::Real(p) => {
                // `matched_path_or_any_parents` ASSERTS that the path is under
                // the matcher's root (the directory holding the rustfmt.toml
                // these ignore entries came from) and PANICS otherwise:
                // `ignore`'s `strip` leaves an absolute path absolute, and the
                // next line is `assert!(!path.has_root(), "path is expected to
                // be under the root")`.
                //
                // MEASURED 2026-09-18: the publication engine formats an
                // exported clone under $TMPDIR while the config it resolved
                // lives in the invoking tree, so a diagnostic's file was
                // outside the root and trustfmt aborted with an ICE dump
                // (`trustfmt-ice-…txt`) instead of formatting — and the dump
                // landed in the engine's working tree, where the clean-tree
                // guard then refused every later `pub stage`.
                //
                // An ignore entry is root-relative by construction, so it can
                // never match a path outside that root: "not ignored" is the
                // answer, not a crash. Relative paths keep the old path
                // exactly (they cannot trip the assert), so no existing
                // decision changes.
                //
                // Trust: "outside" is decided by `path_under_root`, which also
                // relates a root or a file spelled through a symlink, so such
                // a file still honours the ignore list instead of silently
                // counting as outside it.
                match self.path_under_root(p) {
                    Some(p) => self
                        .ignore_set
                        .matched_path_or_any_parents(p, false)
                        .is_ignore(),
                    None => false,
                }
            }
        }
    }

    // Trust: `path` expressed relative to the matcher's root, or `None` when
    // it lies outside it. A relative path, or any path under an empty root
    // (an `IgnoreList` that never saw a rustfmt.toml), is passed through
    // unchanged, as upstream always did: `ignore` itself cannot panic on
    // either. An absolute path is stripped component-wise against the root
    // first; only when that fails are both sides canonicalized, so the
    // common case touches no file system.
    fn path_under_root<'a>(&self, path: &'a Path) -> Option<Cow<'a, Path>> {
        let root = self.ignore_set.path();
        if !path.has_root() || root.as_os_str().is_empty() {
            return Some(Cow::Borrowed(path));
        }
        if let Ok(relative) = path.strip_prefix(root) {
            return Some(Cow::Borrowed(relative));
        }
        let canonical_root = self.canonical_root.as_deref()?;
        let canonical_path = path.canonicalize().ok()?;
        let relative = canonical_path.strip_prefix(canonical_root).ok()?;
        Some(Cow::Owned(relative.to_path_buf()))
    }
}

#[cfg(test)]
mod test {
    use rustfmt_config_proc_macro::nightly_only_test;

    #[nightly_only_test]
    #[test]
    fn test_ignore_path_set() {
        use crate::config::{Config, FileName};
        use crate::ignore_path::IgnorePathSet;
        use std::path::{Path, PathBuf};

        let config = Config::from_toml(
            r#"ignore = ["foo.rs", "bar_dir/*"]"#,
            Path::new("./rustfmt.toml"),
        )
        .unwrap();
        let ignore_path_set = IgnorePathSet::from_ignore_list(&config.ignore()).unwrap();

        assert!(ignore_path_set.is_match(&FileName::Real(PathBuf::from("src/foo.rs"))));
        assert!(ignore_path_set.is_match(&FileName::Real(PathBuf::from("bar_dir/baz.rs"))));
        assert!(!ignore_path_set.is_match(&FileName::Real(PathBuf::from("src/bar.rs"))));
    }

    /// A path OUTSIDE the matcher's root answers "not ignored" instead of
    /// panicking. Before this, `is_match` reached `ignore`'s
    /// `assert!(!path.has_root(), "path is expected to be under the root")`
    /// and aborted the whole run with an ICE dump.
    // Trust: `ignore` is an unstable option, so on a stable channel the config
    // drops it and the first assertion fails. `#[nightly_only_test]` now keeps
    // this test on the `trust` channel (config_proc_macro treats `trust` as
    // nightly, as `is_nightly_channel!` does), so it runs wherever it can pass.
    #[nightly_only_test]
    #[test]
    fn test_ignore_path_set_outside_root_is_not_ignored() {
        use crate::config::{Config, FileName};
        use crate::ignore_path::IgnorePathSet;
        use std::path::{Path, PathBuf};

        let config = Config::from_toml(
            r#"ignore = ["foo.rs", "bar_dir/*"]"#,
            Path::new("/some/root/rustfmt.toml"),
        )
        .unwrap();
        let ignore_path_set = IgnorePathSet::from_ignore_list(&config.ignore()).unwrap();
        // Under the root: matched exactly as before.
        assert!(ignore_path_set.is_match(&FileName::Real(PathBuf::from("/some/root/foo.rs"))));
        // Outside the root: answered, not fatal.
        assert!(!ignore_path_set.is_match(&FileName::Real(PathBuf::from("/elsewhere/foo.rs"))));
        assert!(
            !ignore_path_set.is_match(&FileName::Real(PathBuf::from("/private/tmp/bar_dir/x.rs")))
        );
    }

    #[nightly_only_test]
    #[test]
    fn test_negated_ignore_path_set() {
        use crate::config::{Config, FileName};
        use crate::ignore_path::IgnorePathSet;
        use std::path::{Path, PathBuf};

        let config = Config::from_toml(
            r#"ignore = ["foo.rs", "bar_dir/*", "!bar_dir/*/what.rs"]"#,
            Path::new("./rustfmt.toml"),
        )
        .unwrap();
        let ignore_path_set = IgnorePathSet::from_ignore_list(&config.ignore()).unwrap();
        assert!(ignore_path_set.is_match(&FileName::Real(PathBuf::from("bar_dir/what.rs"))));
        assert!(ignore_path_set.is_match(&FileName::Real(PathBuf::from("bar_dir/baz/a.rs"))));
        assert!(!ignore_path_set.is_match(&FileName::Real(PathBuf::from("bar_dir/baz/what.rs"))));
    }

    // Trust: regression tests for rust-lang/rustfmt#4587 (TRUST-11). Both used
    // to panic in `ignore`'s `matched_path_or_any_parents` with "path is
    // expected to be under the root"; the second one also pins the symlink
    // relation `path_under_root` adds. Both set `ignore`, an unstable option,
    // so both are `#[nightly_only_test]`, for the reason given on
    // `test_ignore_path_set_outside_root_is_not_ignored`: on a stable channel
    // the first would pass vacuously and the second would fail.
    #[nightly_only_test]
    #[test]
    fn test_ignore_path_set_absolute_path_outside_root_is_not_ignored() {
        use crate::config::{Config, FileName};
        use crate::ignore_path::IgnorePathSet;

        let dir = tempfile::tempdir().unwrap();
        let tmp = dir.path().canonicalize().unwrap();
        let root = tmp.join("proj");
        std::fs::create_dir(&root).unwrap();
        let outside = tmp.join("outside.rs");
        std::fs::write(&outside, "").unwrap();

        let config =
            Config::from_toml(r#"ignore = ["outside.rs"]"#, &root.join("rustfmt.toml")).unwrap();
        let ignore_path_set = IgnorePathSet::from_ignore_list(&config.ignore()).unwrap();

        assert!(!ignore_path_set.is_match(&FileName::Real(outside)));
        // `#[path = "/dev/null"] mod m;` names a file that exists outside any root.
        assert!(!ignore_path_set.is_match(&FileName::Real("/dev/null".into())));
        // A path outside the root that does not exist at all.
        assert!(!ignore_path_set.is_match(&FileName::Real(tmp.join("missing/outside.rs"))));
        // A sibling whose name merely extends the root's (`proj` vs `project`).
        let sibling = tmp.join("project");
        std::fs::create_dir(&sibling).unwrap();
        std::fs::write(sibling.join("outside.rs"), "").unwrap();
        assert!(!ignore_path_set.is_match(&FileName::Real(sibling.join("outside.rs"))));
    }

    #[cfg(unix)]
    #[nightly_only_test]
    #[test]
    fn test_ignore_path_set_absolute_path_through_symlink_matches() {
        use crate::config::{Config, FileName};
        use crate::ignore_path::IgnorePathSet;

        let dir = tempfile::tempdir().unwrap();
        let tmp = dir.path().canonicalize().unwrap();
        let root = tmp.join("proj");
        std::fs::create_dir_all(root.join("sub")).unwrap();
        std::fs::write(root.join("sub/ignored.rs"), "").unwrap();
        std::fs::write(root.join("sub/kept.rs"), "").unwrap();
        // The same directory under a second, non-canonical name, as macOS
        // `/tmp` is for `/private/tmp`.
        let link = tmp.join("link");
        std::os::unix::fs::symlink(&root, &link).unwrap();

        let config =
            Config::from_toml(r#"ignore = ["sub/ignored.rs"]"#, &root.join("rustfmt.toml"))
                .unwrap();
        let ignore_path_set = IgnorePathSet::from_ignore_list(&config.ignore()).unwrap();

        assert!(ignore_path_set.is_match(&FileName::Real(root.join("sub/ignored.rs"))));
        assert!(ignore_path_set.is_match(&FileName::Real(link.join("sub/ignored.rs"))));
        assert!(!ignore_path_set.is_match(&FileName::Real(link.join("sub/kept.rs"))));

        // And the other way round: the root spelled through the link, the
        // file spelled canonically.
        let config =
            Config::from_toml(r#"ignore = ["sub/ignored.rs"]"#, &link.join("rustfmt.toml"))
                .unwrap();
        let ignore_path_set = IgnorePathSet::from_ignore_list(&config.ignore()).unwrap();
        assert!(ignore_path_set.is_match(&FileName::Real(root.join("sub/ignored.rs"))));
        assert!(!ignore_path_set.is_match(&FileName::Real(root.join("sub/kept.rs"))));
    }
}
