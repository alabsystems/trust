//! Trust: actual raw Git observations exercise bounded descriptor reuse and refusals.

use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::PathBuf;

use super::*;
use crate::utils::tests::git::{GitCtx, git_test};

fn adjacent_tree(git: &GitCtx) -> String {
    git.write("nested/deep/a", "first committed file");
    git.write("nested/deep/b", "second committed file");
    git.commit()
}

#[test]
fn adjacent_entries_reuse_one_parent_and_parent_changes_reopen_the_chain() {
    git_test(|git| {
        git.write("a/deep/a.bin", "create parent");
        fs::write(git.get_path().join("a/deep/a.bin"), vec![b'x'; 131073]).unwrap();
        git.write("a/deep/b.exec", "executable");
        fs::set_permissions(
            git.get_path().join("a/deep/b.exec"),
            fs::Permissions::from_mode(0o755),
        )
        .unwrap();
        symlink("a.bin", git.get_path().join("a/deep/c.link")).unwrap();
        git.write("a/deep/more/child", "nested child");
        git.write("a/deep/z", "return to previous parent");
        git.write("b/deep/a", "other parent first");
        git.write("b/deep/b", "other parent second");
        git.write("z", "root file");
        let selected = git.commit();
        let root = fs::canonicalize(git.get_path()).unwrap();
        let mut opened = Vec::new();
        let mut ready = Vec::new();
        require_committed_tree_with_hooks(
            git.get_path(),
            &selected,
            |_| {},
            |path| opened.push(path.strip_prefix(&root).unwrap().to_owned()),
            |path| ready.push(path.to_owned()),
        )
        .unwrap();
        assert_eq!(
            opened,
            ["a", "a/deep", "a", "a/deep", "a/deep/more", "a", "a/deep", "b", "b/deep",]
                .map(PathBuf::from),
            "count actual successful Directory::child operations, including cache eviction"
        );
        assert_eq!(ready.len(), 9, "all committed file, executable and symlink rows were observed");
        super::super::require_clean_source(git.get_path(), &selected).unwrap();
    });
}

#[test]
fn a_reused_parent_is_rechecked_before_observing_the_next_entry() {
    for change in ["directory", "parent-symlink", "ancestor-symlink"] {
        git_test(|git| {
            let selected = adjacent_tree(git);
            let root = fs::canonicalize(git.get_path()).unwrap();
            let parent = root.join("nested/deep");
            let displaced = root.join("displaced");
            let mut changed = false;
            let mut opened = 0;
            let mut ready = Vec::new();
            let result = require_committed_tree_with_hooks(
                git.get_path(),
                &selected,
                |path| {
                    if path != Path::new("nested/deep/b") {
                        return;
                    }
                    changed = true;
                    match change {
                        "directory" => {
                            fs::rename(&parent, &displaced).unwrap();
                            fs::create_dir(&parent).unwrap();
                            for file in ["a", "b"] {
                                fs::copy(displaced.join(file), parent.join(file)).unwrap();
                            }
                        }
                        "parent-symlink" => {
                            fs::rename(&parent, &displaced).unwrap();
                            symlink(&displaced, &parent).unwrap();
                        }
                        "ancestor-symlink" => {
                            fs::rename(root.join("nested"), &displaced).unwrap();
                            symlink("displaced", root.join("nested")).unwrap();
                        }
                        _ => unreachable!(),
                    }
                },
                |_| opened += 1,
                |path| ready.push(path.to_owned()),
            );
            assert!(changed, "the mutation reached the adjacent-entry reuse boundary");
            assert!(result.unwrap_err().contains("namespace moved"), "{change}");
            assert_eq!(opened, 2, "the prior parent descriptor was retained: {change}");
            assert_eq!(
                ready.iter().filter(|path| path.starts_with("nested/deep")).count(),
                1,
                "the second entry must refuse before any source observation: {change}"
            );
        });
    }
}

#[test]
fn reused_parents_keep_raw_byte_executable_mode_and_symlink_target_refusals() {
    for change in ["bytes", "mode", "link", "link-mode"] {
        git_test(|git| {
            let mut selected = adjacent_tree(git);
            let second = git.get_path().join("nested/deep/b");
            if matches!(change, "link" | "link-mode") {
                fs::remove_file(&second).unwrap();
                symlink("a", &second).unwrap();
                selected = git.commit();
            }
            let mut changed = false;
            let mut opened = 0;
            let mut ready = Vec::new();
            let result = require_committed_tree_with_hooks(
                git.get_path(),
                &selected,
                |path| {
                    if path != Path::new("nested/deep/b") {
                        return;
                    }
                    changed = true;
                    match change {
                        "bytes" => fs::write(&second, b"different bytes").unwrap(),
                        "mode" => {
                            fs::set_permissions(&second, fs::Permissions::from_mode(0o755)).unwrap()
                        }
                        "link" => {
                            fs::remove_file(&second).unwrap();
                            symlink("different-target", &second).unwrap();
                        }
                        "link-mode" => {
                            fs::remove_file(&second).unwrap();
                            fs::write(&second, b"a").unwrap();
                        }
                        _ => unreachable!(),
                    }
                },
                |_| opened += 1,
                |path| ready.push(path.to_owned()),
            );
            assert!(changed);
            let expected = match change {
                "mode" => "committed mode",
                "link-mode" => "committed symlink mode",
                _ => "committed bytes",
            };
            let error = result.unwrap_err();
            assert!(error.contains(expected), "{change}: {error}");
            let observed = fs::canonicalize(git.get_path()).unwrap().join("nested/deep/b");
            assert!(error.ends_with(&format!(": {}", observed.display())), "{change}: {error}");
            assert_eq!(opened, 2, "the refusal exercised a reused parent: {change}");
            assert!(ready.contains(&PathBuf::from("nested/deep/b")));
        });
    }
}

#[test]
fn raw_comparison_refuses_normalized_clean_worktree_bytes_after_parent_reuse() {
    git_test(|git| {
        git.write(".gitattributes", "nested/deep/b text eol=crlf");
        git.write("nested/deep/a", "first file");
        fs::write(git.get_path().join("nested/deep/b"), b"normalized line\r\n").unwrap();
        let selected = git.commit();
        assert!(cache::git(git.get_path(), &["status", "--porcelain=v1"]).unwrap().is_empty());
        assert_eq!(
            cache::git(git.get_path(), &["show", "HEAD:nested/deep/b"]).unwrap(),
            b"normalized line\n"
        );
        let mut opened = 0;
        let result = require_committed_tree_with_hooks(
            git.get_path(),
            &selected,
            |_| {},
            |_| opened += 1,
            |_| {},
        );
        let error = result.unwrap_err();
        assert!(error.contains("committed bytes"), "{error}");
        let observed = fs::canonicalize(git.get_path()).unwrap().join("nested/deep/b");
        assert!(error.ends_with(&format!(": {}", observed.display())), "{error}");
        assert_eq!(opened, 2, "the raw-byte refusal follows a same-parent entry");
    });
}
