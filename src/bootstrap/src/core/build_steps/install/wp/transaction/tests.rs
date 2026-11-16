//! Trust: real filesystem controls, including independent inode and publication races.
use super::*;

fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf) {
    let temp = tempfile::tempdir().unwrap();
    let parent = fs::canonicalize(temp.path()).unwrap();
    let image = parent.join("component");
    fs::create_dir_all(image.join("bin")).unwrap();
    fs::create_dir_all(image.join("lib")).unwrap();
    fs::write(image.join("bin/trustc"), b"compiler fixture").unwrap();
    fs::set_permissions(image.join("bin/trustc"), fs::Permissions::from_mode(0o755)).unwrap();
    fs::write(image.join("lib/private.rmeta"), b"private fixture").unwrap();
    fs::set_permissions(image.join("lib/private.rmeta"), fs::Permissions::from_mode(0o644))
        .unwrap();
    (temp, parent.join("installed"), image)
}

#[test]
fn independent_component_copy_freeze_publish_preserves_source_inodes_and_modes() {
    let (_temp, destination, image) = fixture();
    let source = image.join("lib/private.rmeta");
    let alias = image.join("lib/alias.rmeta");
    fs::hard_link(&source, &alias).unwrap();
    let before = fs::metadata(&source).unwrap();
    let mut publication = Publication::claim(&destination).unwrap();
    assert!(Publication::claim(&destination).is_err(), "destination has one owner");
    copy_image(&Directory::open(&image).unwrap(), &publication.stage).unwrap();
    let copied = publication.stage.path.join("lib/private.rmeta");
    assert!(!same_inode(&before, &fs::metadata(&copied).unwrap()));
    freeze(&publication.stage).unwrap();
    assert_eq!(fs::metadata(&source).unwrap().mode(), before.mode());
    assert_eq!(fs::metadata(&copied).unwrap().mode() & 0o222, 0);
    assert_eq!(
        fs::metadata(publication.stage.path.join("bin/trustc")).unwrap().mode() & 0o777,
        0o555
    );
    let digest = artifact_digest(&publication.stage).unwrap();
    assert!(!destination.exists());
    assert_eq!(publication.publish().unwrap(), destination);
    assert_eq!(artifact_digest(&publication.stage).unwrap(), digest);
    drop(publication);
    fs::write(&source, b"live rebuild").unwrap();
    assert_eq!(fs::read(destination.join("lib/private.rmeta")).unwrap(), b"private fixture");
    assert!(Publication::claim(&destination).is_err());
    cleanup(&Directory::open(&destination).unwrap()).unwrap();
}

#[test]
fn conflicting_components_and_external_links_refuse_without_publishing() {
    let (_temp, destination, image) = fixture();
    let publication = Publication::claim(&destination).unwrap();
    let stage = publication.stage.path.clone();
    let source = Directory::open(&image).unwrap();
    copy_image(&source, &publication.stage).unwrap();
    copy_image(&source, &publication.stage).unwrap();
    fs::write(image.join("bin/trustc"), b"conflicting compiler").unwrap();
    assert!(copy_image(&source, &publication.stage).unwrap_err().contains("conflicting"));
    fs::write(image.join("bin/trustc"), b"compiler fixture").unwrap();
    copy_image(&source, &publication.stage).unwrap();
    std::os::unix::fs::symlink(&destination, image.join("external")).unwrap();
    assert!(copy_image(&source, &publication.stage).is_err());
    drop(publication);
    assert!(!stage.exists());
    assert!(!destination.exists());
}

#[test]
fn same_byte_external_hard_link_is_refused_before_overlap_or_freeze_mutates_it() {
    let (_temp, destination, image) = fixture();
    let publication = Publication::claim(&destination).unwrap();
    let source = Directory::open(&image).unwrap();
    copy_image(&source, &publication.stage).unwrap();
    let staged = publication.stage.path.join("lib/private.rmeta");
    fs::remove_file(&staged).unwrap();
    let original = image.join("lib/private.rmeta");
    let before = fs::metadata(&original).unwrap();
    fs::hard_link(&original, &staged).unwrap();
    assert!(copy_image(&source, &publication.stage).is_err());
    assert!(freeze(&publication.stage).is_err());
    assert!(artifact_digest(&publication.stage).is_err());
    assert_eq!(fs::metadata(&original).unwrap().mode(), before.mode());
    drop(publication);
    assert!(!destination.exists());
    assert_eq!(fs::metadata(&original).unwrap().mode(), before.mode());
}

#[test]
fn racing_existing_empty_directory_is_not_overwritten_and_failed_stage_is_cleaned() {
    let (_temp, destination, image) = fixture();
    let mut publication = Publication::claim(&destination).unwrap();
    let stage = publication.stage.path.clone();
    copy_image(&Directory::open(&image).unwrap(), &publication.stage).unwrap();
    freeze(&publication.stage).unwrap();
    fs::create_dir(&destination).unwrap();
    let competing = fs::metadata(&destination).unwrap();
    assert!(publication.publish().is_err());
    assert!(same_inode(&competing, &fs::metadata(&destination).unwrap()));
    assert!(fs::read_dir(&destination).unwrap().next().is_none());
    drop(publication);
    assert!(!stage.exists(), "readonly abandoned stage is cleaned");
}

#[test]
fn changed_destination_ownership_and_namespace_refuse_without_touching_foreign_entries() {
    let (_temp, destination, image) = fixture();
    let mut publication = Publication::claim(&destination).unwrap();
    copy_image(&Directory::open(&image).unwrap(), &publication.stage).unwrap();
    let lock = publication.parent.path.join(&publication.lock_name);
    fs::rename(&lock, lock.with_extension("previous")).unwrap();
    fs::write(&lock, b"different owner").unwrap();
    assert!(publication.publish().unwrap_err().contains("ownership moved"));
    drop(publication);
    assert_eq!(fs::read(&lock).unwrap(), b"different owner");
    assert!(!destination.exists());
}

#[test]
fn displaced_staging_namespace_is_preserved_and_never_published_or_cleaned_as_ours() {
    let (_temp, destination, image) = fixture();
    let mut publication = Publication::claim(&destination).unwrap();
    copy_image(&Directory::open(&image).unwrap(), &publication.stage).unwrap();
    let original = publication.stage.path.clone();
    let displaced = original.with_extension("displaced");
    fs::rename(&original, &displaced).unwrap();
    fs::create_dir(&original).unwrap();
    fs::write(original.join("foreign"), b"preserve").unwrap();
    assert!(publication.publish().is_err());
    drop(publication);
    assert_eq!(fs::read(original.join("foreign")).unwrap(), b"preserve");
    assert!(!destination.exists());
}

#[test]
fn installation_parent_and_ownership_links_fail_closed() {
    let (_temp, destination, _image) = fixture();
    let parent = destination.parent().unwrap();
    fs::set_permissions(parent, fs::Permissions::from_mode(0o777)).unwrap();
    assert!(Publication::claim(&destination).is_err());
    fs::set_permissions(parent, fs::Permissions::from_mode(0o700)).unwrap();
    let lock = parent.join(".installed.trust-wp-installation.lock");
    let external = parent.join("external");
    fs::write(&external, b"preserve").unwrap();
    std::os::unix::fs::symlink(&external, &lock).unwrap();
    assert!(Publication::claim(&destination).is_err());
    assert_eq!(fs::read(&external).unwrap(), b"preserve");
}

#[test]
fn clean_source_must_still_name_the_selected_current_commit() {
    crate::utils::tests::git::git_test(|git| {
        let executable = git.get_path().join("executable");
        fs::write(&executable, vec![b'x'; 65537]).unwrap();
        fs::set_permissions(&executable, fs::Permissions::from_mode(0o755)).unwrap();
        let link = git.get_path().join("source-link");
        std::os::unix::fs::symlink("README.md", &link).unwrap();
        let selected = git.commit();
        require_clean_source(git.get_path(), &selected).unwrap();
        fs::remove_file(&link).unwrap();
        std::os::unix::fs::symlink("README.tx", &link).unwrap();
        assert!(
            source::require_committed_tree(git.get_path(), &selected)
                .unwrap_err()
                .contains("committed bytes")
        );
        fs::remove_file(&link).unwrap();
        std::os::unix::fs::symlink("README.md", &link).unwrap();
        require_clean_source(git.get_path(), &selected).unwrap();
        git.write("README.md", "source changed");
        assert!(require_clean_source(git.get_path(), &selected).is_err());
        let next = git.commit();
        assert_ne!(selected, next);
        assert!(
            require_clean_source(git.get_path(), &selected).unwrap_err().contains("HEAD moved")
        );
        require_clean_source(git.get_path(), &next).unwrap();
    });
}

#[test]
fn source_config_or_native_input_movement_cannot_earn_completion() {
    let original = cache::InputSnapshot::from("original observed inputs");
    inputs_unchanged(&original, &cache::InputSnapshot::from("original observed inputs")).unwrap();
    assert!(
        inputs_unchanged(&original, &cache::InputSnapshot::from("changed observed inputs"))
            .is_err()
    );
}

#[test]
fn redirected_git_worktree_or_alternate_index_cannot_hide_dirty_source() {
    const TEST: &str = "core::build_steps::install::wp::transaction::tests::redirected_git_worktree_or_alternate_index_cannot_hide_dirty_source";
    if let Some(root) = std::env::var_os("TRUST_WP_INSTALL_GIT_CONTROL_ROOT") {
        let expected = std::env::var("TRUST_WP_INSTALL_GIT_CONTROL_COMMIT").unwrap();
        assert!(require_clean_source(Path::new(&root), &expected).is_err());
        return;
    }
    crate::utils::tests::git::git_test(|git| {
        let selected = git.get_current_commit();
        let temp = tempfile::tempdir().unwrap();
        let clean_worktree = temp.path().join("clean-worktree");
        fs::create_dir(&clean_worktree).unwrap();
        fs::copy(git.get_path().join("README.md"), clean_worktree.join("README.md")).unwrap();
        let alternate_index = temp.path().join("alternate-index");
        fs::copy(git.get_path().join(".git/index"), &alternate_index).unwrap();
        let output = std::process::Command::new("git")
            .current_dir(git.get_path())
            .env("GIT_INDEX_FILE", &alternate_index)
            .args(["update-index", "--skip-worktree", "README.md"])
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        git.write("README.md", "real source changed");
        require_clean_source(git.get_path(), &selected).unwrap_err();
        for alternate in [false, true] {
            let mut command = crate::test_entry::uncaptured_actor(std::process::Command::new(
                std::env::current_exe().unwrap(),
            ));
            command
                .args(["--exact", TEST, "--nocapture"])
                .env("TRUST_WP_INSTALL_GIT_CONTROL_ROOT", git.get_path())
                .env("TRUST_WP_INSTALL_GIT_CONTROL_COMMIT", &selected);
            if alternate {
                command.env("GIT_INDEX_FILE", &alternate_index);
            } else {
                command
                    .env("GIT_DIR", git.get_path().join(".git"))
                    .env("GIT_WORK_TREE", &clean_worktree);
            }
            // Establish that the actual ambient redirect would hide these bytes.
            let mut redirected = std::process::Command::new("git");
            redirected.current_dir(git.get_path()).args(["status", "--porcelain=v1"]);
            if alternate {
                redirected.env("GIT_INDEX_FILE", &alternate_index);
            } else {
                redirected
                    .env("GIT_DIR", git.get_path().join(".git"))
                    .env("GIT_WORK_TREE", &clean_worktree);
            }
            let output = redirected.output().unwrap();
            assert!(
                output.status.success() && output.stdout.is_empty(),
                "redirect must really hide the dirty source: {output:?}"
            );
            let output = command.output().unwrap();
            assert!(
                output.status.success(),
                "sanitized native authority must retain the refusal: {output:?}"
            );
        }
    });
}

#[test]
fn configured_git_worktree_cannot_hide_changes_in_the_observed_source_root() {
    crate::utils::tests::git::git_test(|git| {
        let selected = git.get_current_commit();
        require_clean_source(git.get_path(), &selected).unwrap();
        let temp = tempfile::tempdir().unwrap();
        let alias = temp.path().join("source-alias");
        std::os::unix::fs::symlink(git.get_path(), &alias).unwrap();
        require_clean_source(&alias, &selected).unwrap();
        let clean_worktree = temp.path().join("clean-worktree");
        fs::create_dir(&clean_worktree).unwrap();
        fs::copy(git.get_path().join("README.md"), clean_worktree.join("README.md")).unwrap();
        git.write("README.md", "observed source changed");
        assert!(require_clean_source(git.get_path(), &selected).is_err());
        git.run_git(&["config", "core.worktree", clean_worktree.to_str().unwrap()]);
        // The same sanitized Git authority now sees the configured clean tree,
        // while the installation observes the changed bytes in the real root.
        assert!(cache::git(git.get_path(), &["status", "--porcelain=v1"]).unwrap().is_empty());
        assert_eq!(
            fs::canonicalize(git.run_git(&["rev-parse", "--show-toplevel"])).unwrap(),
            fs::canonicalize(&clean_worktree).unwrap()
        );
        assert_ne!(
            fs::read(git.get_path().join("README.md")).unwrap(),
            fs::read(clean_worktree.join("README.md")).unwrap()
        );
        assert!(require_clean_source(git.get_path(), &selected).unwrap_err().contains("worktree"));
    });
}

#[test]
fn stat_cache_cannot_hide_changed_committed_source_bytes() {
    crate::utils::tests::git::git_test(|git| {
        let source = git.get_path().join("README.md");
        fs::write(&source, b"AAAA\n").unwrap();
        let old = std::time::UNIX_EPOCH + std::time::Duration::from_secs(946684800);
        File::open(&source).unwrap().set_modified(old).unwrap();
        let selected = git.commit();
        require_clean_source(git.get_path(), &selected).unwrap();
        git.run_git(&["config", "core.trustctime", "false"]);
        git.run_git(&["config", "core.checkStat", "minimal"]);
        fs::write(&source, b"BBBB\n").unwrap();
        File::open(&source).unwrap().set_modified(old).unwrap();
        assert!(cache::git(git.get_path(), &["status", "--porcelain=v1"]).unwrap().is_empty());
        assert_eq!(git.run_git(&["ls-files", "-v", "README.md"]), "H README.md");
        assert_eq!(git.get_current_commit(), selected);
        assert_ne!(
            cache::git(git.get_path(), &["rev-parse", "HEAD:README.md"]).unwrap(),
            cache::git(git.get_path(), &["hash-object", "--no-filters", "--", "README.md"])
                .unwrap()
        );
        let error = require_clean_source(git.get_path(), &selected).unwrap_err();
        assert!(error.contains("committed bytes"), "{error}");
        let observed = fs::canonicalize(git.get_path()).unwrap().join("README.md");
        assert!(error.ends_with(&format!(": {}", observed.display())), "{error}");
        for changed in [b"".as_slice(), b"AAAA\ntrailing".as_slice()] {
            fs::write(&source, changed).unwrap();
            let error = source::require_committed_tree(git.get_path(), &selected).unwrap_err();
            assert!(error.contains("committed bytes"), "{error}");
            assert!(error.ends_with(&format!(": {}", observed.display())), "{error}");
        }
        fs::write(&source, b"AAAA\n").unwrap();
        File::open(&source).unwrap().set_modified(old).unwrap();
        require_clean_source(git.get_path(), &selected).unwrap();
        git.run_git(&["config", "core.filemode", "false"]);
        fs::set_permissions(&source, fs::Permissions::from_mode(0o744)).unwrap();
        assert!(cache::git(git.get_path(), &["status", "--porcelain=v1"]).unwrap().is_empty());
        let error = require_clean_source(git.get_path(), &selected).unwrap_err();
        assert!(error.contains("committed mode"), "{error}");
        assert!(error.ends_with(&format!(": {}", observed.display())), "{error}");
    });
}

#[test]
fn hidden_tracked_source_flags_refuse_even_when_git_status_is_clean() {
    crate::utils::tests::git::git_test(|git| {
        let selected = git.get_current_commit();
        for (set, clear) in [
            ("--assume-unchanged", "--no-assume-unchanged"),
            ("--skip-worktree", "--no-skip-worktree"),
        ] {
            git.run_git(&["update-index", set, "README.md"]);
            git.write("README.md", "hidden source changed");
            assert_eq!(git.run_git(&["status", "--porcelain=v1"]), "");
            assert!(
                require_clean_source(git.get_path(), &selected).unwrap_err().contains("hidden")
            );
            git.run_git(&["update-index", clear, "README.md"]);
            git.run_git(&["checkout", "HEAD", "--", "README.md"]);
            require_clean_source(git.get_path(), &selected).unwrap();
        }
    });
}

#[test]
fn hidden_source_flags_inside_a_matching_gitlink_also_refuse() {
    crate::utils::tests::git::git_test(|parent| {
        crate::utils::tests::git::git_test(|child| {
            parent.run_git(&[
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                child.get_path().to_str().unwrap(),
                "nested",
            ]);
            let selected = parent.commit();
            require_clean_source(parent.get_path(), &selected).unwrap();
            let nested = parent.get_path().join("nested");
            cache::git(&nested, &["update-index", "--assume-unchanged", "README.md"]).unwrap();
            fs::write(nested.join("README.md"), "hidden child source changed").unwrap();
            assert!(
                cache::git(
                    parent.get_path(),
                    &["status", "--porcelain=v1", "--ignore-submodules=none"]
                )
                .unwrap()
                .is_empty()
            );
            assert!(
                require_clean_source(parent.get_path(), &selected).unwrap_err().contains("hidden")
            );
        });
    });
}

#[test]
fn replacement_commit_cannot_label_different_clean_bytes_with_the_selected_raw_commit() {
    crate::utils::tests::git::git_test(|git| {
        let selected = git.get_current_commit();
        git.write("README.md", "different committed tree");
        let other = git.commit();
        // Keep index/worktree at B while HEAD names A; replacement makes
        // ordinary status report clean for B's bytes under A's raw name.
        git.run_git(&["update-ref", "HEAD", &selected]);
        git.run_git(&["replace", &selected, &other]);
        assert_eq!(git.run_git(&["status", "--porcelain=v1"]), "");
        assert!(!git.run_git(&["--no-replace-objects", "status", "--porcelain=v1"]).is_empty());
        assert!(
            require_clean_source(git.get_path(), &selected)
                .unwrap_err()
                .contains("replacement refs")
        );
    });
}
