use super::*;
use std::os::unix::fs::{PermissionsExt as _, symlink};

fn world() -> (tempfile::TempDir, PathBuf) {
    let world = super::super::tests::private_world();
    let path = world.path().canonicalize().unwrap();
    (world, path)
}

#[test]
fn writable_parent_refuses_before_creating_a_container() {
    let (_world, root) = world();
    std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o777)).unwrap();
    let result = Stage::new(&root.join("home"), &[&root.join("donor")]);
    std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700)).unwrap();
    assert!(result.is_err());
    assert!(std::fs::read_dir(root).unwrap().next().is_none());
}

#[test]
fn replaced_container_cannot_redirect_the_first_child_write_into_a_victim() {
    let (_world, root) = world();
    let victim = root.join("victim");
    std::fs::create_dir(&victim).unwrap();
    std::fs::write(victim.join("sentinel"), b"unchanged victim").unwrap();
    let moved = root.join("original-container");
    let result = Stage::new_with(&root.join("output"), &[&root.join("donor")], |container| {
        std::fs::rename(container, &moved)?;
        symlink(&victim, container)?;
        Ok(())
    });
    assert!(result.is_err());
    assert_eq!(
        std::fs::read(victim.join("sentinel")).unwrap(),
        b"unchanged victim"
    );
    assert_eq!(std::fs::read_dir(&victim).unwrap().count(), 1);
    assert!(!moved.join("home").exists());
}

#[test]
fn later_container_replacement_refuses_before_creating_a_data_view() {
    let (_world, root) = world();
    let stage = Stage::new(&root.join("output"), &[&root.join("donor")]).unwrap();
    let victim = root.join("victim");
    std::fs::create_dir(&victim).unwrap();
    let moved = root.join("original-container");
    std::fs::rename(&stage.container.path, &moved).unwrap();
    symlink(&victim, &stage.container.path).unwrap();
    assert!(stage.create_view("database").is_err());
    drop(stage);
    assert!(std::fs::read_dir(&victim).unwrap().next().is_none());
}

#[test]
fn hardlinked_marker_replacement_never_truncates_the_victim() {
    let (_world, root) = world();
    let stage = Stage::new(&root.join("output"), &[&root.join("donor")]).unwrap();
    let marker = stage.path().join(".targo-source-data-state");
    let victim = root.join("victim");
    std::fs::write(&victim, b"foreign inode must remain intact").unwrap();
    std::fs::remove_file(&marker).unwrap();
    std::fs::hard_link(&victim, &marker).unwrap();
    assert!(stage.state(b"must not be written").is_err());
    drop(stage);
    assert_eq!(
        std::fs::read(victim).unwrap(),
        b"foreign inode must remain intact"
    );
}

#[test]
fn post_rename_failure_reports_committed_data_without_quarantine_or_rollback() {
    let (_world, root) = world();
    let destination = root.join("output");
    let mut stage = Stage::new(&destination, &[&root.join("donor")]).unwrap();
    let failure = stage.publish_with(|_| anyhow::bail!("injected post-rename observation failure"));
    assert!(
        failure
            .unwrap_err()
            .to_string()
            .contains("has been published")
    );
    assert!(stage.published);
    drop(stage);
    assert!(destination.is_dir());
    assert_eq!(
        std::fs::read(destination.join(".targo-source-data-state")).unwrap(),
        b"targo-source-data-v1\ncomplete-data-not-authority\n"
    );
}

#[test]
fn every_input_is_checked_for_overlap_before_the_first_staging_write() {
    let (_world, root) = world();
    let destination = root.join("output");
    assert!(Stage::new(&destination, &[&root.join("separate-input"), &root]).is_err());
    assert!(std::fs::read_dir(root).unwrap().next().is_none());
}

#[test]
fn standalone_object_copy_refuses_late_byte_or_root_namespace_changes() {
    for replace_root in [false, true] {
        let (_world, root) = world();
        let objects = root.join("objects");
        let directory = objects.join("aa");
        std::fs::create_dir_all(&directory).unwrap();
        let leaf = "b".repeat(38);
        let source = directory.join(&leaf);
        std::fs::write(&source, b"original object DATA").unwrap();
        let snapshot = ObjectSource::capture_objects(&objects).unwrap();
        let view = root.join("view");
        let result = snapshot.materialize_objects_with(
            &objects,
            &view,
            1024,
            &mut CopyBudget::new(1024).unwrap(),
            true,
            || {
                if replace_root {
                    std::fs::rename(&objects, root.join("original-objects"))?;
                    std::fs::create_dir(&objects)?;
                } else {
                    std::fs::write(&source, b"changed object DATA")?;
                }
                Ok(())
            },
        );
        assert!(result.is_err());
        assert_eq!(
            std::fs::read(view.join("aa").join(leaf)).unwrap(),
            b"original object DATA"
        );
    }
}

fn object_data(root: &Path, name: &str, bytes: &[u8]) -> (ObjectSource, PathBuf, PathBuf) {
    let objects = root.join(name);
    let leaf = objects.join("aa").join("b".repeat(38));
    std::fs::create_dir_all(leaf.parent().unwrap()).unwrap();
    std::fs::write(&leaf, bytes).unwrap();
    (
        ObjectSource::capture_objects(&objects).unwrap(),
        objects,
        leaf,
    )
}

#[test]
fn scoped_source_descendant_refuses_replacement_and_restoration_does_not_rearm_it() {
    for replace_during_scope in [false, true] {
        let (_world, root) = world();
        let objects = root.join("objects");
        let child = objects.join("info/child");
        std::fs::create_dir_all(&child).unwrap();
        std::fs::write(child.join("original"), b"source DATA").unwrap();
        let held = root.join("original-child");
        let source = ObjectSource::capture_objects(&objects).unwrap();
        let replace = || {
            std::fs::rename(&child, &held).unwrap();
            std::fs::create_dir(&child).unwrap();
            // This changes a recorded descendant, not the provider root.
            source.root.current().unwrap();
        };
        if !replace_during_scope {
            replace();
        }
        let mut entered = false;
        let result = source.with_directory(&child, |_| {
            entered = true;
            replace();
            Ok(())
        });
        assert!(result.is_err());
        assert_eq!(entered, replace_during_scope);
        std::fs::remove_dir(&child).unwrap();
        std::fs::rename(&held, &child).unwrap();
        assert!(
            source
                .check_current()
                .unwrap_err()
                .to_string()
                .contains("source object observation has failed")
        );
        assert_eq!(
            std::fs::read(child.join("original")).unwrap(),
            b"source DATA"
        );
    }
}

#[test]
fn fallback_copy_budget_is_shared_across_real_materializations() {
    let (_world, root) = world();
    let (first, first_root, first_leaf) = object_data(&root, "first", b"0123456789");
    let (second, second_root, second_leaf) = object_data(&root, "second", b"01234567890123456789");
    let mut budget = CopyBudget::new(10).unwrap();
    // Suppress only the optional native-clone attempt. The production fallback
    // performs real reads/writes using the original held-directory snapshot.
    let first_view = root.join("first-view");
    let copied = first
        .materialize_objects_with(
            &first_root,
            &first_view,
            1024,
            &mut budget,
            false,
            || Ok(()),
        )
        .unwrap();
    assert_eq!(
        (
            copied.bytes,
            copied.streamed_bytes,
            copied.cloned_files,
            copied.cloned_bytes
        ),
        (10, 10, 0, 0)
    );
    assert_eq!(
        std::fs::read(first_view.join("aa").join("b".repeat(38))).unwrap(),
        b"0123456789"
    );
    let second_view = root.join("second-view");
    let refused = second.materialize_objects_with(
        &second_root,
        &second_view,
        1024,
        &mut budget,
        false,
        || Ok(()),
    );
    let target = second_view.join("aa").join("b".repeat(38));
    let written = std::fs::metadata(&target)
        .map(|metadata| metadata.len())
        .unwrap_or(0);
    std::fs::write(
        root.join("fallback-budget-outcome.txt"),
        format!(
            "first_streamed={}\nsecond_written={written}\nsecond_refused={}\n",
            copied.streamed_bytes,
            refused.is_err()
        ),
    )
    .unwrap();
    assert!(
        refused
            .err()
            .unwrap()
            .to_string()
            .contains("stream-copy budget exceeded")
    );
    assert_eq!(written, 0);
    assert_eq!(budget.remaining, 0);
    assert_eq!(std::fs::read(first_leaf).unwrap(), b"0123456789");
    assert_eq!(std::fs::read(second_leaf).unwrap(), b"01234567890123456789");

    let mut allowed = CopyBudget::new(30).unwrap();
    let a = first
        .materialize_objects_with(
            &first_root,
            &root.join("allowed-first"),
            1024,
            &mut allowed,
            false,
            || Ok(()),
        )
        .unwrap();
    let b = second
        .materialize_objects_with(
            &second_root,
            &root.join("allowed-second"),
            1024,
            &mut allowed,
            false,
            || Ok(()),
        )
        .unwrap();
    assert_eq!(
        (a.streamed_bytes + b.streamed_bytes, allowed.remaining),
        (30, 0)
    );
    assert!(CopyBudget::new(super::super::MAX_TOTAL_BYTES + 1).is_err());
}

#[test]
fn native_clone_and_stream_counters_describe_the_actual_completed_view() {
    let (_world, root) = world();
    let bytes = b"native clone or bounded stream DATA";
    let (snapshot, objects, _) = object_data(&root, "objects", bytes);
    let mut budget = CopyBudget::new(bytes.len() as u64).unwrap();
    let view = root.join("view");
    let copied = snapshot
        .materialize_objects(&objects, &view, 1024, &mut budget)
        .unwrap();
    assert_eq!(copied.bytes, bytes.len() as u64);
    assert_eq!(copied.cloned_bytes + copied.streamed_bytes, copied.bytes);
    assert_eq!(copied.cloned_files, u64::from(copied.cloned_bytes != 0));
    assert_eq!(budget.remaining, bytes.len() as u64 - copied.streamed_bytes);
    assert_eq!(
        std::fs::read(view.join("aa").join("b".repeat(38))).unwrap(),
        bytes
    );
}
