use super::*;
use std::os::unix::fs::{PermissionsExt as _, symlink};

fn fixture() -> (tempfile::TempDir, PathBuf, Stage, OwnedView, ObjectSource) {
    let world = super::super::super::tests::private_world();
    let root = world.path().canonicalize().unwrap();
    let objects = root.join("objects");
    let leaf = objects.join("aa").join("b".repeat(38));
    std::fs::create_dir_all(leaf.parent().unwrap()).unwrap();
    std::fs::write(&leaf, b"owned private DATA").unwrap();
    let source = ObjectSource::capture_objects(&objects).unwrap();
    let stage = Stage::new(&root.join("destination"), &[&objects]).unwrap();
    let mut view = stage.create_view("source").unwrap();
    source
        .materialize_view(
            &objects,
            &mut view,
            1024,
            &mut CopyBudget::new(1024).unwrap(),
        )
        .unwrap();
    (world, root, stage, view, source)
}

#[test]
fn successful_preflight_closes_only_its_live_views_without_publishing() {
    let (_world, root, mut stage, view, source) = fixture();
    let path = view.path().to_owned();
    source.check_current().unwrap();
    stage.finish_preflight(&mut [view]).unwrap();
    assert!(!path.exists());
    assert!(!root.join("destination").exists());
    assert!(!stage.path().join("git").exists());
    assert!(!stage.published);
    let metadata = stage.path().join(".targo-source-data-state");
    drop(stage);
    assert_eq!(
        std::fs::read(metadata).unwrap(),
        b"targo-source-data-v1\npreflight-observed-views-closed-no-adoption\n"
    );
}

#[test]
fn replaced_view_cannot_redirect_cleanup_into_a_victim() {
    let (_world, root, mut stage, view, _) = fixture();
    let path = view.path().to_owned();
    let moved = root.join("original-view");
    let victim = root.join("victim");
    std::fs::create_dir(&victim).unwrap();
    std::fs::write(victim.join("sentinel"), b"untouched victim").unwrap();
    std::fs::rename(&path, &moved).unwrap();
    symlink(&victim, &path).unwrap();
    assert!(stage.finish_preflight(&mut [view]).is_err());
    assert_eq!(
        std::fs::read(victim.join("sentinel")).unwrap(),
        b"untouched victim"
    );
    assert_eq!(std::fs::read_dir(&victim).unwrap().count(), 1);
    assert_eq!(
        std::fs::read(moved.join("aa").join("b".repeat(38))).unwrap(),
        b"owned private DATA"
    );
}

#[test]
fn different_private_building_child_cannot_receive_a_write_or_be_restored_to_use() {
    let world = super::super::super::tests::private_world();
    let root = world.path().canonicalize().unwrap();
    let stage = Stage::new(&root.join("destination"), &[]).unwrap();
    let mut view = stage.create_view("source").unwrap();
    let parent = view.directory(OsStr::new("aa")).unwrap();
    let child = view.path().join("aa");
    let held = root.join("original-child");
    std::fs::rename(&child, &held).unwrap();
    std::fs::create_dir(&child).unwrap();
    std::fs::set_permissions(&child, std::fs::Permissions::from_mode(0o700)).unwrap();
    std::fs::write(child.join("sentinel"), b"different private directory").unwrap();
    let mut entered = false;
    let failure = view.create_file(parent, OsStr::new("new-object"), |directory| {
        entered = true;
        Ok(File::from(rustix::fs::openat(
            directory,
            "new-object",
            OFlags::WRONLY | OFlags::CREATE | OFlags::EXCL | OFlags::NOFOLLOW,
            Mode::from_bits_truncate(0o600),
        )?))
    });
    assert!(
        failure
            .unwrap_err()
            .to_string()
            .contains("original private view directory identity changed")
    );
    assert!(!entered);
    assert_eq!(std::fs::read_dir(&child).unwrap().count(), 1);
    assert_eq!(
        std::fs::read(child.join("sentinel")).unwrap(),
        b"different private directory"
    );
    std::fs::rename(&child, root.join("replacement-child")).unwrap();
    std::fs::rename(&held, &child).unwrap();
    assert!(view.seal().is_err());
    assert!(std::fs::read_dir(child).unwrap().next().is_none());
}

#[test]
fn sealed_child_clock_change_and_restoration_stays_poisoned() {
    let (_world, _root, _stage, mut view, _) = fixture();
    let child = view.path().join("aa");
    let extra = child.join("temporary-entry");
    // Only the child's namespace changes. The root remains the same sealed
    // original, so the refusal requires a descendant observation.
    std::fs::write(&extra, b"unowned DATA").unwrap();
    view.root.current().unwrap();
    assert!(view.check_current().is_err());
    std::fs::remove_file(&extra).unwrap();
    assert!(
        view.check_current()
            .unwrap_err()
            .to_string()
            .contains("lost its original live ownership")
    );
    assert!(view.cleanup().is_err());
    assert_eq!(
        std::fs::read(child.join("b".repeat(38))).unwrap(),
        b"owned private DATA"
    );
}

#[test]
fn building_callback_bookend_refuses_child_replacement_before_recording() {
    let world = super::super::super::tests::private_world();
    let root = world.path().canonicalize().unwrap();
    let stage = Stage::new(&root.join("destination"), &[]).unwrap();
    let mut view = stage.create_view("source").unwrap();
    let parent = view.directory(OsStr::new("aa")).unwrap();
    let child = view.path().join("aa");
    let held = root.join("original-child");
    let result = view.create_file(parent, OsStr::new("created"), |directory| {
        let file = File::from(rustix::fs::openat(
            directory,
            "created",
            OFlags::WRONLY | OFlags::CREATE | OFlags::EXCL | OFlags::NOFOLLOW,
            Mode::from_bits_truncate(0o600),
        )?);
        std::fs::rename(&child, &held)?;
        std::fs::create_dir(&child)?;
        Ok(file)
    });
    assert!(result.is_err());
    assert!(
        view.files.is_empty(),
        "no creation record after a failed bookend"
    );
    assert!(held.join("created").is_file());
    assert!(std::fs::read_dir(&child).unwrap().next().is_none());
    std::fs::remove_dir(&child).unwrap();
    std::fs::rename(&held, &child).unwrap();
    assert!(view.seal().is_err());
    assert!(child.join("created").is_file());
}

#[test]
fn replaced_file_and_unexpected_entries_are_retained_instead_of_cleaned() {
    for replace in [false, true] {
        let (_world, root, mut stage, view, _) = fixture();
        let victim = root.join("victim");
        std::fs::write(&victim, b"unrelated file bytes").unwrap();
        let name = if replace {
            view.path().join("aa").join("b".repeat(38))
        } else {
            view.path().join("unexpected")
        };
        if replace {
            std::fs::remove_file(&name).unwrap();
        }
        std::fs::hard_link(&victim, &name).unwrap();
        assert!(stage.finish_preflight(&mut [view]).is_err());
        assert_eq!(std::fs::read(&victim).unwrap(), b"unrelated file bytes");
        assert_eq!(std::fs::read(name).unwrap(), b"unrelated file bytes");
    }
}

#[test]
fn cleanup_error_retains_remaining_unknown_data_and_cannot_be_retried() {
    let (_world, _root, _stage, mut view, _) = fixture();
    let unexpected = view.path().join("unexpected");
    assert!(
        view.cleanup_with(|| {
            std::fs::write(&unexpected, b"retained unknown DATA")?;
            Ok(())
        })
        .is_err()
    );
    assert_eq!(
        std::fs::read(&unexpected).unwrap(),
        b"retained unknown DATA"
    );
    assert!(view.cleanup().is_err());
}

#[test]
fn view_owner_cannot_be_substituted_from_another_live_stage() {
    let (_a, _root_a, mut stage_a, view_a, _) = fixture();
    let (_b, _root_b, _stage_b, view_b, _) = fixture();
    let a = view_a.path().to_owned();
    let b = view_b.path().to_owned();
    assert!(stage_a.finish_preflight(&mut [view_b]).is_err());
    assert!(a.join("aa").join("b".repeat(38)).exists());
    assert!(b.join("aa").join("b".repeat(38)).exists());
}

#[test]
fn sealed_pack_reads_require_the_original_file_through_the_callback() {
    use std::io::{Read as _, Write as _};

    let world = super::super::super::tests::private_world();
    let root = world.path().canonicalize().unwrap();
    let stage = Stage::new(&root.join("destination"), &[]).unwrap();
    let mut view = stage.create_view("source").unwrap();
    let parent = view.directory(OsStr::new("pack")).unwrap();
    let name = OsStr::new("fixture.pack");
    view.create_file(parent, name, |directory| {
        let mut file = File::from(rustix::fs::openat(
            directory,
            name,
            OFlags::WRONLY | OFlags::CREATE | OFlags::EXCL | OFlags::NOFOLLOW,
            Mode::from_bits_truncate(0o600),
        )?);
        file.write_all(b"original")?;
        Ok(file)
    })
    .unwrap();
    view.seal().unwrap();
    let pack = view.path().join("pack").join(name);
    let moved = root.join("held-original-pack");
    let victim = root.join("unrelated");
    std::fs::write(&victim, b"replacement bytes").unwrap();
    let mut seen = [0; 8];
    let result = view.read_pack(name, |file, len| {
        assert_eq!(len, 8);
        file.read_exact(&mut seen)?;
        std::fs::rename(&pack, &moved)?;
        symlink(&victim, &pack)?;
        Ok(())
    });
    assert_eq!(&seen, b"original");
    assert!(result.is_err());
    assert_eq!(std::fs::read(&victim).unwrap(), b"replacement bytes");
    std::fs::remove_file(&pack).unwrap();
    std::fs::rename(&moved, &pack).unwrap();
    assert!(
        view.read_pack(name, |_, _| panic!("poisoned view re-entered"))
            .unwrap_err()
            .to_string()
            .contains("lost its original live ownership")
    );
}

#[test]
fn pack_lookup_refusals_poison_the_live_view_before_reading() {
    let (_world, root, _stage, view, _) = fixture();
    let path = view.path().to_owned();
    let held = root.join("original-view");
    std::fs::rename(&path, &held).unwrap();
    std::fs::create_dir(&path).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    assert!(
        view.for_each_pack_index(|_, _, _| panic!("replaced root entered"))
            .is_err()
    );
    std::fs::remove_dir(&path).unwrap();
    std::fs::rename(&held, &path).unwrap();
    assert!(
        view.for_each_pack_index(|_, _, _| panic!("poisoned root re-entered"))
            .unwrap_err()
            .to_string()
            .contains("lost its original live ownership")
    );

    let (_world, _root, _stage, view, _) = fixture();
    assert!(
        view.read_pack(OsStr::new("absent.pack"), |_, _| panic!(
            "unowned file entered"
        ))
        .unwrap_err()
        .to_string()
        .contains("lost its indexed pack")
    );
    assert!(
        view.check_current()
            .unwrap_err()
            .to_string()
            .contains("lost its original live ownership")
    );
}
