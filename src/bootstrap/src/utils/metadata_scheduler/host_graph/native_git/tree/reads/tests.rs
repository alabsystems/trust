//! Real local Git objects, physical reads and an actual protected source scope.
//! These do not construct a Host, native selector completion, Seed or SDK.
use std::fs;
use std::os::fd::AsRawFd as _;
use std::os::unix::fs::{PermissionsExt as _, symlink};
use std::time::Duration;

use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
};

use super::super::tests::fixture;
use super::*;

struct World {
    source: Arc<OriginalSourceRoot>,
    rows: RepositoryRows,
    end: Instant,
    _scope: ProtectedWorkScope,
    _directory: tempfile::TempDir,
}
fn make_world() -> World {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    fs::write(root.join("Cargo.toml"), b"[package]\nname='source-row-fixture'\n").unwrap();
    fs::create_dir(root.join("nested")).unwrap();
    fs::write(root.join("nested/Cargo.toml"), b"[package]\nname='source-row-fixture'\n").unwrap();
    // Match the actual committed modes even under a restrictive caller umask.
    // Physical mode validation below must continue rejecting different modes.
    for path in ["Cargo.toml", "nested/Cargo.toml"] {
        fs::set_permissions(root.join(path), fs::Permissions::from_mode(0o644)).unwrap();
    }
    symlink("Cargo.toml", root.join("link")).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual committed selected-read control".into(),
            contract: "original source custody only; no Host/Seed/SDK completion".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected private source contention"),
    };
    let end = Instant::now() + Duration::from_secs(30);
    let scope = ProtectedWorkScope::new(Arc::new(lease.into_withheld().unwrap()), end).unwrap();
    let source = Arc::new(scope.original_source(&root).unwrap());
    let rows = super::super::read_repository(source.directory().unwrap(), &root, end).unwrap();
    World { source, rows, end, _scope: scope, _directory: directory }
}
fn selected(world: &World) -> HeldSourceReadSet {
    HeldSourceReadSet::capture(world.source.directory().unwrap(), world.end).unwrap()
}
fn expected(world: &World, path: &[u8]) -> SourceRead {
    match world.rows.lookup(path, world.end).unwrap() {
        CommittedLookup::Present(entry) => match entry.mode {
            0o100644 | 0o100755 => SourceRead::File {
                mode: entry.mode,
                bytes: committed_blob(&world.rows, entry.object, world.end).unwrap(),
            },
            0o120000 => SourceRead::Link {
                target: committed_blob(&world.rows, entry.object, world.end).unwrap(),
            },
            0o040000 => SourceRead::Directory,
            _ => panic!("test did not resolve the original gitlink"),
        },
        CommittedLookup::Absent => SourceRead::Absent,
        CommittedLookup::Unresolved(_) => panic!("test crossed an unresolved original boundary"),
    }
}
fn observe(world: &World, reads: &mut HeldSourceReadSet, path: &str) -> io::Result<SourceRead> {
    reads.observe(world.source.directory()?, Path::new(path), expected(world, path.as_bytes()))
}

#[test]
fn actual_committed_read_keeps_physical_inputs_and_original_source_hold() {
    let world = make_world();
    let mut reads = selected(&world);
    assert!(matches!(
        observe(&world, &mut reads, "Cargo.toml").unwrap(),
        SourceRead::File { mode: 0o100644, .. }
    ));
    assert!(matches!(
        observe(&world, &mut reads, "nested/Cargo.toml").unwrap(),
        SourceRead::File { .. }
    ));
    observe(&world, &mut reads, "Cargo.toml").unwrap();
    reads.check_current(world.source.directory().unwrap()).unwrap();
    world.source.check_current().unwrap();
    drop(reads);
    assert!(!Manager::open(world.source.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn prospective_config_keeps_first_missing_anchor_and_cannot_recover_after_appearance() {
    let world = make_world();
    let mut reads = selected(&world);
    assert!(matches!(
        observe(&world, &mut reads, "nested/.cargo/config.toml").unwrap(),
        SourceRead::Absent
    ));
    assert_eq!(reads.selected_population(), 3);
    fs::create_dir(world.source.path().join("nested/.cargo")).unwrap();
    assert!(reads.check_current(world.source.directory().unwrap()).is_err());
    fs::remove_dir(world.source.path().join("nested/.cargo")).unwrap();
    assert!(reads.check_current(world.source.directory().unwrap()).is_err());
}

#[test]
fn committed_literal_link_and_selected_glob_directory_keep_physical_membership() {
    let world = make_world();
    let mut reads = selected(&world);
    assert!(matches!(observe(&world, &mut reads, "link").unwrap(), SourceRead::Link { .. }));
    fs::remove_file(world.source.path().join("link")).unwrap();
    symlink("nested/Cargo.toml", world.source.path().join("link")).unwrap();
    assert!(reads.check_current(world.source.directory().unwrap()).is_err());

    let world = make_world();
    let mut reads = selected(&world);
    assert!(matches!(observe(&world, &mut reads, "nested").unwrap(), SourceRead::Directory));
    fs::write(world.source.path().join("nested/untracked"), b"new Cargo glob candidate").unwrap();
    assert!(reads.check_current(world.source.directory().unwrap()).is_err());
}

#[test]
fn altered_file_mode_bytes_and_aliases_refuse_before_returning_selected_data() {
    for changed in ["bytes", "mode", "special-mode", "hardlink", "link"] {
        let world = make_world();
        let wanted = expected(&world, b"Cargo.toml");
        let path = world.source.path().join("Cargo.toml");
        match changed {
            "bytes" => fs::write(&path, b"uncommitted substitute").unwrap(),
            "mode" => fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap(),
            "special-mode" => {
                fs::set_permissions(&path, fs::Permissions::from_mode(0o4644)).unwrap()
            }
            "hardlink" => fs::hard_link(&path, world.source.path().join("other")).unwrap(),
            "link" => {
                fs::remove_file(&path).unwrap();
                symlink("nested/Cargo.toml", &path).unwrap();
            }
            _ => unreachable!(),
        }
        let mut reads = selected(&world);
        assert!(
            reads
                .observe(world.source.directory().unwrap(), Path::new("Cargo.toml"), wanted)
                .is_err(),
            "{changed}"
        );
        assert!(reads.check_current(world.source.directory().unwrap()).is_err());
    }
}

#[test]
fn unreadable_selected_blob_never_falls_back_to_the_present_physical_source() {
    for missing in [true, false] {
        let world = make_world();
        let CommittedLookup::Present(entry) = world.rows.lookup(b"Cargo.toml", world.end).unwrap()
        else {
            panic!()
        };
        let id = entry.object;
        let hex = id.to_string();
        let object = world.source.path().join(".git/objects").join(&hex[..2]).join(&hex[2..]);
        if missing {
            fs::remove_file(object).unwrap();
        } else {
            fs::set_permissions(&object, fs::Permissions::from_mode(0o600)).unwrap();
            fs::write(object, b"corrupt ordinary object body").unwrap();
        }
        assert!(world.source.path().join("Cargo.toml").is_file());
        assert!(committed_blob(&world.rows, id, world.end).is_err());
    }
}

#[test]
fn physical_readset_deadline_and_uncommitted_present_inputs_cannot_be_reinterpreted() {
    let world = make_world();
    fs::write(world.source.path().join("nested/.cargo"), b"a file is not an absent directory")
        .unwrap();
    let mut reads = selected(&world);
    assert!(observe(&world, &mut reads, "nested/.cargo/config.toml").is_err());
    assert!(HeldSourceReadSet::capture(world.source.directory().unwrap(), Instant::now()).is_err());
}

#[test]
fn pending_file_and_absent_leaf_keep_their_slot_while_new_parents_are_captured() {
    for (path, wanted) in [("nested/Cargo.toml", true), ("nested/.cargo/config.toml", false)] {
        let world = make_world();
        let mut reads = selected(&world);
        let root = world.source.directory().unwrap();
        let wanted = if wanted { expected(&world, path.as_bytes()) } else { SourceRead::Absent };
        // Real negative lookups, with one final complete bookend. This reaches
        // the profile's row/descriptor accounting boundary without changing the
        // process limit or constructing thousands of artificial live files.
        let inputs: Vec<_> = (0..8192 - 2)
            .map(|at| {
                (
                    std::path::PathBuf::from(format!("absent-selected-input-{at}")),
                    SourceRead::Absent,
                )
            })
            .collect();
        reads.observe_batch(root, &inputs).unwrap();
        reads.check_current(root).unwrap();
        assert_eq!(reads.selected_population(), 8192 - 1);
        assert!(reads.observe(root, Path::new(path), wanted).is_err(), "{path}");
        assert!(reads.selected_population() <= 8192);
    }
}

#[test]
fn joined_final_physical_checks_keep_original_file_absence_and_listing_guards() {
    for changed in ["file", "absence", "listing"] {
        let world = make_world();
        let mut reads = selected(&world);
        observe(&world, &mut reads, "Cargo.toml").unwrap();
        observe(&world, &mut reads, "nested/.cargo/config.toml").unwrap();
        reads.directory_entries(world.source.directory().unwrap(), Path::new("nested")).unwrap();
        let World { source, rows, end, _scope: scope, _directory } = world;
        let directory = source.directory().unwrap();
        let raw = directory.as_raw_fd();
        let flags = unsafe { libc::fcntl(raw, libc::F_GETFL) };
        let joined = scope.seal().join().unwrap();
        super::selection::check_final_rows(&[&rows], &reads, directory, end).unwrap();
        assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFL) }, flags);
        match changed {
            "file" => {
                fs::write(source.path().join("Cargo.toml"), b"changed selected source").unwrap()
            }
            "absence" => fs::create_dir(source.path().join("nested/.cargo")).unwrap(),
            _ => fs::write(source.path().join("nested/untracked"), b"new glob candidate").unwrap(),
        }
        assert!(super::selection::check_final_rows(&[&rows], &reads, directory, end).is_err());
        assert!(super::selection::check_final_rows(&[&rows], &reads, directory, end).is_err());
        // This is only actual local join/Git/physical input behavior. No live
        // graph or native closure is constructed and no source is retired.
        joined.check_current().unwrap();
        assert!(!Manager::open(source.path()).unwrap().status().unwrap().is_free());
    }
}

#[test]
fn joined_final_git_checks_refuse_changed_head_without_an_open_graph() {
    let world = make_world();
    let mut reads = selected(&world);
    observe(&world, &mut reads, "Cargo.toml").unwrap();
    let World { source, rows, end, _scope: scope, _directory } = world;
    let directory = source.directory().unwrap();
    let joined = scope.seal().join().unwrap();
    super::selection::check_final_rows(&[&rows], &reads, directory, end).unwrap();
    fs::write(source.path().join(".git/HEAD"), format!("{}\n", "1".repeat(40))).unwrap();
    assert!(super::selection::check_final_rows(&[&rows], &reads, directory, end).is_err());
    joined.check_current().unwrap();
    assert!(!Manager::open(source.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn observed_source_drift_quarantines_actual_scope_aliases_after_restoration() {
    for changed in ["file", "absence", "listing"] {
        let world = make_world();
        let alias = Arc::clone(&world.source);
        let dispatch = world._scope.dispatcher();
        let other_dispatch = dispatch.clone();
        let weak = dispatch.downgrade();
        let mut reads = selected(&world);
        observe(&world, &mut reads, "Cargo.toml").unwrap();
        observe(&world, &mut reads, "nested/.cargo/config.toml").unwrap();
        reads.directory_entries(world.source.directory().unwrap(), Path::new("nested")).unwrap();
        let root = world.source.path();
        match changed {
            "file" => fs::write(root.join("Cargo.toml"), b"observed source drift").unwrap(),
            "absence" => fs::create_dir(root.join("nested/.cargo")).unwrap(),
            _ => fs::write(root.join("nested/untracked"), b"observed listing drift").unwrap(),
        }
        let revoked = AtomicBool::new(false);
        let result = reads.check_current(world.source.directory().unwrap());
        let original_error = result.as_ref().unwrap_err();
        let original_kind = original_error.kind();
        let original_text = original_error.to_string();
        // The SAME production quarantine path consumes the actual failed
        // read, local latch and real held scope. Graph-field propagation is
        // source-reviewed; no live Graph or native closure is fabricated.
        let refused = super::selection::quarantine_on_error(result, &revoked, || Some(dispatch));
        let error = refused.unwrap_err();
        assert_eq!(error.kind(), original_kind);
        assert_eq!(error.to_string(), original_text);
        assert!(revoked.load(Ordering::Acquire));
        match changed {
            "file" => fs::write(root.join("Cargo.toml"), b"[package]\nname='source-row-fixture'\n")
                .unwrap(),
            "absence" => fs::remove_dir(root.join("nested/.cargo")).unwrap(),
            _ => fs::remove_file(root.join("nested/untracked")).unwrap(),
        }
        assert!(world.source.check_current().is_err());
        assert!(alias.directory().is_err());
        assert!(weak.upgrade().is_err());
        assert!(other_dispatch.check_current().is_err());
        assert!(other_dispatch.register_launch().is_err());
        assert!(other_dispatch.register_worker().is_err());
        assert!(world._scope.original_source(root).is_err());
        assert!(!Manager::open(root).unwrap().status().unwrap().is_free());
    }
}

#[test]
fn actual_packet_refusal_quarantines_only_its_same_original_scope() {
    let world = make_world();
    let unaffected = make_world();
    let alias = Arc::clone(&world.source);
    let dispatch = world._scope.dispatcher();
    let other_dispatch = dispatch.clone();
    let value = serde_json::json!({"escaped": "\\\n\0\"", "unicode": "λ"});
    let revoked = AtomicBool::new(false);
    let visited = std::cell::Cell::new(false);
    let encoded = super::selection::bounded_packet(&value, 4096);
    let encoded = super::selection::quarantine_on_error(encoded, &revoked, || {
        visited.set(true);
        Some(dispatch.clone())
    });
    assert!(encoded.is_ok());
    assert!(!visited.get());
    assert!(!revoked.load(Ordering::Acquire));
    alias.check_current().unwrap();
    let result = super::selection::bounded_packet(&value, 1);
    let original_text = result.as_ref().unwrap_err().to_string();
    let refused = super::selection::quarantine_on_error(result, &revoked, || Some(dispatch));
    assert_eq!(refused.unwrap_err().to_string(), original_text);
    assert!(revoked.load(Ordering::Acquire));
    assert!(world.source.check_current().is_err());
    assert!(alias.close_only_offer().is_err());
    assert!(other_dispatch.register_worker().is_err());
    assert!(world._scope.original_source(world.source.path()).is_err());
    assert!(!Manager::open(world.source.path()).unwrap().status().unwrap().is_free());
    unaffected.source.check_current().unwrap();
    unaffected._scope.dispatcher().check_current().unwrap();
}
