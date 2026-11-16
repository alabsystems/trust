//! Actual local Git objects only. No fixture creates OriginalHostGraph,
//! OriginalSourceRoot, canonical source rows, native admission or SDK authority.
use std::fs;
use std::os::fd::{AsFd as _, AsRawFd as _};
use std::os::unix::fs::symlink;

use gix::objs::tree::{Entry, EntryKind};

use super::super::tests::commit_tree;
use super::*;

// Exercise the SAME production capture adapter with a real held directory.
// This helper constructs only passive Git DATA, never an enrolled source role.
pub(super) fn read_repository(root: &Path, deadline: Instant) -> io::Result<RepositoryRows> {
    super::read_repository(source_dir(root)?.as_fd(), root, deadline)
}
fn lookup<'a>(rows: &'a RepositoryRows, path: &[u8]) -> io::Result<CommittedLookup<'a>> {
    rows.lookup(path, rows.original_deadline())
}
fn entries(rows: &RepositoryRows) -> &[CommittedEntry] {
    rows.entries(rows.original_deadline()).unwrap()
}

fn end() -> Instant {
    Instant::now() + std::time::Duration::from_secs(60)
}
fn entry(name: &str, kind: EntryKind, object: gix::ObjectId) -> Entry {
    Entry { mode: kind.into(), filename: name.into(), oid: object }
}
pub(super) fn fixture(repo: &gix::Repository) -> gix::ObjectId {
    let blob = repo.write_blob(b"[package]\nname='source-row-fixture'\n").unwrap().detach();
    let link = repo.write_blob(b"Cargo.toml").unwrap().detach();
    let nested = repo
        .write_object(&gix::objs::Tree {
            entries: vec![entry("Cargo.toml", EntryKind::Blob, blob)],
        })
        .unwrap()
        .detach();
    let tree = repo
        .write_object(&gix::objs::Tree {
            entries: vec![
                entry("Cargo.toml", EntryKind::Blob, blob),
                entry("link", EntryKind::Link, link),
                entry("nested", EntryKind::Tree, nested),
                entry(
                    "unresolved",
                    EntryKind::Commit,
                    gix::ObjectId::from_hex(b"1111111111111111111111111111111111111111").unwrap(),
                ),
            ],
        })
        .unwrap()
        .detach();
    commit_tree(repo, tree, 1_600_000_000);
    tree
}

#[test]
fn actual_complete_repository_tree_keeps_directory_link_and_unresolved_gitlink_rows() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    fs::write(root.join("untracked"), b"physical files are not committed membership").unwrap();
    let rows = read_repository(&root, end()).unwrap();
    assert_eq!(
        entries(&rows).iter().map(|row| row.path.as_slice()).collect::<Vec<_>>(),
        [b"Cargo.toml".as_slice(), b"link", b"nested", b"nested/Cargo.toml", b"unresolved"]
    );
    assert_eq!(entries(&rows)[1].mode, 0o120000);
    assert_eq!(entries(&rows)[2].mode, 0o040000);
    assert_eq!(entries(&rows)[4].mode, 0o160000);
    // Its unresolved child is NOT interpreted as an empty committed subtree.
    assert!(!entries(&rows).iter().any(|row| row.path.starts_with(b"unresolved/")));
    assert!(read_repository(&root, Instant::now()).is_err());
}

#[test]
fn unreadable_existing_tree_is_an_error_and_cannot_become_an_empty_inventory() {
    use std::os::unix::fs::PermissionsExt as _;
    for missing in [true, false] {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let repo = gix::init(&root).unwrap();
        let tree = fixture(&repo).to_string();
        let object = root.join(".git/objects").join(&tree[..2]).join(&tree[2..]);
        if missing {
            fs::remove_file(object).unwrap();
        } else {
            // A valid EMPTY tree body under the original NONEMPTY tree's ID.
            // It cannot become successful empty discovery at the old commit.
            fs::set_permissions(&object, fs::Permissions::from_mode(0o600)).unwrap();
            let empty = repo
                .write_object(&gix::objs::Tree { entries: Vec::new() })
                .unwrap()
                .detach()
                .to_string();
            let empty = root.join(".git/objects").join(&empty[..2]).join(&empty[2..]);
            fs::copy(empty, object).unwrap();
        }
        assert!(read_repository(&root, end()).is_err());
    }
}

#[test]
fn original_repository_observation_refuses_moved_head_and_optional_root_fallback() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    let tree = fixture(&repo);
    let rows = read_repository(&root, end()).unwrap();
    commit_tree(&repo, tree, 1_600_000_001);
    assert!(rows.check(rows.original_deadline()).is_err());
    let child = root.join("not-a-repository");
    fs::create_dir(&child).unwrap();
    assert!(read_repository(&child, end()).is_err());
}

#[test]
fn hash_valid_but_escaped_or_repeated_tree_entries_still_refuse() {
    for names in [["..", "ordinary"], ["same", "same"]] {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let repo = gix::init(&root).unwrap();
        let blob = repo.write_blob(b"inert source bytes").unwrap().detach();
        let tree = repo
            .write_object(&gix::objs::Tree {
                entries: names.into_iter().map(|name| entry(name, EntryKind::Blob, blob)).collect(),
            })
            .unwrap()
            .detach();
        commit_tree(&repo, tree, 1_600_000_000);
        assert!(read_repository(&root, end()).is_err());
    }
}

#[test]
fn absent_lookup_requires_the_complete_tree_and_never_crosses_an_unresolved_boundary() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    let rows = read_repository(&root, end()).unwrap();
    assert!(
        matches!(lookup(&rows, b"nested/Cargo.toml").unwrap(), CommittedLookup::Present(entry) if entry.mode==0o100644)
    );
    assert!(matches!(lookup(&rows, b"nested/absent.toml").unwrap(), CommittedLookup::Absent));
    assert!(
        matches!(lookup(&rows, b"unresolved/Cargo.toml").unwrap(), CommittedLookup::Unresolved(entry) if entry.mode==0o160000)
    );
    assert!(
        matches!(lookup(&rows, b"link/unknown").unwrap(), CommittedLookup::Unresolved(entry) if entry.mode==0o120000)
    );
    for path in
        [b"".as_slice(), b"../outside", b"nested//Cargo.toml", b"nested/./Cargo.toml", b"/absolute"]
    {
        // Every malformed path reaches its own actual syntax boundary before
        // the shared observation's permanent quarantine is installed.
        let rows = read_repository(&root, end()).unwrap();
        assert!(lookup(&rows, path).is_err());
        assert!(rows.check(rows.original_deadline()).is_err());
        assert!(lookup(&rows, b"Cargo.toml").is_err());
    }
}

#[test]
fn required_canonical_empty_tree_storage_is_never_synthesized_after_loss_or_corruption() {
    for missing in [true, false] {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let repo = gix::init(&root).unwrap();
        let tree = repo.write_object(&gix::objs::Tree { entries: Vec::new() }).unwrap().detach();
        commit_tree(&repo, tree, 1_600_000_000);
        let hex = tree.to_string();
        let object = root.join(".git/objects").join(&hex[..2]).join(&hex[2..]);
        if object.exists() {
            fs::remove_file(&object).unwrap();
        }
        if !missing {
            fs::create_dir_all(object.parent().unwrap()).unwrap();
            fs::write(object, b"corrupt canonical-empty object storage").unwrap();
        }
        assert!(read_repository(&root, end()).is_err());
    }
}

#[test]
fn native_repository_applies_its_allocation_bound_to_real_loose_object_decoding() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let writer = gix::init(&root).unwrap();
    let size = trust_committed_source::MAX_OBJECT_ALLOC_BYTES + 1;
    let object = writer.write_blob(vec![b'x'; size]).unwrap().detach();
    let ordinary = gix::open_opts(&root, gix::open::Options::isolated()).unwrap();
    let mut buffer = Vec::new();
    let decoded =
        gix::objs::Find::try_find(&ordinary.objects, &object, &mut buffer).unwrap().unwrap();
    assert_eq!(decoded.data.len(), size, "actual unbounded positive control");
    drop(buffer);
    let native = repository(&root).unwrap();
    let mut buffer = Vec::new();
    assert!(gix::objs::Find::try_find(&native.objects, &object, &mut buffer).is_err());
}

#[test]
fn small_selected_pack_tree_does_not_excuse_an_oversized_delta_base_allocation() {
    use std::io::Write as _;

    use gix::objs::WriteTo as _;
    use gix::odb::pack::{cache, data};
    let kind = gix::hash::Kind::Sha1;
    let blob = gix::ObjectId::from_hex(b"1111111111111111111111111111111111111111").unwrap();
    let mut base = Vec::new();
    gix::objs::Tree {
        entries: vec![entry("a", EntryKind::Blob, blob), entry("b", EntryKind::Blob, blob)],
    }
    .write_to(&mut base)
    .unwrap();
    assert_eq!(base.len(), 58);
    let selected = base[..29].to_vec();
    let expected = gix::objs::compute_hash(kind, gix::objs::Kind::Tree, &selected).unwrap();
    let mut pack = data::header::encode(data::Version::V2, 2).to_vec();
    let base_offset = pack.len() as u64;
    data::entry::Header::Tree.write_to(base.len() as u64, &mut pack).unwrap();
    {
        let mut compressed = gix::features::zlib::stream::deflate::Write::new(&mut pack);
        compressed.write_all(&base).unwrap();
        compressed.flush().unwrap();
    }
    let delta_offset = pack.len() as u64;
    // base58/result29/copy offset0,length29: a genuine one-level OFS_DELTA.
    let delta = [0x3a, 0x1d, 0x90, 0x1d];
    data::entry::Header::OfsDelta { base_distance: delta_offset - base_offset }
        .write_to(delta.len() as u64, &mut pack)
        .unwrap();
    {
        let mut compressed = gix::features::zlib::stream::deflate::Write::new(&mut pack);
        compressed.write_all(&delta).unwrap();
        compressed.flush().unwrap();
    }
    let mut hasher = gix::hash::hasher(kind);
    hasher.update(&pack);
    pack.extend_from_slice(hasher.try_finalize().unwrap().as_slice());
    let file =
        data::File::from_data(pack.clone(), "native-source-delta.pack".into(), kind).unwrap();
    let original = file.entry(delta_offset).unwrap();
    let header = file
        .decode_header(original.clone(), &mut gix::features::zlib::Inflate::default(), &|_| None)
        .unwrap();
    assert_eq!(header.kind, gix::objs::Kind::Tree);
    assert_eq!(header.object_size, 29);
    let mut decoded = Vec::new();
    let observed = file
        .decode_entry(
            original,
            &mut decoded,
            &mut gix::features::zlib::Inflate::default(),
            &|_, _| None,
            &mut cache::Never,
        )
        .unwrap();
    assert_eq!(observed.num_deltas, 1);
    assert_eq!(decoded, selected);
    assert_eq!(gix::objs::compute_hash(kind, gix::objs::Kind::Tree, &decoded).unwrap(), expected);
    let bounded = data::File::from_data(pack, "native-source-delta.pack".into(), kind)
        .unwrap()
        .with_alloc_limit_bytes(Some(32));
    assert!(matches!(
        bounded.decode_entry(
            bounded.entry(delta_offset).unwrap(),
            &mut Vec::new(),
            &mut gix::features::zlib::Inflate::default(),
            &|_, _| None,
            &mut cache::Never
        ),
        Err(data::decode::Error::OutOfMemory)
    ));
    // This tests the maintained packed decoder. The separate actual native
    // repository loose-object control proves our early config wiring; this
    // fixture does not pretend to be an indexed native ODB/owner qualification.
}

#[test]
fn submodule_requires_the_actual_exact_parent_pin_and_preserves_unresolved_absence() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    let child_root = root.join("child");
    let child = gix::init(&child_root).unwrap();
    let child_tree = fixture(&child);
    let pin = child.head_id().unwrap().detach();
    let parent_tree = repo
        .write_object(&gix::objs::Tree { entries: vec![entry("child", EntryKind::Commit, pin)] })
        .unwrap()
        .detach();
    commit_tree(&repo, parent_tree, 1_600_000_000);
    let parent = read_repository(&root, end()).unwrap();
    assert!(matches!(
        lookup(&parent, b"child/Cargo.toml").unwrap(),
        CommittedLookup::Unresolved(_)
    ));
    let observed = read_submodule(&parent, b"child", parent.original_deadline()).unwrap();
    assert_eq!(observed.commit(), pin);
    assert!(matches!(lookup(&observed, b"Cargo.toml").unwrap(), CommittedLookup::Present(_)));
    assert!(matches!(lookup(&observed, b"absent").unwrap(), CommittedLookup::Absent));
    commit_tree(&child, child_tree, 1_600_000_001);
    for name in [b"child".as_slice(), b"missing", b"../outside"] {
        let parent = read_repository(&root, end()).unwrap();
        assert!(read_submodule(&parent, name, parent.original_deadline()).is_err());
    }
}

#[test]
fn uninitialized_gitlink_never_supplies_a_parent_repository_or_empty_child() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    fs::create_dir(root.join("unresolved")).unwrap();
    for name in [b"unresolved".as_slice(), b"nested", b"link"] {
        let parent = read_repository(&root, end()).unwrap();
        assert!(read_submodule(&parent, name, parent.original_deadline()).is_err());
    }
}

#[test]
fn committed_capture_requires_the_same_directory_descriptor_and_exact_lexical_root() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    let other = tempfile::tempdir().unwrap();
    let wrong = source_dir(other.path()).unwrap();
    assert!(super::read_repository(wrong.as_fd(), &root, end()).is_err());
    let original = source_dir(&root).unwrap();
    let flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) };
    assert_ne!(flags, -1);
    let rows = super::read_repository(original.as_fd(), &root, end()).unwrap();
    rows.check(rows.original_deadline()).unwrap();
    assert_eq!(unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) }, flags);
    let alias = other.path().join("alias");
    symlink(&root, &alias).unwrap();
    assert!(super::read_repository(original.as_fd(), &alias, end()).is_err());
    assert!(super::read_repository(original.as_fd(), &root.join("."), end()).is_err());
    drop(original);
    rows.check(rows.original_deadline()).unwrap();
}

#[test]
fn committed_observation_cannot_extend_or_recover_its_original_endpoint() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    let original_end = end();
    let rows = read_repository(&root, original_end).unwrap();
    rows.check(original_end).unwrap();
    assert!(rows.check(original_end + std::time::Duration::from_millis(1)).is_err());
    assert!(rows.check(original_end).is_err());
    assert!(rows.lookup(b"Cargo.toml", original_end).is_err());
}

#[test]
fn committed_observation_keeps_the_original_description_after_pathname_restoration() {
    let scratch = tempfile::tempdir().unwrap();
    let outer = scratch.path().canonicalize().unwrap();
    let root = outer.join("source");
    let repo = gix::init(&root).unwrap();
    fixture(&repo);
    let rows = read_repository(&root, end()).unwrap();
    let held = outer.join("held");
    fs::rename(&root, &held).unwrap();
    fs::create_dir(&root).unwrap();
    assert!(rows.check(rows.original_deadline()).is_err());
    fs::remove_dir(&root).unwrap();
    fs::rename(&held, &root).unwrap();
    assert!(rows.check(rows.original_deadline()).is_err());
}
