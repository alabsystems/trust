//! Actual local repository objects only. No fixture creates a graph, SDK,
//! source scope or proof owner from Git observations.
use std::fs;
use std::time::Duration;

use super::*;
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}
fn commit(repo: &gix::Repository, seconds: i64) -> gix::ObjectId {
    let tree = repo.write_object(&gix::objs::Tree { entries: Vec::new() }).unwrap();
    commit_tree(repo, tree.detach(), seconds)
}
pub(super) fn commit_tree(repo: &gix::Repository, tree: gix::ObjectId, seconds: i64) -> gix::ObjectId {
    let signature = gix::actor::Signature {
        name: "Native source fixture".into(),
        email: "source@example.invalid".into(),
        time: gix::date::Time { seconds, offset: 0 },
    };
    let parents = repo.head_id().ok().map(|id| id.detach()).into_iter();
    let mut time = gix::date::parse::TimeBuf::default();
    let signature = signature.to_ref(&mut time);
    repo.commit_as(
        signature,
        signature,
        "HEAD",
        "native source identity fixture",
        tree,
        parents,
    )
    .unwrap()
    .detach()
}
#[test]
fn actual_local_commit_is_read_without_git_child_or_saved_commit_info() {
    let scratch = tempfile::tempdir().unwrap();
    let repo = gix::init(scratch.path()).unwrap();
    let id = commit(&repo, 1_600_000_000);
    let dir = scratch.path();
    // Isolated local configuration cannot follow an include to a missing file
    // or consult environment/global configuration to decide source identity.
    let config = dir.join(".git/config");
    let mut bytes = fs::read_to_string(&config).unwrap();
    bytes.push_str("\n[include]\npath = /must-not-read-native-source-fixture\n");
    fs::write(config, bytes).unwrap();
    let actual = observe(dir, false, deadline()).unwrap();
    let info = actual.info().unwrap();
    assert_eq!(info.sha, id.to_string());
    assert_eq!(info.commit_date, "2020-09-13");
    assert!(info.short_sha.len() >= 9);
    assert!(info.sha.starts_with(&info.short_sha));
    fs::write(dir.join("git-commit-info"), "saved foreign source identity\n").unwrap();
    assert_eq!(observe(dir, false, deadline()).unwrap().info().unwrap().sha, id.to_string());
    let moved = commit(&repo, 1_600_086_400);
    assert_ne!(id, moved);
    assert_eq!(observe(dir, false, deadline()).unwrap().info().unwrap().sha, moved.to_string());
    assert!(observe(dir, false, Instant::now()).is_err());
}
#[test]
fn absent_unborn_and_missing_original_commit_refuse_instead_of_tarball_fallback() {
    let scratch = tempfile::tempdir().unwrap();
    fs::write(
        scratch.path().join("git-commit-info"),
        "saved identity is not a native Git source\n",
    )
    .unwrap();
    assert!(observe(scratch.path(), false, deadline()).is_err());
    let repo = gix::init(scratch.path()).unwrap();
    assert!(observe(scratch.path(), false, deadline()).is_err());
    let id = commit(&repo, 1_600_000_000);
    let hex = id.to_string();
    let object = scratch.path().join(".git/objects").join(&hex[..2]).join(&hex[2..]);
    assert!(object.is_file());
    fs::remove_file(object).unwrap();
    assert!(observe(scratch.path(), false, deadline()).is_err());
}

#[test]
fn optional_component_absence_does_not_substitute_for_the_required_source_root() {
    let scratch = tempfile::tempdir().unwrap();
    let repo = gix::init(scratch.path()).unwrap();
    commit(&repo, 1_600_000_000);
    let component = scratch.path().join("src/tools/unused-component");
    fs::create_dir_all(&component).unwrap();
    assert!(matches!(
        observe_profile(&component, false, deadline(), false).unwrap(),
        GitInfo::Absent
    ));
    assert!(
        observe(&component, false, deadline()).is_err(),
        "a parent repository cannot supply the required exact source Root"
    );
    fs::write(component.join(".git"), b"not a repository locator").unwrap();
    assert!(
        observe_profile(&component, false, deadline(), false).is_err(),
        "malformed observed Git data is unknown, not absent"
    );
    assert!(observe(scratch.path(), false, deadline()).is_ok());
}

#[test]
fn local_source_discovery_uses_actual_worktree_marker_and_refuses_missing_or_expired_source() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let _repo = gix::init(&root).unwrap();
    fs::create_dir_all(root.join("src/bootstrap")).unwrap();
    assert!(discover_source_directory_at(&root, deadline()).is_err());
    fs::write(root.join("src/stage0"), "native stage0 marker\n").unwrap();
    assert_eq!(
        discover_source_directory_at(&root.join("src/bootstrap"), deadline()).unwrap(),
        root
    );
    assert!(discover_source_directory_at(&root, Instant::now()).is_err());
    let foreign = tempfile::tempdir().unwrap();
    assert!(discover_source_directory_at(foreign.path(), deadline()).is_err());
}
