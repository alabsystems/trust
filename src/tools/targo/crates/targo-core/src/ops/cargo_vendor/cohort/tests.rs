// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use super::Source;
use crate::context::GlobalContext;
use crate::ops;
use crate::workspace::{EitherManifest, Package, SourceId, Workspace, parser};
use cargo_util_terminal::Shell;
use std::fs;
use std::path::{Path, PathBuf};

const MANIFEST: &str = "[workspace]\nresolver = '2'\nmembers = ['leaf']\n[workspace.package]\nversion = '0.1.0'\nedition = '2024'\n";
const LOCK: &str = "version = 4\n\n[[package]]\nname = 'cohort-leaf'\nversion = '0.1.0'\n";

fn fixture() -> (PathBuf, GlobalContext) {
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join(".ubd/vendor-cohort-inputs.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("inputs-")
        .tempdir_in(base)
        .unwrap()
        .keep();
    let root = world.join("project");
    fs::create_dir_all(root.join("leaf/src")).unwrap();
    let root = root.canonicalize().unwrap();
    fs::write(root.join("Cargo.toml"), MANIFEST).unwrap();
    fs::write(root.join("Cargo.lock"), LOCK).unwrap();
    fs::write(
        root.join("leaf/Cargo.toml"),
        "[package]\nname = 'cohort-leaf'\nversion.workspace = true\nedition.workspace = true\n",
    )
    .unwrap();
    fs::write(root.join("leaf/src/lib.rs"), "pub fn value() {}\n").unwrap();
    let repo = git2::Repository::init(&root).unwrap();
    let mut index = repo.index().unwrap();
    index
        .add_all(["*"], git2::IndexAddOption::DEFAULT, None)
        .unwrap();
    index.write().unwrap();
    let tree = repo.find_tree(index.write_tree().unwrap()).unwrap();
    let signature = git2::Signature::now("Cohort input fixture", "cohort@example.invalid").unwrap();
    repo.commit(
        Some("HEAD"),
        &signature,
        &signature,
        "Original source inputs",
        &tree,
        &[],
    )
    .unwrap();
    let mut gctx = GlobalContext::new(Shell::new(), root.clone(), world.join("home"));
    gctx.set_search_stop_path(root.clone());
    gctx.set_env(Default::default());
    gctx.configure(0, false, None, false, true, true, &None, &[], &[])
        .unwrap();
    eprintln!("retained cohort input world={}", world.display());
    (root, gctx)
}

#[test]
fn cached_inherited_manifest_bytes_cannot_be_replaced_by_a_clean_reread() {
    let (root, gctx) = fixture();
    let manifest = root.join("Cargo.toml");
    fs::write(&manifest, MANIFEST.replace("'2024'", "'2021'")).unwrap();
    let id = SourceId::for_path(&root).unwrap();
    parser::read_manifest(&manifest, id, &gctx).unwrap();
    fs::write(&manifest, MANIFEST).unwrap();
    let leaf = root.join("leaf/Cargo.toml");
    let EitherManifest::Real(manifest) = parser::read_manifest(&leaf, id, &gctx).unwrap() else {
        panic!("actual package manifest");
    };
    assert_eq!(manifest.edition().to_string(), "2021");
    let package = Package::new(manifest, &leaf);
    let repo = git2::Repository::open(&root).unwrap();
    let mut source = Source::open(&repo).unwrap();
    let error = source.package(&package).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("loaded source cohort input differs from its Git source: Cargo.toml"),
        "{error:#}"
    );
}

#[test]
fn decoded_lock_bytes_cannot_be_replaced_by_a_clean_reread() {
    let (root, gctx) = fixture();
    let ws = Workspace::new(&root.join("Cargo.toml"), &gctx).unwrap();
    let lock = root.join("Cargo.lock");
    let consumed = format!("# consumed dirty lock comment\n{LOCK}");
    fs::write(&lock, &consumed).unwrap();
    let resolve = ops::load_pkg_lockfile(&ws).unwrap().unwrap();
    let (observed_path, observed) = resolve.lockfile_source().unwrap();
    assert_eq!(observed.as_ref(), consumed);
    fs::write(&lock, LOCK).unwrap();
    let repo = git2::Repository::open(&root).unwrap();
    let mut source = Source::open(&repo).unwrap();
    source.file(&lock).unwrap();
    let error = source
        .loaded_input(observed_path, Some(observed))
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("loaded source cohort input differs from its Git source: Cargo.lock"),
        "{error:#}"
    );
}

fn commit(root: &Path) -> git2::Oid {
    let repo = git2::Repository::open(root).unwrap();
    let mut index = repo.index().unwrap();
    index
        .add_all(["*"], git2::IndexAddOption::DEFAULT, None)
        .unwrap();
    index.write().unwrap();
    let tree = repo.find_tree(index.write_tree().unwrap()).unwrap();
    let signature =
        git2::Signature::now("Nested cohort fixture", "cohort@example.invalid").unwrap();
    let parent = repo.head().ok().map(|head| head.peel_to_commit().unwrap());
    repo.commit(
        Some("HEAD"),
        &signature,
        &signature,
        "Nested source identity",
        &tree,
        &parent.iter().collect::<Vec<_>>(),
    )
    .unwrap()
}

#[test]
fn intermediate_gitlink_head_remains_bound_without_its_own_watched_file() {
    let (root, _) = fixture();
    let middle = root.join("middle");
    let deep = middle.join("deep");
    let repo = git2::Repository::open(&root).unwrap();
    let mut middle_link = repo
        .submodule(
            "https://example.invalid/cohort-middle",
            Path::new("middle"),
            true,
        )
        .unwrap();
    let middle_repo = middle_link.open().unwrap();
    let mut deep_link = middle_repo
        .submodule(
            "https://example.invalid/cohort-deep",
            Path::new("deep"),
            true,
        )
        .unwrap();
    deep_link.open().unwrap();
    fs::write(deep.join("input.txt"), "original nested source\n").unwrap();
    commit(&deep);
    deep_link.add_to_index(true).unwrap();
    fs::write(middle.join("marker.txt"), "original middle\n").unwrap();
    commit(&middle);
    middle_link.add_to_index(true).unwrap();
    commit(&root);
    let mut source = Source::open(&repo).unwrap();
    source.file(&deep.join("input.txt")).unwrap();
    assert_eq!(source.gitlinks.len(), 2);
    assert!(!source.watched.contains_key(Path::new("middle")));
    source.check_current().unwrap();
    let middle_repo = git2::Repository::open(&middle).unwrap();
    let original_index = middle_repo
        .index()
        .unwrap()
        .get_path(Path::new("deep"), 0)
        .unwrap()
        .id;
    fs::write(middle.join("marker.txt"), "changed middle\n").unwrap();
    commit(&middle);
    assert_eq!(
        middle_repo
            .index()
            .unwrap()
            .get_path(Path::new("deep"), 0)
            .unwrap()
            .id,
        original_index
    );
    let error = source.check_current().unwrap_err();
    assert!(
        error.to_string().contains("pinned repository HEAD changed"),
        "{error:#}"
    );
}
