use super::super::tests::private_world;
use super::*;

#[test]
fn actual_traversal_guard_distinguishes_active_cycles_completed_dedup_and_bounds() {
    let mut traversal = Traversal::default();
    let mut keys = Vec::new();
    for index in 0..=MAX_SOURCES {
        let url = url::Url::parse(&format!("https://example.invalid/source-{index}.git")).unwrap();
        let id = SourceId::for_git(&url, crate::workspace::GitReference::Rev("1".repeat(40)))
            .unwrap()
            .with_git_precise(Some("1".repeat(40)));
        keys.push((id, url.to_string()));
    }
    assert!(traversal.enter(&keys[0]).unwrap());
    assert!(
        traversal
            .enter(&keys[0])
            .unwrap_err()
            .to_string()
            .contains("cycle")
    );
    traversal.finish(keys[0].clone()).unwrap();
    assert!(!traversal.enter(&keys[0]).unwrap());
    for key in &keys[1..MAX_SOURCES] {
        assert!(traversal.enter(key).unwrap());
        traversal.finish(key.clone()).unwrap();
    }
    assert!(
        traversal
            .enter(&keys[MAX_SOURCES])
            .unwrap_err()
            .to_string()
            .contains("bound")
    );
}

fn repository() -> (tempfile::TempDir, git2::Repository, git2::Oid) {
    let world = private_world();
    let repo = git2::Repository::init_bare(world.path().join("selected.git")).unwrap();
    let tree_id = repo.treebuilder(None).unwrap().write().unwrap();
    let tree = repo.find_tree(tree_id).unwrap();
    let signature = git2::Signature::now("Submodule fixture", "source@example.invalid").unwrap();
    let child = repo
        .commit(
            None,
            &signature,
            &signature,
            "actual gitlink target",
            &tree,
            &[],
        )
        .unwrap();
    drop(tree);
    (world, repo, child)
}

fn selected_commit(
    repo: &git2::Repository,
    child: git2::Oid,
    modules: &[u8],
    mode: i32,
) -> git2::Oid {
    let blob = repo.blob(modules).unwrap();
    let mut tree = repo.treebuilder(None).unwrap();
    tree.insert(".gitmodules", blob, mode).unwrap();
    tree.insert("sat", child, 0o160000).unwrap();
    let tree_id = tree.write().unwrap();
    drop(tree);
    let tree = repo.find_tree(tree_id).unwrap();
    let signature = git2::Signature::now("Submodule fixture", "source@example.invalid").unwrap();
    repo.commit(None, &signature, &signature, "selected tree", &tree, &[])
        .unwrap()
}

#[test]
fn relative_and_scp_identity_use_the_ordinary_checkout_recipe() {
    let (_world, repo, child) = repository();
    let selected_oid = selected_commit(
        &repo,
        child,
        b"[submodule \"sat\"]\npath=sat\nurl=../sat.git\n",
        0o100644,
    );
    for parent in [
        "https://example.invalid/owner/root.git",
        "git@example.invalid:owner/root.git",
    ] {
        let children = selected(&repo, selected_oid, parent).unwrap();
        assert_eq!(children.len(), 1);
        let absolute = absolute_submodule_url(parent, "../sat.git").unwrap();
        let (expected, fetch) = submodule_source_id(&absolute, child).unwrap();
        assert_eq!(children[0].id, expected);
        assert_eq!(
            children[0].parent_url,
            fetch.unwrap_or_else(|| expected.url().to_string())
        );
        assert_eq!(
            children[0].id.precise_git_fragment(),
            Some(child.to_string().as_str())
        );
    }
}

#[test]
fn update_none_skips_resolution_and_child_data_but_still_requires_its_fields() {
    let (_world, repo, child) = repository();
    let commit = selected_commit(
        &repo,
        child,
        b"[submodule \"sat\"]\npath=sat\nurl=not-a-resolvable-URL\nupdate=none\n",
        0o100644,
    );
    assert!(
        selected(&repo, commit, "unparseable parent")
            .unwrap()
            .is_empty()
    );
    let missing = selected_commit(
        &repo,
        child,
        b"[submodule \"sat\"]\npath=sat\nupdate=none\n",
        0o100644,
    );
    assert!(selected(&repo, missing, "unparseable parent").is_err());
}

#[test]
fn includes_duplicates_unbound_paths_and_commands_refuse() {
    let (_world, repo, child) = repository();
    for modules in [
        "[include]\npath=/must-not-read\n[submodule \"sat\"]\npath=sat\nurl=../sat.git\n",
        "[includeIf \"gitdir:/**\"]\npath=/must-not-read\n",
        "[submodule \"sat\"]\npath=sat\nurl=../sat.git\nURL=../other.git\n",
        "[submodule \"sat\"]\npath=sat\nurl=../sat.git\n[submodule \"sat\"]\npath=sat\nurl=../sat.git\n",
        "[submodule \"one\"]\npath=sat\nurl=../sat.git\n[submodule \"two\"]\npath=sat\nurl=../sat.git\n",
        "[submodule \"sat\"]\npath=./sat\nurl=../sat.git\n",
        "[submodule \"sat\"]\npath=../sat\nurl=../sat.git\n",
        "[submodule \"sat\"]\npath=sat//child\nurl=../sat.git\n",
        "[submodule \"sat\"]\npath=.git\nurl=../sat.git\n",
        "[submodule \"sat\"]\npath=other\nurl=../sat.git\n",
        "[submodule \"sat\"]\npath=sat\nurl=../sat.git\nupdate=!must-not-execute\n",
        "[submodule \"sat\"]\npath=sat\nurl\n",
        "[submodule \"sat\"]\npath=sat\nurl=../sat.git\nupdate=unknown\n",
    ] {
        let oid = selected_commit(&repo, child, modules.as_bytes(), 0o100644);
        assert!(
            selected(&repo, oid, "https://example.invalid/owner/root.git").is_err(),
            "{modules}"
        );
    }
    let symlink = selected_commit(&repo, child, b"/must-not-follow", 0o120000);
    assert!(selected(&repo, symlink, "https://example.invalid/root").is_err());
}

#[test]
fn selected_gitlinks_without_a_modules_blob_refuse() {
    let (_world, repo, child) = repository();
    let mut tree = repo.treebuilder(None).unwrap();
    tree.insert("sat", child, 0o160000).unwrap();
    let tree_id = tree.write().unwrap();
    drop(tree);
    let tree = repo.find_tree(tree_id).unwrap();
    let signature = git2::Signature::now("Fixture", "source@example.invalid").unwrap();
    let oid = repo
        .commit(None, &signature, &signature, "unbound", &tree, &[])
        .unwrap();
    assert!(selected(&repo, oid, "https://example.invalid/root").is_err());
}

#[test]
fn raw_and_resolved_url_growth_refuses_before_following_a_child() {
    let (_world, repo, child) = repository();
    let too_long = format!(
        "[submodule \"sat\"]\npath=sat\nurl={}\n",
        "x".repeat(MAX_SOURCE_URL_BYTES + 1)
    );
    let oid = selected_commit(&repo, child, too_long.as_bytes(), 0o100644);
    assert!(selected(&repo, oid, "https://example.invalid/root").is_err());
    let oid = selected_commit(
        &repo,
        child,
        b"[submodule \"sat\"]\npath=sat\nurl=./child\n",
        0o100644,
    );
    // SCP relative resolution appends the raw parent spelling. Both inputs
    // individually fit, but their resolved context must still fit the bound.
    let parent = format!(
        "git@example.invalid:{}",
        "x".repeat(MAX_SOURCE_URL_BYTES - 24)
    );
    assert!(parent.len() <= MAX_SOURCE_URL_BYTES);
    assert!(selected(&repo, oid, &parent).is_err());
}
