use super::*;
use crate::workspace::{GitReference, SourceId};
use std::os::unix::fs::{PermissionsExt as _, symlink};

fn source(donor: &Path) -> SourceId {
    let revision = std::fs::read_to_string(donor.join("revision")).unwrap();
    SourceId::for_git(
        &url::Url::parse("https://example.invalid/dependency").unwrap(),
        GitReference::Rev(revision.clone()),
    )
    .unwrap()
    .with_git_precise(Some(revision))
}

fn database(donor: &Path) -> PathBuf {
    donor
        .join("git/db")
        .join(crate::sources::git::source::ident(&source(donor)))
}

fn selected(donor: &Path) -> Vec<SourceId> {
    if donor.join("git").exists() {
        vec![source(donor)]
    } else {
        Vec::new()
    }
}

fn import(donor: &Path, destination: &Path, registry: Option<&str>) -> CargoResult<Stats> {
    super::import_selected(donor, destination, registry, None, selected(donor), &[])
}

fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf) {
    let world = super::super::super::tests::private_world();
    let root = world.path().canonicalize().unwrap();
    let donor = root.join("donor");
    std::fs::create_dir(&donor).unwrap();
    std::fs::set_permissions(&donor, std::fs::Permissions::from_mode(0o700)).unwrap();
    for lock in LOCKS {
        File::create(donor.join(lock)).unwrap();
    }
    let db = donor.join("git/db/dependency");
    std::fs::create_dir_all(db.parent().unwrap()).unwrap();
    let mut options = git2::RepositoryInitOptions::new();
    options.bare(true).external_template(false);
    let repository = git2::Repository::init_opts(&db, &options).unwrap();
    let blob = repository.blob(b"actual original DATA").unwrap();
    std::fs::write(donor.join("blob-id"), blob.to_string()).unwrap();
    let mut builder = repository.treebuilder(None).unwrap();
    builder.insert("data", blob, 0o100644).unwrap();
    let tree_id = builder.write().unwrap();
    drop(builder);
    let tree = repository.find_tree(tree_id).unwrap();
    let signature = git2::Signature::now("DATA fixture", "fixture@example.invalid").unwrap();
    let revision = repository
        .commit(None, &signature, &signature, "actual fixture", &tree, &[])
        .unwrap();
    std::fs::write(donor.join("revision"), revision.to_string()).unwrap();
    drop(tree);
    drop(repository);
    std::fs::rename(&db, database(&donor)).unwrap();
    let index = donor.join("registry/index/index-fixture");
    std::fs::create_dir_all(index.join(".cache/ex/am")).unwrap();
    std::fs::write(index.join("config.json"), REGISTRY_CONFIG).unwrap();
    std::fs::write(index.join(".cache/ex/am/example"), b"index DATA").unwrap();
    std::fs::create_dir_all(donor.join("registry/cache/index-fixture")).unwrap();
    std::fs::write(
        donor.join("registry/cache/index-fixture/example-1.0.0.crate"),
        b"archive DATA",
    )
    .unwrap();
    (world, root, donor)
}

fn complete_checkout(donor: &Path) -> PathBuf {
    let old_db = database(donor);
    let repository = git2::Repository::open_bare(&old_db).unwrap();
    let manifest = b"[package]\nname='checkout-data-dep'\nversion='0.1.0'\nedition='2021'\n[lib]\npath='lib.rs'\n";
    let library = b"pub fn value()->u32 { 42 }\n";
    let script = b"#!/bin/sh\nexit 0\n";
    let mut tree = repository.treebuilder(None).unwrap();
    for (name, bytes, mode) in [
        ("Cargo.toml", manifest.as_slice(), 0o100644),
        ("lib.rs", library.as_slice(), 0o100644),
        ("tool", script.as_slice(), 0o100755),
    ] {
        tree.insert(name, repository.blob(bytes).unwrap(), mode)
            .unwrap();
    }
    tree.insert("alias.rs", repository.blob(b"lib.rs").unwrap(), 0o120000)
        .unwrap();
    let mut nested = repository.treebuilder(None).unwrap();
    nested
        .insert(
            ".cargo-ok",
            repository.blob(b"actual tracked marker DATA\n").unwrap(),
            0o100644,
        )
        .unwrap();
    nested
        .insert("LICENSE", repository.blob(b"../lib.rs").unwrap(), 0o120000)
        .unwrap();
    tree.insert("nested", nested.write().unwrap(), 0o040000)
        .unwrap();
    drop(nested);
    let tree_id = tree.write().unwrap();
    drop(tree);
    let tree = repository.find_tree(tree_id).unwrap();
    let signature =
        git2::Signature::now("checkout DATA fixture", "fixture@example.invalid").unwrap();
    let revision = repository
        .commit(None, &signature, &signature, "complete package", &tree, &[])
        .unwrap();
    std::fs::write(donor.join("revision"), revision.to_string()).unwrap();
    let checkout = donor
        .join("git/checkouts")
        .join(crate::sources::git::source::ident(&source(donor)))
        .join(
            crate::sources::git::utils::checkout_short_id(&repository.odb().unwrap(), revision)
                .unwrap(),
        );
    std::fs::create_dir_all(checkout.join(".git/hooks")).unwrap();
    std::fs::write(checkout.join(".git/HEAD"), format!("{revision}\n")).unwrap();
    std::fs::write(checkout.join(".git/config"), "must not propagate").unwrap();
    std::fs::write(
        checkout.join(".git/hooks/post-checkout"),
        "must not execute",
    )
    .unwrap();
    std::fs::write(checkout.join("Cargo.toml"), manifest).unwrap();
    std::fs::write(checkout.join("lib.rs"), library).unwrap();
    symlink("lib.rs", checkout.join("alias.rs")).unwrap();
    std::fs::create_dir(checkout.join("nested")).unwrap();
    std::fs::write(
        checkout.join("nested/.cargo-ok"),
        b"actual tracked marker DATA\n",
    )
    .unwrap();
    symlink("../lib.rs", checkout.join("nested/LICENSE")).unwrap();
    std::fs::write(checkout.join("tool"), script).unwrap();
    std::fs::set_permissions(
        checkout.join("tool"),
        std::fs::Permissions::from_mode(0o755),
    )
    .unwrap();
    drop(tree);
    drop(repository);
    if old_db != database(donor) {
        std::fs::rename(old_db, database(donor)).unwrap();
    }
    checkout
}

#[test]
fn complete_selected_checkout_uses_real_tree_not_marker_and_resolves_locked_offline() {
    let (_world, root, donor) = fixture();
    let checkout = complete_checkout(&donor);
    assert!(!checkout.join(".cargo-ok").exists());
    let destination = root.join("output");
    let stats = import(&donor, &destination, None).unwrap();
    assert!(stats.checkout_files >= 8 && stats.checkout_bytes > 0);
    let selected = destination.join(checkout.strip_prefix(&donor).unwrap());
    assert_eq!(
        std::fs::read(selected.join("lib.rs")).unwrap(),
        std::fs::read(checkout.join("lib.rs")).unwrap()
    );
    assert_eq!(
        std::fs::metadata(selected.join("tool")).unwrap().mode() & 0o777,
        0o755
    );
    let repository = git2::Repository::open(&selected).unwrap();
    assert_eq!(
        repository.head().unwrap().target(),
        Some(super::super::super::locked_oid(source(&donor)).unwrap())
    );
    assert_eq!(repository.index().unwrap().len(), 6);
    assert_eq!(
        std::fs::read(selected.join("nested/.cargo-ok")).unwrap(),
        b"actual tracked marker DATA\n"
    );
    assert_eq!(
        std::fs::metadata(selected.join("nested/.cargo-ok"))
            .unwrap()
            .mode()
            & 0o777,
        0o644
    );
    assert!(
        std::fs::read(selected.join(".cargo-ok"))
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        std::fs::read_link(selected.join("alias.rs")).unwrap(),
        Path::new("lib.rs")
    );
    assert_eq!(
        std::fs::read_link(selected.join("nested/LICENSE")).unwrap(),
        Path::new("../lib.rs")
    );
    assert!(!selected.join(".git/hooks").exists());
    assert!(
        !std::fs::read_to_string(selected.join(".git/config"))
            .unwrap()
            .contains("must not propagate")
    );
    assert!(selected.join(".cargo-ok").exists());
    let app = root.join("app");
    std::fs::create_dir_all(app.join("src")).unwrap();
    let revision = std::fs::read_to_string(donor.join("revision")).unwrap();
    std::fs::write(app.join("Cargo.toml"),format!("[workspace]\n[package]\nname='checkout-data-app'\nversion='0.1.0'\nedition='2021'\n[dependencies]\ncheckout-data-dep={{git='https://example.invalid/dependency',rev='{revision}'}}\n")).unwrap();
    std::fs::write(app.join("src/lib.rs"), "").unwrap();
    let lock = format!(
        "version = 4\n\n[[package]]\nname = \"checkout-data-app\"\nversion = \"0.1.0\"\ndependencies = [\n \"checkout-data-dep\",\n]\n\n[[package]]\nname = \"checkout-data-dep\"\nversion = \"0.1.0\"\nsource = \"git+https://example.invalid/dependency?rev={revision}#{revision}\"\n"
    );
    std::fs::write(app.join("Cargo.lock"), &lock).unwrap();
    let mut gctx =
        crate::GlobalContext::new(cargo_util_terminal::Shell::new(), app.clone(), destination);
    gctx.configure(
        0,
        false,
        None,
        false,
        true,
        true,
        &None,
        &[],
        &[
            "resolver.incompatible-rust-versions='allow'".into(),
            "net.git-fetch-with-cli=true".into(),
        ],
    )
    .unwrap();
    let ws = crate::workspace::Workspace::new(&app.join("Cargo.toml"), &gctx).unwrap();
    let (resolved, _) = crate::ops::fetch(
        &ws,
        &crate::ops::FetchOptions {
            gctx: &gctx,
            targets: Vec::new(),
        },
    )
    .unwrap();
    assert_eq!(resolved.iter().count(), 2);
    assert_eq!(
        std::fs::read_to_string(app.join("Cargo.lock")).unwrap(),
        lock
    );
}

#[test]
fn checkout_names_distinguish_tracked_nested_markers_from_root_metadata() {
    for root in [false, true] {
        for name in ["", ".", "..", "a/b", ".git"] {
            assert!(super::checkout::validate_checkout_name(OsStr::new(name), root).is_err());
        }
    }
    assert!(super::checkout::validate_checkout_name(OsStr::new(".cargo-ok"), true).is_err());
    super::checkout::validate_checkout_name(OsStr::new(".cargo-ok"), false).unwrap();
}

#[test]
fn complete_checkout_changed_file_mode_reference_and_untracked_data_refuse() {
    for mutation in [
        "bytes",
        "mode",
        "reference",
        "extra",
        "link",
        "link-target",
        "nested-marker",
        "untracked-marker",
    ] {
        let (_world, root, donor) = fixture();
        let checkout = complete_checkout(&donor);
        // Even a preexisting copied completion marker cannot discharge a join.
        std::fs::write(checkout.join(".cargo-ok"), "").unwrap();
        match mutation {
            "bytes" => std::fs::write(checkout.join("lib.rs"), "different source").unwrap(),
            "mode" => std::fs::set_permissions(
                checkout.join("tool"),
                std::fs::Permissions::from_mode(0o644),
            )
            .unwrap(),
            "reference" => {
                std::fs::write(checkout.join(".git/HEAD"), format!("{}\n", "1".repeat(40))).unwrap()
            }
            "extra" => std::fs::write(checkout.join("extra.rs"), "untracked").unwrap(),
            "nested-marker" => {
                std::fs::write(checkout.join("nested/.cargo-ok"), "forged marker").unwrap()
            }
            "untracked-marker" => {
                std::fs::write(checkout.join(".cargo-ok-untracked"), "untracked marker").unwrap()
            }
            "link-target" => {
                std::fs::remove_file(checkout.join("alias.rs")).unwrap();
                symlink("tool", checkout.join("alias.rs")).unwrap();
            }
            "link" => {
                std::fs::remove_file(checkout.join("lib.rs")).unwrap();
                symlink(checkout.join("Cargo.toml"), checkout.join("lib.rs")).unwrap();
            }
            _ => unreachable!(),
        }
        let output = root.join("output");
        assert!(import(&donor, &output, None).is_err(), "{mutation}");
        assert!(!output.exists());
    }
}

#[test]
fn symbolic_checkout_head_joins_the_original_branch_without_repository_configuration() {
    let (_world, root, donor) = fixture();
    let checkout = complete_checkout(&donor);
    let git = checkout.join(".git");
    std::fs::create_dir_all(git.join("refs/heads")).unwrap();
    let revision = std::fs::read_to_string(donor.join("revision")).unwrap();
    std::fs::write(git.join("refs/heads/master"), format!("{revision}\n")).unwrap();
    std::fs::write(git.join("HEAD"), "ref: refs/heads/master\n").unwrap();
    let output = root.join("output");
    import(&donor, &output, None).unwrap();
    let selected = output.join(checkout.strip_prefix(&donor).unwrap());
    assert_eq!(
        git2::Repository::open(selected)
            .unwrap()
            .head()
            .unwrap()
            .target(),
        Some(revision.parse().unwrap())
    );
    std::fs::write(
        git.join("refs/heads/master"),
        format!("{}\n", "1".repeat(40)),
    )
    .unwrap();
    assert!(import(&donor, &root.join("wrong-branch"), None).is_err());
    std::fs::write(git.join("refs/heads/master"), format!("{revision}\n")).unwrap();
    std::fs::write(git.join("HEAD"), "ref: refs/heads/../../outside\n").unwrap();
    assert!(import(&donor, &root.join("escape"), None).is_err());
    std::fs::write(git.join("HEAD"), "ref: refs/heads/master\n").unwrap();
    std::fs::remove_file(git.join("refs/heads/master")).unwrap();
    symlink(donor.join("revision"), git.join("refs/heads/master")).unwrap();
    assert!(import(&donor, &root.join("linked-branch"), None).is_err());
}

#[test]
fn stored_snapshot_preserves_git_objects_refs_and_registry_data_without_configuration() {
    let (_world, root, donor) = fixture();
    for name in ["config.toml", "credentials.toml"] {
        std::fs::write(donor.join(name), b"must not propagate").unwrap();
    }
    let db = database(&donor);
    std::fs::create_dir_all(db.join("hooks")).unwrap();
    std::fs::write(
        db.join("hooks/pre-upload-pack"),
        b"must not execute or propagate",
    )
    .unwrap();
    let destination = root.join("output");
    let stats = import(&donor, &destination, Some("index-fixture")).unwrap();
    assert!(stats.files >= 5 && stats.bytes > 0);
    assert_eq!(stats.bytes, stats.cloned_bytes + stats.streamed_bytes);
    assert!(!destination.join("config.toml").exists());
    assert!(!destination.join("credentials.toml").exists());
    let destination_db = destination
        .join("git/db")
        .join(crate::sources::git::source::ident(&source(&donor)));
    assert!(!destination_db.join("hooks").exists());
    let oid: git2::Oid = std::fs::read_to_string(donor.join("blob-id"))
        .unwrap()
        .parse()
        .unwrap();
    let repository = git2::Repository::open_bare(destination_db).unwrap();
    assert_eq!(
        repository.find_blob(oid).unwrap().content(),
        b"actual original DATA"
    );
    assert_eq!(
        std::fs::read(destination.join("registry/cache/index-fixture/example-1.0.0.crate"))
            .unwrap(),
        b"archive DATA"
    );
    assert_eq!(
        std::fs::read(destination.join("registry/index/index-fixture/config.json")).unwrap(),
        REGISTRY_CONFIG
    );
}

#[test]
fn routing_credentials_symlinks_and_git_indirection_refuse_without_publication() {
    let (_world, root, donor) = fixture();
    let config = donor.join("registry/index/index-fixture/config.json");
    std::fs::write(
        &config,
        br#"{"dl":"https://attacker.invalid","api":"https://crates.io"}"#,
    )
    .unwrap();
    assert!(import(&donor, &root.join("wrong-routing"), Some("index-fixture")).is_err());
    assert!(!root.join("wrong-routing").exists());
    std::fs::write(config, REGISTRY_CONFIG).unwrap();
    let cache = donor.join("registry/cache/index-fixture/example-1.0.0.crate");
    std::fs::remove_file(&cache).unwrap();
    symlink(donor.join("blob-id"), &cache).unwrap();
    assert!(import(&donor, &root.join("symlink"), Some("index-fixture")).is_err());
    assert!(!root.join("symlink").exists());
    std::fs::remove_file(cache).unwrap();
    let credential = donor.join("registry/cache/index-fixture/credentials.toml");
    std::fs::write(&credential, b"excluded credential-shaped cache entry").unwrap();
    assert!(
        import(
            &donor,
            &root.join("credential-entry"),
            Some("index-fixture")
        )
        .is_err()
    );
    assert!(!root.join("credential-entry").exists());
    std::fs::remove_file(credential).unwrap();
    std::fs::write(
        database(&donor).join("objects/info/alternates"),
        b"/outside",
    )
    .unwrap();
    assert!(import(&donor, &root.join("alternates"), None).is_err());
    assert!(!root.join("alternates").exists());
}

#[test]
fn stored_bound_refuses_before_copy_and_original_tree_replacement_is_sticky() {
    let (_world, root, donor) = fixture();
    let source_path = donor.join("registry/cache/index-fixture");
    let tree = Tree::capture(Directory::open(&source_path).unwrap()).unwrap();
    std::fs::rename(&source_path, donor.join("original-cache")).unwrap();
    std::fs::create_dir(&source_path).unwrap();
    assert!(tree.source.check_current().is_err());
    std::fs::remove_dir(&source_path).unwrap();
    std::fs::rename(donor.join("original-cache"), &source_path).unwrap();
    assert!(tree.source.check_current().is_err());
    let stage = Stage::new(&root.join("output"), &[&donor]).unwrap();
    let mut output = Output::new(&stage).unwrap();
    let mut input = tempfile::tempfile().unwrap();
    let mut stats = Stats {
        bytes: super::super::super::MAX_TOTAL_BYTES,
        ..Stats::default()
    };
    let mut budget = CopyBudget::new(0).unwrap();
    assert!(
        output
            .copy(
                Path::new("too-much"),
                &mut input,
                1,
                &mut stats,
                &mut budget
            )
            .is_err()
    );
    assert!(!stage.path().join("too-much").exists());
}

#[test]
fn snapshot_cache_owner_excludes_mutation_on_original_descriptions() {
    let (_world, _root, donor) = fixture();
    let held = Cache::source(&donor).unwrap();
    for name in LOCKS {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(donor.join(name))
            .unwrap();
        assert!(
            rustix::fs::flock(&file, rustix::fs::FlockOperation::NonBlockingLockExclusive).is_err()
        );
    }
    held.check_current().unwrap();
    drop(held);
    for name in LOCKS {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(donor.join(name))
            .unwrap();
        rustix::fs::flock(&file, rustix::fs::FlockOperation::NonBlockingLockExclusive).unwrap();
    }
}

#[test]
fn duplicate_or_unknown_routing_keys_refuse_and_registry_only_home_remains_supported() {
    let (_world, root, donor) = fixture();
    let config = donor.join("registry/index/index-fixture/config.json");
    for (name, bytes) in [
        ("duplicate", br#"{"dl":"https://attacker.invalid","dl":"https://static.crates.io/crates","api":"https://crates.io"}"#.as_slice()),
        ("unknown", br#"{"dl":"https://static.crates.io/crates","api":"https://crates.io","token":"must not propagate"}"#.as_slice()),
    ] {
        std::fs::write(&config, bytes).unwrap();
        assert!(import(&donor, &root.join(name), Some("index-fixture")).is_err());
        assert!(!root.join(name).exists());
    }
    std::fs::write(config, REGISTRY_CONFIG).unwrap();
    // A registry-only Cargo home has no Git subtree to materialize.
    std::fs::rename(donor.join("git"), root.join("unused-git")).unwrap();
    let destination = root.join("registry-only");
    import(&donor, &destination, Some("index-fixture")).unwrap();
    assert!(!destination.join("git").exists());
    assert_eq!(
        std::fs::read(destination.join("registry/cache/index-fixture/example-1.0.0.crate"))
            .unwrap(),
        b"archive DATA"
    );
}

#[test]
fn scoped_output_reopens_require_the_factory_inode_before_any_write() {
    let (_world, root, donor) = fixture();
    let stage = Stage::new(&root.join("output"), &[&donor]).unwrap();
    let mut output = Output::new(&stage).unwrap();
    output.directory(Path::new("data/child")).unwrap();
    let original = stage.path().join("data/child");
    std::fs::rename(&original, stage.path().join("data/original-child")).unwrap();
    std::fs::create_dir(&original).unwrap();
    std::fs::set_permissions(&original, std::fs::Permissions::from_mode(0o700)).unwrap();
    let mut source = tempfile::tempfile().unwrap();
    source.write_all(b"must not enter replacement").unwrap();
    source.rewind().unwrap();
    assert!(
        output
            .copy(
                Path::new("data/child/value"),
                &mut source,
                26,
                &mut Stats::default(),
                &mut CopyBudget::new(32).unwrap()
            )
            .is_err()
    );
    assert!(std::fs::read_dir(original).unwrap().next().is_none());
    assert!(!root.join("output").exists());
}

#[test]
fn separate_registry_owner_supplies_only_registry_data_and_same_home_is_deduplicated() {
    let (_world, root, donor) = fixture();
    let registry_donor = root.join("registry-owner");
    std::fs::create_dir(&registry_donor).unwrap();
    std::fs::set_permissions(&registry_donor, std::fs::Permissions::from_mode(0o700)).unwrap();
    for lock in LOCKS {
        File::create(registry_donor.join(lock)).unwrap();
    }
    std::fs::rename(donor.join("registry"), registry_donor.join("registry")).unwrap();
    std::fs::write(
        registry_donor.join("credentials.toml"),
        b"never inspect or copy",
    )
    .unwrap();
    // Even malformed non-registry namespaces are outside this donor's role.
    symlink(root.join("missing-git"), registry_donor.join("git")).unwrap();
    let destination = root.join("two-owner-output");
    let stats = super::import_selected(
        &donor,
        &destination,
        Some("index-fixture"),
        Some(&registry_donor),
        selected(&donor),
        &[],
    )
    .unwrap();
    assert!(stats.bytes > 0);
    assert!(
        destination
            .join("git/db")
            .join(crate::sources::git::source::ident(&source(&donor)))
            .join("HEAD")
            .is_file()
    );
    assert_eq!(
        std::fs::read(destination.join("registry/cache/index-fixture/example-1.0.0.crate"))
            .unwrap(),
        b"archive DATA"
    );
    assert!(!destination.join("credentials.toml").exists());
    assert!(
        super::import_selected(
            &registry_donor,
            &root.join("unused"),
            None,
            Some(&registry_donor),
            Vec::new(),
            &[],
        )
        .is_err()
    );
    assert!(!root.join("unused").exists());
    // Existing single-owner cases acquire that home exactly once. Verify the
    // explicit same-home spelling also completes rather than locking itself.
    std::fs::remove_file(registry_donor.join("git")).unwrap();
    super::import_selected(
        &registry_donor,
        &root.join("same-owner-output"),
        Some("index-fixture"),
        Some(&registry_donor),
        Vec::new(),
        &[],
    )
    .unwrap();
}

#[test]
fn selected_snapshot_ignores_unrelated_databases_and_derived_graphs_but_binds_exact_revision() {
    let (_world, root, donor) = fixture();
    let unrelated = donor.join("git/db/unselected/objects/info");
    std::fs::create_dir_all(&unrelated).unwrap();
    std::fs::write(unrelated.join("alternates"), b"/not-a-selected-input").unwrap();
    let graphs = database(&donor).join("objects/info/commit-graphs");
    std::fs::create_dir_all(&graphs).unwrap();
    std::fs::write(graphs.join("derived.graph"), b"never supplied to Git").unwrap();
    let destination = root.join("selected");
    import(&donor, &destination, None).unwrap();
    assert!(!destination.join("git/db/unselected").exists());
    let selected_db = destination
        .join("git/db")
        .join(crate::sources::git::source::ident(&source(&donor)));
    assert!(!selected_db.join("objects/info/commit-graphs").exists());
    let revision = std::fs::read_to_string(donor.join("revision")).unwrap();
    assert_eq!(
        std::fs::read_to_string(selected_db.join("refs/commit").join(&revision)).unwrap(),
        format!("{revision}\n")
    );
    let missing = SourceId::for_git(source(&donor).url(), GitReference::Rev("f".repeat(40)))
        .unwrap()
        .with_git_precise(Some("f".repeat(40)));
    assert!(
        super::import_selected(
            &donor,
            &root.join("missing"),
            None,
            None,
            vec![missing],
            &[]
        )
        .is_err()
    );
    assert!(!root.join("missing").exists());
    // Normal Cargo locks a branch/tag/default source to its actual precise OID
    // too. Stored DATA must preserve this existing capability; the separate
    // expanded-history importer retains its strict full-revision profile.
    let branch = SourceId::for_git(source(&donor).url(), GitReference::Branch("main".into()))
        .unwrap()
        .with_git_precise(Some(revision));
    super::import_selected(
        &donor,
        &root.join("locked-branch"),
        None,
        None,
        vec![branch],
        &[],
    )
    .unwrap();
}

#[test]
fn explicit_original_object_selector_is_checked_and_unused_selection_refuses() {
    let (_world, root, donor) = fixture();
    let objects = database(&donor).join("objects");
    let selected = vec![(source(&donor).url().clone(), objects.clone())];
    super::import_selected(
        &donor,
        &root.join("explicit"),
        None,
        None,
        vec![source(&donor)],
        &selected,
    )
    .unwrap();
    let foreign = vec![(
        url::Url::parse("https://example.invalid/foreign").unwrap(),
        objects,
    )];
    assert!(
        super::import_selected(
            &donor,
            &root.join("foreign"),
            None,
            None,
            vec![source(&donor)],
            &foreign
        )
        .is_err()
    );
    assert!(!root.join("foreign").exists());
}

#[test]
fn selected_snapshot_recurses_the_actual_gitlink_and_missing_child_cannot_publish() {
    let (_world, root, donor) = fixture();
    let child_url = url::Url::parse("https://example.invalid/child").unwrap();
    let preliminary = SourceId::for_git(&child_url, GitReference::Rev("0".repeat(40))).unwrap();
    let child_path = donor
        .join("git/db")
        .join(crate::sources::git::source::ident(&preliminary));
    let mut options = git2::RepositoryInitOptions::new();
    options.bare(true).external_template(false);
    let child = git2::Repository::init_opts(&child_path, &options).unwrap();
    let empty = child.treebuilder(None).unwrap().write().unwrap();
    let tree = child.find_tree(empty).unwrap();
    let signature = git2::Signature::now("Child DATA", "fixture@example.invalid").unwrap();
    let child_commit = child
        .commit(None, &signature, &signature, "child", &tree, &[])
        .unwrap();
    drop(tree);
    drop(child);
    let parent = git2::Repository::open_bare(database(&donor)).unwrap();
    let modules = parent
        .blob(format!("[submodule \"child\"]\npath = child\nurl = {child_url}\n").as_bytes())
        .unwrap();
    let mut builder = parent.treebuilder(None).unwrap();
    builder.insert(".gitmodules", modules, 0o100644).unwrap();
    builder.insert("child", child_commit, 0o160000).unwrap();
    let tree_id = builder.write().unwrap();
    drop(builder);
    let tree = parent.find_tree(tree_id).unwrap();
    let revision = parent
        .commit(None, &signature, &signature, "with child", &tree, &[])
        .unwrap();
    std::fs::write(donor.join("revision"), revision.to_string()).unwrap();
    drop(tree);
    drop(parent);
    let destination = root.join("complete");
    import(&donor, &destination, None).unwrap();
    let copied_child = git2::Repository::open_bare(
        destination
            .join("git/db")
            .join(crate::sources::git::source::ident(&preliminary)),
    )
    .unwrap();
    copied_child.find_commit(child_commit).unwrap();
    drop(copied_child);
    std::fs::rename(child_path, root.join("retained-child")).unwrap();
    assert!(import(&donor, &root.join("incomplete"), None).is_err());
    assert!(!root.join("incomplete").exists());
}

#[test]
fn checkout_link_targets_reject_escape_chain_and_ambiguous_parent_resolution() {
    let (_world, _root, donor) = fixture();
    complete_checkout(&donor);
    let repository = git2::Repository::open_bare(database(&donor)).unwrap();
    let tree = repository
        .find_commit(super::super::super::locked_oid(source(&donor)).unwrap())
        .unwrap()
        .tree()
        .unwrap();
    use super::checkout::validate_link_target;
    assert!(validate_link_target(&tree, Path::new("nested/LICENSE"), b"../lib.rs").is_ok());
    for target in [
        b"../../lib.rs".as_slice(),
        b"/lib.rs",
        b"../alias.rs",
        b"../nested/LICENSE",
        b"a/../../lib.rs",
        b".././lib.rs",
        b"..//lib.rs",
        b"../missing",
        b"../lib.rs\0",
    ] {
        assert!(
            validate_link_target(&tree, Path::new("nested/LICENSE"), target).is_err(),
            "{target:?}"
        );
    }
}

#[test]
fn created_checkout_link_replacement_cannot_satisfy_original_output_bookends() {
    let (_world, root, _donor) = fixture();
    let stage = Stage::new(&root.join("output"), &[]).unwrap();
    let mut output = Output::new(&stage).unwrap();
    let mut stats = Stats::default();
    let mut budget = CopyBudget::new(1024).unwrap();
    output
        .link(Path::new("alias"), b"file", &mut stats, &mut budget)
        .unwrap();
    output.check_current().unwrap();
    let path = stage.path().join("alias");
    std::fs::remove_file(&path).unwrap();
    symlink("file", &path).unwrap();
    assert!(output.check_current().is_err());
}

#[test]
fn stored_and_expanded_entry_domains_remain_finite_and_do_not_reset_each_other() {
    let mut budget = EntryBudget {
        stored: MAX_ENTRIES - 1,
        checkouts: MAX_CHECKOUT_ENTRIES - 1,
    };
    budget
        .reserve(Path::new("git/db/source/objects/aa/object"))
        .unwrap();
    budget
        .reserve(Path::new("git/checkouts/source/revision/last"))
        .unwrap();
    for path in [
        "registry/cache/index/file.crate",
        "git/db/other/config",
        "git/checkouts-escape/file",
    ] {
        assert!(
            budget.reserve(Path::new(path)).is_err(),
            "original stored cap changed: {path}"
        );
    }
    assert!(
        budget
            .reserve(Path::new("git/checkouts/source/revision/extra"))
            .is_err()
    );
    assert_eq!(
        (budget.stored, budget.checkouts),
        (MAX_ENTRIES, MAX_CHECKOUT_ENTRIES)
    );
}

#[test]
fn actual_output_entries_charge_their_original_domains_across_shared_parents() {
    let (_world, root, _) = fixture();
    let stage = Stage::new(&root.join("output"), &[]).unwrap();
    let mut output = Output::new(&stage).unwrap();
    let mut stats = Stats::default();
    let mut budget = CopyBudget::new(1024).unwrap();
    output
        .generated(
            Path::new("git/db/source/HEAD"),
            b"stored",
            &mut stats,
            &mut budget,
        )
        .unwrap();
    output
        .generated(
            Path::new("git/checkouts/source/revision/file"),
            b"checkout",
            &mut stats,
            &mut budget,
        )
        .unwrap();
    output.check_current().unwrap();
    assert_eq!((output.entries.stored, output.entries.checkouts), (4, 4));
    assert_eq!(
        output.entries.stored + output.entries.checkouts,
        output.files.len() + output.directories.len()
    );
}

#[test]
fn multiple_actual_locked_workspaces_snapshot_one_guarded_source_union() {
    let (_world, root, donor) = fixture();
    complete_checkout(&donor);
    let first = source(&donor);
    let revision = std::fs::read_to_string(donor.join("revision")).unwrap();
    let second_url = url::Url::parse("https://example.invalid/second").unwrap();
    let second = SourceId::for_git(&second_url, GitReference::Rev(revision.clone()))
        .unwrap()
        .with_git_precise(Some(revision.clone()));
    let destination = root.join("output");
    let mut manifests = Vec::new();
    for (name, source) in [("first-app", first), ("second-app", second)] {
        let app = root.join(name);
        std::fs::create_dir_all(app.join("src")).unwrap();
        let url = source.url();
        std::fs::write(app.join("Cargo.toml"),format!("[workspace]\n[package]\nname='{name}'\nversion='0.1.0'\nedition='2021'\n[dependencies]\ncheckout-data-dep={{git='{url}',rev='{revision}'}}\n")).unwrap();
        std::fs::write(app.join("src/lib.rs"), "").unwrap();
        std::fs::write(app.join("Cargo.lock"),format!("version = 4\n\n[[package]]\nname = \"{name}\"\nversion = \"0.1.0\"\ndependencies = [\n \"checkout-data-dep\",\n]\n\n[[package]]\nname = \"checkout-data-dep\"\nversion = \"0.1.0\"\nsource = \"git+{url}?rev={revision}#{revision}\"\n")).unwrap();
        manifests.push(app.join("Cargo.toml"));
    }
    let mut gctx = crate::GlobalContext::new(
        cargo_util_terminal::Shell::new(),
        root.clone(),
        destination.clone(),
    );
    gctx.configure(
        0,
        false,
        None,
        false,
        true,
        true,
        &None,
        &[],
        &[
            "resolver.incompatible-rust-versions='allow'".into(),
            "net.git-fetch-with-cli=true".into(),
        ],
    )
    .unwrap();
    let primary = crate::workspace::Workspace::new(&manifests[0], &gctx).unwrap();
    super::super::super::snapshot_locked_cache_data_workspaces(
        &primary,
        &manifests[1..],
        &donor,
        None,
        &[(second_url, database(&donor).join("objects"))],
    )
    .unwrap();
    for (manifest, source) in manifests.iter().zip([first, second]) {
        let db = destination
            .join("git/db")
            .join(crate::sources::git::source::ident(&source));
        assert!(
            git2::Repository::open_bare(db)
                .unwrap()
                .find_commit(revision.parse().unwrap())
                .is_ok()
        );
        let ws = crate::workspace::Workspace::new(manifest, &gctx).unwrap();
        let (resolved, _) = crate::ops::fetch(
            &ws,
            &crate::ops::FetchOptions {
                gctx: &gctx,
                targets: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(resolved.iter().count(), 2);
    }
}
