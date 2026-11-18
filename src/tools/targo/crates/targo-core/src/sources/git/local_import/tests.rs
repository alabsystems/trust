use super::*;
use std::fs::File;
use std::os::unix::fs::PermissionsExt as _;

pub(super) fn private_world() -> tempfile::TempDir {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-local-source-unit.noindex");
    std::fs::create_dir_all(&base).unwrap();
    tempfile::Builder::new()
        .prefix("source-")
        .permissions(std::fs::Permissions::from_mode(0o700))
        .tempdir_in(base)
        .unwrap()
}

struct Fixture {
    _world: tempfile::TempDir,
    root: std::path::PathBuf,
    donor: std::path::PathBuf,
    repository: git2::Repository,
    source: SourceId,
    first: git2::Oid,
    last: git2::Oid,
    blob: git2::Oid,
}

impl Fixture {
    fn new() -> Self {
        let world = private_world();
        let root = world.path().canonicalize().unwrap();
        let donor = root.join("donor");
        std::fs::create_dir(&donor).unwrap();
        for name in [".package-cache-mutate", ".package-cache"] {
            File::create(donor.join(name)).unwrap();
        }
        let url = url::Url::parse("https://github.com/source-data-fixture/dep").unwrap();
        let preliminary = SourceId::for_git(&url, GitReference::Rev("0".repeat(40))).unwrap();
        let path = donor
            .join("git/db")
            .join(super::super::source::ident(&preliminary));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let mut options = git2::RepositoryInitOptions::new();
        options
            .bare(true)
            .external_template(false)
            .initial_head("master");
        let repository = git2::Repository::init_opts(path, &options).unwrap();
        let signature = git2::Signature::now("Source fixture", "fixture@example.invalid").unwrap();
        let blob = repository.blob(b"first source bytes\n").unwrap();
        let mut builder = repository.treebuilder(None).unwrap();
        builder.insert("source.txt", blob, 0o100644).unwrap();
        let tree_id = builder.write().unwrap();
        drop(builder);
        let tree = repository.find_tree(tree_id).unwrap();
        let first = repository
            .commit(None, &signature, &signature, "first", &tree, &[])
            .unwrap();
        let parent = repository.find_commit(first).unwrap();
        let last = repository
            .commit(None, &signature, &signature, "second", &tree, &[&parent])
            .unwrap();
        drop(parent);
        drop(tree);
        let source = SourceId::for_git(&url, GitReference::Rev(last.to_string()))
            .unwrap()
            .with_git_precise(Some(last.to_string()));
        Self {
            _world: world,
            root,
            donor,
            repository,
            source,
            first,
            last,
            blob,
        }
    }

    fn destination(&self) -> std::path::PathBuf {
        self.root.join("fresh-home")
    }

    fn import(&self) -> CargoResult<Stats> {
        import(&self.donor, &self.destination(), vec![self.source])
    }
}

#[test]
fn exact_locked_objects_keep_complete_parent_history_without_donor_refs_or_config() {
    let fixture = Fixture::new();
    fixture
        .repository
        .reference(
            "refs/heads/unrelated-donor-name",
            fixture.first,
            false,
            "fixture",
        )
        .unwrap();
    let stats = fixture.import().unwrap();
    assert_eq!(stats.sources, 1);
    assert_eq!(stats.objects, 4); // two commits, one tree, one blob
    let path = fixture
        .destination()
        .join("git/db")
        .join(super::super::source::ident(&fixture.source));
    let output = git2::Repository::open_bare(path).unwrap();
    assert_eq!(
        output
            .find_commit(fixture.last)
            .unwrap()
            .parent_id(0)
            .unwrap(),
        fixture.first
    );
    assert_eq!(
        output.find_blob(fixture.blob).unwrap().content(),
        b"first source bytes\n"
    );
    assert!(
        output
            .find_reference("refs/heads/unrelated-donor-name")
            .is_err()
    );
    assert_eq!(
        output
            .find_reference(&format!("refs/commit/{}", fixture.last))
            .unwrap()
            .target(),
        Some(fixture.last)
    );
    for absent in ["config", "config.toml", "bin", "git/checkouts", "registry"] {
        assert!(!fixture.destination().join(absent).exists());
    }
    assert!(!output.path().join("objects/info/alternates").exists());
    assert!(
        fixture.import().is_err(),
        "published homes are never adopted"
    );
}

#[test]
fn packed_native_objects_are_imported_without_a_git_process() {
    let fixture = Fixture::new();
    let mut walk = fixture.repository.revwalk().unwrap();
    walk.push(fixture.last).unwrap();
    let mut pack = fixture.repository.packbuilder().unwrap();
    pack.insert_walk(&mut walk).unwrap();
    pack.write(&fixture.repository.path().join("objects/pack"), 0)
        .unwrap();
    drop(pack);
    for entry in std::fs::read_dir(fixture.repository.path().join("objects")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name().to_string_lossy().len() == 2 {
            std::fs::remove_dir_all(entry.path()).unwrap();
        }
    }
    assert_eq!(fixture.import().unwrap().objects, 4);
}

#[test]
fn preflight_uses_the_same_full_closure_and_never_writes_output_objects() {
    let fixture = Fixture::new();
    let (planned, requirements) = inspect_sources(
        Some(&fixture.donor),
        &[],
        &fixture.destination(),
        vec![fixture.source],
        MAX_TOTAL_BYTES,
        true,
    )
    .unwrap();
    assert_eq!((planned.sources, planned.objects), (1, 4));
    assert_eq!(requirements.len(), 1);
    assert!(requirements[0]["children"].as_array().unwrap().is_empty());
    assert!(!fixture.destination().exists());
    let staged = std::fs::read_dir(&fixture.root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with(".targo-git-source-import-")
        })
        .collect::<Vec<_>>();
    assert_eq!(staged.len(), 1);
    assert!(!staged[0].join("home/git").exists());
    assert!(
        std::fs::read_dir(staged[0].join("views"))
            .unwrap()
            .next()
            .is_none()
    );
    let imported = fixture.import().unwrap();
    assert_eq!(
        (planned.sources, planned.objects, planned.bytes),
        (imported.sources, imported.objects, imported.bytes)
    );
}

#[test]
fn failed_preflight_retains_views_and_never_publishes_partial_data() {
    let fixture = Fixture::new();
    let hex = fixture.first.to_string();
    std::fs::remove_file(
        fixture
            .repository
            .path()
            .join("objects")
            .join(&hex[..2])
            .join(&hex[2..]),
    )
    .unwrap();
    assert!(
        inspect_sources(
            Some(&fixture.donor),
            &[],
            &fixture.destination(),
            vec![fixture.source],
            MAX_TOTAL_BYTES,
            true
        )
        .is_err()
    );
    assert!(!fixture.destination().exists());
    let staged = std::fs::read_dir(&fixture.root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with(".targo-git-source-import-")
        })
        .unwrap();
    assert!(!staged.join("home/git").exists());
    assert!(
        std::fs::read_dir(staged.join("views"))
            .unwrap()
            .next()
            .is_some()
    );
    assert_eq!(
        std::fs::read(staged.join("home/.targo-source-data-state")).unwrap(),
        b"targo-source-data-v1\nquarantined-no-adoption\n"
    );
}

#[test]
fn source_requirement_display_omits_url_credentials() {
    let url =
        url::Url::parse("https://private-user:secret-passphrase@example.invalid/repo").unwrap();
    let displayed = display_url(&url).unwrap();
    assert_eq!(displayed, "https://example.invalid/repo");
}

#[test]
fn closure_limit_reports_the_next_locked_object_without_url_components() {
    let fixture = Fixture::new();
    let url = url::Url::parse(
        "https://user-fixture:password-fixture@example.invalid/team/path-fixture?token=query-fixture#fragment-fixture",
    )
    .unwrap();
    // One database can be reused for more than one revision. The refusal
    // must name the current locked request, even when the representative
    // which identifies this provider was an earlier revision.
    let representative = SourceId::for_git(&url, GitReference::Rev(fixture.first.to_string()))
        .unwrap()
        .with_git_precise(Some(fixture.first.to_string()));
    let ident = super::super::source::ident(&representative);
    let (_, provider) = ident.rsplit_once('-').unwrap();
    let objects = fixture.repository.path().join("objects");
    let original = custody::ObjectSource::capture_objects(&objects).unwrap();
    let stage = custody::Stage::new(&fixture.destination(), &[&objects]).unwrap();
    let mut view = stage.create_view(&ident).unwrap();
    original
        .materialize_view(
            &objects,
            &mut view,
            MAX_TOTAL_BYTES,
            &mut custody::CopyBudget::new(MAX_TOTAL_BYTES).unwrap(),
        )
        .unwrap();
    let odb = git2::Odb::new().unwrap();
    odb.add_disk_alternate(view.path().to_str().unwrap())
        .unwrap();
    let (selected_bytes, _) = odb.read_header(fixture.last).unwrap();
    let (parent_bytes, _) = odb.read_header(fixture.first).unwrap();
    let mut database = Database {
        representative,
        input: git2::Repository::from_odb(odb).unwrap(),
        output: None,
        view,
        original,
        copied: HashMap::default(),
    };
    // The real selected commit reaches equality. The real parent is next
    // in the walk and its header pushes the aggregate over the same guard.
    let mut stats = Stats {
        objects: 7,
        bytes: MAX_TOTAL_BYTES - selected_bytes as u64,
        ..Stats::default()
    };
    let error = inspect_closure(
        &mut database,
        fixture.last,
        &mut stats,
        &mut pack_stream::ReadBudget::default(),
    )
    .unwrap_err()
    .to_string();
    assert!(error.contains(&format!(
        "for provider {provider} at locked revision {}",
        fixture.last
    )));
    assert!(error.contains(&format!(
        "after verifying 8 objects and {MAX_TOTAL_BYTES} logical bytes"
    )));
    assert!(error.contains(&format!(
        "Next object {} declares {parent_bytes} logical bytes",
        fixture.first
    )));
    for omitted in [
        "user-fixture",
        "password-fixture",
        "example.invalid",
        "path-fixture",
        "query-fixture",
        "fragment-fixture",
    ] {
        assert!(!error.contains(omitted));
    }
    assert_eq!((stats.objects, stats.bytes), (8, MAX_TOTAL_BYTES));
    assert!(!fixture.destination().exists());
    assert!(!stage.path().join("git").exists());
}

#[test]
fn standalone_object_data_keeps_history_without_reading_repository_policy() {
    let fixture = Fixture::new();
    // These enclosing repository controls are outside this DATA-only input.
    // Neither their bytes nor any configured execution reaches the private ODB.
    for name in ["config", "info/grafts", "shallow"] {
        let path = fixture.repository.path().join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, b"[include]\npath = never-read-policy\n").unwrap();
    }
    let objects = fixture.repository.path().join("objects");
    let stats = import_sources(
        None,
        &[(fixture.source.url().clone(), objects)],
        &fixture.destination(),
        vec![fixture.source],
    )
    .unwrap();
    assert_eq!((stats.sources, stats.objects), (1, 4));
    let output = git2::Repository::open_bare(
        fixture
            .destination()
            .join("git/db")
            .join(super::super::source::ident(&fixture.source)),
    )
    .unwrap();
    assert_eq!(
        output
            .find_commit(fixture.last)
            .unwrap()
            .parent_id(0)
            .unwrap(),
        fixture.first
    );
    assert_eq!(
        output.find_blob(fixture.blob).unwrap().content(),
        b"first source bytes\n"
    );
    assert!(!output.path().join("info/grafts").exists());
    assert!(!output.path().join("shallow").exists());
    assert!(!output.path().join("objects/info/alternates").exists());
}

#[test]
fn explicit_object_input_never_falls_back_for_missing_history_or_bad_bytes() {
    for (missing, corrupt) in [(true, false), (false, false), (false, true)] {
        let fixture = Fixture::new();
        let objects = fixture.repository.path().join("objects");
        let separate = fixture.root.join("standalone");
        let original = custody::ObjectSource::capture_objects(&objects).unwrap();
        original
            .materialize_objects(
                &objects,
                &separate,
                MAX_TOTAL_BYTES,
                &mut custody::CopyBudget::new(MAX_TOTAL_BYTES).unwrap(),
            )
            .unwrap();
        let oid = if missing { fixture.first } else { fixture.blob }.to_string();
        let path = separate.join(&oid[..2]).join(&oid[2..]);
        std::fs::remove_file(&path).unwrap();
        if corrupt {
            std::fs::write(path, b"not a Git object").unwrap();
        }
        // Cargo fallback still has all valid bytes. An explicit bad input must
        // refuse rather than silently use that different provider.
        assert!(
            import_sources(
                Some(&fixture.donor),
                &[(fixture.source.url().clone(), separate)],
                &fixture.destination(),
                vec![fixture.source]
            )
            .is_err()
        );
        assert!(!fixture.destination().exists());
    }
}

#[test]
fn missing_original_objects_keep_source_revision_and_typed_cause_without_url_secrets() {
    for selected in [false, true] {
        for missing in ["commit", "blob", "parent"] {
            let fixture = Fixture::new();
            let url = url::Url::parse(
                "https://user-fixture:password-fixture@github.com/Source-Fixture/Dependency.git?token=query-fixture#fragment-fixture",
            )
            .unwrap();
            let source = SourceId::for_git(&url, GitReference::Rev(fixture.last.to_string()))
                .unwrap()
                .with_git_precise(Some(fixture.last.to_string()));
            let earlier = SourceId::for_git(&url, GitReference::Rev(fixture.first.to_string()))
                .unwrap()
                .with_git_precise(Some(fixture.first.to_string()));
            let oid = match missing {
                "commit" => fixture.last,
                "blob" => fixture.blob,
                _ => fixture.first,
            };
            let objects = fixture.repository.path().join("objects");
            let hex = oid.to_string();
            std::fs::remove_file(objects.join(&hex[..2]).join(&hex[2..])).unwrap();
            // The same provider serves multiple original revisions. Attribution
            // must use the failing selected request, not its representative.
            let sources = if missing == "commit" {
                vec![earlier, source]
            } else {
                vec![source]
            };
            let selectors = [(url, objects)];
            let error = if selected {
                custody::snapshot::import_selected(
                    &fixture.donor,
                    &fixture.destination(),
                    None,
                    None,
                    sources,
                    &selectors,
                )
                .unwrap_err()
            } else {
                import_sources(None, &selectors, &fixture.destination(), sources).unwrap_err()
            };
            let displayed = format!("{error:#}");
            assert!(
                displayed.contains("Git source `https://github.com/source-fixture/dependency`"),
                "{displayed}"
            );
            assert!(
                displayed.contains(&format!("selected commit {}", fixture.last)),
                "{displayed}"
            );
            assert!(displayed.contains(&hex), "{displayed}");
            for secret in [
                "user-fixture",
                "password-fixture",
                "token",
                "query-fixture",
                "fragment-fixture",
            ] {
                assert!(!displayed.contains(secret), "{displayed}");
            }
            let cause = error
                .downcast_ref::<git2::Error>()
                .expect("original typed Git cause");
            assert_eq!(cause.class(), git2::ErrorClass::Odb, "{displayed}");
            assert_eq!(cause.code(), git2::ErrorCode::NotFound, "{displayed}");
            assert!(!fixture.destination().exists());
        }
    }
}

#[test]
fn duplicate_unused_and_indirect_object_selectors_refuse_publication() {
    for case in ["duplicate", "unused", "alternates", "http-alternates"] {
        let fixture = Fixture::new();
        let objects = fixture.repository.path().join("objects");
        let mut selectors = vec![(fixture.source.url().clone(), objects.clone())];
        match case {
            "duplicate" => {
                let mut equivalent = fixture.source.url().clone();
                equivalent.set_path("/source-data-fixture/dep.git");
                selectors.push((equivalent, objects));
            }
            "unused" => selectors.push((
                url::Url::parse("https://github.com/source-data-fixture/unselected").unwrap(),
                objects,
            )),
            name => {
                std::fs::create_dir_all(objects.join("info")).unwrap();
                std::fs::write(
                    objects.join("info").join(name),
                    b"/untrusted/object/backend\n",
                )
                .unwrap();
            }
        }
        assert!(
            import_sources(
                None,
                &selectors,
                &fixture.destination(),
                vec![fixture.source]
            )
            .is_err(),
            "{case}"
        );
        assert!(!fixture.destination().exists(), "{case}");
    }
}

#[test]
fn missing_and_corrupt_objects_refuse_without_publishing_any_home() {
    for corrupt in [false, true] {
        let fixture = Fixture::new();
        let hex = fixture.blob.to_string();
        let path = fixture
            .repository
            .path()
            .join("objects")
            .join(&hex[..2])
            .join(&hex[2..]);
        std::fs::remove_file(&path).unwrap();
        if corrupt {
            std::fs::write(path, b"not a Git object").unwrap();
        }
        assert!(fixture.import().is_err());
        assert!(!fixture.destination().exists());
    }
}

#[test]
fn execution_configuration_and_object_indirections_never_enter_the_data_view() {
    for injected in [
        "config",
        "objects/info/alternates",
        "objects/info/http-alternates",
        "info/grafts",
        "shallow",
        "commondir",
        "refs/replace",
    ] {
        let fixture = Fixture::new();
        let path = fixture.repository.path().join(injected);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        if injected == "config" {
            std::fs::write(path, b"[include]\npath = forbidden-execution-config\n").unwrap();
        } else {
            std::fs::write(path, b"untrusted indirection\n").unwrap();
        }
        assert!(fixture.import().is_err(), "{injected}");
        assert!(!fixture.destination().exists(), "{injected}");
    }
}

#[test]
fn missing_selected_child_database_refuses_before_home_publication() {
    let mut fixture = Fixture::new();
    let child = git2::Repository::init_bare(fixture.root.join("nested-source")).unwrap();
    let child_tree_id = child.treebuilder(None).unwrap().write().unwrap();
    let child_tree = child.find_tree(child_tree_id).unwrap();
    let child_signature = git2::Signature::now("Nested fixture", "nested@example.invalid").unwrap();
    let nested = child
        .commit(
            None,
            &child_signature,
            &child_signature,
            "actual nested source",
            &child_tree,
            &[],
        )
        .unwrap();
    let mut builder = fixture.repository.treebuilder(None).unwrap();
    builder.insert("nested", nested, 0o160000).unwrap();
    let modules = fixture
        .repository
        .blob(b"[submodule \"nested\"]\npath = nested\nurl = ../nested\n")
        .unwrap();
    builder.insert(".gitmodules", modules, 0o100644).unwrap();
    let tree_id = builder.write().unwrap();
    drop(builder);
    let tree = fixture.repository.find_tree(tree_id).unwrap();
    let signature = git2::Signature::now("Source fixture", "fixture@example.invalid").unwrap();
    let commit = fixture
        .repository
        .commit(None, &signature, &signature, "nested", &tree, &[])
        .unwrap();
    drop(tree);
    let url = fixture.source.url().clone();
    fixture.source = SourceId::for_git(&url, GitReference::Rev(commit.to_string()))
        .unwrap()
        .with_git_precise(Some(commit.to_string()));
    let error = fixture.import().unwrap_err();
    let displayed = format!("{error:#}");
    assert!(
        displayed.contains("source-data database unavailable"),
        "{displayed}"
    );
    assert!(
        displayed.contains(&format!(
            "Git source `https://github.com/source-data-fixture/nested` at selected commit {nested}"
        )),
        "{displayed}"
    );
    assert!(
        !displayed.contains(&format!("selected commit {commit}")),
        "{displayed}"
    );
    assert!(!fixture.destination().exists());
}

#[test]
fn historical_gitlinks_are_data_not_selected_child_imports() {
    let mut fixture = Fixture::new();
    let mut old_tree = fixture.repository.treebuilder(None).unwrap();
    // A real older commit is a valid gitlink value; no same-ODB traversal or
    // child recipe may be inferred from this historical tree entry.
    old_tree.insert("old-sat", fixture.first, 0o160000).unwrap();
    let tree_id = old_tree.write().unwrap();
    drop(old_tree);
    let old_tree = fixture.repository.find_tree(tree_id).unwrap();
    let signature = git2::Signature::now("History", "source@example.invalid").unwrap();
    let old = fixture
        .repository
        .commit(
            None,
            &signature,
            &signature,
            "historical link",
            &old_tree,
            &[],
        )
        .unwrap();
    let old = fixture.repository.find_commit(old).unwrap();
    let selected_tree = fixture
        .repository
        .find_commit(fixture.last)
        .unwrap()
        .tree()
        .unwrap();
    let selected = fixture
        .repository
        .commit(
            None,
            &signature,
            &signature,
            "selected without modules",
            &selected_tree,
            &[&old],
        )
        .unwrap();
    fixture.source = SourceId::for_git(
        fixture.source.url(),
        GitReference::Rev(selected.to_string()),
    )
    .unwrap()
    .with_git_precise(Some(selected.to_string()));
    assert_eq!(fixture.import().unwrap().sources, 1);
    let output = git2::Repository::open_bare(
        fixture
            .destination()
            .join("git/db")
            .join(super::super::source::ident(&fixture.source)),
    )
    .unwrap();
    let historical = output
        .find_commit(selected)
        .unwrap()
        .parent(0)
        .unwrap()
        .tree()
        .unwrap();
    let entry = historical.get_name("old-sat").unwrap();
    assert_eq!(entry.filemode(), 0o160000);
    assert_eq!(entry.id(), fixture.first);
    // The historical gitlink does not make its target an ancestor/object edge.
    assert!(output.find_commit(fixture.first).is_err());
}

#[test]
fn source_namespace_substitution_is_refused_even_if_the_name_is_restored() {
    let fixture = Fixture::new();
    let snapshot = custody::ObjectSource::capture(fixture.repository.path()).unwrap();
    let objects = fixture.repository.path().join("objects");
    let moved = fixture.repository.path().join("original-objects");
    std::fs::rename(&objects, &moved).unwrap();
    std::fs::create_dir(&objects).unwrap();
    assert!(snapshot.check_current().is_err());
    std::fs::remove_dir(&objects).unwrap();
    std::fs::rename(&moved, &objects).unwrap();
    assert!(snapshot.check_current().is_err());
}
