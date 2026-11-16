//! Native source DATA import, followed by ordinary locked/offline consumption.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "macos", target_os = "linux"))]

use std::fs;
use std::io::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::os::unix::process::CommandExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture binds its original CLI/compiler before project configuration"
)]
fn command(world: &Path, home: &str) -> Command {
    let executable = std::env::var_os("TARGO_LOCAL_SOURCE_TEST_BINARY")
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(world.join("project"))
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join(home))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("original compiler"),
        )
        .env("CARGO_INCREMENTAL", "0");
    // These consumers run check only. Forward an original rustdoc when the
    // caller supplied one, without requiring or claiming an unused doc cohort.
    if let Some(rustdoc) = std::env::var_os("RUSTDOC").filter(|value| !value.is_empty()) {
        command.env("RUSTDOC", rustdoc);
    }
    command
}

fn recorded(command: &mut Command, world: &Path, label: &str) -> Output {
    let evidence = world.join(label);
    fs::create_dir(&evidence).unwrap();
    fs::write(
        evidence.join("command.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "program":command.get_program().to_string_lossy(),
            "args":command.get_args().map(|arg|arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd":command.get_current_dir(),
        }))
        .unwrap(),
    )
    .unwrap();
    let output = command.output().unwrap();
    fs::write(evidence.join("stdout"), &output.stdout).unwrap();
    fs::write(evidence.join("stderr"), &output.stderr).unwrap();
    fs::write(evidence.join("status"), output.status.to_string()).unwrap();
    output
}

fn success(output: &Output, world: &Path) {
    assert!(
        output.status.success(),
        "world={} status={}\nstdout={}\nstderr={}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn repository(path: &Path, children: &[(&str, &Path, git2::Oid)], source: &[u8]) -> git2::Oid {
    repository_with_loose_objects(path, children, source, 0)
}

fn repository_with_loose_objects(
    path: &Path,
    children: &[(&str, &Path, git2::Oid)],
    source: &[u8],
    loose_objects: usize,
) -> git2::Oid {
    let mut options = git2::RepositoryInitOptions::new();
    options
        .bare(true)
        .external_template(false)
        .initial_head("master");
    let repo = git2::Repository::init_opts(path, &options).unwrap();
    let package = if path.file_name().unwrap() == "source.git" {
        "local_source_dep".to_owned()
    } else {
        path.file_stem()
            .unwrap()
            .to_str()
            .unwrap()
            .replace('-', "_")
    };
    let manifest = repo
        .blob(format!("[package]\nname='{package}'\nversion='1.0.0'\nedition='2021'\n").as_bytes())
        .unwrap();
    let source = repo.blob(source).unwrap();
    let mut source_tree = repo.treebuilder(None).unwrap();
    source_tree.insert("lib.rs", source, 0o100644).unwrap();
    let src = source_tree.write().unwrap();
    let mut root = repo.treebuilder(None).unwrap();
    root.insert("Cargo.toml", manifest, 0o100644).unwrap();
    root.insert("src", src, 0o040000).unwrap();
    if loose_objects != 0 {
        let mut payloads = repo.treebuilder(None).unwrap();
        for index in 0..loose_objects {
            let payload = format!("source view fanout {package} {index}\n");
            let blob = repo.blob(payload.as_bytes()).unwrap();
            payloads
                .insert(format!("{index}.data"), blob, 0o100644)
                .unwrap();
        }
        root.insert("payloads", payloads.write().unwrap(), 0o040000)
            .unwrap();
    }
    if !children.is_empty() {
        let mut declarations = String::new();
        for (name, child_path, oid) in children {
            // Exercise ordinary relative resolution rather than inventing a
            // local URL namespace for the importer.
            let relative = format!("../{}", child_path.file_name().unwrap().to_str().unwrap());
            declarations.push_str(&format!(
                "[submodule \"{name}\"]\npath = {name}\nurl = {relative}\n"
            ));
            root.insert(name, *oid, 0o160000).unwrap();
        }
        let modules = repo.blob(declarations.as_bytes()).unwrap();
        root.insert(".gitmodules", modules, 0o100644).unwrap();
    }
    let tree = repo.find_tree(root.write().unwrap()).unwrap();
    let signature =
        git2::Signature::now("Native source fixture", "fixture@example.invalid").unwrap();
    let first = repo
        .commit(
            Some("HEAD"),
            &signature,
            &signature,
            "first actual source",
            &tree,
            &[],
        )
        .unwrap();
    let first = repo.find_commit(first).unwrap();
    repo.commit(
        Some("HEAD"),
        &signature,
        &signature,
        "second actual source",
        &tree,
        &[&first],
    )
    .unwrap()
}

fn new_world(nested: bool) -> (PathBuf, git2::Oid) {
    new_world_with_loose_objects(nested, 0)
}

fn new_world_with_loose_objects(nested: bool, loose_objects: usize) -> (PathBuf, git2::Oid) {
    new_world_with_repository(nested, loose_objects, |_, revision| revision)
}

fn new_world_with_repository(
    nested: bool,
    loose_objects: usize,
    prepare: impl FnOnce(&Path, git2::Oid) -> git2::Oid,
) -> (PathBuf, git2::Oid) {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-local-source-data.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("source")
        .permissions(fs::Permissions::from_mode(0o700))
        .tempdir_in(base)
        .unwrap()
        .keep()
        .canonicalize()
        .unwrap();
    let mut children = Vec::new();
    if nested {
        let leaf_path = world.join("leaf.git");
        let leaf = repository_with_loose_objects(
            &leaf_path,
            &[],
            b"pub const VALUE:u32=11;\n",
            loose_objects,
        );
        let a = world.join("sat-a.git");
        let a_oid = repository_with_loose_objects(
            &a,
            &[("leaf", &leaf_path, leaf)],
            b"#[path=\"../leaf/src/lib.rs\"] mod leaf;\npub const VALUE:u32=leaf::VALUE;\n",
            loose_objects,
        );
        children.push(("sat-a", a, a_oid));
        for (name, value) in [("sat-b", 20), ("sat-c", 30)] {
            let path = world.join(format!("{name}.git"));
            let oid = repository_with_loose_objects(
                &path,
                &[],
                format!("pub const VALUE:u32={value};\n").as_bytes(),
                loose_objects,
            );
            children.push((name, path, oid));
        }
    }
    let source_path = world.join("source.git");
    let child_refs = children
        .iter()
        .map(|(name, path, oid)| (*name, path.as_path(), *oid))
        .collect::<Vec<_>>();
    let oid = repository_with_loose_objects(
        &source_path,
        &child_refs,
        if nested {
            b"#[path=\"../sat-a/src/lib.rs\"] mod a;\n#[path=\"../sat-b/src/lib.rs\"] mod b;\n#[path=\"../sat-c/src/lib.rs\"] mod c;\npub const VALUE:u32=a::VALUE+b::VALUE+c::VALUE;\npub fn value()->u32 {VALUE}\n"
        } else {
            b"pub fn value()->u32 {42}\n"
        },
        loose_objects,
    );
    let oid = prepare(&source_path, oid);
    fs::write(world.join("source-identities.json"), serde_json::to_vec_pretty(&serde_json::json!({
        "root":oid.to_string(), "children":children.iter().map(|(name,path,oid)|serde_json::json!({"path":name,"source":path,"oid":oid.to_string()})).collect::<Vec<_>>()
    })).unwrap()).unwrap();
    fs::create_dir_all(world.join("project/src")).unwrap();
    let url = url::Url::from_file_path(&source_path).unwrap();
    fs::write(world.join("project/Cargo.toml"), format!("[package]\nname='local_source_owner'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\nlocal_source_dep={{git='{url}',rev='{oid}'}}\n[profile.dev]\ndebug=0\nincremental=false\n")).unwrap();
    fs::write(
        world.join("project/src/lib.rs"),
        if nested { "const _: [();61]=[();local_source_dep::VALUE as usize];\npub fn value()->u32 {local_source_dep::value()}\n" }
        else { "pub fn value() -> u32 { local_source_dep::value() }\n" },
    )
    .unwrap();
    let output = recorded(
        command(&world, "donor").args(["generate-lockfile"]),
        &world,
        "prime-source-data",
    );
    success(&output, &world);
    for name in [".package-cache", ".package-cache-mutate"] {
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(world.join("donor").join(name))
        {
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => panic!("native fixture lock: {error}"),
        }
    }
    (world, oid)
}

const PACKED_HISTORY_BYTES: usize = 64 * 1024 * 1024 + 1;

fn add_packed_history(path: &Path, revision: git2::Oid) -> git2::Oid {
    let repo = git2::Repository::open_bare(path).unwrap();
    let odb = repo.odb().unwrap();
    let mut writer = odb
        .writer(PACKED_HISTORY_BYTES, git2::ObjectType::Blob)
        .unwrap();
    let bytes = [b'x'; 16 * 1024];
    let mut remaining = PACKED_HISTORY_BYTES;
    while remaining != 0 {
        let count = remaining.min(bytes.len());
        writer.write_all(&bytes[..count]).unwrap();
        remaining -= count;
    }
    let blob = writer.finalize().unwrap();
    drop(writer);
    let parent = repo.find_commit(revision).unwrap();
    let tree = parent.tree().unwrap();
    let mut historical_tree = repo.treebuilder(Some(&tree)).unwrap();
    historical_tree
        .insert("historical.data", blob, 0o100644)
        .unwrap();
    let historical_tree = repo.find_tree(historical_tree.write().unwrap()).unwrap();
    let signature =
        git2::Signature::now("Native source fixture", "fixture@example.invalid").unwrap();
    let historical = repo
        .commit(
            Some("HEAD"),
            &signature,
            &signature,
            "oversized historical blob",
            &historical_tree,
            &[&parent],
        )
        .unwrap();
    let historical = repo.find_commit(historical).unwrap();
    let selected = repo
        .commit(
            Some("HEAD"),
            &signature,
            &signature,
            "selected source without the historical blob",
            &tree,
            &[&historical],
        )
        .unwrap();
    let mut pack = repo.packbuilder().unwrap();
    // Exactly one object in this native Git pack gives it no delta base.
    pack.insert_object(blob, Some("historical.data")).unwrap();
    pack.write(&repo.path().join("objects/pack"), 0).unwrap();
    let blob_hex = blob.to_string();
    fs::remove_file(
        repo.path()
            .join("objects")
            .join(&blob_hex[..2])
            .join(&blob_hex[2..]),
    )
    .unwrap();
    let reopened = git2::Repository::open_bare(path).unwrap();
    assert_eq!(
        reopened.odb().unwrap().read_header(blob).unwrap(),
        (PACKED_HISTORY_BYTES, git2::ObjectType::Blob)
    );
    selected
}

#[test]
fn oversized_packed_base_blob_in_history_is_preflighted_and_imported() {
    let (world, revision) = new_world_with_repository(false, 0, add_packed_history);
    let donor = world.join("source.git");
    let donor_url = url::Url::from_file_path(&donor).unwrap();
    let repo = git2::Repository::open_bare(&donor).unwrap();
    let selected = repo.find_commit(revision).unwrap();
    assert!(
        selected
            .tree()
            .unwrap()
            .get_name("historical.data")
            .is_none()
    );
    let historical = selected.parent(0).unwrap();
    let historical_tree = historical.tree().unwrap();
    let blob = historical_tree.get_name("historical.data").unwrap().id();
    let preflight = recorded(
        command(&world, "preflight-home")
            .args([
                "fetch",
                "--locked",
                "--offline",
                "--local-git-source-preflight",
            ])
            .arg("--local-git-object-source")
            .arg(donor_url.as_str())
            .arg(donor.join("objects")),
        &world,
        "packed-history-preflight",
    );
    success(&preflight, &world);
    let report: serde_json::Value = serde_json::from_slice(&preflight.stdout).unwrap();
    assert_eq!(report["schema"], "targo-git-source-preflight-v1");
    assert_eq!(report["destination_published"], false);
    assert_eq!(report["private_views"], "closed");
    assert_eq!(report["observed_counts"]["sources"], 1);
    assert!(report["observed_counts"]["bytes"].as_u64().unwrap() > PACKED_HISTORY_BYTES as u64);
    assert!(!world.join("preflight-home").exists());
    let preflight_stage = fs::read_dir(&world)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with(".targo-git-source-import-")
        })
        .unwrap();
    assert!(!preflight_stage.join("home/git").exists());
    assert!(
        fs::read_dir(preflight_stage.join("views"))
            .unwrap()
            .next()
            .is_none()
    );
    let imported = recorded(
        command(&world, "imported-home")
            .args([
                "fetch",
                "--locked",
                "--offline",
                "--local-git-object-source",
            ])
            .arg(donor_url.as_str())
            .arg(donor.join("objects")),
        &world,
        "packed-history-import",
    );
    success(&imported, &world);
    let database = fs::read_dir(world.join("imported-home/git/db"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let seeded = git2::Repository::open_bare(database).unwrap();
    assert_eq!(
        seeded.find_commit(revision).unwrap().parent_id(0).unwrap(),
        historical.id()
    );
    assert_eq!(
        seeded.odb().unwrap().read_header(blob).unwrap(),
        (PACKED_HISTORY_BYTES, git2::ObjectType::Blob)
    );
    let consumed = recorded(
        command(&world, "imported-home").args([
            "--unverified",
            "check",
            "--locked",
            "--offline",
            "--lib",
            "--jobs=1",
        ]),
        &world,
        "packed-history-offline-consumer",
    );
    success(&consumed, &world);
}

#[test]
fn real_locked_source_imports_into_a_fresh_home_and_builds_offline() {
    let (world, oid) = new_world(false);
    let control = recorded(
        command(&world, "empty-control").args(["fetch", "--locked", "--offline"]),
        &world,
        "empty-offline-control",
    );
    assert!(
        !control.status.success(),
        "fresh offline source unexpectedly existed: {}",
        world.display()
    );
    let donor = world.join("donor");
    let imported = recorded(
        command(&world, "fresh-home")
            .args(["fetch", "--locked", "--offline", "--local-git-source-cache"])
            .arg(&donor),
        &world,
        "import",
    );
    success(&imported, &world);
    let consumed = recorded(
        command(&world, "fresh-home").args([
            "--unverified",
            "check",
            "--locked",
            "--offline",
            "--lib",
            "--jobs=1",
        ]),
        &world,
        "ordinary-consumer",
    );
    success(&consumed, &world);
    let database = fs::read_dir(world.join("fresh-home/git/db"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let repo = git2::Repository::open_bare(database).unwrap();
    let mut history = repo.revwalk().unwrap();
    history.push(oid).unwrap();
    assert_eq!(
        history.count(),
        2,
        "full actual parent history must remain available"
    );
    for absent in ["config", "config.toml", "bin"] {
        assert!(!world.join("fresh-home").join(absent).exists());
    }
    assert!(!repo.path().join("objects/info/alternates").exists());
}

#[test]
fn standalone_root_and_ir_objects_mix_with_locked_recursive_cargo_sources_offline() {
    let (world, _) = new_world(true);
    let ir_path = world.join("ir.git");
    let ir = repository(&ir_path, &[], b"pub const VALUE:u32=17;\n");
    let ir_url = url::Url::from_file_path(&ir_path).unwrap();
    let manifest = world.join("project/Cargo.toml");
    let mut contents = fs::read_to_string(&manifest).unwrap();
    contents.push_str(&format!(
        "\n[dependencies.ir]\ngit='{ir_url}'\nrev='{ir}'\n"
    ));
    fs::write(manifest, contents).unwrap();
    let source = world.join("project/src/lib.rs");
    let mut contents = fs::read_to_string(&source).unwrap();
    contents.push_str("\nconst _: [();17]=[();ir::VALUE as usize];\n");
    fs::write(source, contents).unwrap();
    success(
        &recorded(
            command(&world, "donor").arg("generate-lockfile"),
            &world,
            "prime-ir-source-data",
        ),
        &world,
    );

    let mut removed = Vec::new();
    for entry in fs::read_dir(world.join("donor/git/db")).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name
            .to_str()
            .is_some_and(|name| name.starts_with("source-") || name.starts_with("ir-"))
        {
            removed.push(name);
            fs::remove_dir_all(entry.path()).unwrap();
        }
    }
    fs::write(
        world.join("standalone-selected-databases.json"),
        serde_json::to_vec_pretty(
            &removed
                .iter()
                .map(|name| name.to_string_lossy())
                .collect::<Vec<_>>(),
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(removed.len(), 2, "world={}", world.display());
    // Enclosing repository policy is neither opened nor copied by this profile.
    // The ordinary consumer must use the newly generated config-free DBs.
    for repository in [world.join("source.git"), ir_path.clone()] {
        fs::write(repository.join("config"), b"[include]\npath=/never-read-source-policy\n[core]\nhooksPath=/never-run-source-hooks\n").unwrap();
    }
    let root_url = url::Url::from_file_path(world.join("source.git")).unwrap();
    let imported = recorded(
        command(&world, "mixed-home")
            .args(["fetch", "--locked", "--offline", "--local-git-source-cache"])
            .arg(world.join("donor"))
            .arg("--local-git-object-source")
            .arg(root_url.as_str())
            .arg(world.join("source.git/objects"))
            .arg("--local-git-object-source")
            .arg(ir_url.as_str())
            .arg(ir_path.join("objects")),
        &world,
        "mixed-object-data-import",
    );
    success(&imported, &world);
    assert!(String::from_utf8_lossy(&imported.stderr).contains("6 locked Git sources"));
    let checked = recorded(
        command(&world, "mixed-home").args([
            "--unverified",
            "check",
            "--locked",
            "--offline",
            "--jobs=1",
        ]),
        &world,
        "mixed-object-data-offline-check",
    );
    success(&checked, &world);
    assert!(!world.join("mixed-home/config.toml").exists());
    assert!(!world.join("mixed-home/bin").exists());
}

#[test]
fn explicit_missing_object_refuses_instead_of_using_valid_cargo_fallback() {
    let (world, oid) = new_world(false);
    let source_path = world.join("source.git");
    let repo = git2::Repository::open_bare(&source_path).unwrap();
    let blob = repo
        .find_commit(oid)
        .unwrap()
        .tree()
        .unwrap()
        .get_path(Path::new("src/lib.rs"))
        .unwrap()
        .id()
        .to_string();
    fs::remove_file(
        source_path
            .join("objects")
            .join(&blob[..2])
            .join(&blob[2..]),
    )
    .unwrap();
    let url = url::Url::from_file_path(&source_path).unwrap();
    let refused = recorded(
        command(&world, "refused-home")
            .args(["fetch", "--locked", "--offline", "--local-git-source-cache"])
            .arg(world.join("donor"))
            .arg("--local-git-object-source")
            .arg(url.as_str())
            .arg(source_path.join("objects")),
        &world,
        "explicit-missing-object-refusal",
    );
    assert!(!refused.status.success(), "world={}", world.display());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("missing locked Git object"));
    assert!(!world.join("refused-home").exists());
}

#[test]
fn stream_budget_requires_a_provider_and_refuses_values_above_the_hard_limit() {
    let (world, _) = new_world(false);
    let no_provider = recorded(
        command(&world, "no-provider-home").args([
            "fetch",
            "--locked",
            "--offline",
            "--local-git-source-copy-budget",
            "0",
        ]),
        &world,
        "copy-budget-no-provider",
    );
    let too_large = recorded(
        command(&world, "too-large-home")
            .args([
                "fetch",
                "--locked",
                "--offline",
                "--local-git-source-copy-budget",
                "34359738369",
                "--local-git-source-cache",
            ])
            .arg(world.join("donor")),
        &world,
        "copy-budget-too-large",
    );
    assert!(!no_provider.status.success());
    assert!(
        String::from_utf8_lossy(&no_provider.stderr)
            .contains("requires a local Git source-data input")
    );
    assert!(!world.join("no-provider-home").exists());
    assert!(!too_large.status.success());
    assert!(
        String::from_utf8_lossy(&too_large.stderr).contains("stream-copy budget exceeds 32 GiB")
    );
    assert!(!world.join("too-large-home").exists());
}

#[test]
fn preflight_reports_selected_recursive_data_and_does_not_seed_the_consumer() {
    let (world, _) = new_world(true);
    let planned = recorded(
        command(&world, "preflight-home")
            .args([
                "fetch",
                "--locked",
                "--offline",
                "--local-git-source-preflight",
                "--local-git-source-cache",
            ])
            .arg(world.join("donor")),
        &world,
        "recursive-preflight",
    );
    success(&planned, &world);
    let report: serde_json::Value = serde_json::from_slice(&planned.stdout).unwrap();
    assert_eq!(report["schema"], "targo-git-source-preflight-v1");
    assert_eq!(report["destination_published"], false);
    assert_eq!(report["private_views"], "closed");
    assert_eq!(report["observed_counts"]["sources"], 5);
    assert_eq!(report["observed_counts"]["objects"], 32);
    assert_eq!(report["required_sources"].as_array().unwrap().len(), 5);
    assert_eq!(
        report["required_sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["children"].as_array().unwrap().len())
            .sum::<usize>(),
        4
    );
    assert!(!world.join("preflight-home").exists());
    let stages = fs::read_dir(&world)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with(".targo-git-source-import-")
        })
        .collect::<Vec<_>>();
    assert_eq!(stages.len(), 1);
    assert!(
        fs::read_dir(stages[0].join("views"))
            .unwrap()
            .next()
            .is_none()
    );
    assert!(!stages[0].join("home/git").exists());
    let empty = recorded(
        command(&world, "preflight-empty-consumer").args(["fetch", "--locked", "--offline"]),
        &world,
        "preflight-is-not-a-source-cache",
    );
    assert!(!empty.status.success());
    let actual = recorded(
        command(&world, "preflight-home")
            .args(["fetch", "--locked", "--offline", "--local-git-source-cache"])
            .arg(world.join("donor")),
        &world,
        "import-after-independent-preflight",
    );
    success(&actual, &world);
    assert!(String::from_utf8_lossy(&actual.stderr).contains("5 locked Git sources, 32 objects"));
}

#[test]
fn preflight_many_loose_provider_views_fit_a_bounded_child_descriptor_limit() {
    const CHILD_NOFILE: libc::rlim_t = 128;
    const BLOBS_PER_PROVIDER: usize = 96;
    let mut inherited = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: only queries this process's limit into initialized local storage.
    assert_eq!(
        unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut inherited) },
        0
    );
    assert!(
        inherited.rlim_cur >= CHILD_NOFILE && inherited.rlim_max >= CHILD_NOFILE,
        "native fixture must only lower inherited descriptor limits"
    );
    let (world, _) = new_world_with_loose_objects(true, BLOBS_PER_PROVIDER);
    let providers = [
        "source.git",
        "sat-a.git",
        "sat-b.git",
        "sat-c.git",
        "leaf.git",
    ];
    let mut preflight = command(&world, "bounded-fd-home");
    preflight.args([
        "fetch",
        "--locked",
        "--offline",
        "--local-git-source-preflight",
    ]);
    let mut total_fanout = 0;
    for name in providers {
        let repository = world.join(name);
        let objects = repository.join("objects");
        let fanout = fs::read_dir(&objects)
            .unwrap()
            .map(Result::unwrap)
            .filter(|entry| {
                let name = entry.file_name();
                name.as_encoded_bytes().len() == 2
                    && name.as_encoded_bytes().iter().all(u8::is_ascii_hexdigit)
                    && entry.file_type().unwrap().is_dir()
            })
            .count();
        assert!(
            fanout > 64,
            "{name} has too little actual loose-object fanout: {fanout}"
        );
        total_fanout += fanout;
        preflight
            .arg("--local-git-object-source")
            .arg(url::Url::from_file_path(&repository).unwrap().as_str())
            .arg(objects);
    }
    fs::write(
        world.join("bounded-fd-inputs.txt"),
        format!("inherited_soft_nofile={}\ninherited_hard_nofile={}\nchild_soft_nofile={CHILD_NOFILE}\nchild_hard_nofile={CHILD_NOFILE}\nproviders={}\nactual_loose_fanout={total_fanout}\n", inherited.rlim_cur, inherited.rlim_max, providers.len()),
    )
    .unwrap();
    // SAFETY: only the forked child lowers its own limit before exec. The
    // callback makes one libc call and reports errno without allocating.
    unsafe {
        preflight.pre_exec(|| {
            let limit = libc::rlimit {
                rlim_cur: CHILD_NOFILE,
                rlim_max: CHILD_NOFILE,
            };
            if libc::setrlimit(libc::RLIMIT_NOFILE, &limit) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let output = recorded(&mut preflight, &world, "bounded-fd-preflight");
    success(&output, &world);
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["schema"], "targo-git-source-preflight-v1");
    assert_eq!(report["destination_published"], false);
    assert_eq!(report["private_views"], "closed");
    assert_eq!(report["observed_counts"]["sources"], providers.len());
    assert!(
        report["observed_counts"]["objects"].as_u64().unwrap()
            >= (providers.len() * BLOBS_PER_PROVIDER) as u64
    );
    assert_eq!(
        report["required_sources"].as_array().unwrap().len(),
        providers.len()
    );
    assert!(!world.join("bounded-fd-home").exists());
    let stages = fs::read_dir(&world)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .as_encoded_bytes()
                .starts_with(b".targo-git-source-import-")
        })
        .collect::<Vec<_>>();
    assert_eq!(stages.len(), 1);
    assert!(
        fs::read_dir(stages[0].join("views"))
            .unwrap()
            .next()
            .is_none()
    );
    assert!(!stages[0].join("home/git").exists());
}

#[test]
fn real_sibling_and_nested_submodules_are_consumed_offline_and_missing_child_refuses() {
    let (world, _) = new_world(true);
    let donor = world.join("donor");
    let imported = recorded(
        command(&world, "fresh-home")
            .args(["fetch", "--locked", "--offline", "--local-git-source-cache"])
            .arg(&donor),
        &world,
        "recursive-import",
    );
    success(&imported, &world);
    assert!(String::from_utf8_lossy(&imported.stderr).contains("5 locked Git sources"));
    let consumed = recorded(
        command(&world, "fresh-home").args([
            "--unverified",
            "check",
            "--locked",
            "--offline",
            "--lib",
            "--jobs=1",
        ]),
        &world,
        "recursive-consumer",
    );
    success(&consumed, &world);

    let (world, _) = new_world(true);
    let child = git2::Repository::open_bare(world.join("sat-c.git"))
        .unwrap()
        .head()
        .unwrap()
        .target()
        .unwrap();
    let databases = fs::read_dir(world.join("donor/git/db"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            git2::Repository::open_bare(path)
                .unwrap()
                .find_commit(child)
                .is_ok()
        })
        .collect::<Vec<_>>();
    assert_eq!(databases.len(), 1);
    fs::write(
        world.join("withheld-child-data.json"),
        serde_json::to_vec_pretty(
            &serde_json::json!({"oid":child.to_string(), "database":databases[0]}),
        )
        .unwrap(),
    )
    .unwrap();
    fs::remove_dir_all(&databases[0]).unwrap();
    let output = recorded(
        command(&world, "fresh-home")
            .args(["fetch", "--locked", "--offline", "--local-git-source-cache"])
            .arg(world.join("donor")),
        &world,
        "missing-child-refusal",
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("source-data database unavailable"));
    assert!(
        !world.join("fresh-home").exists(),
        "no incomplete closure may become a published home"
    );
}

#[test]
fn stored_snapshot_consumes_original_git_offline_with_many_prefixes_and_low_nofile() {
    let (world, revision) = new_world(false);
    let databases = fs::read_dir(world.join("donor/git/db"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    assert_eq!(databases.len(), 1);
    let repository = git2::Repository::open_bare(&databases[0]).unwrap();
    for index in 0..2048 {
        repository
            .blob(format!("bounded stored prefix {index}\n").as_bytes())
            .unwrap();
    }
    let prefixes = fs::read_dir(repository.path().join("objects"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .filter(|name| {
            name.to_str()
                .is_some_and(|name| name.len() == 2 && name.bytes().all(|b| b.is_ascii_hexdigit()))
        })
        .count();
    assert!(
        prefixes > 192,
        "fixture must exceed the actual child FD limit"
    );
    fs::write(
        world.join("donor/config.toml"),
        b"excluded source configuration",
    )
    .unwrap();
    fs::write(
        world.join("donor/credentials.toml"),
        b"excluded credential DATA",
    )
    .unwrap();
    const CHILD_NOFILE: libc::rlim_t = 128;
    let mut inherited = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: writable storage for the kernel's complete limit record.
    assert_eq!(
        unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut inherited) },
        0
    );
    assert!(inherited.rlim_cur >= CHILD_NOFILE && inherited.rlim_max >= CHILD_NOFILE);
    let mut fetch = command(&world, "stored-home");
    fetch
        .args(["fetch", "--locked", "--offline", "--local-cargo-data-cache"])
        .arg(world.join("donor"));
    // SAFETY: the post-fork callback invokes only setrlimit with fixed owned
    // scalar DATA. It allocates nothing, takes no locks and only lowers limits.
    unsafe {
        fetch.pre_exec(|| {
            let limit = libc::rlimit {
                rlim_cur: CHILD_NOFILE,
                rlim_max: CHILD_NOFILE,
            };
            if libc::setrlimit(libc::RLIMIT_NOFILE, &limit) == 0 {
                Ok(())
            } else {
                Err(std::io::Error::last_os_error())
            }
        });
    }
    success(
        &recorded(&mut fetch, &world, "stored-low-nofile-fetch"),
        &world,
    );
    assert!(!world.join("stored-home/config.toml").exists());
    assert!(!world.join("stored-home/credentials.toml").exists());
    let copied = git2::Repository::open_bare(
        world
            .join("stored-home/git/db")
            .join(databases[0].file_name().unwrap()),
    )
    .unwrap();
    assert_eq!(copied.find_commit(revision).unwrap().id(), revision);
    success(
        &recorded(
            command(&world, "stored-home").args([
                "--unverified",
                "check",
                "--locked",
                "--offline",
                "--lib",
                "--jobs=1",
            ]),
            &world,
            "stored-offline-consumer",
        ),
        &world,
    );

    let unused = recorded(
        command(&world, "stored-unused-registry-home")
            .args(["fetch", "--locked", "--offline", "--local-cargo-data-cache"])
            .arg(world.join("donor"))
            .arg("--local-cargo-registry-data-cache")
            .arg(world.join("donor")),
        &world,
        "stored-unused-registry-refusal",
    );
    assert!(!unused.status.success());
    assert!(
        String::from_utf8_lossy(&unused.stderr)
            .contains("registry DATA donor requires a selected registry")
    );
    assert!(!world.join("stored-unused-registry-home").exists());
}
