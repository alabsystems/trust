use std::cell::Cell;
use std::fs;
use std::sync::{Arc, Barrier};

use sha2::Digest;

use super::{
    Lease, Reuse, ReusePolicy, file_digest_with_hooks, repository_digest, run, tree_digest,
};

fn commit_fixture(root: &std::path::Path) {
    super::git(root, &["add", "."]).unwrap();
    super::git(
        root,
        &[
            "-c",
            "user.name=Native hash test",
            "-c",
            "user.email=hash@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "--allow-empty",
            "-m",
            "fixture",
        ],
    )
    .unwrap();
}

#[test]
fn sha256_known_answers_are_preserved() {
    assert_eq!(
        super::bytes_digest(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
    assert_eq!(super::bytes_digest(b"abc"), expected);
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("input");
    fs::write(&path, b"abc").unwrap();
    assert_eq!(super::file_digest(&path).unwrap(), expected);

    // Exercise padding across a compression block and the file reader's 64 KiB
    // chunks, independently of whichever SHA-256 backend this host selects.
    let block_boundary = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
    assert_eq!(super::bytes_digest(block_boundary), expected);
    fs::write(&path, block_boundary).unwrap();
    assert_eq!(super::file_digest(&path).unwrap(), expected);

    let million_a = vec![b'a'; 1_000_000];
    let expected = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0";
    assert_eq!(super::bytes_digest(&million_a), expected);
    fs::write(&path, &million_a).unwrap();
    assert_eq!(super::file_digest(&path).unwrap(), expected);
}

#[cfg(unix)]
#[test]
fn parallel_repository_digest_keeps_exact_alias_frames_in_serial_order() {
    use std::os::unix::fs::PermissionsExt;

    let temporary = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(temporary.path()).unwrap();
    super::git(&root, &["init"]).unwrap();
    fs::write(root.join(".gitignore"), "ignored/\n").unwrap();
    fs::write(root.join("a.txt"), b"first").unwrap();
    fs::write(root.join("space name.txt"), vec![42; 65537]).unwrap();
    fs::write(root.join("z.txt"), b"last").unwrap();
    fs::create_dir(root.join("first-party")).unwrap();
    std::os::unix::fs::symlink("..", root.join("first-party/trust")).unwrap();
    std::os::unix::fs::symlink("a.txt", root.join("linked")).unwrap();
    commit_fixture(&root);
    fs::write(root.join("m-new.txt"), b"untracked source").unwrap();
    fs::create_dir(root.join("ignored")).unwrap();
    fs::write(root.join("ignored/input"), b"ignored by Git").unwrap();

    // Independently frame the versioned alias digest BETWEEN its neighbors.
    // Moving it out of the sorted leaf fold must change this value.
    let mut expected = sha2::Sha256::new();
    super::add(
        &mut expected,
        super::git(&root, &["rev-parse", "--verify", "HEAD^{commit}"]).unwrap(),
    );
    let entries = super::git(&root, &["ls-files", "--stage", "-z"]).unwrap();
    for entry in entries.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
        super::add(&mut expected, entry);
    }
    for name in [
        ".gitignore",
        "a.txt",
        "first-party/trust",
        "linked",
        "m-new.txt",
        "space name.txt",
        "z.txt",
    ] {
        let path = root.join(name);
        if name == "first-party/trust" {
            let mut alias = sha2::Sha256::new();
            super::add(&mut alias, b"source-directory-alias/v1");
            super::add(&mut alias, path.as_os_str().as_encoded_bytes());
            super::add(&mut alias, b"..");
            super::add(&mut alias, root.as_os_str().as_encoded_bytes());
            super::add(
                &mut alias,
                fs::symlink_metadata(&path).unwrap().permissions().mode().to_le_bytes(),
            );
            super::add(
                &mut alias,
                fs::symlink_metadata(&root).unwrap().permissions().mode().to_le_bytes(),
            );
            super::add(&mut expected, super::finish(alias));
        } else {
            super::add(&mut expected, tree_digest(&path).unwrap());
        }
    }
    let expected = super::finish(expected);
    for jobs in [1, 2, 7] {
        assert_eq!(repository_digest(&root, jobs).unwrap(), expected);
    }
    fs::write(root.join("m-new.txt"), b"changed untracked source").unwrap();
    let changed = repository_digest(&root, 1).unwrap();
    assert_ne!(changed, expected);
    assert_eq!(repository_digest(&root, 7).unwrap(), changed);
}

struct ActiveLeaf<'a>(&'a std::sync::atomic::AtomicUsize);

impl Drop for ActiveLeaf<'_> {
    fn drop(&mut self) {
        self.0.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
    }
}

fn await_first_two(started: &std::sync::atomic::AtomicUsize) {
    use std::sync::atomic::Ordering::SeqCst;
    if started.fetch_add(1, SeqCst) < 2 {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while started.load(SeqCst) < 2 && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        assert!(started.load(SeqCst) >= 2, "the owning leaf mapper did not execute concurrently");
    }
}

#[test]
fn leaf_workers_obey_the_budget_and_join_before_returning_the_first_ordered_error() {
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering::SeqCst;
    let root = tempfile::tempdir().unwrap();
    let paths = (0..6).map(|i| root.path().join(format!("{i}-input"))).collect::<Vec<_>>();
    for path in &paths[2..] {
        fs::write(path, b"real input").unwrap();
    }
    let (started, active, peak, completed) =
        (AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0));
    let result = super::hash_leaves(&paths, 2, |path| {
        let current = active.fetch_add(1, SeqCst) + 1;
        let _active = ActiveLeaf(&active);
        peak.fetch_max(current, SeqCst);
        await_first_two(&started);
        if path == paths[0] {
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        let result =
            super::file_digest(path).map_err(|error| format!("{}: {error}", path.display()));
        completed.fetch_add(1, SeqCst);
        result
    });
    assert!(
        result.unwrap_err().contains("0-input"),
        "completion order cannot choose the diagnostic"
    );
    assert_eq!(peak.load(SeqCst), 2);
    assert_eq!(active.load(SeqCst), 0, "no worker may outlive a failed snapshot");
    assert_eq!(completed.load(SeqCst), paths.len());
    assert!(super::hash_leaves::<String>(&[], 0, |_| panic!("zero budget must refuse")).is_err());
    assert!(
        super::hash_leaves::<String>(&[], 7, |_| panic!("empty inventory needs no worker"))
            .unwrap()
            .is_empty()
    );
}

#[test]
fn parallel_leaf_hashing_keeps_descriptor_and_path_replacement_refusals() {
    let root = tempfile::tempdir().unwrap();
    let input = root.path().join("input");
    let other = root.path().join("other");
    fs::write(&input, b"before").unwrap();
    fs::write(&other, b"unchanged").unwrap();
    let paths = [input.clone(), other];
    let modified = fs::metadata(&input).unwrap().modified().unwrap();
    let result = super::hash_leaves(&paths, 2, |path| {
        if path != input {
            return super::file_digest(path);
        }
        file_digest_with_hooks(
            path,
            || {},
            || {
                let replacement = root.path().join("replacement");
                fs::write(&replacement, b"after!").unwrap();
                fs::File::open(&replacement).unwrap().set_modified(modified).unwrap();
                fs::rename(replacement, path).unwrap();
            },
        )
    });
    assert!(result.unwrap_err().contains("moved while it was read"));
    #[cfg(unix)]
    {
        let result = super::hash_leaves(&paths, 2, |path| {
            if path != input {
                return super::file_digest(path);
            }
            file_digest_with_hooks(
                path,
                || {
                    let preserved = root.path().join("preserved");
                    fs::rename(path, &preserved).unwrap();
                    std::os::unix::fs::symlink(preserved, path).unwrap();
                },
                || panic!("parallel hashing must not read a replaced symlink"),
            )
        });
        assert_eq!(result.unwrap_err(), std::io::Error::from_raw_os_error(libc::ELOOP).to_string());
    }
}

#[test]
fn parallel_repository_rechecks_head_and_refuses_directory_replacements() {
    let root = tempfile::tempdir().unwrap();
    super::git(root.path(), &["init"]).unwrap();
    fs::write(root.path().join("a"), b"first").unwrap();
    fs::write(root.path().join("z"), b"last").unwrap();
    commit_fixture(root.path());
    let result =
        super::repository(&mut sha2::Sha256::new(), root.path(), 2, &|root, path, gitlinks| {
            let leaf = super::repository_leaf(root, path, gitlinks)?;
            if path == root.join("a") {
                commit_fixture(root);
            }
            Ok(leaf)
        });
    assert!(result.unwrap_err().contains("HEAD moved"));
    fs::remove_file(root.path().join("a")).unwrap();
    fs::create_dir(root.path().join("a")).unwrap();
    assert!(repository_digest(root.path(), 2).unwrap_err().contains("unexpected directory"));
}

#[test]
fn nested_gitlinks_share_one_leaf_worker_budget_and_bind_the_full_child_inventory() {
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering::SeqCst;
    let root = tempfile::tempdir().unwrap();
    super::git(root.path(), &["init"]).unwrap();
    let child = root.path().join("child");
    fs::create_dir(&child).unwrap();
    super::git(&child, &["init"]).unwrap();
    for (directory, names) in [(root.path(), ["a", "z"]), (child.as_path(), ["c", "y"])] {
        for name in names {
            fs::write(directory.join(name), b"tracked source").unwrap();
        }
    }
    commit_fixture(&child);
    commit_fixture(root.path());
    let (started, active, peak) = (AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0));
    let mut hash = sha2::Sha256::new();
    super::repository(&mut hash, root.path(), 2, &|root, path, gitlinks| {
        let current = active.fetch_add(1, SeqCst) + 1;
        let _active = ActiveLeaf(&active);
        peak.fetch_max(current, SeqCst);
        await_first_two(&started);
        super::repository_leaf(root, path, gitlinks)
    })
    .unwrap();
    let before = super::finish(hash);
    assert_eq!(before, repository_digest(root.path(), 1).unwrap());
    assert_eq!(peak.load(SeqCst), 2);
    assert_eq!(active.load(SeqCst), 0);
    fs::write(child.join("untracked"), b"child runtime fixture").unwrap();
    let changed = repository_digest(root.path(), 1).unwrap();
    assert_ne!(changed, before);
    assert_eq!(repository_digest(root.path(), 2).unwrap(), changed);
    commit_fixture(&child);
    assert!(repository_digest(root.path(), 2).unwrap_err().contains("does not match its pin"));
}

#[test]
fn unchanged_success_reuses_but_mutated_outputs_execute_again() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let output = root.path().join("outputs");
    let count = Cell::new(0);
    let execute = || {
        count.set(count.get() + 1);
        fs::create_dir_all(&output).unwrap();
        fs::write(output.join("compiler"), "compiler bytes").unwrap();
        Ok(())
    };
    assert_eq!(
        run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("inputs".into()), execute)
            .unwrap(),
        Reuse::Executed
    );
    assert_eq!(
        run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("inputs".into()), execute)
            .unwrap(),
        Reuse::Cached
    );
    fs::write(output.join("compiler"), "tampered bytes").unwrap();
    assert_eq!(
        run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("inputs".into()), execute)
            .unwrap(),
        Reuse::Executed
    );
    assert_eq!(count.get(), 2);
}

#[test]
fn record_only_reexecutes_when_an_unrecorded_external_input_changes() {
    let root = tempfile::tempdir().unwrap();
    let external = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let input = root.path().join("selected.rs");
    let output = root.path().join("outputs");
    let unrecorded = external.path().join("runtime-input");
    fs::write(&input, "fn main() {}").unwrap();
    fs::write(&unrecorded, "passes").unwrap();
    fs::create_dir(&output).unwrap();
    let snapshot = || tree_digest(&input).map(super::InputSnapshot::from);
    let before = snapshot().unwrap();
    let count = Cell::new(0);
    let execute = || {
        count.set(count.get() + 1);
        match fs::read_to_string(&unrecorded).unwrap().as_str() {
            "passes" => Ok(()),
            _ => Err("selected test failed on its unrecorded external input".into()),
        }
    };
    assert_eq!(
        run(ReusePolicy::RecordOnly, &cache, &output, snapshot, execute).unwrap(),
        Reuse::Executed
    );
    assert!(cache.join("success.json").is_file());
    assert_eq!(
        run(ReusePolicy::RecordOnly, &cache, &output, snapshot, execute).unwrap(),
        Reuse::Executed
    );
    assert_eq!(count.get(), 2, "even unchanged repository invocations must execute");
    fs::write(&unrecorded, "fails!").unwrap();
    assert_eq!(snapshot().unwrap(), before, "the observed snapshot misses this read");
    let failed = run(ReusePolicy::RecordOnly, &cache, &output, snapshot, execute);
    assert!(failed.unwrap_err().contains("unrecorded external input"));
    assert_eq!(count.get(), 3, "a prior success must not skip the actual test");
    assert!(!cache.join("success.json").exists());
}

#[test]
fn source_change_does_not_reuse_a_prior_success() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let input = root.path().join("input.rs");
    let output = root.path().join("outputs");
    fs::write(&input, "first").unwrap();
    fs::create_dir(&output).unwrap();
    let snapshot = || tree_digest(&input).map(super::InputSnapshot::from);
    assert_eq!(
        run(ReusePolicy::ControlledFixture, &cache, &output, snapshot, || Ok(())).unwrap(),
        Reuse::Executed
    );
    fs::write(&input, "other").unwrap();
    assert_eq!(
        run(ReusePolicy::ControlledFixture, &cache, &output, snapshot, || Ok(())).unwrap(),
        Reuse::Executed
    );
}

#[test]
fn failed_or_panicking_retry_cannot_resurrect_the_old_success() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let output = root.path().join("outputs");
    fs::create_dir(&output).unwrap();
    run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("old".into()), || Ok(())).unwrap();
    let failed = run(
        ReusePolicy::ControlledFixture,
        &cache,
        &output,
        || Ok("new".into()),
        || Err("compiler failed".into()),
    );
    assert!(failed.unwrap_err().contains("compiler failed"));
    assert!(!cache.join("success.json").exists());
    run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("old".into()), || Ok(())).unwrap();
    let interrupted = std::panic::catch_unwind(|| {
        let _ = run(
            ReusePolicy::ControlledFixture,
            &cache,
            &output,
            || Ok("new".into()),
            || panic!("interrupted"),
        );
    });
    assert!(interrupted.is_err());
    assert!(!cache.join("success.json").exists());
    // The RAII lease also retires on interruption.
    assert!(Lease::acquire(&cache).is_ok());
}

#[test]
fn moved_inputs_never_publish_success() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let output = root.path().join("outputs");
    fs::create_dir(&output).unwrap();
    let input = Cell::new("before");
    let result = run(
        ReusePolicy::ControlledFixture,
        &cache,
        &output,
        || Ok(input.get().into()),
        || {
            input.set("after");
            Ok(())
        },
    );
    assert!(result.unwrap_err().contains("inputs moved"));
    assert!(!cache.join("success.json").exists());
}

#[test]
fn a_cache_hit_rechecks_artifacts_after_validating_inputs() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let output = root.path().join("outputs");
    fs::create_dir(&output).unwrap();
    fs::write(output.join("compiler"), "before").unwrap();
    run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("same".into()), || Ok(())).unwrap();
    let snapshots = Cell::new(0);
    let result = run(
        ReusePolicy::ControlledFixture,
        &cache,
        &output,
        || {
            snapshots.set(snapshots.get() + 1);
            if snapshots.get() == 2 {
                fs::write(output.join("compiler"), "after!").unwrap();
            }
            Ok("same".into())
        },
        || panic!("cache lookup must not start an action"),
    );
    assert!(result.unwrap_err().contains("outputs moved"));
}

#[test]
fn incomplete_and_malformed_results_are_misses() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let output = root.path().join("outputs");
    fs::create_dir(&cache).unwrap();
    fs::create_dir(&output).unwrap();
    for bytes in [b"{\"completed\":false}".as_slice(), b"interrupted JSON"] {
        fs::write(cache.join("success.json"), bytes).unwrap();
        assert_eq!(
            run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("same".into()), || Ok(()))
                .unwrap(),
            Reuse::Executed
        );
    }
    let mut record: serde_json::Value =
        serde_json::from_slice(&fs::read(cache.join("success.json")).unwrap()).unwrap();
    record["completed"] = false.into();
    fs::write(cache.join("success.json"), serde_json::to_vec(&record).unwrap()).unwrap();
    assert_eq!(
        run(ReusePolicy::ControlledFixture, &cache, &output, || Ok("same".into()), || Ok(()))
            .unwrap(),
        Reuse::Executed
    );
}

#[test]
fn a_live_writer_excludes_a_second_execution() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("cache");
    let output = root.path().join("outputs");
    fs::create_dir(&output).unwrap();
    let entered = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let writer = std::thread::spawn({
        let (cache, output, entered, release) =
            (cache.clone(), output.clone(), entered.clone(), release.clone());
        move || {
            run(
                ReusePolicy::ControlledFixture,
                &cache,
                &output,
                || Ok("same".into()),
                || {
                    entered.wait();
                    release.wait();
                    Ok(())
                },
            )
        }
    });
    entered.wait();
    let denied = run(
        ReusePolicy::ControlledFixture,
        &cache,
        &output,
        || Ok("same".into()),
        || panic!("second writer entered"),
    );
    release.wait();
    assert!(denied.unwrap_err().contains("already owned"));
    assert_eq!(writer.join().unwrap().unwrap(), Reuse::Executed);
}

#[cfg(unix)]
#[test]
fn output_permissions_and_symlink_target_contents_are_bound() {
    use std::os::unix::fs::{PermissionsExt, symlink};

    let root = tempfile::tempdir().unwrap();
    let target = root.path().join("actual");
    let output = root.path().join("outputs");
    fs::create_dir(&output).unwrap();
    fs::write(&target, "before").unwrap();
    symlink(&target, output.join("compiler")).unwrap();
    let before = tree_digest(&output).unwrap();
    fs::write(&target, "after!").unwrap();
    let after = tree_digest(&output).unwrap();
    assert_ne!(before, after);
    fs::set_permissions(&target, fs::Permissions::from_mode(0o700)).unwrap();
    assert_ne!(after, tree_digest(&output).unwrap());
}

#[cfg(unix)]
#[test]
fn an_unresolved_tree_link_refuses_with_its_exact_input_path() {
    let root = tempfile::tempdir().unwrap();
    let directory = root.path().join("installation/bin");
    fs::create_dir_all(&directory).unwrap();
    let link = directory.join("missing-tool");
    std::os::unix::fs::symlink("../missing", &link).unwrap();
    let error = tree_digest(root.path()).unwrap_err();
    assert!(error.contains(link.to_str().unwrap()), "lost the unresolved entry: {error}");
    assert!(error.contains(&std::io::Error::from_raw_os_error(libc::ENOENT).to_string()));
}

#[cfg(unix)]
#[test]
fn installation_inputs_bind_missing_links_without_accepting_required_trees() {
    use std::os::unix::fs::symlink;

    let root = tempfile::tempdir().unwrap();
    let bin = root.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let link = bin.join("optional-helper");
    symlink("../missing/leaf", &link).unwrap();
    let before = super::installation_tree_digest(root.path()).unwrap();
    assert_eq!(before, super::installation_tree_digest(root.path()).unwrap());
    assert!(tree_digest(root.path()).unwrap_err().contains(link.to_str().unwrap()));
    fs::remove_file(&link).unwrap();
    symlink("../other-missing/leaf", &link).unwrap();
    let retargeted = super::installation_tree_digest(root.path()).unwrap();
    assert_ne!(before, retargeted, "the raw missing destination is still an input");
    fs::create_dir(root.path().join("other-missing")).unwrap();
    let parent_appeared = super::installation_tree_digest(root.path()).unwrap();
    assert_ne!(retargeted, parent_appeared, "the nearest existing namespace matters");
    fs::write(root.path().join("other-missing/leaf"), b"available").unwrap();
    let appeared = super::installation_tree_digest(root.path()).unwrap();
    assert_ne!(parent_appeared, appeared);
    fs::write(root.path().join("other-missing/leaf"), b"different").unwrap();
    assert_ne!(appeared, super::installation_tree_digest(root.path()).unwrap());
}

#[cfg(unix)]
#[test]
fn missing_installation_links_refuse_appearance_and_namespace_replacement() {
    use std::os::unix::fs::symlink;

    for mode in ["appearance", "parent-replacement", "prefix-link", "permissions", "link"] {
        let root = tempfile::tempdir().unwrap();
        let namespace = root.path().join("namespace");
        let other = root.path().join("other");
        fs::create_dir(&namespace).unwrap();
        fs::create_dir(&other).unwrap();
        let prefix = root.path().join("prefix");
        symlink("namespace", &prefix).unwrap();
        fs::create_dir(root.path().join("bin")).unwrap();
        let link = root.path().join("bin/helper");
        // Parent components and a second symlink both participate in resolving
        // the missing destination; neither can erase namespace ownership.
        symlink("../prefix/missing/leaf", &link).unwrap();
        let result = super::missing_installation_link_digest_with_hook(&link, || match mode {
            "appearance" => {
                fs::create_dir(namespace.join("missing")).unwrap();
                fs::write(namespace.join("missing/leaf"), b"new input").unwrap();
            }
            "parent-replacement" => {
                fs::rename(&namespace, root.path().join("preserved")).unwrap();
                fs::create_dir(&namespace).unwrap();
            }
            "prefix-link" => {
                fs::remove_file(&prefix).unwrap();
                symlink("other", &prefix).unwrap();
            }
            "permissions" => {
                use std::os::unix::fs::PermissionsExt;
                let mode = fs::metadata(&namespace).unwrap().permissions().mode();
                fs::set_permissions(&namespace, fs::Permissions::from_mode(mode ^ 0o020)).unwrap();
            }
            "link" => {
                fs::remove_file(&link).unwrap();
                symlink("../prefix/missing/leaf", &link).unwrap();
            }
            _ => unreachable!(),
        });
        assert!(result.is_err(), "accepted {mode} during an absence observation");
    }
}

#[cfg(unix)]
#[test]
fn missing_installation_links_bind_resolved_alias_routes_outside_the_installation() {
    use std::os::unix::fs::symlink;

    for replacement in ["namespace", "./namespace"] {
        let installation = tempfile::tempdir().unwrap();
        let external = tempfile::tempdir().unwrap();
        fs::create_dir(external.path().join("namespace")).unwrap();
        fs::create_dir(external.path().join("namespace/existing")).unwrap();
        let route = external.path().join("route");
        symlink("namespace", &route).unwrap();
        let link = installation.path().join("helper");
        symlink(route.join("existing/missing/leaf"), &link).unwrap();
        let before = super::installation_tree_digest(installation.path()).unwrap();
        let result = super::missing_installation_link_digest_with_hook(&link, || {
            fs::rename(&route, external.path().join("preserved-route")).unwrap();
            symlink(replacement, &route).unwrap();
        });
        assert!(result.unwrap_err().contains("namespace route moved"));
        if replacement == "./namespace" {
            assert_ne!(before, super::installation_tree_digest(installation.path()).unwrap());
        }
        assert!(super::namespace_route_links([external.path()], 0).is_err());
    }
}

#[cfg(unix)]
#[test]
fn resolved_installation_route_chains_bookend_aliases_before_terminal_components() {
    use std::os::unix::fs::symlink;

    for suffix in ["", "/", "/."] {
        for replacement in ["namespace", "./namespace"] {
            let installation = tempfile::tempdir().unwrap();
            let external = tempfile::tempdir().unwrap();
            fs::create_dir(external.path().join("namespace")).unwrap();
            fs::create_dir(external.path().join("namespace/existing")).unwrap();
            let intermediate = external.path().join("intermediate");
            symlink("namespace", &intermediate).unwrap();
            let route = external.path().join("route");
            symlink(format!("intermediate{suffix}"), &route).unwrap();
            let link = installation.path().join("helper");
            symlink(route.join("existing/missing/leaf"), &link).unwrap();
            let before = super::installation_tree_digest(installation.path()).unwrap();
            assert_eq!(before, super::installation_tree_digest(installation.path()).unwrap());
            let result = super::missing_installation_link_digest_with_hook(&link, || {
                fs::rename(&intermediate, external.path().join("preserved-intermediate")).unwrap();
                symlink(replacement, &intermediate).unwrap();
            });
            assert!(result.unwrap_err().contains("namespace route moved"), "accepted {suffix:?}");
            if replacement == "./namespace" {
                assert_ne!(before, super::installation_tree_digest(installation.path()).unwrap());
            }
        }
    }
}

#[cfg(unix)]
#[test]
fn secondary_dangling_installation_routes_refuse_before_observing_a_false_parent() {
    use std::os::unix::fs::symlink;

    for suffix in ["", "/", "/."] {
        let installation = tempfile::tempdir().unwrap();
        let external = tempfile::tempdir().unwrap();
        fs::create_dir(external.path().join("namespace")).unwrap();
        let route = external.path().join("route");
        symlink("namespace/missing/leaf", &route).unwrap();
        let link = installation.path().join("helper");
        symlink(format!("{}{suffix}", route.display()), &link).unwrap();
        let reached_observation = Cell::new(false);
        let result = super::missing_installation_link_digest_with_hook(&link, || {
            reached_observation.set(true);
            fs::create_dir(external.path().join("namespace/missing")).unwrap();
        });
        let error = result.unwrap_err();
        assert!(error.contains("unsupported secondary unresolved installation link"));
        assert!(error.contains(route.to_str().unwrap()));
        assert!(
            !reached_observation.get(),
            "the unresolved route must never earn an absence record"
        );
        fs::create_dir(external.path().join("namespace/missing")).unwrap();
        assert!(super::installation_tree_digest(installation.path()).is_err());
        fs::remove_file(&route).unwrap();
        symlink("./namespace/missing/leaf", &route).unwrap();
        assert!(super::installation_tree_digest(installation.path()).is_err());
    }
}

#[cfg(unix)]
#[test]
fn installation_inputs_refuse_loops_non_directories_and_unsupported_files() {
    use std::os::unix::fs::symlink;

    let root = tempfile::tempdir().unwrap();
    let link = root.path().join("helper");
    symlink("helper", &link).unwrap();
    assert!(super::installation_tree_digest(root.path()).is_err());
    fs::remove_file(&link).unwrap();
    fs::write(root.path().join("file"), b"ordinary file").unwrap();
    symlink("file/missing", &link).unwrap();
    assert!(super::installation_tree_digest(root.path()).is_err());
    fs::remove_file(&link).unwrap();
    // Root can legitimately traverse a mode-000 directory. The ordinary-user
    // branch verifies that an actual permission error is never called absence.
    if unsafe { libc::geteuid() } != 0 {
        use std::os::unix::fs::PermissionsExt;
        let protected = root.path().join("protected");
        fs::create_dir(&protected).unwrap();
        symlink("protected/missing", &link).unwrap();
        fs::set_permissions(&protected, fs::Permissions::from_mode(0o000)).unwrap();
        let resolution = fs::canonicalize(&link);
        let result = super::installation_tree_digest(root.path());
        fs::set_permissions(&protected, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(resolution.unwrap_err().kind(), std::io::ErrorKind::PermissionDenied);
        assert!(result.unwrap_err().contains(link.to_str().unwrap()));
        fs::remove_file(&link).unwrap();
        println!("installation permission-error control executed as an ordinary user");
    }
    let fifo = root.path().join("unsupported");
    assert!(std::process::Command::new("mkfifo").arg(&fifo).status().unwrap().success());
    assert!(super::installation_tree_digest(root.path()).is_err());
}

#[test]
fn equal_length_replacement_with_restored_mtime_is_refused_during_read() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("compiler");
    fs::write(&path, "before").unwrap();
    let modified = fs::metadata(&path).unwrap().modified().unwrap();
    let result = file_digest_with_hooks(
        &path,
        || {},
        || {
            let replacement = root.path().join("replacement");
            fs::write(&replacement, "after!").unwrap();
            std::fs::File::open(&replacement).unwrap().set_modified(modified).unwrap();
            fs::rename(replacement, &path).unwrap();
        },
    );
    assert!(result.unwrap_err().contains("moved while it was read"));
}

#[cfg(unix)]
#[test]
fn a_regular_input_replaced_with_a_symlink_is_not_followed() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("input");
    fs::write(&path, b"original").unwrap();
    let result = file_digest_with_hooks(
        &path,
        || {
            let preserved = root.path().join("preserved");
            fs::rename(&path, &preserved).unwrap();
            std::os::unix::fs::symlink(preserved, &path).unwrap();
        },
        || panic!("a replaced symlink must not reach the read boundary"),
    );
    assert_eq!(
        result.unwrap_err(),
        std::io::Error::from_raw_os_error(libc::ELOOP).to_string(),
        "the open itself must refuse the replaced leaf"
    );
}

#[cfg(unix)]
#[test]
fn a_regular_input_replaced_with_a_fifo_is_refused_without_blocking() {
    const CONTROL_PATH: &str = "TRUST_NATIVE_REPO_FIFO_CONTROL_PATH";
    if let Some(path) = std::env::var_os(CONTROL_PATH) {
        let path = std::path::Path::new(&path);
        let other = path.with_extension("other");
        fs::write(&other, b"another leaf").unwrap();
        let result = super::hash_leaves(&[path.to_owned(), other], 2, |candidate| {
            if candidate != path {
                return super::file_digest(candidate);
            }
            file_digest_with_hooks(
                candidate,
                || {
                    fs::rename(path, path.with_extension("preserved")).unwrap();
                    assert!(
                        std::process::Command::new("mkfifo").arg(path).status().unwrap().success()
                    );
                },
                || panic!("a replaced FIFO must not reach the read boundary"),
            )
        });
        assert!(result.unwrap_err().contains("opened input is not a regular file"));
        println!("replaced FIFO refused before reading");
        return;
    }

    // Trust: the regression must fail within a bound if open ever blocks again.
    // The parent kills/reaps only its own control child before retiring the fixture.
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("input");
    fs::write(&path, b"original").unwrap();
    let mut child = crate::test_entry::uncaptured_actor(std::process::Command::new(std::env::current_exe().unwrap()))
        .args([
            "--exact",
            "utils::trust_repo_cache::tests::a_regular_input_replaced_with_a_fifo_is_refused_without_blocking",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CONTROL_PATH, &path)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        match child.try_wait() {
            Ok(Some(_)) => {
                let output = child.wait_with_output().unwrap();
                assert!(output.status.success(), "{output:?}");
                assert!(
                    String::from_utf8_lossy(&output.stdout)
                        .contains("replaced FIFO refused before reading"),
                    "zero executed controls cannot pass: {output:?}"
                );
                break;
            }
            Ok(None) if std::time::Instant::now() < deadline => {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            state => {
                let killed = child.kill();
                let output = child.wait_with_output().unwrap();
                panic!("FIFO control did not complete: {state:?}; kill={killed:?}; {output:?}");
            }
        }
    }
}

#[test]
fn a_tracked_leaf_replaced_with_a_directory_is_not_a_gitlink() {
    let root = tempfile::tempdir().unwrap();
    let git = |arguments: &[&str]| {
        let result = std::process::Command::new("git")
            .arg("-C")
            .arg(root.path())
            .args(arguments)
            .output()
            .unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    };
    git(&["init"]);
    fs::write(root.path().join("input.rs"), "fn main() {}").unwrap();
    git(&["add", "input.rs"]);
    git(&[
        "-c",
        "user.name=Native cache test",
        "-c",
        "user.email=native-cache@example.invalid",
        "commit",
        "-m",
        "fixture",
    ]);
    let before = repository_digest(root.path(), 1).unwrap();
    fs::write(root.path().join("input.rs"), "fn main() { panic!() }").unwrap();
    assert_ne!(before, repository_digest(root.path(), 1).unwrap());
    fs::remove_file(root.path().join("input.rs")).unwrap();
    fs::create_dir(root.path().join("input.rs")).unwrap();
    let result = repository_digest(root.path(), 1);
    assert!(result.unwrap_err().contains("unexpected directory"));
}

#[cfg(unix)]
fn commit_source_fixture(root: &std::path::Path) {
    for arguments in [
        vec!["init"],
        vec!["add", "--all"],
        vec![
            "-c",
            "user.name=Native alias test",
            "-c",
            "user.email=native-alias@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-m",
            "fixture",
        ],
    ] {
        let output =
            std::process::Command::new("git").arg("-C").arg(root).args(arguments).output().unwrap();
        assert!(output.status.success(), "{output:?}");
    }
}

#[cfg(unix)]
#[test]
fn directory_aliases_bind_inventoried_sources_without_recursing_into_ignored_trees() {
    use std::os::unix::fs::symlink;

    let root = tempfile::tempdir().unwrap();
    fs::create_dir(root.path().join("real")).unwrap();
    fs::write(root.path().join("real/input.rs"), b"before").unwrap();
    symlink("real", root.path().join("alias")).unwrap();
    symlink("alias", root.path().join("indirect")).unwrap();
    symlink(".", root.path().join("ancestor")).unwrap();
    fs::create_dir(root.path().join("first-party")).unwrap();
    symlink("..", root.path().join("first-party/trust")).unwrap();
    fs::write(root.path().join(".gitignore"), b"build/\n").unwrap();
    fs::create_dir(root.path().join("build")).unwrap();
    // Following the ancestor alias into this ignored tree would fail. Source
    // aliases name the Git inventory; they do not start another directory walk.
    assert!(
        std::process::Command::new("mkfifo")
            .arg(root.path().join("build/not-source"))
            .status()
            .unwrap()
            .success()
    );
    commit_source_fixture(root.path());
    let before = repository_digest(root.path(), 2).unwrap();
    fs::write(root.path().join("real/input.rs"), b"after!").unwrap();
    assert_ne!(before, repository_digest(root.path(), 2).unwrap());
}

#[cfg(unix)]
#[test]
fn directory_aliases_refuse_external_dangling_and_unresolvable_targets() {
    use std::os::unix::fs::symlink;

    let root = tempfile::tempdir().unwrap();
    let external = tempfile::tempdir().unwrap();
    fs::create_dir(root.path().join("real")).unwrap();
    fs::write(root.path().join("real/input.rs"), b"source").unwrap();
    let alias = root.path().join("alias");
    symlink("real", &alias).unwrap();
    commit_source_fixture(root.path());
    for target in [external.path(), std::path::Path::new("missing"), std::path::Path::new("alias")]
    {
        fs::remove_file(&alias).unwrap();
        symlink(target, &alias).unwrap();
        assert!(repository_digest(root.path(), 2).is_err(), "accepted {target:?}");
    }
}

#[cfg(unix)]
#[test]
fn directory_alias_fd_and_path_bookends_refuse_link_target_and_chain_replacement() {
    use std::os::unix::fs::symlink;

    for mode in ["link", "target", "chain"] {
        let root = tempfile::tempdir().unwrap();
        let real = root.path().join("real");
        let other = root.path().join("other");
        fs::create_dir(&real).unwrap();
        fs::create_dir(&other).unwrap();
        fs::write(real.join("input.rs"), b"identical").unwrap();
        fs::write(other.join("input.rs"), b"identical").unwrap();
        let alias = root.path().join("alias");
        let chain = root.path().join("chain");
        symlink("real", &chain).unwrap();
        symlink("chain", &alias).unwrap();
        let before =
            super::source_directory_link_digest_with_hook(root.path(), &alias, || {}).unwrap();
        let result =
            super::source_directory_link_digest_with_hook(root.path(), &alias, || match mode {
                "link" => {
                    fs::remove_file(&alias).unwrap();
                    symlink("chain", &alias).unwrap();
                }
                "target" => {
                    fs::rename(&real, root.path().join("preserved")).unwrap();
                    fs::create_dir(&real).unwrap();
                    fs::write(real.join("input.rs"), b"identical").unwrap();
                }
                "chain" => {
                    fs::remove_file(&chain).unwrap();
                    symlink("other", &chain).unwrap();
                }
                _ => unreachable!(),
            });
        assert!(result.is_err(), "accepted {mode} replacement");
        if mode == "chain" {
            assert_ne!(
                before,
                super::source_directory_link_digest_with_hook(root.path(), &alias, || {}).unwrap(),
                "the resolved target matters even when the outer link bytes do not change"
            );
        }
    }
}

#[cfg(unix)]
#[test]
fn record_only_reexecutes_when_a_source_alias_reaches_a_changed_ignored_input() {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join(".gitignore"), b"build/\n").unwrap();
    fs::write(root.path().join("input.rs"), b"fn main() {}").unwrap();
    std::os::unix::fs::symlink(".", root.path().join("ancestor")).unwrap();
    let build = root.path().join("build");
    let outputs = build.join("outputs");
    let cache = build.join("cache");
    fs::create_dir_all(&outputs).unwrap();
    fs::write(build.join("runtime-input"), b"passes").unwrap();
    commit_source_fixture(root.path());
    let snapshot = || repository_digest(root.path(), 2).map(super::InputSnapshot::from);
    let before = snapshot().unwrap();
    let executions = Cell::new(0);
    let execute = || {
        executions.set(executions.get() + 1);
        if fs::read(root.path().join("ancestor/build/runtime-input")).unwrap() == b"passes" {
            Ok(())
        } else {
            Err("selected test failed on an ignored input reached through its source alias".into())
        }
    };
    assert_eq!(
        run(ReusePolicy::RecordOnly, &cache, &outputs, snapshot, execute).unwrap(),
        Reuse::Executed
    );
    fs::write(build.join("runtime-input"), b"fails!").unwrap();
    assert_eq!(before, snapshot().unwrap(), "ignored reads still are not a complete closure");
    let failed = run(ReusePolicy::RecordOnly, &cache, &outputs, snapshot, execute);
    assert!(failed.unwrap_err().contains("ignored input"));
    assert_eq!(executions.get(), 2);
    assert!(!cache.join("success.json").exists());
}

// Trust: the landing gate's audit rows of trust_repo_cache.rs and of the WP
// transaction rest on this refusal (scripts/gates/land-escape-audits.toml).
#[test]
#[should_panic(expected = "a unit test never runs git in this checkout")]
fn a_unit_test_never_runs_git_in_this_checkout() {
    let _ = super::git_command(std::path::Path::new(env!("CARGO_MANIFEST_DIR")));
}
