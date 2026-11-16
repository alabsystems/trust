//! Planner/removal controls use fixture DATA and actual native exclusion.
//! They never execute fixture bytes or manufacture a healthy compiler/SDK.

use std::fs;
use std::os::unix::fs::{MetadataExt as _, symlink};
use std::time::Duration;

use build_helper::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};

use super::*;

const HOST: &str = "native-cache-fixture-host";
// Isolate before ANY fixture FD: other tests may spawn while a lock is being
// closed (crate::utils::tests::isolated).
use crate::utils::tests::isolated;

struct Fixture {
    _temp: tempfile::TempDir,
    root: PathBuf,
    build: PathBuf,
    host: PathBuf,
    output: OutputLock,
}
impl Fixture {
    fn new() -> Self {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().canonicalize().unwrap();
        let build = root.join("build");
        let host = build.join(HOST);
        fs::create_dir_all(&host).unwrap();
        let output = OutputLock::try_acquire(&build).unwrap().unwrap();
        Self { _temp: temp, root, build, host, output }
    }
    fn put(&self, relative: &str, bytes: &[u8]) -> PathBuf {
        let path = self.build.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, bytes).unwrap();
        path
    }
    fn tree(&self, name: &str) -> PathBuf {
        self.put(&format!("{HOST}/{name}/release/deps/cache.bin"), &[b'c'; 32768]);
        self.host.join(name)
    }
    fn request(&self, compilers: bool, preview: bool) -> WholeRequest {
        WholeRequest::new(&self.root, Path::new(HOST), compilers, preview).unwrap()
    }
    fn lease(&self) -> Lease {
        match Manager::open(&self.root)
            .unwrap()
            .acquire_lease(&Acquire {
                kind: Kind::Build,
                owner_pid: std::process::id(),
                purpose: "native whole-cache regression".into(),
                contract: "actual independent fixture ownership; no compiler/SDK claim".into(),
                wait: Duration::ZERO,
                inherited_token: None,
                break_reason: None,
            })
            .unwrap()
        {
            LeaseAcquisition::Granted(lease) => lease,
            LeaseAcquisition::Busy(_) => panic!("private native fixture unexpectedly held"),
        }
    }
}
fn report(request: &WholeRequest, prepared: &Prepared) -> WholeReport {
    WholeReport {
        profile: request.profile,
        dry_run: request.dry_run,
        compiler_caches: request.compiler_caches,
        planned_trees: prepared.candidates.iter().map(|c| c.path.clone()).collect(),
        removed_trees: Vec::new(),
        preserved: prepared.preserved.clone(),
        planned_file_space: prepared.inventory.finish().unwrap(),
        volume_space: None,
        removed_allocated_bytes: 0,
        sysroots: Vec::new(),
        failures: Vec::new(),
    }
}
fn selected(prepared: &Prepared, path: &Path) -> bool {
    prepared.candidates.iter().any(|c| c.path == path)
}
fn snapshot(path: &Path) -> BTreeMap<PathBuf, (u64, u64, Vec<u8>)> {
    fn visit(root: &Path, path: &Path, out: &mut BTreeMap<PathBuf, (u64, u64, Vec<u8>)>) {
        let meta = fs::symlink_metadata(path).unwrap();
        let bytes = if meta.is_file() {
            fs::read(path).unwrap()
        } else if meta.file_type().is_symlink() {
            fs::read_link(path).unwrap().as_os_str().as_bytes().to_vec()
        } else {
            Vec::new()
        };
        out.insert(path.strip_prefix(root).unwrap().to_owned(), (meta.dev(), meta.ino(), bytes));
        if meta.is_dir() {
            for entry in fs::read_dir(path).unwrap() {
                visit(root, &entry.unwrap().path(), out);
            }
        }
    }
    let mut result = BTreeMap::new();
    visit(path, path, &mut result);
    result
}

#[test]
fn exact_tools_are_selected_and_compiler_targets_require_separate_opt_in() {
    isolated(|| {
        let f = Fixture::new();
        for tree in TOOLS.iter().chain(COMPILERS) {
            f.tree(tree);
        }
        for keep in [
            "stage0",
            "stage0-sysroot",
            "stage1",
            "stage2",
            "stage1-std",
            "llvm",
            "stage1-tools-bin",
            "stage2-tools-bin",
            "stage3-tools-bin",
            "stage1-tools-lookalike",
        ] {
            f.tree(keep);
        }
        let request = f.request(false, true);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        assert_eq!(prepared.candidates.len(), TOOLS.len());
        for tool in TOOLS {
            assert!(selected(&prepared, &f.host.join(tool)));
        }
        for compiler in COMPILERS {
            assert!(!selected(&prepared, &f.host.join(compiler)));
        }
        drop(prepared);
        let request = f.request(true, true);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        assert_eq!(prepared.candidates.len(), TOOLS.len() + COMPILERS.len());
    });
}

#[test]
fn preview_measures_both_selected_links_once_and_holds_actual_cargo_locks() {
    isolated(|| {
        let f = Fixture::new();
        let a = f.put(&format!("{HOST}/stage1-tools/release/deps/a"), &[b'a'; 65536]);
        let b = f.host.join("stage2-tools/release/deps/b");
        fs::create_dir_all(b.parent().unwrap()).unwrap();
        fs::hard_link(&a, &b).unwrap();
        let lock = f.put(&format!("{HOST}/stage1-tools/release/.cargo-lock"), b"");
        let request = f.request(false, true);
        let before = snapshot(&f.build);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        assert_eq!(prepared.inventory.finish().unwrap().counted_inodes, 2); // payload + actual lock
        let other = File::open(&lock).unwrap();
        assert!(matches!(other.try_lock(), Err(fs::TryLockError::WouldBlock)));
        assert_eq!(snapshot(&f.build), before);
        assert!(prepared.detached.is_empty());
        drop(prepared);
        other.try_lock().unwrap();
    });
}

#[test]
fn busy_or_nonregular_cargo_lock_refuses_before_any_detach() {
    isolated(|| {
        for nonregular in [false, true] {
            let f = Fixture::new();
            f.tree("stage1-tools");
            let path = f.host.join("stage1-tools/release/.cargo-lock");
            let held = if nonregular {
                symlink("deps/cache.bin", &path).unwrap();
                None
            } else {
                let file = File::create(&path).unwrap();
                file.try_lock().unwrap();
                Some(file)
            };
            let before = snapshot(&f.build);
            assert!(Prepared::new(&f.request(false, false), &f.output).is_err());
            assert_eq!(snapshot(&f.build), before);
            drop(held);
        }
    });
}

#[test]
fn safe_reclaim_names_and_recovery_husks_need_their_preserved_primary() {
    isolated(|| {
        let f = Fixture::new();
        f.tree("stage1");
        for name in [
            "stage1-tools.slim-reclaim-12-34",
            "stage2-rustc.slim-reclaim-12-34",
            "stage1.pre-cache-recovery.saved",
            "stage2.pre-cache-recovery.saved",
            "stage1-tools.slim-reclaim-0-34",
            "stage1-tools.slim-reclaim-12-034",
            "stage1-tools.slim-reclaim-12-34-extra",
        ] {
            f.tree(name);
        }
        let prepared = Prepared::new(&f.request(false, true), &f.output).unwrap();
        assert!(selected(&prepared, &f.host.join("stage1-tools.slim-reclaim-12-34")));
        assert!(selected(&prepared, &f.host.join("stage1.pre-cache-recovery.saved")));
        for name in [
            "stage2-rustc.slim-reclaim-12-34",
            "stage2.pre-cache-recovery.saved",
            "stage1-tools.slim-reclaim-0-34",
            "stage1-tools.slim-reclaim-12-034",
            "stage1-tools.slim-reclaim-12-34-extra",
        ] {
            assert!(!selected(&prepared, &f.host.join(name)), "{name}");
        }
    });
}

#[test]
fn newest_private_sysroot_ties_stay_and_only_older_variants_are_selected() {
    isolated(|| {
        let f = Fixture::new();
        for (name, time) in [("old", 1), ("new", 2), ("tie", 2)] {
            let path = f.tree(&format!("rustc-private-sysroots/rustc-private-tool-{name}"));
            File::open(path).unwrap().set_modified(UNIX_EPOCH + Duration::from_secs(time)).unwrap();
        }
        let prepared = Prepared::new(&f.request(false, true), &f.output).unwrap();
        assert_eq!(prepared.candidates.len(), 1);
        assert!(selected(&prepared, &f.host.join("rustc-private-sysroots/rustc-private-tool-old")));
        assert_eq!(prepared.preserved.len(), 2);
    });
}

#[test]
fn native_apply_preserves_installed_hardlinks_and_recreates_only_scratch() {
    isolated(|| {
        let f = Fixture::new();
        for tool in TOOLS {
            f.tree(tool);
        }
        f.tree("stage1-rustc");
        let source = f.host.join("stage1-rustc/release/deps/cache.bin");
        let kept = f.host.join("stage1/lib/librustc_driver.dylib");
        fs::create_dir_all(kept.parent().unwrap()).unwrap();
        fs::hard_link(&source, &kept).unwrap();
        let installed = f.put(&format!("{HOST}/stage1-tools-bin/installed"), b"installed product");
        f.put("tmp/scratch", b"scratch");
        let original = fs::read(&kept).unwrap();
        let request = f.request(true, false);
        let lease = f.lease();
        let mut prepared = Prepared::new(&request, &f.output).unwrap();
        let mut result = report(&request, &prepared);
        prepared.apply(&request, &lease, &f.output, &mut result).unwrap();
        assert!(result.failures.is_empty(), "{result:?}");
        assert_eq!(result.removed_trees.len(), TOOLS.len() + 2); // compiler + scratch
        assert_eq!(fs::read(&kept).unwrap(), original);
        assert_eq!(fs::read(installed).unwrap(), b"installed product");
        assert!(f.build.join("tmp").is_dir());
        assert_eq!(fs::read_dir(f.build.join("tmp")).unwrap().count(), 0);
        prepared.check_kept(&prepared.removed_links).unwrap();
        lease.check_root(&f.root).unwrap();
        f.output.check_current().unwrap();
    });
}

#[test]
fn kept_symlink_into_selected_tree_refuses_and_kept_outside_hardlink_counts_zero() {
    isolated(|| {
        let f = Fixture::new();
        let tree = f.tree("stage1-tools");
        let payload = tree.join("release/deps/cache.bin");
        let kept = f.host.join("stage1/lib/keep");
        fs::create_dir_all(kept.parent().unwrap()).unwrap();
        fs::hard_link(&payload, &kept).unwrap();
        let request = f.request(false, true);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        assert_eq!(prepared.inventory.finish().unwrap().counted_inodes, 0);
        drop(prepared);
        symlink(&payload, f.host.join("stage1/selected-alias")).unwrap();
        let before = snapshot(&f.build);
        assert!(Prepared::new(&request, &f.output).is_err());
        assert_eq!(snapshot(&f.build), before);
    });
}

#[test]
fn selected_symlink_or_fifo_never_opens_a_target_or_blocks() {
    isolated(|| {
        for fifo in [false, true] {
            let f = Fixture::new();
            let outside = f.put("outside/keep", b"outside");
            let target = f.host.join("stage1-tools");
            if fifo {
                let name = cstring(target.as_os_str()).unwrap();
                assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
            } else {
                symlink(outside.parent().unwrap(), &target).unwrap();
            }
            assert!(Prepared::new(&f.request(false, true), &f.output).is_err());
            assert_eq!(fs::read(outside).unwrap(), b"outside");
        }
    });
}

#[test]
fn atomic_detach_never_clobbers_an_existing_reclaim_destination() {
    isolated(|| {
        let f = Fixture::new();
        f.tree("stage1-tools");
        f.tree("stage1-tools.slim-reclaim-12-34");
        let parent =
            space::open_at(f.output.original_directory().unwrap(), OsStr::new(HOST), true).unwrap();
        assert!(
            rename_exclusive(
                parent.as_fd(),
                OsStr::new("stage1-tools"),
                OsStr::new("stage1-tools.slim-reclaim-12-34")
            )
            .is_err()
        );
        assert!(f.host.join("stage1-tools/release/deps/cache.bin").is_file());
        assert!(f.host.join("stage1-tools.slim-reclaim-12-34/release/deps/cache.bin").is_file());
    });
}

#[test]
fn new_selected_entry_retains_detached_leftover_without_following_it() {
    isolated(|| {
        let f = Fixture::new();
        let tree = f.tree("stage1-tools");
        let request = f.request(false, false);
        let mut prepared = Prepared::new(&request, &f.output).unwrap();
        let aside = OsStr::new("stage1-tools.slim-reclaim-12-34");
        let parent =
            space::open_at(f.output.original_directory().unwrap(), OsStr::new(HOST), true).unwrap();
        rename_exclusive(parent.as_fd(), OsStr::new("stage1-tools"), aside).unwrap();
        let retained = f.host.join(aside);
        fs::write(retained.join("unexpected"), b"new input").unwrap();
        let mut bytes = 0;
        assert!(
            remove_selected(
                parent.as_fd(),
                aside,
                relative(&request, &tree).unwrap(),
                &prepared.inventory,
                &mut prepared.removed_links,
                &mut bytes
            )
            .is_err()
        );
        assert_eq!(fs::read(retained.join("unexpected")).unwrap(), b"new input");
    });
}

#[test]
fn outside_link_added_after_own_unlink_is_not_hidden_by_old_max_nlink() {
    isolated(|| {
        let f = Fixture::new();
        let a = f.put(&format!("{HOST}/stage1-tools/release/deps/a"), &[b'x'; 32768]);
        let b = f.host.join("stage2-tools/release/deps/b");
        fs::create_dir_all(b.parent().unwrap()).unwrap();
        fs::hard_link(&a, &b).unwrap();
        let request = f.request(false, false);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        assert_eq!(prepared.inventory.finish().unwrap().counted_inodes, 1);
        let (ap, an) = prepared.inventory.parent(relative(&request, &a).unwrap()).unwrap();
        let mut removed = BTreeMap::new();
        let mut bytes = 0;
        remove_selected(
            ap.as_fd(),
            &an,
            relative(&request, &a).unwrap(),
            &prepared.inventory,
            &mut removed,
            &mut bytes,
        )
        .unwrap();
        let outside = f._temp.path().join("outside-link");
        fs::hard_link(&b, &outside).unwrap();
        let (bp, bn) = prepared.inventory.parent(relative(&request, &b).unwrap()).unwrap();
        assert!(
            remove_selected(
                bp.as_fd(),
                &bn,
                relative(&request, &b).unwrap(),
                &prepared.inventory,
                &mut removed,
                &mut bytes
            )
            .is_err()
        );
        assert_eq!(bytes, 0);
        assert_eq!(fs::read(&outside).unwrap(), vec![b'x'; 32768]);
        assert!(b.is_file());
    });
}

#[test]
fn changed_output_or_holder_cannot_authorize_apply() {
    isolated(|| {
        for output in [false, true] {
            let f = Fixture::new();
            let tree = f.tree("stage1-tools");
            let request = f.request(false, false);
            let lease = f.lease();
            let mut prepared = Prepared::new(&request, &f.output).unwrap();
            let mut result = report(&request, &prepared);
            let path =
                if output { f.build.join("lock") } else { f.root.join(".trust-build-lock/info") };
            fs::rename(&path, path.with_extension("original")).unwrap();
            fs::write(&path, b"foreign replacement").unwrap();
            assert!(prepared.apply(&request, &lease, &f.output, &mut result).is_err());
            assert!(tree.is_dir());
            assert_eq!(fs::read(&path).unwrap(), b"foreign replacement");
        }
    });
}

#[test]
fn kept_parent_replacement_cannot_redirect_whole_tree_traversal() {
    isolated(|| {
        let f = Fixture::new();
        f.tree("stage1-tools");
        let kept = f.put(&format!("{HOST}/stage1/lib/keep"), b"original");
        let request = f.request(false, true);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        let old = kept.parent().unwrap();
        let saved = old.with_extension("original");
        fs::rename(old, &saved).unwrap();
        fs::create_dir(old).unwrap();
        fs::write(old.join("keep"), b"foreign").unwrap();
        assert!(prepared.check_kept(&BTreeMap::new()).is_err());
        assert_eq!(fs::read(saved.join("keep")).unwrap(), b"original");
        assert_eq!(fs::read(old.join("keep")).unwrap(), b"foreign");
    });
}

#[test]
fn actual_native_controller_inode_inside_a_selected_tool_target_refuses_before_detach() {
    isolated(|| {
        let f = Fixture::new();
        let source = std::env::current_exe().unwrap().canonicalize().unwrap();
        let selected_image = f.host.join("stage1-tools/release/native-controller");
        fs::create_dir_all(selected_image.parent().unwrap()).unwrap();
        // A distinct copy of this genuine native test image, not a script or
        // manufactured SDK. The held original identity supplies a refusal
        // input only; this fixture never executes or certifies the copy.
        fs::copy(source, &selected_image).unwrap();
        let original = File::open(&selected_image).unwrap();
        let metadata = original.metadata().unwrap();
        let request = f.request(false, false);
        let prepared = Prepared::new(&request, &f.output).unwrap();
        assert!(prepared.protect_original_inputs([(metadata.dev(), metadata.ino())]).is_err());
        assert!(selected_image.is_file());
        assert!(prepared.detached.is_empty());
        assert_eq!(original.metadata().unwrap().ino(), metadata.ino());
    });
}

#[test]
fn sparse_file_removed_allocation_is_actual_blocks_including_zero() {
    isolated(|| {
        let f = Fixture::new();
        let sparse = f.host.join("stage1-tools/release/deps/sparse");
        fs::create_dir_all(sparse.parent().unwrap()).unwrap();
        let file = File::create(&sparse).unwrap();
        file.set_len(128 * 1024 * 1024).unwrap();
        let before = file.metadata().unwrap();
        assert_eq!(before.blocks(), 0, "fixture must be an actually unallocated sparse file");
        let request = f.request(false, false);
        let lease = f.lease();
        let mut prepared = Prepared::new(&request, &f.output).unwrap();
        let mut result = report(&request, &prepared);
        prepared.apply(&request, &lease, &f.output, &mut result).unwrap();
        assert!(result.failures.is_empty(), "{result:?}");
        assert_eq!(result.removed_allocated_bytes, 0);
        assert!(!sparse.exists());
        assert_eq!(file.metadata().unwrap().len(), before.len());
    });
}

#[test]
fn kept_symlink_bridge_and_dotdot_dependencies_refuse_before_any_selected_unlink() {
    isolated(|| {
        for dotdot in [false, true] {
            let f = Fixture::new();
            let selected = f.tree("stage1-tools");
            let kept = f.put("kept.dat", b"preserved final inode");
            let name = f.build.join("kept-link");
            if dotdot {
                symlink(format!("{HOST}/stage1-tools/../../kept.dat"), &name).unwrap();
            } else {
                symlink("../../kept.dat", selected.join("bridge")).unwrap();
                symlink(format!("{HOST}/stage1-tools/bridge"), &name).unwrap();
            }
            // Both aliases really reach the SAME unselected inode before
            // mutation; final-target-only checking therefore cannot catch it.
            assert_eq!(fs::metadata(&name).unwrap().ino(), fs::metadata(&kept).unwrap().ino());
            let before = snapshot(&f.build);
            let error = match Prepared::new(&f.request(false, false), &f.output) {
                Err(error) => error,
                Ok(_) => panic!("kept link dependency entered the plan"),
            };
            assert!(error.to_string().contains("traverses selected namespace"), "{error}");
            assert_eq!(snapshot(&f.build), before);
            assert!(selected.join("release/deps/cache.bin").is_file());
            assert_eq!(fs::read(&name).unwrap(), b"preserved final inode");
        }
    });
}

#[test]
fn unselected_relative_absolute_and_outside_symlink_targets_remain_allowed() {
    isolated(|| {
        let f = Fixture::new();
        f.tree("stage1-tools");
        let kept = f.put("preserved/data", b"kept");
        let outside = f._temp.path().join("outside");
        fs::write(&outside, b"outside").unwrap();
        symlink("preserved/data", f.build.join("relative-link")).unwrap();
        symlink(&kept, f.build.join("absolute-link")).unwrap();
        symlink(&outside, f.build.join("outside-link")).unwrap();
        let request = f.request(false, false);
        let lease = f.lease();
        let mut prepared = Prepared::new(&request, &f.output).unwrap();
        let mut result = report(&request, &prepared);
        prepared.apply(&request, &lease, &f.output, &mut result).unwrap();
        assert!(result.failures.is_empty(), "{result:?}");
        assert_eq!(fs::read(f.build.join("relative-link")).unwrap(), b"kept");
        assert_eq!(fs::read(f.build.join("absolute-link")).unwrap(), b"kept");
        assert_eq!(fs::read(f.build.join("outside-link")).unwrap(), b"outside");
    });
}

#[test]
fn scratch_or_stale_scratch_host_cannot_select_its_primary_sysroots() {
    isolated(|| {
        for host in ["tmp", "tmp.slim-reclaim-12-34"] {
            let f = Fixture::new();
            f.put(&format!("{host}/stage1/bin/trustc"), b"health fixture DATA; never executed");
            f.put(&format!("{host}/stage2/lib/keep"), b"preserved product DATA");
            assert!(WholeRequest::new(&f.root, Path::new(host), true, false).is_err());
            // Independently enforce the plan invariant even for an internal
            // caller already holding selection DATA. No health/SDK is forged.
            let request = WholeRequest {
                selection: SelectedOutput::capture(&f.root).unwrap(),
                profile: WholeProfile::Compilers,
                root: f.root.clone(),
                build: f.build.clone(),
                host: f.build.join(host),
                compiler_caches: true,
                dry_run: false,
            };
            let before = snapshot(&f.build);
            let error = match Prepared::new(&request, &f.output) {
                Err(error) => error,
                Ok(_) => panic!("scratch candidate contained the actual preserved host"),
            };
            assert!(error.to_string().contains("protected original host/sysroot"), "{error}");
            assert_eq!(snapshot(&f.build), before);
        }
    });
}

#[test]
fn host_discovery_does_not_treat_scratch_stage_names_as_a_host() {
    isolated(|| {
        let f = Fixture::new();
        f.put(&format!("{HOST}/stage1/keep"), b"real host namespace DATA");
        f.put("tmp/stage1/keep", b"scratch namespace DATA");
        f.put("tmp.slim-reclaim-12-34/stage2/keep", b"stale scratch DATA");
        assert_eq!(
            WholeRequest::detect_host(&SelectedOutput::capture(&f.root).unwrap(), &f.output)
                .unwrap(),
            OsStr::new(HOST)
        );
    });
}

#[test]
fn scratch_host_case_aliases_are_refused_before_health_or_path_work() {
    isolated(|| {
        let f = Fixture::new();
        for host in ["TMP", "Tmp.Slim-Reclaim-12-34"] {
            let error = match WholeRequest::new(&f.root, Path::new(host), true, false) {
                Err(error) => error,
                Ok(_) => panic!("case alias selected a scratch host"),
            };
            assert!(error.contains("scratch/reclaim"), "{error}");
        }
    });
}

#[test]
fn seed_tools_profile_selects_only_explicit_tool_trees_and_rejects_compiler_opt_in() {
    isolated(|| {
        let f = Fixture::new();
        let lease = f.lease();
        let tool = f.tree("bootstrap-tools");
        let compiler = f.tree("stage1-rustc");
        let seed = f.put(&format!("{HOST}/stage0/bin/trustc"), b"fixture input bytes, not health");
        let std = f.put(&format!("{HOST}/stage0-sysroot/lib/std"), b"preserved");
        let scratch = f.put("tmp/work", b"preserved");
        f.put(
            &format!("{HOST}/rustc-private-sysroots/rustc-private-tool-old/member"),
            b"preserved",
        );
        assert!(f.request(true, true).with_profile(WholeProfile::SeedTools).is_err());
        let request = f.request(false, false).with_profile(WholeProfile::SeedTools).unwrap();
        let mut prepared = Prepared::new(&request, &f.output).unwrap();
        assert_eq!(prepared.candidates.iter().map(|c| &c.path).collect::<Vec<_>>(), vec![&tool]);
        let mut result = report(&request, &prepared);
        Ownership::native(&f.output, &lease)
            .with_current(&f.root, &f.build, || {
                prepared.apply(&request, &lease, &f.output, &mut result)
            })
            .unwrap()
            .unwrap();
        assert!(!tool.exists());
        for path in [compiler, seed, std, scratch, f.host.join("rustc-private-sysroots")] {
            assert!(path.exists(), "{}", path.display());
        }
    });
}
#[test]
fn configured_output_uses_same_guard_and_changed_config_prevents_detach() {
    isolated(|| {
        let f = Fixture::new();
        let lease = f.lease();
        let nested = f.build.join("component");
        fs::create_dir_all(nested.join(HOST)).unwrap();
        let output = OutputLock::try_acquire(&nested).unwrap().unwrap();
        assert!(OutputLock::try_acquire_existing(&nested).unwrap().is_none());
        fs::write(f.root.join("bootstrap.toml"), "[build]\nbuild-dir='build/component'\n").unwrap();
        let request = WholeRequest::new(&f.root, Path::new(HOST), false, false).unwrap();
        assert!(Prepared::new(&request, &f.output).is_err()); // wrong actual lock
        fs::create_dir_all(nested.join(HOST).join("bootstrap-tools/release/deps")).unwrap();
        fs::write(
            nested.join(HOST).join("bootstrap-tools/release/deps/file"),
            b"obsolete fixture bytes",
        )
        .unwrap();
        let mut prepared = Prepared::new(&request, &output).unwrap();
        let mut result = report(&request, &prepared);
        fs::write(f.root.join("bootstrap.toml"), "[build]\nbuild-dir='build'\n").unwrap();
        assert!(prepared.apply(&request, &lease, &output, &mut result).is_err());
        assert!(nested.join(HOST).join("bootstrap-tools/release/deps/file").is_file());
        assert!(result.removed_trees.is_empty());
    });
}

#[test]
fn changed_config_after_actual_removal_preserves_failure_and_complete_outcomes() {
    isolated(|| {
        let f = Fixture::new();
        let lease = f.lease();
        let tool = f.tree("bootstrap-tools");
        fs::write(f.root.join("bootstrap.toml"), "[build]\nbuild-dir='build'\n").unwrap();
        let request = f.request(false, false);
        let mut prepared = Prepared::new(&request, &f.output).unwrap();
        let mut result = report(&request, &prepared);
        prepared.apply(&request, &lease, &f.output, &mut result).unwrap();
        assert!(!tool.exists());
        assert_eq!(result.removed_trees, vec![tool.clone()]);
        fs::write(f.root.join("bootstrap.toml"), "[build]\nbuild-dir='changed'\n").unwrap();
        super::super::finish_selection(&request.selection, &mut result.failures);
        assert!(!result.is_complete());
        assert_eq!(result.planned_trees, vec![tool.clone()]);
        assert_eq!(result.removed_trees, vec![tool]);
        assert!(result.removed_allocated_bytes > 0);
        assert!(result.failures.iter().any(|error| error.contains("output selection changed")));
    });
}
