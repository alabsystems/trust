use super::*;
use git2::{IndexAddOption, Signature};
use std::fs;
use std::time::Duration;

// DescriptorBudget observations are process-wide. Keep all fixture owners
// serialized so another test cannot refund capacity between accounting bookends.
static REPOSITORY_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

struct Fixture {
    root: PathBuf,
    baseline: Repository,
    candidate: Repository,
    budget: Arc<DescriptorBudget>,
}
impl Fixture {
    fn new(extra: bool) -> Self {
        // Retain every real input, including a panic/failure. No test Drop
        // erases a world that a later independent verifier may need.
        let root = tempfile::tempdir().unwrap().keep().canonicalize().unwrap();
        eprintln!("native repository source fixture={}", root.display());
        let baseline = Repository::init(root.join("baseline")).unwrap();
        let source = baseline.workdir().unwrap().join("package");
        fs::create_dir_all(source.join("src")).unwrap();
        fs::write(
            source.join("Cargo.toml"),
            b"[package]\nname='native-source-fixture'\nversion='0.1.0'\n",
        )
        .unwrap();
        fs::write(source.join("src/lib.rs"), b"pub fn value()->u32 {41}\n").unwrap();
        fs::write(
            baseline.workdir().unwrap().join("README"),
            b"retained unrelated input\n",
        )
        .unwrap();
        fs::write(
            baseline.workdir().unwrap().join(".gitignore"),
            b"unknown/\n",
        )
        .unwrap();
        commit(&baseline);
        baseline
            .worktree("candidate", &root.join("candidate"), None)
            .unwrap();
        let candidate = Repository::open(root.join("candidate")).unwrap();
        fs::write(
            candidate.workdir().unwrap().join("package/src/lib.rs"),
            b"pub fn value()->u32 {42}\n",
        )
        .unwrap();
        if extra {
            fs::write(
                candidate.workdir().unwrap().join("README"),
                b"not selected or validated\n",
            )
            .unwrap();
        }
        commit(&candidate);
        let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
        Self {
            root,
            baseline,
            candidate,
            budget,
        }
    }
    fn original(&self, repo: &Repository, deadline: Instant) -> Arc<AdmittedPackageSource> {
        self.budget
            .capture_source(&repo.workdir().unwrap().join("package"), deadline)
            .unwrap()
    }
    fn owner(&self, repo: &Repository, deadline: Instant) -> RepositorySource {
        RepositorySource::capture(self.original(repo, deadline), self.budget.clone(), deadline)
            .unwrap()
    }
}
fn commit(repo: &Repository) -> Oid {
    let mut index = repo.index().unwrap();
    index.add_all(["."], IndexAddOption::DEFAULT, None).unwrap();
    index.write().unwrap();
    let tree = repo.find_tree(index.write_tree().unwrap()).unwrap();
    let signature = Signature::now("native fixture", "native-fixture@invalid").unwrap();
    let parent = repo.head().ok().and_then(|head| head.peel_to_commit().ok());
    repo.commit(
        Some("HEAD"),
        &signature,
        &signature,
        "native source fixture",
        &tree,
        &parent.as_ref().into_iter().collect::<Vec<_>>(),
    )
    .unwrap()
}
fn new_deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn linked_commits_bind_same_original_source_and_refund_only_after_final_owner_drop() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let old = f.original(&f.baseline, deadline);
    let new = f.original(&f.candidate, deadline);
    let before = f.budget.observation().unwrap();
    {
        let old_owner = RepositorySource::capture(old.clone(), f.budget.clone(), deadline).unwrap();
        let new_owner = RepositorySource::capture(new.clone(), f.budget.clone(), deadline).unwrap();
        assert!(Arc::ptr_eq(new_owner.source(), &new));
        assert_eq!(
            new_owner
                .require_candidate_of(&old_owner, deadline)
                .unwrap(),
            vec![PathBuf::from("package/src/lib.rs")]
        );
        new_owner.validate(deadline).unwrap();
        old_owner.validate(deadline).unwrap();
        let live = f.budget.observation().unwrap();
        assert!(live.pending > before.pending);
        assert!(live.held_directories > before.held_directories);
    }
    let after = f.budget.observation().unwrap();
    assert_eq!(after.pending, before.pending);
    assert_eq!(after.held_directories, before.held_directories);
    eprintln!(
        "native-repository-originals-and-final-close-ok {}",
        f.root.display()
    );
}
#[test]
fn full_commit_delta_cannot_hide_a_sibling_change() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(true);
    let deadline = new_deadline();
    let old = f.owner(&f.baseline, deadline);
    let new = f.owner(&f.candidate, deadline);
    let error = new.require_candidate_of(&old, deadline).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("outside validated package scope"),
        "{error}"
    );
    assert!(new.validate(deadline).is_err());
}
#[test]
fn dirty_and_ignored_unknown_scope_are_refused_even_when_selected_package_matches() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    for relative in ["untracked", "unknown/ignored"] {
        let f = Fixture::new(false);
        let deadline = new_deadline();
        let path = f.candidate.workdir().unwrap().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, b"unowned\n").unwrap();
        let source = f.original(&f.candidate, deadline);
        assert!(RepositorySource::capture(source, f.budget.clone(), deadline).is_err());
    }
}
#[test]
fn changed_head_and_new_negative_control_stay_terminal_after_restore() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let old = f.baseline.head().unwrap().target().unwrap();
    f.candidate.set_head_detached(old).unwrap();
    assert!(owner.validate(deadline).is_err());
    f.candidate.set_head("refs/heads/candidate").unwrap();
    assert!(owner.validate(deadline).is_err());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let shallow = f.candidate.commondir().join("shallow");
    fs::write(&shallow, b"unknown\n").unwrap();
    assert!(owner.validate(deadline).is_err());
    fs::remove_file(shallow).unwrap();
    assert!(owner.validate(deadline).is_err());
}
#[test]
fn original_control_directory_parent_aba_cannot_be_restored_into_validity() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let path = f.candidate.path().to_path_buf();
    let saved = path.with_extension("retained-original");
    fs::rename(&path, &saved).unwrap();
    fs::create_dir(&path).unwrap();
    assert!(owner.validate(deadline).is_err());
    fs::remove_dir(&path).unwrap();
    fs::rename(&saved, &path).unwrap();
    assert!(owner.validate(deadline).is_err());
}
#[test]
fn empty_directory_and_git_control_symlink_do_not_become_committed_source() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    fs::create_dir(f.candidate.workdir().unwrap().join("package/empty")).unwrap();
    let source = f.original(&f.candidate, deadline);
    assert!(RepositorySource::capture(source, f.budget.clone(), deadline).is_err());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let source = f.original(&f.candidate, deadline);
    let marker = f.candidate.workdir().unwrap().join(".git");
    let original = marker.with_extension("original");
    fs::rename(&marker, &original).unwrap();
    std::os::unix::fs::symlink(&original, &marker).unwrap();
    assert!(RepositorySource::capture(source, f.budget.clone(), deadline).is_err());
}
#[test]
fn source_mutation_and_pack_population_change_preserve_the_original_failed_owner() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let path = f.candidate.workdir().unwrap().join("package/src/lib.rs");
    let original = fs::read(&path).unwrap();
    fs::write(&path, b"pub fn value()->u32 {43}\n").unwrap();
    assert!(owner.validate(deadline).is_err());
    fs::write(path, original).unwrap();
    assert!(owner.validate(deadline).is_err());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let added = f.candidate.commondir().join("objects/pack/unowned.keep");
    fs::write(&added, b"unknown\n").unwrap();
    assert!(owner.validate(deadline).is_err());
    fs::remove_file(added).unwrap();
    assert!(owner.validate(deadline).is_err());
}

#[test]
fn fork_rejects_original_process_before_an_inherited_repository_mutex() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let _charge = f.budget.reserve_original_inputs(2).unwrap();
    let mut pipe = [-1; 2];
    assert_eq!(unsafe { libc::pipe(pipe.as_mut_ptr()) }, 0);
    let held = owner.inner.state.lock().unwrap();
    let pid = unsafe { libc::fork() };
    assert!(pid >= 0);
    if pid == 0 {
        unsafe {
            libc::close(pipe[0]);
        }
        // This must stop at the native original-process guard, before any
        // allocator, inherited mutex, Git library or source namespace access.
        let refused = owner
            .validate(deadline)
            .err()
            .is_some_and(|error| error.raw_os_error() == Some(libc::EPERM));
        let marker = if refused { b'R' } else { b'F' };
        unsafe {
            libc::write(pipe[1], (&marker as *const u8).cast(), 1);
            libc::_exit(if refused { 0 } else { 3 });
        }
    }
    unsafe {
        libc::close(pipe[1]);
    }
    let mut interest = libc::pollfd {
        fd: pipe[0],
        events: libc::POLLIN | libc::POLLHUP,
        revents: 0,
    };
    let observed = unsafe { libc::poll(&mut interest, 1, 2000) };
    let mut marker = 0u8;
    let read = if observed > 0 {
        unsafe { libc::read(pipe[0], (&mut marker as *mut u8).cast(), 1) }
    } else {
        0
    };
    // The actual fork return owns this unreaped child; it cannot be a reused
    // PID. Kill on missing progress, then reap before asserting or unwinding.
    if observed <= 0 {
        unsafe {
            libc::kill(pid, libc::SIGKILL);
        }
    }
    let mut status = 0;
    let waited = unsafe { libc::waitpid(pid, &mut status, 0) };
    unsafe {
        libc::close(pipe[0]);
    }
    drop(held);
    assert_eq!(waited, pid, "own fork child was not reaped");
    assert!(
        observed > 0,
        "child blocked before the original-process refusal; retained {}",
        f.root.display()
    );
    assert_eq!((read, marker), (1, b'R'));
    assert!(libc::WIFEXITED(status));
    assert_eq!(libc::WEXITSTATUS(status), 0);
    owner.validate(deadline).unwrap();
}

#[test]
fn actual_packed_object_backings_are_retained_and_tamper_cannot_be_restored() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let before = f.baseline.head().unwrap().target().unwrap();
    let after = f.candidate.head().unwrap().target().unwrap();
    let directory = f.candidate.commondir().join("objects/pack");
    {
        let mut pack = f.candidate.packbuilder().unwrap();
        assert_eq!(pack.set_threads(1), 1);
        pack.insert_commit(before).unwrap();
        pack.insert_commit(after).unwrap();
        // An owner-writable fixture lets the real later corruption execute;
        // the production owner still opens it read-only and detects mutation.
        pack.write(&directory, 0o644).unwrap();
    }
    // Only this new fixture's own loose objects are retired, before creating
    // any source/repository owner. The real pack/index must serve both commits.
    for entry in fs::read_dir(f.candidate.commondir().join("objects")).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        let bytes = name.as_bytes();
        if bytes.len() == 2
            && bytes.iter().all(u8::is_ascii_hexdigit)
            && entry.file_type().unwrap().is_dir()
        {
            for object in fs::read_dir(entry.path()).unwrap() {
                let object = object.unwrap();
                assert!(object.file_type().unwrap().is_file());
                assert_eq!(object.file_name().as_bytes().len(), 38);
                fs::remove_file(object.path()).unwrap();
            }
            fs::remove_dir(entry.path()).unwrap();
        }
    }
    let old = f.owner(&f.baseline, deadline);
    let new = f.owner(&f.candidate, deadline);
    assert_eq!(
        new.require_candidate_of(&old, deadline).unwrap(),
        vec![PathBuf::from("package/src/lib.rs")]
    );
    let pack = fs::read_dir(&directory)
        .unwrap()
        .map(Result::unwrap)
        .map(|entry| entry.path())
        .find(|path| {
            path.extension()
                .is_some_and(|extension| extension == "pack")
        })
        .unwrap();
    let original = fs::read(&pack).unwrap();
    let mut damaged = original.clone();
    damaged[0] ^= 1;
    fs::write(&pack, &damaged).unwrap();
    assert!(new.validate(deadline).is_err());
    fs::write(&pack, original).unwrap();
    assert!(new.validate(deadline).is_err());
    eprintln!("native-repository-packed-originals-ok {}", f.root.display());
}

#[test]
fn writable_control_inputs_are_refused_before_native_git_status_reads() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    use std::os::unix::fs::PermissionsExt;
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let source = f.original(&f.candidate, deadline);
    fs::set_permissions(
        f.candidate.path().join("index"),
        fs::Permissions::from_mode(0o666),
    )
    .unwrap();
    assert!(RepositorySource::capture(source, f.budget.clone(), deadline).is_err());
}

#[test]
fn linked_worktree_backpointer_is_an_original_control_and_restore_stays_terminal() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new(false);
    let deadline = new_deadline();
    let owner = f.owner(&f.candidate, deadline);
    let pointer = f.candidate.path().join("gitdir");
    let original = fs::read(&pointer).unwrap();
    fs::write(&pointer, b"/not-the-original-worktree/.git\n").unwrap();
    assert!(
        owner.validate(deadline).is_err(),
        "mutated native worktree control was accepted; retain {}",
        f.root.display()
    );
    fs::write(pointer, original).unwrap();
    assert!(
        owner.validate(deadline).is_err(),
        "restored failed control lost its sticky refusal"
    );
}

struct MultiFixture {
    fixture: Fixture,
}
impl MultiFixture {
    fn new() -> Self {
        let root = tempfile::tempdir().unwrap().keep().canonicalize().unwrap();
        eprintln!("native repository package-set fixture={}", root.display());
        let baseline = Repository::init(root.join("baseline")).unwrap();
        for (name, value) in [("alpha", 41), ("beta", 8), ("stable", 3)] {
            let package = baseline.workdir().unwrap().join(name);
            fs::create_dir_all(package.join("src")).unwrap();
            fs::write(
                package.join("Cargo.toml"),
                format!("[package]\nname='{name}'\nversion='0.1.0'\n"),
            )
            .unwrap();
            fs::write(
                package.join("src/lib.rs"),
                format!("pub fn value()->u32 {{{value}}}\n"),
            )
            .unwrap();
        }
        commit(&baseline);
        baseline
            .worktree("candidate", &root.join("candidate"), None)
            .unwrap();
        let candidate = Repository::open(root.join("candidate")).unwrap();
        for (name, value) in [("alpha", 42), ("beta", 9)] {
            fs::write(
                candidate.workdir().unwrap().join(name).join("src/lib.rs"),
                format!("pub fn value()->u32 {{{value}}}\n"),
            )
            .unwrap();
        }
        commit(&candidate);
        Self {
            fixture: Fixture {
                root,
                baseline,
                candidate,
                budget: DescriptorBudget::for_preparation(2, 0).unwrap(),
            },
        }
    }
    fn sources(
        &self,
        repo: &Repository,
        names: &[&str],
        deadline: Instant,
    ) -> Vec<Arc<AdmittedPackageSource>> {
        names
            .iter()
            .map(|name| {
                self.fixture
                    .budget
                    .capture_source(&repo.workdir().unwrap().join(name), deadline)
                    .unwrap()
            })
            .collect()
    }
    fn owner(&self, repo: &Repository, names: &[&str], deadline: Instant) -> RepositorySources {
        RepositorySources::capture(
            self.sources(repo, names, deadline),
            self.fixture.budget.clone(),
            deadline,
        )
        .unwrap()
    }
}

#[test]
fn actual_multi_package_commit_reports_every_affected_original_independent_of_order() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let m = MultiFixture::new();
    let f = &m.fixture;
    let deadline = new_deadline();
    let old_sources = m.sources(&f.baseline, &["alpha", "beta", "stable"], deadline);
    let new_sources = m.sources(&f.candidate, &["stable", "beta", "alpha"], deadline);
    let before = f.budget.observation().unwrap();
    {
        let old =
            RepositorySources::capture(old_sources.clone(), f.budget.clone(), deadline).unwrap();
        let new =
            RepositorySources::capture(new_sources.clone(), f.budget.clone(), deadline).unwrap();
        assert!(
            old_sources
                .iter()
                .zip(old.sources())
                .all(|(a, b)| Arc::ptr_eq(a, b))
        );
        assert!(
            new_sources
                .iter()
                .zip(new.sources())
                .all(|(a, b)| Arc::ptr_eq(a, b))
        );
        let delta = new.require_candidate_of(&old, deadline).unwrap();
        assert_eq!(
            delta.paths,
            [
                PathBuf::from("alpha/src/lib.rs"),
                PathBuf::from("beta/src/lib.rs")
            ]
        );
        assert_eq!(delta.affected.len(), 2);
        assert_eq!(
            (delta.affected[0].baseline, delta.affected[0].candidate),
            (0, 2)
        );
        assert_eq!(delta.affected[0].paths, [PathBuf::from("alpha/src/lib.rs")]);
        assert_eq!(
            (delta.affected[1].baseline, delta.affected[1].candidate),
            (1, 1)
        );
        assert_eq!(delta.affected[1].paths, [PathBuf::from("beta/src/lib.rs")]);
        old.validate(deadline).unwrap();
        new.validate(deadline).unwrap();
        assert!(f.budget.observation().unwrap().pending > before.pending);
    }
    let after = f.budget.observation().unwrap();
    assert_eq!(after.pending, before.pending);
    assert_eq!(after.held_directories, before.held_directories);
}

#[test]
fn changed_package_cannot_be_omitted_on_both_sides_or_only_one_side() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    for candidate_names in [&["alpha"][..], &["alpha", "beta"][..]] {
        let m = MultiFixture::new();
        let f = &m.fixture;
        let deadline = new_deadline();
        let old = m.owner(&f.baseline, &["alpha"], deadline);
        let new = m.owner(&f.candidate, candidate_names, deadline);
        assert!(new.require_candidate_of(&old, deadline).is_err());
        assert!(new.validate(deadline).is_err());
        old.validate(deadline).unwrap();
    }
}

#[test]
fn actual_duplicate_overlapping_empty_or_foreign_package_populations_are_refused() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let m = MultiFixture::new();
    let f = &m.fixture;
    let deadline = new_deadline();
    let alpha = m.sources(&f.candidate, &["alpha"], deadline).remove(0);
    let child = f
        .budget
        .capture_source(&f.candidate.workdir().unwrap().join("alpha/src"), deadline)
        .unwrap();
    for sources in [
        vec![],
        vec![alpha.clone(), alpha.clone()],
        vec![alpha.clone(), child],
    ] {
        assert!(RepositorySources::capture(sources, f.budget.clone(), deadline).is_err());
    }
    let foreign = m.sources(&f.baseline, &["beta"], deadline).remove(0);
    assert!(RepositorySources::capture(vec![alpha, foreign], f.budget.clone(), deadline).is_err());
}

#[test]
fn mutation_of_any_retained_package_is_terminal_even_for_an_unchanged_owner() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let m = MultiFixture::new();
    let f = &m.fixture;
    let deadline = new_deadline();
    let old = m.owner(&f.baseline, &["alpha", "beta", "stable"], deadline);
    let new = m.owner(&f.candidate, &["alpha", "beta", "stable"], deadline);
    new.require_candidate_of(&old, deadline).unwrap();
    let stable = f.candidate.workdir().unwrap().join("stable/src/lib.rs");
    let bytes = fs::read(&stable).unwrap();
    fs::write(&stable, b"pub fn value()->u32 {99}\n").unwrap();
    assert!(new.validate(deadline).is_err());
    fs::write(stable, bytes).unwrap();
    assert!(new.validate(deadline).is_err());
    old.validate(deadline).unwrap();
}

#[test]
fn equal_package_names_in_an_independent_repository_cannot_replace_common_objects() {
    let _serial = REPOSITORY_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let a = MultiFixture::new();
    let b = MultiFixture::new();
    let deadline = new_deadline();
    let old = a.owner(&a.fixture.baseline, &["alpha", "beta"], deadline);
    let new = b.owner(&b.fixture.candidate, &["alpha", "beta"], deadline);
    assert!(new.require_candidate_of(&old, deadline).is_err());
    assert!(new.validate(deadline).is_err());
}
