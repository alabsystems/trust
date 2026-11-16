use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};

use tempfile::TempDir;

use super::RepairCheckout;
use crate::Git;
use crate::tests::TestGit;

struct Fixture {
    _temporary: TempDir,
    control: PathBuf,
    candidate: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let temporary = TempDir::new().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let control = root.join("control");
        let candidate = root.join("candidate");
        fs::create_dir(&control).unwrap();
        TestGit::run(&control, &["init", "-q"]);
        fs::write(control.join("lib.rs"), b"pub fn value() -> u8 { 1 }\n").unwrap();
        fs::write(control.join("other.rs"), b"pub fn other() {}\n").unwrap();
        TestGit::run(&control, &["add", "."]);
        TestGit::run(&control, &["commit", "-qm", "original"]);
        TestGit::run(
            &control,
            &["worktree", "add", "--detach", candidate.to_str().unwrap(), "HEAD"],
        );
        Self { _temporary: temporary, control, candidate }
    }
    fn open(&self) -> RepairCheckout {
        RepairCheckout::open(&TestGit, &self.control, &self.candidate, &["lib.rs".into()]).unwrap()
    }
    fn commit(&self, path: &Path, contents: &[u8]) -> String {
        fs::write(self.candidate.join(path), contents).unwrap();
        TestGit::run(&self.candidate, &["add", "."]);
        TestGit::run(&self.candidate, &["commit", "-qm", "agent proposal"]);
        String::from_utf8(TestGit.probe(&self.candidate, &["rev-parse", "HEAD"]).unwrap())
            .unwrap()
            .trim()
            .into()
    }
}

#[test]
fn actual_clean_single_parent_repair_is_bound_and_later_drift_refuses() {
    let fixture = Fixture::new();
    let checkout = fixture.open();
    let commit = fixture.commit(Path::new("lib.rs"), b"pub fn value() -> u8 { 2 }\n");
    let proposal = checkout.submit(&TestGit, &commit).unwrap_or_else(|e| panic!("{}", e.reason));
    assert_eq!(proposal.source().commit, commit);
    assert_ne!(proposal.source().tree, proposal.baseline().tree);
    assert_eq!(proposal.changed_paths(), &[PathBuf::from("lib.rs")]);
    proposal.check_unchanged(&TestGit).unwrap();
    fs::write(fixture.candidate.join("lib.rs"), b"uncommitted drift").unwrap();
    assert!(proposal.check_unchanged(&TestGit).is_err());
}

#[test]
fn agent_commit_name_cannot_authorize_different_or_unselected_source() {
    for wrong_name in [true, false] {
        let fixture = Fixture::new();
        let checkout = fixture.open();
        let commit =
            fixture.commit(Path::new(if wrong_name { "lib.rs" } else { "other.rs" }), b"changed\n");
        let supplied_commit = if wrong_name { "a".repeat(40) } else { commit };
        let rejected =
            checkout.submit(&TestGit, &supplied_commit).err().expect("proposal must refuse");
        assert!(rejected.checkout.baseline().path.is_dir());
        assert!(rejected.checkout.candidate_root().is_dir());
        assert_eq!(
            fs::read(fixture.control.join("lib.rs")).unwrap(),
            b"pub fn value() -> u8 { 1 }\n"
        );
    }
}

#[test]
fn extra_history_and_removed_or_symlinked_files_refuse() {
    for case in 0..3 {
        let fixture = Fixture::new();
        let checkout = fixture.open();
        let mut commit = fixture.commit(Path::new("lib.rs"), b"changed\n");
        match case {
            0 => commit = fixture.commit(Path::new("lib.rs"), b"second commit\n"),
            1 => {
                TestGit::run(&fixture.candidate, &["rm", "-q", "lib.rs"]);
                TestGit::run(&fixture.candidate, &["commit", "--amend", "--no-edit", "-q"]);
            }
            _ => {
                fs::remove_file(fixture.candidate.join("lib.rs")).unwrap();
                symlink("other.rs", fixture.candidate.join("lib.rs")).unwrap();
                TestGit::run(&fixture.candidate, &["add", "."]);
                TestGit::run(&fixture.candidate, &["commit", "--amend", "--no-edit", "-q"]);
            }
        }
        if case != 0 {
            commit = String::from_utf8(
                TestGit.probe(&fixture.candidate, &["rev-parse", "HEAD"]).unwrap(),
            )
            .unwrap()
            .trim()
            .into();
        }
        assert!(checkout.submit(&TestGit, &commit).is_err());
    }
}

#[test]
fn changed_control_or_replaced_candidate_directory_never_becomes_a_proposal() {
    for replace in [false, true] {
        let fixture = Fixture::new();
        let checkout = fixture.open();
        let commit = fixture.commit(Path::new("lib.rs"), b"changed\n");
        if replace {
            fs::rename(&fixture.candidate, fixture.candidate.with_extension("original")).unwrap();
            fs::create_dir(&fixture.candidate).unwrap();
        } else {
            fs::write(fixture.control.join("lib.rs"), b"control drift\n").unwrap();
        }
        assert!(checkout.submit(&TestGit, &commit).is_err());
    }
}

#[test]
fn selection_and_initial_input_aliases_are_closed_before_repair() {
    let fixture = Fixture::new();
    for selected in
        [vec![], vec![PathBuf::from("../lib.rs")], vec!["lib.rs".into(), "lib.rs".into()]]
    {
        assert!(
            RepairCheckout::open(&TestGit, &fixture.control, &fixture.candidate, &selected)
                .is_err()
        );
    }
    assert!(
        RepairCheckout::open(&TestGit, &fixture.control, &fixture.control, &["lib.rs".into()])
            .is_err()
    );
    fixture.commit(Path::new("lib.rs"), b"already changed\n");
    assert!(
        RepairCheckout::open(&TestGit, &fixture.control, &fixture.candidate, &["lib.rs".into()])
            .is_err()
    );
}

#[test]
fn measured_selection_and_same_checkout_are_consumed_through_actual_source_inspection() {
    let fixture = Fixture::new();
    let checkout = fixture.open();
    let mut measurements = super::Measurements::new(&["native read".into()]).unwrap();
    let work = measurements.start("native read").unwrap();
    assert!(!fs::read(fixture.control.join("lib.rs")).unwrap().is_empty());
    work.finish(true);
    let waiting = super::AwaitingRepair::new(measurements.select().unwrap(), checkout);
    assert_eq!(waiting.bottleneck().name(), "native read");
    assert_eq!(waiting.checkout().candidate_root(), fixture.candidate);
    let commit = fixture.commit(Path::new("lib.rs"), b"pub fn value() -> u8 { 2 }\n");
    let measured = waiting
        .observe_proposed_commit(&TestGit, &commit)
        .unwrap_or_else(|(_, rejection)| panic!("{}", rejection.reason));
    assert_eq!(measured.bottleneck().name(), "native read");
    assert_eq!(measured.proposal().source().commit, commit);
    measured.proposal().check_unchanged(&TestGit).unwrap();
}
