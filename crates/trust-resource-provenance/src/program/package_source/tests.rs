// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
use std::fs;
use std::time::Duration;

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}
struct Fixture(Option<tempfile::TempDir>);
impl Drop for Fixture {
    fn drop(&mut self) {
        if std::thread::panicking() {
            let path = self.0.take().unwrap().keep();
            eprintln!("retained original package failure input={}", path.display());
        }
    }
}
fn fixture() -> (Fixture, PathBuf) {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap().join("package");
    fs::create_dir_all(root.join("src/empty")).unwrap();
    fs::write(root.join("Cargo.toml"), b"[package]\nname='original'\n").unwrap();
    fs::write(root.join("src/lib.rs"), b"mod absent;\n").unwrap();
    fs::write(root.join(".hidden"), b"").unwrap();
    (Fixture(Some(temp)), root)
}
#[test]
fn complete_original_package_keeps_hidden_empty_and_positional_bytes() {
    let (_temp, root) = fixture();
    let original =
        PackageSourcePlan::capture(&root, deadline()).unwrap().materialize(deadline()).unwrap();
    assert_eq!(original.entries().len(), 6);
    assert!(original.entries().iter().any(|e| e.path == Path::new("src/empty") && e.directory));
    assert_eq!(original.read(Path::new("src/lib.rs"), deadline()).unwrap(), b"mod absent;\n");
    assert_eq!(original.read(Path::new(".hidden"), deadline()).unwrap(), b"");
    // An unrelated sibling is outside this selected namespace.
    fs::create_dir(root.parent().unwrap().join("unrelated-output")).unwrap();
    original.validate(deadline()).unwrap();
}
#[test]
fn mutation_replacement_negative_membership_and_parent_replacement_stay_terminal() {
    for mode in 0..5 {
        let (_temp, root) = fixture();
        let original =
            PackageSourcePlan::capture(&root, deadline()).unwrap().materialize(deadline()).unwrap();
        match mode {
            0 => {
                fs::write(root.join("src/lib.rs"), b"different").unwrap();
            }
            1 => {
                fs::rename(root.join("src/lib.rs"), root.parent().unwrap().join("old-file"))
                    .unwrap();
                fs::write(root.join("src/lib.rs"), b"mod absent;\n").unwrap();
            }
            2 => {
                fs::write(root.join("src/absent.rs"), b"new negative-lookup candidate").unwrap();
            }
            3 => {
                fs::create_dir(root.join("new-empty")).unwrap();
            }
            4 => {
                fs::rename(root.join("src"), root.join("old-src")).unwrap();
                fs::create_dir(root.join("src")).unwrap();
            }
            _ => unreachable!(),
        }
        assert!(original.validate(deadline()).is_err(), "changed original mode={mode}");
        // Restored bytes/membership cannot clear any observed failure.
        if mode == 0 {
            fs::write(root.join("src/lib.rs"), b"mod absent;\n").unwrap();
        }
        if mode == 2 {
            fs::remove_file(root.join("src/absent.rs")).unwrap();
        }
        if mode == 3 {
            fs::remove_dir(root.join("new-empty")).unwrap();
        }
        assert!(original.validate(deadline()).is_err());
        assert!(original.read(Path::new("Cargo.toml"), deadline()).is_err());
    }
}
#[test]
fn planning_and_late_failure_cannot_recapture_or_resurrect_originals() {
    let (_temp, root) = fixture();
    let plan = PackageSourcePlan::capture(&root, deadline()).unwrap();
    fs::write(root.join("src/lib.rs"), b"new input").unwrap();
    assert!(plan.descriptor_demand(deadline()).is_err());
    fs::write(root.join("src/lib.rs"), b"mod absent;\n").unwrap();
    assert!(plan.materialize(deadline()).is_err());
    let original =
        PackageSourcePlan::capture(&root, deadline()).unwrap().materialize(deadline()).unwrap();
    assert!(original.validate(Instant::now()).is_err());
    assert!(original.validate(deadline()).is_err());
}
#[test]
fn complete_source_never_follows_links_or_special_files_or_hides_depth() {
    let (_temp, root) = fixture();
    std::os::unix::fs::symlink("src/lib.rs", root.join("alias")).unwrap();
    assert!(PackageSourcePlan::capture(&root, deadline()).is_err());
    fs::remove_file(root.join("alias")).unwrap();
    let fifo = CString::new(root.join("pipe").as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
    assert!(PackageSourcePlan::capture(&root, deadline()).is_err());
    fs::remove_file(root.join("pipe")).unwrap();
    let mut path = root.clone();
    for _ in 0..65 {
        path.push("d");
        fs::create_dir(&path).unwrap();
    }
    assert!(PackageSourcePlan::capture(&root, deadline()).is_err());
}

#[test]
fn original_outer_parent_and_selected_root_cannot_be_replaced_and_restored() {
    let (temp, root) = fixture();
    let original =
        PackageSourcePlan::capture(&root, deadline()).unwrap().materialize(deadline()).unwrap();
    let parent = root.parent().unwrap();
    let moved = parent.with_extension("original-moved");
    fs::rename(parent, &moved).unwrap();
    fs::create_dir(parent).unwrap();
    fs::create_dir(parent.join("package")).unwrap();
    assert!(original.validate(deadline()).is_err());
    fs::remove_dir_all(parent).unwrap();
    fs::rename(&moved, parent).unwrap();
    assert!(original.validate(deadline()).is_err());
    drop(original);
    drop(temp);
}
#[test]
fn oversized_sparse_source_is_refused_before_materialization() {
    let (_temp, root) = fixture();
    File::create(root.join("too-large")).unwrap().set_len(512 * 1024 * 1024 + 1).unwrap();
    assert!(PackageSourcePlan::capture(&root, deadline()).is_err());
}
