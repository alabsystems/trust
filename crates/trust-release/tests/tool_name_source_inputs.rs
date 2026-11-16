//! Current-source qualification of the guide's production tool-name reader.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use trust_release::{GateStatus, check_tool_names_files, default_tool_name_evidence_paths};

const GUIDE: &str = "docs/USING_TRUST.md";

struct World(PathBuf);

impl World {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "trust-tool-name-inputs-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("fresh test world; never reuse an existing path");
        fs::create_dir(path.join("docs")).unwrap();
        Self(path)
    }
}

impl Drop for World {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn source_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap()
}

#[test]
fn current_source_guide_passes_tool_name_reader() {
    let guide = source_root().join(GUIDE);
    let metadata = fs::symlink_metadata(&guide).expect("actual current-source guide must exist");
    assert!(metadata.is_file() && !metadata.file_type().is_symlink());
    let inputs = default_tool_name_evidence_paths(source_root());
    assert!(inputs.contains(&guide), "production inventory must include the actual guide");
    let report = check_tool_names_files([guide]).expect("read the actual guide");
    assert_eq!(report.status, GateStatus::Pass, "{:#?}", report.findings);
    assert!(report.findings.is_empty());
}

#[test]
fn changed_guide_bytes_reach_the_production_reader() {
    let world = World::new();
    let original = fs::read_to_string(source_root().join(GUIDE)).unwrap();
    let changed = format!("{original}\nrustup run trust cargo build\n");
    let guide = world.0.join(GUIDE);
    fs::write(&guide, &changed).unwrap();
    assert!(default_tool_name_evidence_paths(&world.0).contains(&guide));
    let report = check_tool_names_files([guide.as_path()]).unwrap();
    assert_eq!(report.status, GateStatus::Fail);
    let expected_line = changed.lines().count();
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "rustup-trust-cargo"
                && finding.location.as_ref().is_some_and(|location| {
                    location.line == expected_line && location.path == guide.display().to_string()
                })
        }),
        "the changed bytes must produce their own exact finding: {:#?}",
        report.findings
    );
}

#[test]
fn missing_guide_is_a_read_refusal() {
    let world = World::new();
    let guide = world.0.join(GUIDE);
    assert!(!default_tool_name_evidence_paths(&world.0).contains(&guide));
    assert!(
        check_tool_names_files([guide]).is_err(),
        "missing input must not become empty success"
    );
}

#[test]
fn guide_directory_is_a_read_refusal() {
    let world = World::new();
    let guide = world.0.join(GUIDE);
    fs::create_dir(&guide).unwrap();
    assert!(!default_tool_name_evidence_paths(&world.0).contains(&guide));
    assert!(check_tool_names_files([guide]).is_err());
}
