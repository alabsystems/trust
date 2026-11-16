//! A real thin Mach-O input for runtime-closure inspection tests.
//!
//! The bootstrap test executable can live below a writable temporary ancestor
//! and carry LC_RPATH. Neither is an admissible release-candidate baseline.
//! Copy an actual system executable slice; do not manufacture load commands or
//! change the validator. This fixture is inspected, never executed as trustd.

use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};

use trust_binary_parse::MachO;

pub(crate) struct RuntimeClosureFixture {
    root: tempfile::TempDir,
    candidate: PathBuf,
}

impl RuntimeClosureFixture {
    pub(crate) fn new() -> Self {
        let source = Path::new("/usr/bin/iconv");
        super::validate_root_owned_inspector_chain(source)
            .expect("system iconv must have an immutable root-owned source chain");
        let bytes = std::fs::read(source).expect("read real system iconv image");
        // These tests inspect load commands without executing the candidate.
        // AArch64 preference is therefore valid even for an x86-64 test runner.
        let image = MachO::parse_prefer_aarch64(&bytes).expect("select real iconv image slice");
        assert!(!MachO::is_fat(image.data()), "fixture must be an actual thin image");

        // HOME only locates test storage; the unchanged production authority
        // validator below checks every component. Never fall back to /tmp or
        // chmod a pre-existing ancestor to make this positive pass.
        let home = std::env::var_os("HOME").expect("owner-private HOME for candidate fixture");
        let home = std::fs::canonicalize(home).expect("canonical fixture HOME");
        let root = tempfile::Builder::new()
            .prefix(".trustd-runtime-closure-test-")
            .tempdir_in(home)
            .expect("create owner-private candidate fixture");
        std::fs::set_permissions(root.path(), std::fs::Permissions::from_mode(0o700))
            .expect("harden newly created fixture root");
        let candidate = root.path().join("trustd-inspection-fixture");
        std::fs::write(&candidate, image.data()).expect("copy actual thin iconv slice");
        std::fs::set_permissions(&candidate, std::fs::Permissions::from_mode(0o700))
            .expect("make candidate privately executable");
        super::validate_trustd_candidate_authority(&candidate)
            .expect("fixture must satisfy the unchanged candidate authority validator");
        Self { root, candidate }
    }

    pub(crate) fn candidate(&self) -> &Path {
        &self.candidate
    }

    pub(crate) fn root(&self) -> &Path {
        self.root.path()
    }
}
