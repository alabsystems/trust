// Owned filesystem/cache-DATA controls. These files are not LLVM programs,
// provider readiness, a native execution/OS observation or an SDK certificate.
use super::*;

struct Fixture {
    _directory: tempfile::TempDir,
    llvm: LlvmOutput,
    inputs: ExternalInputs,
    target: TargetSelection,
}
impl Fixture {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path().join("llvm");
        for path in ["bin", "include", "lib/cmake/llvm"] {
            fs::create_dir_all(root.join(path)).unwrap();
        }
        for path in [
            "bin/llvm-config",
            "include/llvm.h",
            "lib/libLLVM.a",
            "lib/cmake/llvm/LLVMConfig.cmake",
            "lib/cmake/llvm/LLVMExports.cmake",
        ] {
            fs::write(root.join(path), b"controlled cache input bytes\n").unwrap();
        }
        let inputs = ExternalInputs { paths: vec![root.join("lib/cmake/llvm")] };
        Self {
            _directory: directory,
            llvm: LlvmOutput {
                llvm_config: root.join("bin/llvm-config"),
                llvm_root_dir: root,
                kind: LlvmKind::External,
                link_shared: false,
            },
            inputs,
            target: TargetSelection::from_user("aarch64-unknown-linux-gnu"),
        }
    }
    fn key(&self) -> Option<String> {
        self.inputs.key_with_context(&self.llvm, self.target, "controlled OS build A")
    }
}

#[test]
fn selected_external_prefix_binds_headers_archives_exports_and_membership() {
    let fixture = Fixture::new();
    let original = fixture.key().expect("complete controlled inputs must admit cache DATA");
    assert_eq!(fixture.key(), Some(original.clone()));
    for name in ["include/llvm.h", "lib/libLLVM.a", "lib/cmake/llvm/LLVMExports.cmake"] {
        let path = fixture.llvm.root_dir().join(name);
        let before = fs::read(&path).unwrap();
        fs::write(&path, b"different input of the same declared provider").unwrap();
        assert_ne!(fixture.key(), Some(original.clone()));
        fs::write(&path, before).unwrap();
        assert_eq!(fixture.key(), Some(original.clone()));
    }
    fs::write(fixture.llvm.root_dir().join("include/added.h"), b"new member").unwrap();
    assert_ne!(fixture.key(), Some(original));
}

#[test]
fn selected_paths_target_mode_and_os_build_are_part_of_external_cache_data() {
    let mut fixture = Fixture::new();
    let original = fixture.key().unwrap();
    assert_ne!(
        fixture.inputs.key_with_context(&fixture.llvm, fixture.target, "OS build B"),
        Some(original.clone())
    );
    fixture.llvm.link_shared = true;
    assert_ne!(fixture.key(), Some(original.clone()));
    fixture.llvm.link_shared = false;
    assert_ne!(
        fixture.inputs.key_with_context(
            &fixture.llvm,
            TargetSelection::from_user("x86_64-unknown-linux-gnu"),
            "controlled OS build A"
        ),
        Some(original.clone())
    );
    fixture.inputs.paths.push(fixture.llvm.root_dir().join("not-declared-present"));
    assert!(fixture.key().is_none());
    fixture.inputs.paths = vec![PathBuf::from("relative-input")];
    assert!(fixture.key().is_none());
}

#[cfg(unix)]
#[test]
fn changed_external_symlink_referent_invalidates_cache_observation() {
    use std::os::unix::fs::symlink;
    let fixture = Fixture::new();
    let referent = fixture._directory.path().join("actual-header");
    fs::write(&referent, b"first actual referent").unwrap();
    symlink(&referent, fixture.llvm.root_dir().join("include/linked.h")).unwrap();
    let original = fixture.key().unwrap();
    fs::write(&referent, b"later actual referent").unwrap();
    assert_ne!(fixture.key(), Some(original));
}

#[cfg(unix)]
#[test]
fn unused_installation_absence_does_not_supply_a_required_program() {
    use std::os::unix::fs::symlink;
    let fixture = Fixture::new();
    let absent = fixture._directory.path().join("absent");
    symlink(&absent, fixture.llvm.root_dir().join("unused-link")).unwrap();
    assert!(fixture.key().is_some(), "unused link absence is installed namespace DATA");
    fs::remove_file(fixture.llvm.llvm_config()).unwrap();
    symlink(&absent, fixture.llvm.llvm_config()).unwrap();
    assert!(fixture.key().is_none(), "required llvm-config is not available");
}
