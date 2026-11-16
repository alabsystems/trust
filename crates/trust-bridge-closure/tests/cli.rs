use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "trust-bridge-closure-{}-{}",
            std::process::id(),
            NEXT_DIR.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn run(args: &[&std::ffi::OsStr]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_bridge_closure")).args(args).output().unwrap()
}

#[test]
fn roots_are_the_shared_replay_roots() {
    let output = run(&["--roots".as_ref()]);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let expected = trust_bridge_closure::BRIDGE_ROOT_MODULES.join("\n") + "\n";
    assert_eq!(output.stdout, expected.as_bytes());
}

#[test]
fn incomplete_arguments_and_extra_root_arguments_refuse() {
    for args in [
        vec![],
        vec!["only-one-path".as_ref()],
        vec!["--roots".as_ref(), "extra".as_ref()],
        vec!["--admit-lean-toolchain".as_ref()],
        vec!["--admit-lean-toolchain".as_ref(), "snapshot".as_ref()],
        vec!["--admit-lean-toolchain".as_ref(), "snapshot".as_ref(), "bin".as_ref()],
        vec![
            "--admit-lean-toolchain".as_ref(),
            "snapshot".as_ref(),
            "bin".as_ref(),
            "report".as_ref(),
            "extra".as_ref(),
        ],
        vec!["one".as_ref(), "two".as_ref(), "extra".as_ref()],
        vec!["--snapshot-lean".as_ref()],
        vec!["--snapshot-lean".as_ref(), "repo".as_ref(), "commit".as_ref()],
        vec![
            "--snapshot-lean".as_ref(),
            "repo".as_ref(),
            "commit".as_ref(),
            "dest".as_ref(),
            "extra".as_ref(),
        ],
    ] {
        let output = run(&args);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).starts_with("usage: bridge_closure"));
    }
}

#[test]
fn missing_root_refuses_instead_of_printing_a_partial_closure() {
    let scratch = Scratch::new();
    let output = run(&[scratch.0.as_os_str(), scratch.0.as_os_str()]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("ModuleNotFound"));
}

#[test]
fn corrupt_root_refuses_instead_of_printing_a_partial_closure() {
    let scratch = Scratch::new();
    let root = scratch.0.join("TrustIr/Semantics/Compare.olean");
    std::fs::create_dir_all(root.parent().unwrap()).unwrap();
    std::fs::write(root, b"invalid olean header").unwrap();
    let output = run(&[scratch.0.as_os_str(), scratch.0.as_os_str()]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).starts_with("bridge_closure: import failed:"));
    assert!(!String::from_utf8_lossy(&output.stderr).contains("ModuleNotFound"));
}
