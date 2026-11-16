//! Explicit real-program qualification. These private fixture roots are not a
//! canonical pool, SDK, Host job or release input.

use std::ffi::{OsStr, OsString};
use std::fs;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Duration;

use trust_build_tree::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};

fn world(evidence: &Path, name: &str) -> PathBuf {
    let temporary = tempfile::Builder::new()
        .prefix(name)
        .tempdir_in(evidence)
        .unwrap();
    let root = fs::canonicalize(temporary.path()).unwrap();
    // Preserve original inputs and namespace records on both panic and success.
    let _ = temporary.keep();
    fs::write(root.join("Cargo.toml"), "not valid Cargo metadata [\n").unwrap();
    fs::create_dir(root.join(".cargo")).unwrap();
    fs::write(
        root.join(".cargo/config.toml"),
        "not valid project configuration [\n",
    )
    .unwrap();
    root
}

struct Public {
    binary: PathBuf,
    evidence: PathBuf,
    sequence: usize,
}
impl Public {
    fn call(&mut self, root: &Path, words: &[OsString], inherited: Option<&str>) -> Output {
        let mut command = Command::new(&self.binary);
        command
            .current_dir(root)
            // The cold source tree has no Bootstrap or helper to construct.
            // Administration must use the native provider embedded in this
            // exact image, independently of project configuration and PATH.
            .env("PATH", self.evidence.join("unavailable-program-search"))
            .args(["trust", "repo", "lock"])
            .args(words);
        // Fresh standalone administrative actors have no producing GNU work.
        // This is not a test of inherited Root/GNU execution or its retirement.
        for key in [
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            "TRUST_REPO",
            "TRUST_BUILD_LOCK_TOKEN",
            "TRUST_BUILD_LOCK_WAIT",
            "TRUST_INCREMENTAL_MAX_GIB",
            "TRUST_INCREMENTAL_MIN_FREE_GIB",
        ] {
            command.env_remove(key);
        }
        if let Some(token) = inherited {
            command.env("TRUST_BUILD_LOCK_TOKEN", token);
        }
        let result = command.output().unwrap();
        let log = self
            .evidence
            .join(format!("native-admin-{:02}.log", self.sequence));
        self.sequence += 1;
        fs::write(&log, format!("{command:?}\n{result:?}\n")).unwrap();
        fs::set_permissions(log, fs::Permissions::from_mode(0o600)).unwrap();
        result
    }

    fn code(&mut self, root: &Path, words: &[OsString], token: Option<&str>, code: i32) -> Output {
        let result = self.call(root, words, token);
        assert_eq!(result.status.code(), Some(code), "{result:?}");
        result
    }
}

fn words(values: &[&OsStr]) -> Vec<OsString> {
    values.iter().map(|value| value.to_os_string()).collect()
}

fn acquire(root: &Path) -> Vec<OsString> {
    words(&[
        OsStr::new("acquire"),
        OsStr::new("--repo-root"),
        root.as_os_str(),
        OsStr::new("--kind"),
        OsStr::new("measurement"),
        OsStr::new("--pid"),
        OsStr::new(&std::process::id().to_string()),
        OsStr::new("--wait"),
        OsStr::new("0"),
        OsStr::new("--purpose"),
        OsStr::new("actual native administrative frontdoor"),
    ])
}

#[test]
#[ignore = "requires actual same-source normal Targo and private evidence directory"]
fn actual_native_provider_protocol_ownership_and_withholding() {
    const NAME: &str =
        "repo_lock::public_tests::actual_native_provider_protocol_ownership_and_withholding";
    if std::env::var_os("TRUST_NATIVE_ADMIN_ACTOR").is_none() {
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", NAME, "--ignored", "--nocapture"])
            .env("TRUST_NATIVE_ADMIN_ACTOR", "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "real administrative actor failed: {output:?}"
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("native-admin-checked"));
        return;
    }
    let binary =
        fs::canonicalize(std::env::var_os("TRUST_NATIVE_TARGO_ADMIN_IMAGE").unwrap()).unwrap();
    let evidence =
        fs::canonicalize(std::env::var_os("TRUST_NATIVE_TARGO_ADMIN_EVIDENCE").unwrap()).unwrap();
    let metadata = evidence.metadata().unwrap();
    assert!(
        metadata.is_dir()
            && metadata.uid() == unsafe { libc::geteuid() }
            && metadata.mode() & 0o022 == 0
    );
    let mut public = Public {
        binary,
        evidence: evidence.clone(),
        sequence: 0,
    };
    let root = world(&evidence, "ordinary-");
    let protocol = public.code(&root, &words(&[OsStr::new("--protocol")]), None, 0);
    assert_eq!(protocol.stdout, b"trust-build-tree-manager-v2\n");
    let help = public.code(&root, &words(&[OsStr::new("--help")]), None, 0);
    assert!(String::from_utf8_lossy(&help.stdout).contains("--pid is required"));
    let status = words(&[
        OsStr::new("status"),
        OsStr::new("--repo-root"),
        root.as_os_str(),
    ]);
    public.code(&root, &status, None, 0);
    let output = public.code(&root, &acquire(&root), None, 0);
    let token = String::from_utf8(output.stdout).unwrap();
    let token = token.trim();
    assert!(!token.is_empty() && !token.contains('\n'));
    let manager = Manager::open(&root).unwrap();
    let before = fs::read(root.join(".trust-build-lock/info")).unwrap();
    let holder = manager.status().unwrap().holder.unwrap();
    assert_eq!(holder.pid, std::process::id());
    assert_eq!(holder.token, token);
    public.code(&root, &status, None, 3);
    public.code(&root, &acquire(&root), None, 3);
    let borrowed = public.code(&root, &acquire(&root), Some(token), 0);
    assert_eq!(String::from_utf8(borrowed.stdout).unwrap().trim(), token);
    assert_eq!(
        fs::read(root.join(".trust-build-lock/info")).unwrap(),
        before
    );
    public.code(
        &root,
        &words(&[
            OsStr::new("release"),
            OsStr::new("not-the-owner"),
            OsStr::new("--repo-root"),
            root.as_os_str(),
        ]),
        None,
        4,
    );
    public.code(
        &root,
        &words(&[
            OsStr::new("release"),
            OsStr::new(token),
            OsStr::new("--repo-root"),
            root.as_os_str(),
        ]),
        None,
        0,
    );
    public.code(&root, &status, None, 0);
    assert!(manager.status().unwrap().is_free());

    let root = world(&evidence, "withheld-");
    let manager = Manager::open(&root).unwrap();
    let owned = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual opaque withholding input".into(),
            contract: "no legacy release or Host closure".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(owned) => owned,
        LeaseAcquisition::Busy(_) => panic!("private original unexpectedly busy"),
    };
    let token = manager.status().unwrap().holder.unwrap().token;
    let withheld = owned.into_withheld().unwrap();
    withheld.check_current().unwrap();
    let before = fs::read(root.join(".trust-build-lock/info")).unwrap();
    public.code(&root, &acquire(&root), Some(&token), 3);
    public.code(
        &root,
        &words(&[
            OsStr::new("release"),
            OsStr::new(&token),
            OsStr::new("--repo-root"),
            root.as_os_str(),
        ]),
        None,
        4,
    );
    public.code(
        &root,
        &words(&[
            OsStr::new("break"),
            OsStr::new("--reason"),
            OsStr::new("data is not closure"),
            OsStr::new("--repo-root"),
            root.as_os_str(),
        ]),
        None,
        2,
    );
    assert_eq!(
        fs::read(root.join(".trust-build-lock/info")).unwrap(),
        before
    );
    withheld.check_current().unwrap();
    drop(withheld);
    assert!(manager.status().unwrap().holder.unwrap().is_withheld());
    public.code(
        &root,
        &words(&[
            OsStr::new("release"),
            OsStr::new(&token),
            OsStr::new("--repo-root"),
            root.as_os_str(),
        ]),
        None,
        4,
    );
    println!("native-admin-checked");
}
