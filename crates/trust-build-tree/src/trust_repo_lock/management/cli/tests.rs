use std::fs;

use super::*;

fn args(words: &[&str]) -> Vec<OsString> {
    words.iter().map(OsString::from).collect()
}
fn environment(root: &Path) -> Environment {
    Environment { root: Some(root.as_os_str().to_owned()), ..Environment::default() }
}
fn acquire(kind: &str) -> Vec<OsString> {
    args(&[
        "acquire",
        "--kind",
        kind,
        "--pid",
        &std::process::id().to_string(),
        "--purpose",
        "native CLI regression",
    ])
}
fn invoke(words: &[OsString], environment: &Environment) -> (u8, String, String) {
    let mut output = Vec::new();
    let mut diagnostics = Vec::new();
    let code = execute(words, environment, &mut output, &mut diagnostics);
    (code, String::from_utf8(output).unwrap(), String::from_utf8(diagnostics).unwrap())
}

#[test]
fn help_and_protocol_do_not_require_a_tree_or_parse_ambient_policy() {
    let environment = Environment {
        root: Some("/nonexistent/native/manager/root".into()),
        wait: Some("not-a-number".into()),
        token: Some("not-authority".into()),
        incremental_max: Some("not-a-number".into()),
        incremental_min_free: Some("not-a-number".into()),
    };
    assert_eq!(
        invoke(&args(&["--protocol"]), &environment),
        (0, format!("{PROTOCOL}\n"), String::new())
    );
    let (code, output, error) = invoke(&args(&["acquire", "--help"]), &environment);
    assert_eq!(code, 0);
    assert!(output.contains("--pid is required"));
    assert!(error.is_empty());
}

#[test]
fn fresh_acquisition_reclaims_only_idle_cache_before_single_token_delivery() {
    let root = tempfile::tempdir().unwrap();
    let idle = root.path().join("crates/target-idle/debug/incremental");
    let busy = root.path().join("crates/target-busy/debug/incremental");
    for cache in [&idle, &busy] {
        fs::create_dir_all(cache).unwrap();
        fs::write(cache.join("state"), b"rebuildable incremental state").unwrap();
    }
    let profile = fs::File::create(busy.parent().unwrap().join(".cargo-lock")).unwrap();
    profile.lock().unwrap();
    let mut environment = environment(root.path());
    environment.incremental_max = Some("0".into());
    environment.incremental_min_free = Some("0".into());
    let (code, output, diagnostic) = invoke(&acquire("build"), &environment);
    assert_eq!(code, 0, "{diagnostic}");
    assert_eq!(output.lines().count(), 1);
    assert!(diagnostic.contains("Reclaimed"), "{diagnostic}");
    assert!(diagnostic.contains("Busy"), "{diagnostic}");
    assert!(!idle.exists());
    assert!(busy.join("state").is_file());
    let manager = Manager::open(root.path()).unwrap();
    let token = output.trim();
    assert_eq!(manager.status().unwrap().holder.unwrap().token, token);

    // A reentrant borrower does not restart maintenance or mint ownership.
    fs::create_dir(&idle).unwrap();
    fs::write(idle.join("next-state"), b"a later compilation owns this").unwrap();
    environment.token = Some(token.into());
    let borrowed = invoke(&acquire("build"), &environment);
    assert_eq!(borrowed, (0, output.clone(), String::new()));
    assert!(idle.join("next-state").is_file());
    assert_eq!(invoke(&args(&["release", token]), &environment).0, 0);
}

#[test]
fn refused_optional_maintenance_preserves_cache_and_actual_tree_ownership() {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("crates/target/debug/incremental");
    fs::create_dir_all(&cache).unwrap();
    fs::write(cache.join("state"), b"retain on unknown policy").unwrap();
    let mut environment = environment(root.path());
    environment.incremental_max = Some("NaN".into());
    let (code, output, diagnostic) = invoke(&acquire("measurement"), &environment);
    assert_eq!(code, 0, "{diagnostic}");
    assert_eq!(output.lines().count(), 1);
    assert!(diagnostic.contains("maintenance refused"));
    assert!(cache.join("state").is_file());
    assert_eq!(invoke(&acquire("build"), &environment).0, 3);
    assert_eq!(invoke(&args(&["release", output.trim()]), &environment).0, 0);
}

#[test]
fn real_cli_measurement_excludes_build_and_exact_token_releases() {
    let root = tempfile::tempdir().unwrap();
    let environment = environment(root.path());
    let (code, output, error) = invoke(&acquire("measurement"), &environment);
    assert_eq!(code, 0, "{error}");
    assert_eq!(output.lines().count(), 1);
    let token = output.trim().to_owned();
    assert!(!token.is_empty());
    let (code, output, error) = invoke(&acquire("build"), &environment);
    assert_eq!(code, 3);
    assert!(output.is_empty());
    assert!(error.contains("measurement"));
    assert!(!error.contains(&token));
    assert_eq!(invoke(&args(&["release", "another-token"]), &environment).0, 4);
    assert_eq!(invoke(&args(&["status"]), &environment).0, 3);
    assert_eq!(invoke(&args(&["release", &token]), &environment).0, 0);
    assert_eq!(
        invoke(&args(&["status"]), &environment),
        (0, "trust build-tree lock: free\n".into(), String::new())
    );
}

#[test]
fn borrowing_original_family_token_never_changes_holder_or_issues_new_token() {
    let root = tempfile::tempdir().unwrap();
    let mut environment = environment(root.path());
    let (_, output, _) = invoke(&acquire("build"), &environment);
    let original = fs::read(root.path().join(".trust-build-lock/info")).unwrap();
    environment.token = Some(output.trim().into());
    assert_eq!(invoke(&acquire("build"), &environment), (0, output.clone(), String::new()));
    assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), original);
    assert_eq!(invoke(&args(&["release", output.trim()]), &environment).0, 0);
}

#[test]
fn transient_or_unbounded_owners_and_duplicate_flags_refuse_before_publication() {
    let root = tempfile::tempdir().unwrap();
    let environment = environment(root.path());
    for words in [
        args(&["acquire", "--kind", "build"]),
        args(&["acquire", "--kind", "build", "--pid", "0"]),
        args(&["acquire", "--kind", "build", "--pid", "1"]),
        args(&["acquire", "--kind", "build", "--pid", "-2"]),
        args(&["acquire", "--kind", "build", "--pid", "4294967295"]),
        args(&["status", "--repo-root", "a", "--repo-root", "b"]),
        args(&["release", "a", "b"]),
        args(&["break"]),
        args(&["break", "--reason", " "]),
    ] {
        let (code, output, _) = invoke(&words, &environment);
        assert_eq!(code, 2, "{words:?}");
        assert!(output.is_empty());
        assert!(!root.path().join(".trust-build-lock").exists());
    }
    assert!(!root.path().join(".trust-build-lock.guard").exists());
}

#[test]
fn explicit_recovery_is_audited_and_native_parent_ownership_stays_retained() {
    let root = tempfile::tempdir().unwrap();
    let environment = environment(root.path());
    let (_, token, _) = invoke(&acquire("build"), &environment);
    let path = root.path().join(".trust-build-lock/info");
    let record = fs::read_to_string(&path).unwrap() + "release_token=\n";
    fs::write(&path, &record).unwrap();
    assert_eq!(invoke(&args(&["release", token.trim()]), &environment).0, 4);
    assert_eq!(fs::read_to_string(&path).unwrap(), record);
    assert_eq!(
        invoke(&args(&["break", "--reason", "owned native CLI recovery control"]), &environment).0,
        0
    );
    assert!(!path.exists());
    assert!(
        fs::read_to_string(root.path().join(".trust-build-lock.breaks"))
            .unwrap()
            .contains("owned native CLI recovery control")
    );
}

#[test]
fn invalid_wait_never_becomes_an_unbounded_wait_or_a_fresh_claim() {
    let root = tempfile::tempdir().unwrap();
    let mut environment = environment(root.path());
    for wait in ["", "-1", "+1", "1.5", "18446744073709551616"] {
        environment.wait = Some(wait.into());
        assert_eq!(invoke(&acquire("build"), &environment).0, 2);
        assert!(!root.path().join(".trust-build-lock").exists());
    }
    environment.wait = Some("-1".into());
    let mut words = acquire("build");
    words.extend(args(&["--wait", "0"]));
    let (code, token, error) = invoke(&words, &environment);
    assert_eq!(code, 0, "{error}");
    assert_eq!(invoke(&args(&["release", token.trim()]), &environment).0, 0);
}

#[test]
fn failed_partial_token_delivery_rolls_back_only_the_new_acquisition() {
    struct Partial {
        bytes: Vec<u8>,
    }
    impl Write for Partial {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if self.bytes.is_empty() {
                let count = bytes.len().min(4);
                self.bytes.extend_from_slice(&bytes[..count]);
                Ok(count)
            } else {
                Err(io::ErrorKind::BrokenPipe.into())
            }
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let root = tempfile::tempdir().unwrap();
    let mut output = Partial { bytes: Vec::new() };
    let mut diagnostics = Vec::new();
    assert_eq!(
        execute(&acquire("build"), &environment(root.path()), &mut output, &mut diagnostics),
        2
    );
    assert_eq!(output.bytes.len(), 4);
    assert!(String::from_utf8(diagnostics).unwrap().contains("token delivery failed"));
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn literal_unicode_root_never_becomes_shell_syntax() {
    let parent = tempfile::tempdir().unwrap();
    let root = parent.path().join("root-ユニコード $(touch NEVER)");
    fs::create_dir(&root).unwrap();
    let mut words = acquire("build");
    words.push("--repo-root".into());
    words.push(root.as_os_str().to_owned());
    let (code, token, error) = invoke(&words, &Environment::default());
    assert_eq!(code, 0, "{error}");
    assert!(!parent.path().join("NEVER").exists());
    let mut release = args(&["release", token.trim(), "--repo-root"]);
    release.push(root.as_os_str().to_owned());
    assert_eq!(invoke(&release, &Environment::default()).0, 0);
}

#[test]
fn non_utf8_root_remains_an_os_path_including_when_the_filesystem_refuses_it() {
    use std::os::unix::ffi::OsStringExt;
    let parent = tempfile::tempdir().unwrap();
    let root = parent.path().join(OsString::from_vec(b"root-\xff".to_vec()));
    let mut words = args(&["status", "--repo-root"]);
    words.push(root.as_os_str().to_owned());
    assert_eq!(parse(&words).unwrap().root.as_deref(), Some(root.as_path()));
    match fs::create_dir(&root) {
        Ok(()) => {
            assert_eq!(invoke(&words, &Environment::default()).0, 0);
            assert!(!root.join(".trust-build-lock").exists());
        }
        Err(error) => {
            assert_eq!(
                error.raw_os_error(),
                Some(libc::EILSEQ),
                "unexpected fixture failure: {error}"
            );
            let (code, output, diagnostic) = invoke(&words, &Environment::default());
            assert_eq!(code, 2);
            assert!(output.is_empty());
            assert!(!diagnostic.is_empty());
            assert!(!root.exists());
        }
    }
}

#[cfg(feature = "native-cli-tests")]
#[test]
fn concurrent_actual_bootstrap_status_commands_are_observers_not_build_writers() {
    use std::process::{Child, Command, Stdio};
    struct Children(Vec<Child>);
    impl Drop for Children {
        fn drop(&mut self) {
            for child in &mut self.0 {
                if child.try_wait().unwrap().is_none() {
                    let _ = child.kill();
                }
                let _ = child.wait();
            }
        }
    }
    let executable = std::env::var_os("TRUST_BUILD_TREE_BOOTSTRAP")
        .expect("native-cli-tests requires the actual newly built Bootstrap executable");
    let protocol = Command::new(&executable)
        .args(["--trust-build-tree-lock", "--protocol"])
        .output()
        .expect("the selected actual Bootstrap executable must run");
    assert!(protocol.status.success(), "{protocol:?}");
    assert_eq!(protocol.stdout, format!("{PROTOCOL}\n").as_bytes());
    let root = tempfile::tempdir().unwrap();
    let guard = crate::trust_build_lock::NamespaceGuard::acquire(root.path()).unwrap();
    let mut children = Children(Vec::new());
    for _ in 0..2 {
        children.0.push(
            Command::new(&executable)
                .args([
                    OsStr::new("--trust-build-tree-lock"),
                    OsStr::new("status"),
                    OsStr::new("--repo-root"),
                    root.path().as_os_str(),
                ])
                .current_dir(root.path())
                .env_remove("TRUST_REPO")
                .env_remove("TRUST_BUILD_LOCK_TOKEN")
                .env_remove("TRUST_BUILD_LOCK_WAIT")
                .env_remove("TRUST_BUILD_LOCK_BREAK")
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap(),
        );
    }
    std::thread::sleep(Duration::from_millis(200));
    assert!(children.0.iter_mut().all(|child| child.try_wait().unwrap().is_none()));
    drop(guard);
    let outputs: Vec<_> =
        children.0.drain(..).map(|child| child.wait_with_output().unwrap()).collect();
    for output in outputs {
        assert!(output.status.success(), "metadata peer was mistaken for a writer: {output:?}");
        assert_eq!(output.stdout, b"trust build-tree lock: free\n");
    }
    assert!(!root.path().join(".trust-build-lock").exists());
}
