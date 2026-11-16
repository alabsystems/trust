use std::process::{Command, Stdio};

use super::*;

const MODE: &str = "TRUST_SCOPED_HANDOFF_TEST";
const TEST: &str = "handoff::scoped_tests::scoped_member_transport";

fn child(mode: &str, endpoint: &ScopedHandoff) -> Command {
    let mut child = Command::new(std::env::current_exe().unwrap());
    child.args(["--exact", TEST, "--nocapture"]).env(MODE, mode);
    // This actor exercises only the endpoint supplied by this fixture. An
    // enclosing native test run may also advertise its own CPU transport.
    child.env_remove(super::super::CPU_HANDOFF_ENV).env_remove(ENV);
    endpoint.configure(&mut child);
    child
}

fn receive() -> io::Result<()> {
    if let Some(ad) = std::env::var_os(super::super::CPU_HANDOFF_ENV) {
        let (primary, fences) = recover_cpu_resources(&ad)?;
        validate_cpu_file(&primary)?;
        let identity = FileIdentity::read(&primary)?;
        assert_eq!(
            format!("{}:{}", identity.0, identity.1),
            std::env::var("TRUST_SCOPED_CPU_ID").unwrap()
        );
        assert!(fences.is_empty());
    } else {
        let ad = std::env::var_os(ENV).unwrap();
        let parsed = Advertisement::parse(&ad)?;
        assert_eq!(parsed.pair, [900, 901]);
        let pair = recover(&ad, OsStr::new(&flags([900, 901])))?;
        assert_ne!(pair[0].as_raw_fd(), 900);
        let mut read = std::fs::File::from(pair[0].try_clone()?);
        let mut token = [0];
        read.read_exact(&mut token)?;
        assert_eq!(token, *b"t");
    }
    Ok(())
}

#[test]
fn scoped_member_transport() {
    if let Ok(mode) = std::env::var(MODE) {
        match mode.as_str() {
            "sibling" => assert!(receive().is_err()),
            "descendant" => receive().unwrap(),
            "exec-target" => {
                let original: u32 =
                    std::env::var("TRUST_SCOPED_EXEC_PID").unwrap().parse().unwrap();
                assert_eq!(std::process::id(), original, "exec must preserve the bound PID");
                receive().unwrap();
            }
            "member" | "gnu" | "parent" | "exec-cpu" | "exec-gnu" => {
                assert!(receive().is_err(), "unarmed endpoint must refuse");
                std::fs::write(std::env::var_os("TRUST_SCOPED_READY").unwrap(), b"ready").unwrap();
                let mut go = [0];
                std::io::stdin().read_exact(&mut go).unwrap();
                if mode.starts_with("exec-") {
                    use std::os::unix::process::CommandExt;
                    let error = Command::new(std::env::current_exe().unwrap())
                        .args(["--exact", TEST, "--nocapture"])
                        .env(MODE, "exec-target")
                        .env("TRUST_SCOPED_EXEC_PID", std::process::id().to_string())
                        .exec();
                    panic!("member exec failed: {error}");
                }
                receive().unwrap();
                if mode == "parent" {
                    let mut child = Command::new(std::env::current_exe().unwrap());
                    assert!(
                        child
                            .args(["--exact", TEST, "--nocapture"])
                            .env(MODE, "descendant")
                            .status()
                            .unwrap()
                            .success()
                    );
                }
            }
            _ => panic!("unexpected child mode"),
        }
        return;
    }
    for mode in ["member", "gnu", "parent", "exec-cpu", "exec-gnu"] {
        let path =
            std::env::temp_dir().join(format!("scoped-test-{}", hex(&random().unwrap()[..8])));
        let mut cleanup = None;
        let mut remaining = None;
        let mut cpu_identity = None;
        let endpoint = if matches!(mode, "gnu" | "exec-gnu") {
            let [read, write] = super::tests::pipe();
            remaining = Some(read.try_clone().unwrap());
            std::fs::File::from(write.try_clone().unwrap()).write_all(b"t").unwrap();
            ScopedHandoff::jobserver([read, write], [900, 901]).unwrap()
        } else {
            let (file, fd) = super::tests::cpu_file();
            cleanup = Some(file);
            let identity = FileIdentity::read(&fd).unwrap();
            cpu_identity = Some(format!("{}:{}", identity.0, identity.1));
            ScopedHandoff::cpu_bundle(fd, vec![]).unwrap()
        };
        let mut command = child(mode, &endpoint);
        command.env("TRUST_SCOPED_READY", &path).stdin(Stdio::piped());
        if let Some(identity) = cpu_identity {
            command.env("TRUST_SCOPED_CPU_ID", identity);
        }
        let mut member = command.spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        while !path.exists() {
            assert!(Instant::now() < deadline, "member did not report unarmed refusal");
            std::thread::sleep(Duration::from_millis(5));
        }
        endpoint.bind_child(member.id()).unwrap();
        // A native transport witness retains this SAME endpoint through the
        // actual member. Dropping the preparing wrapper must neither close it
        // early nor create another bind attempt/pool.
        let retained = endpoint.clone();
        drop(endpoint);
        let endpoint = retained;
        assert!(endpoint.bind_child(member.id()).is_err());
        assert!(child("sibling", &endpoint).status().unwrap().success());
        member.stdin.take().unwrap().write_all(b"g").unwrap();
        assert!(member.wait().unwrap().success());
        if let Some(read) = remaining {
            // SAFETY: read is a live owned pipe; fcntl changes only its flags,
            // and the one-byte read buffer is valid for the complete call.
            unsafe {
                let flags = libc::fcntl(read.as_raw_fd(), libc::F_GETFL);
                assert!(flags >= 0);
                assert_eq!(
                    libc::fcntl(read.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK),
                    0
                );
                let mut byte = [0_u8];
                assert_eq!(libc::read(read.as_raw_fd(), byte.as_mut_ptr().cast(), 1), -1);
                assert_eq!(io::Error::last_os_error().kind(), io::ErrorKind::WouldBlock);
            }
        }
        std::fs::remove_file(path).unwrap();
        if let Some(path) = cleanup {
            std::fs::remove_file(path).unwrap();
        }
    }
}

#[test]
fn scoped_failed_bind_cannot_be_retried() {
    let endpoint = ScopedHandoff::jobserver(super::tests::pipe(), [900, 901]).unwrap();
    assert!(endpoint.bind_child(std::process::id()).is_err());
    let retained = endpoint.clone();
    drop(endpoint);
    let mut child = Command::new("/bin/sleep").arg("1").spawn().unwrap();
    assert!(retained.bind_child(child.id()).is_err());
    child.kill().unwrap();
    child.wait().unwrap();
}

#[test]
fn exited_member_cannot_authorize_another_process() {
    let endpoint = ScopedHandoff::jobserver(super::tests::pipe(), [900, 901]).unwrap();
    let mut child = Command::new("/bin/sleep").arg("1").spawn().unwrap();
    endpoint.bind_child(child.id()).unwrap();
    child.kill().unwrap();
    child.wait().unwrap();
    let current = Process::current().unwrap();
    assert!(scoped::authorize(endpoint.0.scope.as_deref(), &current).is_err());
}

#[test]
fn scoped_named_fifo_transport_preserves_inventory_and_refuses_replacement() {
    const NAMED: &str = "TRUST_SCOPED_NAMED_TEST";
    const EXACT: &str = "handoff::scoped_tests::scoped_named_fifo_transport_preserves_inventory_and_refuses_replacement";
    #[cfg(feature = "client")]
    if std::env::var_os(NAMED).as_deref() == Some(OsStr::new("leaf")) {
        // SAFETY: this fresh descendant imports only the original named pool.
        let inherited = unsafe { super::super::InheritedJobserver::from_env() }.unwrap();
        assert!(inherited.is_present());
        return;
    }
    if std::env::var_os(NAMED).is_some() {
        let ad = std::env::var_os(ENV).unwrap();
        assert!(recover_named_fifo_resources(&ad).is_err(), "unbound member must refuse");
        #[cfg(feature = "client")]
        // SAFETY: this fixture advertises only named metadata, no reusable slots.
        assert!(unsafe { super::super::Jobserver::from_env_with_handoff() }.is_err());
        #[cfg(feature = "client")]
        // SAFETY: same fresh named-only fixture; the shim must check scope too.
        assert!(unsafe { super::super::InheritedJobserver::from_env() }.is_err());
        std::fs::write(std::env::var_os("TRUST_SCOPED_READY").unwrap(), b"ready").unwrap();
        let mut go = [0];
        std::io::stdin().read_exact(&mut go).unwrap();
        let pair = recover_named_fifo_resources(&ad).unwrap();
        validate_named_pair(&pair).unwrap();
        assert!(recover_cpu_resources(&ad).is_err());
        assert!(recover(&ad, OsStr::new(&flags([900, 901]))).is_err());
        // The advertisement contains counts2,0; these already-open standard
        // descriptors must never be read, closed or treated as recovery slots.
        // SAFETY: read-only queries of this fixture's live standard descriptors.
        unsafe {
            assert!(libc::fcntl(0, libc::F_GETFD) >= 0);
            assert!(libc::fcntl(2, libc::F_GETFD) >= 0);
        }
        #[cfg(feature = "client")]
        {
            // SAFETY: this child advertises only a named FIFO, never numeric
            // descriptors; import must authenticate the scoped witnesses first.
            let server =
                unsafe { super::super::Jobserver::from_env_with_handoff() }.unwrap().unwrap();
            let token = server.client().acquire().unwrap();
            drop(token);
            // SAFETY: only checked named witnesses are advertised in this child.
            let inherited = unsafe { super::super::InheritedJobserver::from_env() }.unwrap();
            assert!(inherited.is_present());
            let mut next = Command::new(std::env::current_exe().unwrap());
            inherited.configure(&mut next);
            let exported = next.get_envs().find(|(key, _)| *key == "CARGO_MAKEFLAGS").unwrap();
            let mut direct = Command::new("unused");
            server.configure(&mut direct);
            let expected = direct.get_envs().find(|(key, _)| *key == "CARGO_MAKEFLAGS").unwrap();
            assert_eq!(exported.1, expected.1);
            assert_eq!(
                next.get_envs().find(|(key, _)| *key == ENV).unwrap().1,
                Some(ad.as_os_str())
            );
            assert!(!format!("{inherited:?}").contains(ad.to_str().unwrap()));
            assert!(next.args(["--exact", EXACT]).env(NAMED, "leaf").status().unwrap().success());
        }
        std::fs::write(std::env::var_os("TRUST_SCOPED_CONSUMED").unwrap(), b"done").unwrap();
        std::io::stdin().read_exact(&mut go).unwrap();
        #[cfg(feature = "client")]
        // SAFETY: named-only metadata as above, now pointing at a replaced node.
        assert!(unsafe { super::super::Jobserver::from_env_with_handoff() }.is_err());
        #[cfg(feature = "client")]
        // SAFETY: same fresh named-only fixture; the shim must check scope too.
        assert!(unsafe { super::super::InheritedJobserver::from_env() }.is_err());
        return;
    }
    use std::os::unix::fs::OpenOptionsExt;
    let world = tempfile::tempdir().unwrap();
    let path = world.path().join("pool");
    let cpath = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
    // SAFETY: terminated path inside this newly owned private fixture directory.
    assert_eq!(unsafe { libc::mkfifo(cpath.as_ptr(), 0o600) }, 0);
    let read =
        std::fs::OpenOptions::new().read(true).custom_flags(libc::O_NONBLOCK).open(&path).unwrap();
    let mut write =
        std::fs::OpenOptions::new().write(true).custom_flags(libc::O_NONBLOCK).open(&path).unwrap();
    write.write_all(b"t").unwrap();
    let endpoint =
        ScopedHandoff::named_fifo([read.try_clone().unwrap().into(), write.into()]).unwrap();
    let ready = world.path().join("ready");
    let consumed = world.path().join("consumed");
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", EXACT, "--nocapture"])
        .env(NAMED, "1")
        .env("TRUST_SCOPED_READY", &ready)
        .env("TRUST_SCOPED_CONSUMED", &consumed)
        .env("CARGO_MAKEFLAGS", format!("--jobserver-auth=fifo:{}", path.display()))
        .stdin(Stdio::piped());
    endpoint.configure(&mut command);
    let mut member = command.spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    for marker in [&ready, &consumed] {
        while !marker.exists() {
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(1));
        }
        if marker == &ready {
            endpoint.bind_child(member.id()).unwrap();
            member.stdin.as_mut().unwrap().write_all(b"g").unwrap();
        }
    }
    std::fs::remove_file(&path).unwrap();
    // SAFETY: replace only this fixture's removed locator; original witnesses
    // remain live and must reject the new node rather than joining its pool.
    assert_eq!(unsafe { libc::mkfifo(cpath.as_ptr(), 0o600) }, 0);
    member.stdin.as_mut().unwrap().write_all(b"u").unwrap();
    assert!(member.wait().unwrap().success());
    let mut read = read;
    let mut token = [0];
    read.read_exact(&mut token).unwrap();
    assert_eq!(token, *b"t");
    assert_eq!(read.read(&mut token).unwrap_err().kind(), io::ErrorKind::WouldBlock);
}
