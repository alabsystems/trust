use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;

use jobserver::Client;

// Trust: bind a moved real queued credit to its actual originating owner,
// without importing ownership from descriptor numbers or transport metadata.
#[test]
fn acquired_credit_matches_only_the_same_original_client() {
    let original = Client::new(1).unwrap();
    let clone = original.clone();
    let foreign = Client::new(1).unwrap();
    assert!(original.same_origin(&clone));
    assert!(!original.same_origin(&foreign));
    let credit = original.acquire().unwrap();
    assert!(credit.belongs_to(&original));
    assert!(credit.belongs_to(&clone));
    assert!(!credit.belongs_to(&foreign));
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;
        let witnesses = original.transport_witnesses().unwrap();
        let (read, write) = match &witnesses {
            jobserver::TransportWitnesses::NumericPipe { read, write }
            | jobserver::TransportWitnesses::NamedFifo { read, write, .. } => (read, write),
        };
        let reopened = Client::from_pipe(read.as_fd(), write.as_fd()).unwrap();
        assert!(!original.same_origin(&reopened));
        assert!(!credit.belongs_to(&reopened));
    }
    credit.return_to_server().unwrap();
    let returned = clone.acquire().unwrap();
    assert!(returned.belongs_to(&original));
    assert!(!returned.belongs_to(&foreign));
}

// Trust: explicit FIFO transport, isolated from ambient scheduler state.
#[cfg(unix)]
mod explicit_fifo_import {
    use super::*;
    use std::ffi::{CString, OsString};
    use std::fs::{self, OpenOptions};
    use std::os::fd::AsRawFd;
    use std::os::unix::{ffi::OsStrExt, ffi::OsStringExt, fs::OpenOptionsExt};
    use std::path::{Path, PathBuf};
    use std::process::{Child, Stdio};
    use std::time::{Duration, Instant};

    const ROLE: &str = "JOBSERVER_EXPLICIT_FIFO_ROLE";
    const WORLD: &str = "JOBSERVER_EXPLICIT_FIFO_WORLD";
    const HANG: Duration = Duration::from_secs(60);

    fn world() -> PathBuf {
        tempfile::Builder::new()
            .prefix("jobserver-fifo-")
            .suffix(".noindex")
            .tempdir()
            .unwrap()
            .keep()
    }

    fn fifo(path: &Path) {
        let name = CString::new(path.as_os_str().as_bytes()).unwrap();
        // SAFETY: name is NUL-terminated and remains live through mkfifo.
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    }

    struct OwnedChild(Child);
    impl Drop for OwnedChild {
        fn drop(&mut self) {
            if !matches!(self.0.try_wait(), Ok(Some(_))) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
    }

    fn child(test: &str, role: &str, world: &Path, client: Option<&Client>) -> OwnedChild {
        let log = File::create(world.join("child.log")).unwrap();
        let mut command = Command::new(env::current_exe().unwrap());
        command
            .args(["--exact", test, "--nocapture", "--test-threads=1"])
            .env(ROLE, role)
            .env(WORLD, world)
            .stdout(Stdio::from(log.try_clone().unwrap()))
            .stderr(Stdio::from(log));
        if let Some(client) = client {
            client.configure(&mut command);
        }
        OwnedChild(command.spawn().unwrap())
    }

    fn marker(child: &mut OwnedChild, world: &Path, name: &str) {
        let until = Instant::now() + HANG;
        while !world.join(name).is_file() {
            assert!(
                child.0.try_wait().unwrap().is_none(),
                "FIFO child exited before {name}; evidence: {world:?}\n{}",
                fs::read_to_string(world.join("child.log")).unwrap()
            );
            if Instant::now() >= until {
                fs::write(world.join("parent.expired"), b"missing child marker").unwrap();
                panic!("FIFO child never reached {name}; evidence: {world:?}");
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    fn finish(child: &mut OwnedChild, world: &Path) {
        let until = Instant::now() + HANG;
        let status = loop {
            if let Some(status) = child.0.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= until {
                fs::write(world.join("parent.expired"), b"child did not finish").unwrap();
                panic!("FIFO child timed out; evidence: {world:?}");
            }
            thread::sleep(Duration::from_millis(10));
        };
        assert!(
            status.success()
                && world.join("passed").is_file()
                && !world.join("parent.expired").exists()
                && !world.join("actor.expired").exists(),
            "FIFO child failed; evidence: {world:?}\n{}",
            fs::read_to_string(world.join("child.log")).unwrap()
        );
    }

    #[test]
    fn empty_pool_shares_tokens_without_environment_or_foreign_flag_changes() {
        if env::var_os(ROLE).is_some() {
            let world = PathBuf::from(env::var_os(WORLD).unwrap());
            let path = world.join("tokens");
            let blocking = OpenOptions::new()
                .read(true)
                .write(true)
                .open(&path)
                .unwrap();
            // SAFETY: blocking owns this descriptor throughout both queries.
            let flags = unsafe { libc::fcntl(blocking.as_raw_fd(), libc::F_GETFL) };
            assert!(flags >= 0 && flags & libc::O_NONBLOCK == 0);
            let keys = [
                "CARGO_MAKEFLAGS",
                "MAKEFLAGS",
                "MFLAGS",
                "CARGO_JOBSERVER_HANDOFF",
            ];
            let before = keys.map(env::var_os);
            let owner = Client::from_fifo(&path).unwrap();
            assert_eq!(owner.available().unwrap(), 0, "constructor minted tokens");
            assert!(owner.try_acquire().unwrap().is_none());
            owner.release_raw().unwrap();
            let peer = Client::from_fifo(&path).unwrap();
            assert_eq!(
                peer.available().unwrap(),
                1,
                "constructor changed seeded tokens"
            );
            let held = peer
                .try_acquire()
                .unwrap()
                .expect("same FIFO token missing");
            assert!(owner.try_acquire().unwrap().is_none());
            drop(held);
            let returned = owner.acquire().unwrap();
            returned.drop_without_releasing();
            assert!(peer.try_acquire().unwrap().is_none());
            // SAFETY: blocking still owns its independent description.
            assert_eq!(
                unsafe { libc::fcntl(blocking.as_raw_fd(), libc::F_GETFL) },
                flags
            );
            assert!(
                before == keys.map(env::var_os),
                "constructor changed environment"
            );
            fs::write(world.join("passed"), b"same FIFO and unchanged flags").unwrap();
            return;
        }
        let world = world();
        fifo(&world.join("tokens"));
        let mut child = child("explicit_fifo_import::empty_pool_shares_tokens_without_environment_or_foreign_flag_changes", "identity", &world, None);
        finish(&mut child, &world);
        fs::remove_dir_all(world).unwrap();
    }

    #[test]
    fn refuses_unadvertisable_paths_regular_files_and_symlinks() {
        let world = world();
        for path in [
            PathBuf::from("relative-fifo"),
            world.join("space name"),
            world.join("line\nname"),
            world.join(OsString::from_vec(vec![b'x', 0xff])),
        ] {
            assert_eq!(
                Client::from_fifo(&path).unwrap_err().kind(),
                std::io::ErrorKind::InvalidInput
            );
        }
        let regular = world.join("regular");
        fs::write(&regular, b"keep original bytes").unwrap();
        assert!(Client::from_fifo(&regular).is_err());
        assert_eq!(fs::read(&regular).unwrap(), b"keep original bytes");
        let actual = world.join("tokens");
        fifo(&actual);
        let link = world.join("link");
        std::os::unix::fs::symlink(&actual, &link).unwrap();
        assert!(Client::from_fifo(&link).is_err());
        assert_eq!(Client::from_fifo(&actual).unwrap().available().unwrap(), 0);
        fs::remove_dir_all(world).unwrap();
    }

    #[test]
    fn configured_child_acquires_and_returns_the_exact_fifo_token() {
        if env::var_os(ROLE).is_some() {
            let world = PathBuf::from(env::var_os(WORLD).unwrap());
            // SAFETY: this isolated child was explicitly configured with a
            // named FIFO; no numbered descriptor import or env mutation occurs.
            let inherited = unsafe { Client::from_env() }.expect("configured FIFO missing");
            assert_eq!(inherited.available().unwrap(), 0);
            // Exercise blocking acquire on the explicitly nonblocking client;
            // the independently imported ordinary client witnesses its return.
            let client = Client::from_fifo(&world.join("tokens")).unwrap();
            fs::write(world.join("ready"), b"actual child before acquire").unwrap();
            let held = client.acquire().unwrap();
            fs::write(world.join("acquired"), b"actual child owns token").unwrap();
            let until = Instant::now() + HANG;
            while !world.join("release").exists() {
                if Instant::now() >= until {
                    fs::write(world.join("actor.expired"), b"parent did not release").unwrap();
                    panic!("FIFO parent did not release child");
                }
                thread::sleep(Duration::from_millis(10));
            }
            drop(held);
            assert_eq!(
                inherited.available().unwrap(),
                1,
                "imported FIFO lost its readable count"
            );
            let returned = inherited.acquire().unwrap();
            assert_eq!(inherited.available().unwrap(), 0);
            returned.drop_without_releasing();
            inherited.release_raw().unwrap();
            assert_eq!(inherited.available().unwrap(), 1);
            fs::write(world.join("passed"), b"actual child returned token").unwrap();
            return;
        }
        let world = world();
        fifo(&world.join("tokens"));
        let client = Client::from_fifo(&world.join("tokens")).unwrap();
        let mut child = child(
            "explicit_fifo_import::configured_child_acquires_and_returns_the_exact_fifo_token",
            "roundtrip",
            &world,
            Some(&client),
        );
        marker(&mut child, &world, "ready");
        assert!(!world.join("acquired").exists());
        client.release_raw().unwrap();
        marker(&mut child, &world, "acquired");
        assert!(
            client.try_acquire().unwrap().is_none(),
            "child did not own the token"
        );
        fs::write(world.join("release"), b"return the token").unwrap();
        finish(&mut child, &world);
        let returned = client.try_acquire().unwrap().expect("child token was lost");
        assert!(
            client.try_acquire().unwrap().is_none(),
            "duplicate token returned"
        );
        returned.drop_without_releasing();
        fs::remove_dir_all(world).unwrap();
    }

    #[test]
    fn full_fifo_owner_write_reports_would_block_without_waiting() {
        if env::var_os(ROLE).is_some() {
            let world = PathBuf::from(env::var_os(WORLD).unwrap());
            let path = world.join("tokens");
            let client = Client::from_fifo(&path).unwrap();
            let mut fill = OpenOptions::new()
                .read(true)
                .write(true)
                .custom_flags(libc::O_NONBLOCK)
                .open(&path)
                .unwrap();
            for block in [&[b'+'; 4096][..], &[b'+'][..]] {
                loop {
                    match fill.write(block) {
                        Ok(0) => panic!("FIFO fill wrote no bytes"),
                        Ok(_) => {}
                        Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => break,
                        Err(error) => panic!("FIFO fill: {error}"),
                    }
                }
            }
            assert_eq!(
                client.release_raw().unwrap_err().kind(),
                std::io::ErrorKind::WouldBlock
            );
            // Kernel FIFO buffer slots need not become writable after removing
            // one byte. Drain all existing bytes before testing a new write.
            let mut drained = 0;
            while let Some(token) = client.try_acquire().unwrap() {
                token.drop_without_releasing();
                drained += 1;
            }
            assert!(drained != 0, "full FIFO was empty");
            client.release_raw().unwrap();
            let token = client
                .try_acquire()
                .unwrap()
                .expect("new FIFO byte missing");
            assert!(client.try_acquire().unwrap().is_none());
            token.drop_without_releasing();
            fs::write(
                world.join("passed"),
                b"full owner write refused; drained FIFO reused",
            )
            .unwrap();
            return;
        }
        let world = world();
        fifo(&world.join("tokens"));
        // The external watchdog kills only this owned child if a regressed
        // constructor gives release_raw a blocking descriptor on a full FIFO.
        let mut child = child(
            "explicit_fifo_import::full_fifo_owner_write_reports_would_block_without_waiting",
            "full",
            &world,
            None,
        );
        finish(&mut child, &world);
        fs::remove_dir_all(world).unwrap();
    }
}

#[cfg(unix)]
mod explicit_pipe_import {
    use super::*;
    use std::os::unix::io::{AsFd, AsRawFd, FromRawFd};

    fn pipe() -> (File, File) {
        let mut pair = [-1; 2];
        // SAFETY: fresh pipe ownership is transferred to exactly two Files.
        assert_eq!(unsafe { libc::pipe(pair.as_mut_ptr()) }, 0);
        unsafe { (File::from_raw_fd(pair[0]), File::from_raw_fd(pair[1])) }
    }

    #[test]
    fn preserves_the_same_tokens_and_environment_without_borrowed_ownership() {
        let keys = [
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            "CARGO_JOBSERVER_HANDOFF",
        ];
        let before = keys.map(env::var_os);
        let (mut read, mut write) = pipe();
        let client = Client::from_pipe(read.as_fd(), write.as_fd()).unwrap();
        assert_eq!(
            client.available().unwrap(),
            0,
            "import minted scheduling tokens"
        );
        write.write_all(b"+").unwrap();
        assert_eq!(client.available().unwrap(), 1);
        let held = client.acquire().unwrap();
        assert_eq!(client.available().unwrap(), 0);
        drop(held);
        assert_eq!(client.available().unwrap(), 1);
        let mut token = [0];
        read.read_exact(&mut token).unwrap();
        assert_eq!(token, *b"+");
        assert_eq!(
            client.available().unwrap(),
            0,
            "client used a different pipe"
        );
        write.write_all(&token).unwrap();
        assert_eq!(client.available().unwrap(), 1);
        assert_eq!(before, keys.map(env::var_os));
        drop((read, write));
        drop(client.acquire().unwrap());
        assert_eq!(
            client.available().unwrap(),
            1,
            "borrowed owners were retained instead of cloned"
        );
    }

    #[test]
    fn refuses_regular_files_and_reversed_pipe_access_without_closing_borrows() {
        let (read, write) = pipe();
        assert!(Client::from_pipe(write.as_fd(), read.as_fd()).is_err());
        let file = tempfile::tempfile().unwrap();
        assert!(Client::from_pipe(file.as_fd(), file.as_fd()).is_err());
        for fd in [read.as_raw_fd(), write.as_raw_fd(), file.as_raw_fd()] {
            // SAFETY: all three borrowed owners remain live after refusal.
            assert!(unsafe { libc::fcntl(fd, libc::F_GETFD) } >= 0);
        }
    }

    #[test]
    fn configured_child_uses_owned_descriptors_after_originals_close() {
        const CHILD: &str = "JOBSERVER_OWNED_PIPE_CHILD";
        if env::var_os(CHILD).is_some() {
            // SAFETY: the parent explicitly configured this child with its
            // jobserver. This test process has no concurrent environment edits.
            let client = unsafe { Client::from_env() }.expect("configured pipe was not inherited");
            assert_eq!(client.available().unwrap(), 1);
            let held = client.acquire().unwrap();
            assert_eq!(client.available().unwrap(), 0);
            drop(held);
            assert_eq!(client.available().unwrap(), 1);
            return;
        }

        let (read, mut write) = pipe();
        write.write_all(b"+").unwrap();
        let client = Client::from_pipe(read.as_fd(), write.as_fd()).unwrap();
        drop((read, write));

        for configure_make in [false, true] {
            let mut cmd = Command::new(env::current_exe().unwrap());
            cmd.args([
                "--exact",
                "explicit_pipe_import::configured_child_uses_owned_descriptors_after_originals_close",
                "--nocapture",
            ]);
            cmd.env(CHILD, "1");
            if configure_make {
                client.configure_make(&mut cmd);
            } else {
                client.configure(&mut cmd);
            }
            assert!(cmd.status().unwrap().success());
            assert_eq!(client.available().unwrap(), 1);
        }
    }
}

macro_rules! t {
    ($e:expr) => {
        match $e {
            Ok(e) => e,
            Err(e) => panic!("{} failed with {}", stringify!($e), e),
        }
    };
}

#[test]
fn server_smoke() {
    let c = t!(Client::new(1));
    drop(c.acquire().unwrap());
    drop(c.acquire().unwrap());
}

#[test]
fn server_multiple() {
    let c = t!(Client::new(2));
    let a = c.acquire().unwrap();
    let b = c.acquire().unwrap();
    drop((a, b));
}

#[test]
fn server_available() {
    let c = t!(Client::new(10));
    assert_eq!(c.available().unwrap(), 10);
    let a = c.acquire().unwrap();
    assert_eq!(c.available().unwrap(), 9);
    drop(a);
    assert_eq!(c.available().unwrap(), 10);
}

#[test]
fn server_none_available() {
    let c = t!(Client::new(2));
    assert_eq!(c.available().unwrap(), 2);
    let a = c.acquire().unwrap();
    assert_eq!(c.available().unwrap(), 1);
    let b = c.acquire().unwrap();
    assert_eq!(c.available().unwrap(), 0);
    drop(a);
    assert_eq!(c.available().unwrap(), 1);
    drop(b);
    assert_eq!(c.available().unwrap(), 2);
}

#[test]
fn server_blocks() {
    let c = t!(Client::new(1));
    let a = c.acquire().unwrap();
    let hit = Arc::new(AtomicBool::new(false));
    let hit2 = hit.clone();
    let (tx, rx) = mpsc::channel();
    let t = thread::spawn(move || {
        tx.send(()).unwrap();
        let _b = c.acquire().unwrap();
        hit2.store(true, Ordering::SeqCst);
    });
    rx.recv().unwrap();
    assert!(!hit.load(Ordering::SeqCst));
    drop(a);
    t.join().unwrap();
    assert!(hit.load(Ordering::SeqCst));
}

#[test]
fn make_as_a_single_thread_client() {
    let c = t!(Client::new(1));
    let td = tempfile::tempdir().unwrap();

    let prog = env::var("MAKE").unwrap_or_else(|_| "make".to_string());
    let mut cmd = Command::new(prog);
    cmd.current_dir(td.path());

    t!(t!(File::create(td.path().join("Makefile"))).write_all(
        b"
all: foo bar
foo:
\techo foo
bar:
\techo bar
"
    ));

    // The jobserver protocol means that the `make` process itself "runs with a
    // token", so we acquire our one token to drain the jobserver, and this
    // should mean that `make` itself never has a second token available to it.
    let _a = c.acquire();
    c.configure(&mut cmd);
    let output = t!(cmd.output());
    println!(
        "\n\t=== stderr\n\t\t{}",
        String::from_utf8_lossy(&output.stderr).replace("\n", "\n\t\t")
    );
    println!(
        "\t=== stdout\n\t\t{}",
        String::from_utf8_lossy(&output.stdout).replace("\n", "\n\t\t")
    );

    assert!(output.status.success());
    assert!(output.stderr.is_empty());

    let stdout = String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n");
    let a = "\
echo foo
foo
echo bar
bar
";
    let b = "\
echo bar
bar
echo foo
foo
";

    assert!(stdout == a || stdout == b);
}

#[test]
fn make_as_a_multi_thread_client() {
    let c = t!(Client::new(1));
    let td = tempfile::tempdir().unwrap();

    let prog = env::var("MAKE").unwrap_or_else(|_| "make".to_string());
    let mut cmd = Command::new(prog);
    cmd.current_dir(td.path());

    t!(t!(File::create(td.path().join("Makefile"))).write_all(
        b"
all: foo bar
foo:
\techo foo
bar:
\techo bar
"
    ));

    // We're leaking one extra token to `make` sort of violating the makefile
    // jobserver protocol. It has the desired effect though.
    c.configure(&mut cmd);
    let output = t!(cmd.output());
    println!(
        "\n\t=== stderr\n\t\t{}",
        String::from_utf8_lossy(&output.stderr).replace("\n", "\n\t\t")
    );
    println!(
        "\t=== stdout\n\t\t{}",
        String::from_utf8_lossy(&output.stdout).replace("\n", "\n\t\t")
    );

    assert!(output.status.success());
}

#[test]
fn zero_client() {
    let client = t!(Client::new(0));
    let (tx, rx) = mpsc::channel();
    let helper = client
        .into_helper_thread(move |a| drop(tx.send(a)))
        .unwrap();
    helper.request_token();
    helper.request_token();

    for _ in 0..1000 {
        assert!(rx.try_recv().is_err());
    }
}
