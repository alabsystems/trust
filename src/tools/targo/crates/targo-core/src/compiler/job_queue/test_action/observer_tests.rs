// Trust: exercise the production reporter control with this still-linked test
// image. Actors own real supervised process groups and real jobserver permits;
// no second scheduler, generated executable or shell wrapper runs the fixture.
use super::{CancelTestWorkers, TestReporter, graph};
use crate::CargoResult;
use cargo_util::{Jobserver, ProcessBuilder, StreamingProcessScope};
use std::cell::{Cell, RefCell};
use std::fs;
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::sync::{Arc, mpsc};
use std::time::{Duration, Instant};

const ROLE: &str = "__TARGO_GRAPH_OBSERVER_TEST_ROLE";
const WORLD: &str = "__TARGO_GRAPH_OBSERVER_TEST_WORLD";
const CASE: &str = "__TARGO_GRAPH_OBSERVER_TEST_CASE";
const ACTOR_LIFETIME: Duration = Duration::from_secs(15);

fn test_name(name: &str) -> String {
    // libtest omits the crate prefix from a unit test's fully qualified name.
    let (_, module) = module_path!().split_once("::").unwrap();
    format!("{module}::{name}")
}

fn self_command(test: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args([
        "--exact",
        &test_name(test),
        "--nocapture",
        "--quiet",
        "--test-threads=1",
    ]);
    command
}

#[expect(
    clippy::disallowed_methods,
    reason = "the child actor's scratch path comes from its actual inherited test protocol, without a GlobalContext"
)]
fn world() -> PathBuf {
    std::env::var_os(WORLD).unwrap().into()
}

fn wait_for(path: &Path) {
    let deadline = Instant::now() + ACTOR_LIFETIME;
    while !path.exists() {
        assert!(Instant::now() < deadline, "missing readiness: {path:?}");
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the subprocess actor must read its actual inherited role before any Cargo context exists"
)]
fn observer_actor() {
    let Ok(role) = std::env::var(ROLE) else {
        return;
    };
    let root = world();
    if role == "a" {
        wait_for(&root.join("b.started"));
        wait_for(&root.join("grandchild.started"));
        fs::write(root.join("a.finished"), b"actual child success").unwrap();
        return;
    }
    if role == "c" {
        fs::write(root.join("c.started"), b"must stay unlaunched").unwrap();
        return;
    }
    assert!(matches!(role.as_str(), "b" | "grandchild"));
    // Each actor retains its own connection. EOF establishes that cancellation
    // closed both lifetimes without guessing from reusable PIDs or zombies.
    let mut lifetime = UnixStream::connect(root.join("lifetime.sock")).unwrap();
    lifetime
        .write_all(if role == "b" { b"b" } else { b"g" })
        .unwrap();
    if role == "b" {
        // The descendant deliberately remains in B's owned process group.
        let _grandchild = self_command("observer_actor")
            .env(ROLE, "grandchild")
            .env(WORLD, &root)
            .spawn()
            .unwrap();
    }
    fs::write(root.join(format!("{role}.started")), b"actual actor ready").unwrap();
    // The external controller cannot kill these independent owned groups.
    // Finite actor lifetimes contain a deliberately regressed cancellation.
    let deadline = Instant::now() + ACTOR_LIFETIME;
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(10));
    }
    fs::write(root.join(format!("{role}.expired")), b"cancellation failed").unwrap();
    drop(lifetime);
    panic!("observer fixture outlived cancellation");
}

fn command(role: &str, root: &Path, server: &Jobserver) -> ProcessBuilder {
    let mut command = ProcessBuilder::new(std::env::current_exe().unwrap());
    command
        .args(&[
            "--exact",
            &test_name("observer_actor"),
            "--nocapture",
            "--quiet",
        ])
        .env(ROLE, role)
        .env(WORLD, root)
        .env("RUST_TEST_THREADS", "1")
        .inherit_jobserver(server);
    command
}

fn reject(panic: bool) -> CargoResult<()> {
    if panic {
        panic!("deliberate observer panic");
    }
    anyhow::bail!("deliberate observer error")
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the subprocess driver must read its actual inherited case selector, without a GlobalContext"
)]
fn observer_driver() {
    let Ok(case) = std::env::var(CASE) else {
        return;
    };
    let root = world();
    let at_start = case.starts_with("started");
    let panic = case.ends_with("panic");
    let lifetime = UnixListener::bind(root.join("lifetime.sock")).unwrap();
    lifetime.set_nonblocking(true).unwrap();
    let coordinator = std::thread::current().id();
    let calls = RefCell::new(Vec::new());
    let rejected = Cell::new(false);
    let mut reporter = TestReporter::default();
    let signals = Arc::new(StreamingProcessScope::new().unwrap());
    // A owns the invocation's implicit permit; B holds the pool's only explicit
    // token until its real execution has returned and its worker has joined.
    let server = Jobserver::new(1).unwrap();
    let token = server.client().acquire().unwrap();
    assert_eq!(server.client().available().unwrap(), 0);
    let commands = [command("a", &root, &server), command("b", &root, &server)];
    let (send, receive) = mpsc::channel();
    let mut completed = Vec::new();
    std::thread::scope(|workers| {
        let _cancel = CancelTestWorkers::new(Some(&signals));
        for (index, (command, token)) in commands.into_iter().zip([None, Some(token)]).enumerate() {
            assert!(reporter.observe(&signals, || {
                assert_eq!(std::thread::current().id(), coordinator);
                calls.borrow_mut().push(("started", index));
                Ok(())
            }));
            let signals = signals.clone();
            let send = send.clone();
            workers.spawn(move || {
                let _token = token;
                let result =
                    graph::execute(&command, None, None, &signals, graph::OutputSink::Raw, None);
                send.send((index, result)).unwrap();
            });
        }
        let completion = receive.recv_timeout(ACTOR_LIFETIME).unwrap();
        assert_eq!(completion.0, 0, "B retired before its cancellation");
        assert!(
            completion.1.is_ok(),
            "A did not actually finish successfully"
        );
        // Match production: retain the actual result before delivering a
        // fallible terminal observation. A reporter cannot erase completion.
        completed.push(completion);
        let observed = reporter.observe(&signals, || {
            assert_eq!(std::thread::current().id(), coordinator);
            calls.borrow_mut().push(("finished", 0));
            assert!(root.join("a.finished").exists());
            assert!(root.join("b.started").exists());
            assert!(root.join("grandchild.started").exists());
            if !at_start {
                rejected.set(true);
                return reject(panic);
            }
            Ok(())
        });
        assert_eq!(observed, at_start);
        if at_start {
            // A's implicit slot has retired, but C's rejected start observation
            // must cancel B without authorizing another user process.
            assert!(!reporter.observe(&signals, || {
                assert_eq!(std::thread::current().id(), coordinator);
                calls.borrow_mut().push(("started", 2));
                rejected.set(true);
                reject(panic)
            }));
        }
        assert!(rejected.get());
        assert!(
            signals.interrupted(),
            "observer failure did not cancel peers"
        );
        assert!(!reporter.observe(&signals, || { panic!("observer retried after failure") }));
        let completion = receive.recv_timeout(ACTOR_LIFETIME).unwrap();
        assert_eq!(completion.0, 1);
        assert!(completion.1.is_err(), "B did not observe cancellation");
        // Trust: B ended by the signal Targo sent its group; its record names
        // no exit of its own.
        assert_eq!(
            graph::Termination::of(&completion.1),
            graph::Termination::default(),
            "a cancelled test reported Targo's signal as its own exit"
        );
        completed.push(completion);
    });
    let error = reporter.error.expect("observer failure was lost");
    let expected = if panic {
        "native test execution observer panicked"
    } else {
        "deliberate observer error"
    };
    assert!(format!("{error:#}").contains(expected), "{error:#}");
    assert_eq!(completed.len(), 2, "actual completions were lost");
    assert_eq!(completed[0].0, 0);
    assert!(completed[0].1.is_ok());
    assert_eq!(completed[1].0, 1);
    assert!(completed[1].1.is_err());
    let mut expected_calls = vec![("started", 0), ("started", 1), ("finished", 0)];
    if at_start {
        expected_calls.push(("started", 2));
    }
    assert_eq!(*calls.borrow(), expected_calls);
    assert!(!root.join("c.started").exists());
    assert_eq!(server.client().available().unwrap(), 1, "lost pool token");
    Arc::try_unwrap(signals).ok().unwrap().finish().unwrap();
    let mut retired = Vec::new();
    for _ in 0..2 {
        let (mut actor, _) = lifetime.accept().expect("ready actor never connected");
        // Darwin can reject SO_RCVTIMEO on an already-closed Unix socket.
        // Read the identity and EOF directly; the external controller bounds
        // broken cancellation without imposing a host scheduling speed gate.
        actor.set_nonblocking(true).unwrap();
        let mut identity = Vec::new();
        let mut byte = [0];
        loop {
            match actor.read(&mut byte) {
                Ok(0) => break,
                Ok(_) => {
                    identity.push(byte[0]);
                    assert_eq!(identity.len(), 1, "extra actor identity bytes");
                }
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(error) => panic!("actor lifetime read: {error}"),
            }
        }
        assert_eq!(identity.len(), 1, "missing actor identity");
        retired.push(identity[0]);
    }
    assert!(!root.join("b.expired").exists());
    assert!(!root.join("grandchild.expired").exists());
    retired.sort_unstable();
    assert_eq!(retired.as_slice(), b"bg");
    fs::write(root.join("driver.passed"), b"all lifecycle checks passed").unwrap();
}

// Trust: bound reporter regressions outside the signal-owning driver. Kill and
// reap only the controller process this test spawned; actors have finite guards.
struct Controller(Child);

impl Drop for Controller {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn exercise(case: &str) {
    // Keep the world before spawning, so every failure preserves its evidence.
    // A short path stays below macOS's Unix-domain socket pathname limit.
    let root = tempfile::Builder::new()
        .prefix("targo-graph-observer-")
        .tempdir_in("/tmp")
        .unwrap()
        .keep();
    let log = fs::File::create(root.join("controller.log")).unwrap();
    let mut controller = Controller(
        self_command("observer_driver")
            .env(CASE, case)
            .env(WORLD, &root)
            .stdout(log.try_clone().unwrap())
            .stderr(log)
            .spawn()
            .unwrap(),
    );
    let deadline = Instant::now() + Duration::from_secs(30);
    let status = loop {
        if let Some(status) = controller.0.try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "observer controller timed out; evidence: {root:?}"
        );
        std::thread::sleep(Duration::from_millis(10));
    };
    assert!(
        status.success() && root.join("driver.passed").exists(),
        "{case} failed; evidence: {root:?}\n{}",
        fs::read_to_string(root.join("controller.log")).unwrap()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn started_error_cancels_and_drains_owned_peers() {
    exercise("started-error");
}

#[test]
fn started_panic_cancels_and_drains_owned_peers() {
    exercise("started-panic");
}

#[test]
fn finished_error_preserves_completion_and_cancels_owned_peers() {
    exercise("finished-error");
}

#[test]
fn finished_panic_preserves_completion_and_cancels_owned_peers() {
    exercise("finished-panic");
}
