// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Real Git service and causal barriers for independently admitted cache tests.
//! Events are fixture DATA, never admission, SDK or snapshot authority.
#![cfg_attr(trust_std, feature(trust_process_inherit_fds))]

#[cfg(all(trust_std, any(target_os = "linux", target_os = "macos")))]
mod supported {
    use std::fs::{self, File};
    use std::io::{self, Write};
    use std::net::{TcpListener, TcpStream};
    use std::os::fd::{AsRawFd, OwnedFd};
    use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
    use std::os::unix::net::UnixDatagram;
    use std::os::unix::process::CommandExt;
    use std::path::{Path, PathBuf};
    use std::process::Stdio;
    use std::time::{Duration, Instant};

    use anyhow::{Context as _, Result, bail, ensure};
    use cargo_util::{Jobserver, PreparedIsolatedChild, ProcessBuilder, StreamingProcessScope};
    use serde_json::json;
    use trust_resource_controller::client::sdk;

    const HANG: Duration = Duration::from_secs(60);
    const MAX_COMMAND: usize = 32;
    const MAX_STDERR: u64 = 256 * 1024;

    struct OwnedSocketPath {
        path: Option<PathBuf>,
        device: u64,
        inode: u64,
    }

    impl OwnedSocketPath {
        fn capture(path: PathBuf) -> Result<Self> {
            let metadata = fs::symlink_metadata(&path)?;
            ensure!(
                metadata.file_type().is_socket(),
                "created control path is not a socket"
            );
            Ok(Self {
                path: Some(path),
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        }
        fn cleanup(&mut self) -> io::Result<bool> {
            let Some(path) = self.path.take() else {
                return Ok(false);
            };
            let metadata = match fs::symlink_metadata(&path) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
                Err(error) => return Err(error),
            };
            // This owned fixture directory has no concurrent namespace writers.
            // A replaced or aliased pathname is never ours to remove.
            if !metadata.file_type().is_socket()
                || (metadata.dev(), metadata.ino()) != (self.device, self.inode)
            {
                return Ok(false);
            }
            fs::remove_file(path)?;
            Ok(true)
        }
    }

    impl Drop for OwnedSocketPath {
        fn drop(&mut self) {
            let _ = self.cleanup();
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Command {
        Status,
        Arm,
        Release,
        WaitArrived,
        WaitServed,
        Stop,
    }

    fn command(bytes: &[u8]) -> Result<Command> {
        match bytes {
            b"status" => Ok(Command::Status),
            b"arm" => Ok(Command::Arm),
            b"release" => Ok(Command::Release),
            b"wait-arrived" => Ok(Command::WaitArrived),
            b"wait-served" => Ok(Command::WaitServed),
            b"stop" => Ok(Command::Stop),
            _ => bail!("unknown fixture command"),
        }
    }

    #[derive(Default)]
    struct Gate {
        armed: bool,
        arrived: bool,
        released: bool,
        serving: bool,
        stopped: bool,
        number: u64,
        served: u64,
    }

    impl Gate {
        fn arm(&mut self) -> Result<()> {
            ensure!(
                !self.stopped && !self.armed && !self.arrived && !self.serving,
                "request already armed, active or stopped"
            );
            self.armed = true;
            Ok(())
        }
        fn arrival(&mut self) -> Result<()> {
            ensure!(!self.arrived && !self.serving, "another request is active");
            self.number = self
                .number
                .checked_add(1)
                .context("request counter exhausted")?;
            self.arrived = true;
            self.released = !self.armed;
            Ok(())
        }
        fn release(&mut self) -> Result<()> {
            ensure!(
                self.armed && self.arrived && !self.released,
                "no paused request to release"
            );
            self.released = true;
            Ok(())
        }
        fn begin(&mut self) -> Result<()> {
            ensure!(
                self.arrived && self.released && !self.serving,
                "request is not released"
            );
            self.serving = true;
            Ok(())
        }
        fn complete(&mut self) {
            self.served = self.number;
            self.armed = false;
            self.arrived = false;
            self.released = false;
            self.serving = false;
        }
        fn status(&self) -> serde_json::Value {
            json!({"request":self.number,"served":self.served,"armed":self.armed,
                "arrived":self.arrived,"released":self.released,"serving":self.serving,
                "stopped":self.stopped})
        }
    }

    struct Control {
        socket: UnixDatagram,
        arrived_waiter: Option<PathBuf>,
        served_waiter: Option<(PathBuf, u64)>,
    }

    impl Control {
        fn reply(&self, destination: &Path, value: serde_json::Value) -> Result<()> {
            self.socket
                .send_to(&serde_json::to_vec(&value)?, destination)?;
            Ok(())
        }
        // At most one bounded datagram per observation, including child waits.
        fn poll(&mut self, gate: &mut Gate) -> Result<()> {
            let mut bytes = [0; MAX_COMMAND + 1];
            let (length, peer) = match self.socket.recv_from(&mut bytes) {
                Ok(value) => value,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(()),
                Err(error) => return Err(error.into()),
            };
            let peer = peer
                .as_pathname()
                .context("fixture client must bind a reply socket")?;
            let request = if length > MAX_COMMAND {
                Err(anyhow::anyhow!("oversize fixture command"))
            } else {
                command(&bytes[..length])
            };
            let result = match request {
                Ok(Command::Status) => Ok(()),
                Ok(Command::Arm) => gate.arm(),
                Ok(Command::Release) => gate.release(),
                Ok(Command::Stop) => {
                    gate.stopped = true;
                    Ok(())
                }
                Ok(Command::WaitArrived) if !gate.arrived => {
                    if self.arrived_waiter.is_some() {
                        return self.reply(
                            peer,
                            json!({"ok":false,"error":"arrival waiter already registered"}),
                        );
                    }
                    self.arrived_waiter = Some(peer.to_owned());
                    return Ok(());
                }
                Ok(Command::WaitServed) if gate.number == 0 || gate.armed || gate.arrived => {
                    if self.served_waiter.is_some() {
                        return self.reply(
                            peer,
                            json!({"ok":false,"error":"completion waiter already registered"}),
                        );
                    }
                    let target = if gate.arrived {
                        gate.number
                    } else {
                        gate.number
                            .checked_add(1)
                            .context("request counter exhausted")?
                    };
                    self.served_waiter = Some((peer.to_owned(), target));
                    return Ok(());
                }
                Ok(Command::WaitArrived | Command::WaitServed) => Ok(()),
                Err(error) => Err(error),
            };
            self.reply(
                peer,
                match result {
                    Ok(()) => json!({"ok":true,"state":gate.status()}),
                    Err(error) => {
                        json!({"ok":false,"error":error.to_string(),"state":gate.status()})
                    }
                },
            )
        }
        fn notify(&mut self, gate: &Gate) -> Result<()> {
            if gate.arrived {
                if let Some(peer) = self.arrived_waiter.take() {
                    self.reply(&peer, json!({"ok":true,"state":gate.status()}))?;
                }
            }
            if !gate.arrived && gate.served > 0 {
                if self
                    .served_waiter
                    .as_ref()
                    .is_some_and(|(_, target)| gate.served >= *target)
                {
                    let (peer, _) = self.served_waiter.take().unwrap();
                    self.reply(&peer, json!({"ok":true,"state":gate.status()}))?;
                }
            }
            Ok(())
        }
    }

    fn poll_descriptors(descriptors: &[i32], timeout: Duration) -> Result<()> {
        let mut descriptors = descriptors
            .iter()
            .map(|&fd| libc::pollfd {
                fd,
                events: libc::POLLIN,
                revents: 0,
            })
            .collect::<Vec<_>>();
        let millis = i32::try_from(timeout.as_millis().min(i32::MAX as u128)).unwrap();
        // SAFETY: poll receives this owned writable array of live descriptors.
        let result =
            unsafe { libc::poll(descriptors.as_mut_ptr(), descriptors.len() as _, millis) };
        if result < 0 {
            return Err(io::Error::last_os_error().into());
        }
        ensure!(result != 0, "fixture one-minute hang detector expired");
        Ok(())
    }

    fn serve(git: &Path, repository: &Path, state: &Path, scheduler: &Jobserver) -> Result<()> {
        ensure!(
            git.is_absolute() && git.is_file(),
            "select an actual absolute Git image"
        );
        ensure!(
            repository.is_absolute()
                && repository.canonicalize()? == repository
                && repository.is_dir(),
            "repository must be a canonical directory"
        );
        let base = repository
            .parent()
            .context("repository requires an owned parent")?;
        let metadata = if repository.join(".git").exists() {
            repository.join(".git")
        } else {
            repository.to_owned()
        };
        ensure!(
            fs::symlink_metadata(&metadata)?.file_type().is_dir()
                && fs::symlink_metadata(metadata.join("objects"))?
                    .file_type()
                    .is_dir()
                && fs::symlink_metadata(metadata.join("HEAD"))?
                    .file_type()
                    .is_file(),
            "selected fixture repository must have actual unaliased Git metadata"
        );
        // Git's strict whitelist names the actual Git directory, including
        // `.git` for a worktree; it does not expand a worktree URL to that path.
        let exported = metadata.strip_prefix(base)?;
        ensure!(state.is_absolute(), "state directory must be absolute");
        fs::create_dir(state).context("fixture state must be a fresh owned directory")?;
        fs::set_permissions(state, fs::Permissions::from_mode(0o700))?;
        let control_path = state.join("control.sock");
        let socket = UnixDatagram::bind(&control_path)?;
        let mut owned_path = OwnedSocketPath::capture(control_path)?;
        socket.set_nonblocking(true)?;
        let listener = TcpListener::bind((std::net::Ipv4Addr::LOCALHOST, 0))?;
        listener.set_nonblocking(true)?;
        let mut repository_url = url::Url::parse(&format!("git://{}", listener.local_addr()?))?;
        {
            let mut segments = repository_url
                .path_segments_mut()
                .map_err(|()| anyhow::anyhow!("Git fixture URL cannot contain path segments"))?;
            segments.clear();
            for component in exported {
                segments.push(
                    component
                        .to_str()
                        .context("Git fixture path must be UTF-8")?,
                );
            }
        }
        let mut control = Control {
            socket,
            arrived_waiter: None,
            served_waiter: None,
        };
        let mut gate = Gate::default();
        let scope = StreamingProcessScope::new()?;
        let result = (|| -> Result<()> {
            println!(
                "{}",
                json!({"event":"ready","address":listener.local_addr()?.to_string(),"url":repository_url.as_str(),"control":state.join("control.sock"),"git":git})
            );
            io::stdout().flush()?;
            let mut pending: Option<TcpStream> = None;
            let mut deadline = Instant::now() + HANG;
            loop {
                ensure!(!scope.interrupted(), "fixture interrupted");
                control.poll(&mut gate)?;
                if gate.stopped {
                    break;
                }
                if pending.is_none() {
                    match listener.accept() {
                        Ok((stream, _)) => {
                            stream.set_nonblocking(true)?;
                            pending = Some(stream);
                        }
                        Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
                        Err(error) => return Err(error.into()),
                    }
                }
                if let Some(stream) = &pending {
                    if !gate.arrived {
                        let mut byte = [0];
                        match stream.peek(&mut byte) {
                            Ok(0) => bail!("Git connection closed before an actual request"),
                            Ok(_) => {
                                gate.arrival()?;
                                deadline = Instant::now() + HANG;
                                control.notify(&gate)?;
                            }
                            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
                            Err(error) => return Err(error.into()),
                        }
                    }
                }
                if gate.arrived && gate.released {
                    gate.begin()?;
                    let stream = pending.take().unwrap();
                    stream.set_nonblocking(false)?;
                    let stderr_path = state.join(format!("git-{}.stderr", gate.number));
                    let stderr = File::create(&stderr_path)?;
                    let mut builder = ProcessBuilder::new(git);
                    builder.args(&["daemon", "--inetd", "--export-all", "--strict-paths"]);
                    builder.arg(format!("--base-path={}", base.display()));
                    builder.arg(&metadata);
                    builder.inherit_jobserver(scheduler);
                    let mut command = builder.build_command();
                    // Transparent single-child borrowing retains original CPU/store
                    // descriptions too; no descriptor or resource credit is made.
                    command.inherit_all_fds().process_group(0);
                    sdk::inherit_original_lease(&mut command)?;
                    command.stdin(Stdio::from(OwnedFd::from(stream.try_clone()?)));
                    command.stdout(Stdio::from(OwnedFd::from(stream)));
                    command.stderr(Stdio::from(stderr));
                    let prepared = PreparedIsolatedChild::prepare(&scope)?;
                    prepared.check_cancelled()?;
                    let child = command.spawn()?;
                    // SAFETY: our direct unreaped child was placed in its own
                    // group at spawn; this guard becomes its only waiter.
                    let owned = unsafe { prepared.adopt_std(child) };
                    let mut failure = None;
                    let mut deadline_cancelled = false;
                    let child_deadline = Instant::now() + HANG;
                    let status = owned.wait_with_cancel(|| {
                        if let Err(error) = control.poll(&mut gate) {
                            failure = Some(error);
                        }
                        match fs::metadata(&stderr_path) {
                            Ok(metadata) if metadata.len() <= MAX_STDERR => {}
                            Ok(_) => {
                                failure = Some(anyhow::anyhow!("Git stderr exceeded capture limit"))
                            }
                            Err(error) => failure = Some(error.into()),
                        }
                        deadline_cancelled |= Instant::now() >= child_deadline;
                        gate.stopped || failure.is_some() || deadline_cancelled
                    });
                    // The production owner has retired the group before any
                    // status, capture or protocol assertion below.
                    if let Some(error) = failure {
                        return Err(error);
                    }
                    if gate.stopped {
                        match status {
                            Ok(_) => return Ok(()),
                            Err(error) if error.kind() == io::ErrorKind::Interrupted => {
                                return Ok(());
                            }
                            Err(error) => return Err(error.into()),
                        }
                    }
                    ensure!(
                        !deadline_cancelled,
                        "Git one-minute hang detector cancelled the child"
                    );
                    let status = status?;
                    ensure!(
                        fs::metadata(&stderr_path)?.len() <= MAX_STDERR,
                        "Git stderr exceeded bounded capture"
                    );
                    println!(
                        "{}",
                        json!({"event":"served","request":gate.number,"success":status.success(),"code":status.code(),"stderr":stderr_path})
                    );
                    io::stdout().flush()?;
                    ensure!(status.success(), "actual Git daemon failed: {status}");
                    gate.complete();
                    control.notify(&gate)?;
                    deadline = Instant::now() + HANG;
                    continue;
                }
                let remaining = deadline
                    .checked_duration_since(Instant::now())
                    .context("fixture one-minute hang detector expired")?;
                let mut descriptors = vec![control.socket.as_raw_fd()];
                if let Some(stream) = &pending {
                    if !gate.arrived {
                        descriptors.push(stream.as_raw_fd());
                    }
                } else {
                    descriptors.push(listener.as_raw_fd());
                }
                poll_descriptors(&descriptors, remaining)?;
            }
            Ok(())
        })();
        let finished = scope.finish();
        let cleaned = owned_path.cleanup();
        finished?;
        cleaned?;
        result
    }

    fn client(state: &Path, requested: &str) -> Result<()> {
        command(requested.as_bytes())?;
        let directory = tempfile::Builder::new()
            .prefix("git-control-")
            .tempdir_in(state)?;
        let socket = UnixDatagram::bind(directory.path().join("reply.sock"))?;
        socket.set_read_timeout(Some(HANG))?;
        socket.send_to(requested.as_bytes(), state.join("control.sock"))?;
        let mut bytes = [0; 4096];
        let length = socket.recv(&mut bytes)?;
        let value: serde_json::Value = serde_json::from_slice(&bytes[..length])?;
        println!("{}", value);
        ensure!(value["ok"] == true, "fixture command refused");
        Ok(())
    }

    pub fn main() -> Result<()> {
        // FIRST: snapshot original SDK before the checked GNU importer can open
        // descriptors. No parser, fixture file, listener or logger precedes it.
        let pending = sdk::snapshot_sdk_lease()?;
        // SAFETY: genuine native entry; only the descriptor-free snapshot ran.
        let inherited = unsafe { Jobserver::from_env_with_handoff_checked() }?;
        // SAFETY: only the prescribed checked GNU importer followed snapshot.
        unsafe { sdk::capture_sdk_lease(pending) }?;
        let args = std::env::args_os().skip(1).collect::<Vec<_>>();
        if args == ["--help"] {
            println!(
                "cache-git-fixture serve GIT REPOSITORY FRESH_STATE\ncache-git-fixture ctl STATE status|arm|release|wait-arrived|wait-served|stop\nRequires separate genuine root admission; adds no resource credits."
            );
            return Ok(());
        }
        if args.len() == 3 && args[0] == "ctl" {
            return client(
                Path::new(&args[1]),
                args[2].to_str().context("command must be UTF-8")?,
            );
        }
        ensure!(
            args.len() == 4 && args[0] == "serve",
            "use --help for supported commands"
        );
        ensure!(
            std::env::var("BUILD_SLOT_HELD").as_deref() == Ok("1"),
            "requires an actually admitted root; marker alone grants nothing"
        );
        let scheduler = inherited
            .context("actual original inherited GNU scheduler required")?
            .for_descendant()?;
        serve(
            Path::new(&args[1]),
            Path::new(&args[2]),
            Path::new(&args[3]),
            &scheduler,
        )
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::io::Read as _;

        fn ipc() -> (tempfile::TempDir, Control, UnixDatagram) {
            let directory = tempfile::tempdir().unwrap();
            let server = UnixDatagram::bind(directory.path().join("control.sock")).unwrap();
            server.set_nonblocking(true).unwrap();
            let client = UnixDatagram::bind(directory.path().join("reply.sock")).unwrap();
            client
                .connect(directory.path().join("control.sock"))
                .unwrap();
            client.set_read_timeout(Some(HANG)).unwrap();
            (
                directory,
                Control {
                    socket: server,
                    arrived_waiter: None,
                    served_waiter: None,
                },
                client,
            )
        }

        fn response(client: &UnixDatagram) -> serde_json::Value {
            let mut bytes = [0; 4096];
            let size = client.recv(&mut bytes).unwrap();
            serde_json::from_slice(&bytes[..size]).unwrap()
        }

        #[test]
        fn actual_control_socket_waits_for_arrival_and_refuses_premature_release() {
            let (_directory, mut control, client) = ipc();
            let mut gate = Gate::default();
            client.send(&[b'x'; MAX_COMMAND + 1]).unwrap();
            control.poll(&mut gate).unwrap();
            assert_eq!(response(&client)["ok"], false);
            client.send(b"release").unwrap();
            control.poll(&mut gate).unwrap();
            assert_eq!(response(&client)["ok"], false);
            client.send(b"arm").unwrap();
            control.poll(&mut gate).unwrap();
            assert_eq!(response(&client)["ok"], true);
            client.send(b"wait-arrived").unwrap();
            control.poll(&mut gate).unwrap();
            client.set_nonblocking(true).unwrap();
            assert_eq!(
                client.recv(&mut [0; 1]).unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            );
            client.set_nonblocking(false).unwrap();
            gate.arrival().unwrap();
            control.notify(&gate).unwrap();
            let arrived = response(&client);
            assert_eq!(arrived["state"]["request"], 1);
            assert_eq!(arrived["state"]["released"], false);
            client.send(b"release").unwrap();
            control.poll(&mut gate).unwrap();
            assert_eq!(response(&client)["state"]["released"], true);
            gate.begin().unwrap();
        }

        #[test]
        fn completion_waiter_for_new_arm_cannot_observe_previous_completion() {
            let (_directory, mut control, client) = ipc();
            let mut gate = Gate::default();
            gate.arrival().unwrap();
            gate.begin().unwrap();
            gate.complete();
            gate.arm().unwrap();
            client.send(b"wait-served").unwrap();
            control.poll(&mut gate).unwrap();
            control.notify(&gate).unwrap();
            client.set_nonblocking(true).unwrap();
            assert_eq!(
                client.recv(&mut [0; 1]).unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            );
            client.set_nonblocking(false).unwrap();
            gate.arrival().unwrap();
            gate.release().unwrap();
            gate.begin().unwrap();
            gate.complete();
            control.notify(&gate).unwrap();
            assert_eq!(response(&client)["state"]["served"], 2);
        }

        #[test]
        fn socket_cleanup_removes_only_the_created_identity() {
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("control.sock");
            let socket = UnixDatagram::bind(&path).unwrap();
            let mut owned = OwnedSocketPath::capture(path.clone()).unwrap();
            assert!(owned.cleanup().unwrap());
            assert!(!path.exists());
            drop(socket);

            let socket = UnixDatagram::bind(&path).unwrap();
            let mut owned = OwnedSocketPath::capture(path.clone()).unwrap();
            let original = directory.path().join("original.sock");
            fs::rename(&path, &original).unwrap();
            fs::write(&path, b"replacement evidence").unwrap();
            assert!(!owned.cleanup().unwrap());
            drop(owned);
            assert_eq!(fs::read(&path).unwrap(), b"replacement evidence");
            assert!(
                fs::symlink_metadata(original)
                    .unwrap()
                    .file_type()
                    .is_socket()
            );
            drop(socket);
        }

        #[test]
        fn socket_peek_preserves_the_actual_request_bytes() {
            let listener = TcpListener::bind((std::net::Ipv4Addr::LOCALHOST, 0)).unwrap();
            let mut client = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
            let (mut server, _) = listener.accept().unwrap();
            server.set_read_timeout(Some(HANG)).unwrap();
            let request = b"fixture request DATA";
            client.write_all(request).unwrap();
            let mut first = [0];
            assert_eq!(server.peek(&mut first).unwrap(), 1);
            assert_eq!(first[0], request[0]);
            let mut actual = vec![0; request.len()];
            server.read_exact(&mut actual).unwrap();
            assert_eq!(actual, request);
        }
    }
}

fn main() -> std::process::ExitCode {
    #[cfg(all(trust_std, any(target_os = "linux", target_os = "macos")))]
    match supported::main() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("cache-git-fixture: {error:#}");
            std::process::ExitCode::from(1)
        }
    }
    #[cfg(not(all(trust_std, any(target_os = "linux", target_os = "macos"))))]
    {
        eprintln!("cache-git-fixture requires Trust native Linux/macOS custody");
        std::process::ExitCode::from(75)
    }
}
