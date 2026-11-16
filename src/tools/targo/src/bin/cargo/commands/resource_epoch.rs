// Trust: private host-owned GNU transport qualification. No global allocator or proof claim.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use crate::command_prelude::*;

#[cfg(unix)]
#[path = "resource_epoch_recipe.rs"]
mod recipe;

pub fn cli() -> Command {
    subcommand("__resource-epoch")
        .hide(true)
        .about("Private controller-owned GNU transport epoch")
        .arg(
            Arg::new("directory")
                .long("directory")
                .required(true)
                .value_name("PATH"),
        )
        .arg(
            Arg::new("epoch")
                .long("epoch")
                .required(true)
                .value_name("HEX"),
        )
        .arg(
            Arg::new("backing")
                .long("backing")
                .required(true)
                .value_parser(clap::value_parser!(u32)),
        )
        .arg(
            Arg::new("roots")
                .long("roots")
                .required(true)
                .value_parser(clap::value_parser!(u32)),
        )
        .arg(
            Arg::new("root-recipe")
                .long("root-recipe")
                .action(clap::ArgAction::Append)
                .value_name("JSON"),
        )
}

pub fn exec(_gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    if !targo::is_targo_invocation() {
        return Err(anyhow::anyhow!("the private epoch helper requires genuine Targo").into());
    }
    #[cfg(unix)]
    {
        native::run(
            std::path::Path::new(
                args.get_one::<String>("directory")
                    .expect("required directory"),
            ),
            args.get_one::<String>("epoch").expect("required epoch"),
            *args.get_one::<u32>("backing").expect("required backing"),
            *args.get_one::<u32>("roots").expect("required roots"),
            &args
                .get_many::<String>("root-recipe")
                .map(|rows| rows.cloned().collect::<Vec<_>>())
                .unwrap_or_default(),
        )?;
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        Err(anyhow::anyhow!("private GNU FIFO epochs are currently Unix-only").into())
    }
}

#[cfg(unix)]
mod native {
    use super::recipe::Recipe;
    use anyhow::{Context as _, Result, ensure};
    use serde::Deserialize;
    use serde_json::{Value, json};
    use std::collections::VecDeque;
    use std::ffi::CString;
    use std::fs::{File, OpenOptions};
    use std::io::{self, Read as _, Write as _};
    use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd, RawFd};
    use std::os::unix::fs::{
        FileTypeExt as _, MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _,
    };
    use std::os::unix::net::UnixStream;
    use std::path::{Component, Path, PathBuf};
    use std::process::{Child, Command, Stdio};

    const MAX_BACKING: u32 = 256;
    const MAX_ROOTS: u32 = 64;
    // Trust: one Spawn and Cancel per root, followed by Close and Finalize.
    const MAX_COMMANDS: usize = 2 * MAX_ROOTS as usize + 2;
    const MAX_FRAME: usize = 16 * 1024;
    const MAX_OUTPUT: usize = 64 * 1024;
    const FIFO: &str = "credits.fifo";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Identity(u64, u64);

    impl Identity {
        fn of(file: &File) -> io::Result<Self> {
            let metadata = file.metadata()?;
            Ok(Self(metadata.dev(), metadata.ino()))
        }
    }

    struct Endpoint {
        parent: File,
        directory: File,
        path: PathBuf,
        identity: Identity,
        fifo: Identity,
        client: Option<jobserver::Client>,
    }

    fn component(name: &str) -> Result<CString> {
        ensure!(
            !name.is_empty() && name != "." && name != ".." && !name.contains('/'),
            "invalid epoch leaf"
        );
        Ok(CString::new(name)?)
    }

    fn open_at(parent: &File, name: &str, flags: i32, mode: u32) -> Result<File> {
        let name = component(name)?;
        // SAFETY: parent is a held directory and name is one checked NUL-terminated leaf.
        let fd = unsafe {
            libc::openat(
                parent.as_raw_fd(),
                name.as_ptr(),
                flags | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK,
                mode,
            )
        };
        ensure!(
            fd >= 0,
            "epoch entry open failed: {}",
            io::Error::last_os_error()
        );
        // SAFETY: successful openat returned this newly owned descriptor.
        Ok(unsafe { File::from_raw_fd(fd) })
    }

    fn private(file: &File, directory: bool) -> Result<()> {
        let metadata = file.metadata()?;
        // SAFETY: geteuid reads only this process's effective account identity.
        let uid = unsafe { libc::geteuid() };
        ensure!(
            metadata.uid() == uid && metadata.mode() & 0o077 == 0,
            "epoch entry is not private and owned"
        );
        ensure!(
            if directory {
                metadata.is_dir()
            } else {
                metadata.is_file() && metadata.nlink() == 1
            },
            "invalid epoch entry type or links"
        );
        Ok(())
    }

    fn owned_parent(file: &File) -> Result<()> {
        let metadata = file.metadata()?;
        // SAFETY: geteuid reads only this process's effective account identity.
        let uid = unsafe { libc::geteuid() };
        ensure!(
            metadata.is_dir() && metadata.uid() == uid && metadata.mode() & 0o022 == 0,
            "epoch parent must stay owned and not writable by others"
        );
        Ok(())
    }

    impl Endpoint {
        fn create(path: &Path) -> Result<Self> {
            let encoded = path.to_str().context("epoch path is not UTF-8")?;
            ensure!(
                path.is_absolute() && !encoded.chars().any(char::is_whitespace),
                "epoch path must be absolute and GNU-representable"
            );
            let parent_path = path.parent().context("epoch path has no parent")?;
            let parent = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(parent_path)?;
            owned_parent(&parent)?;
            let leaf = path
                .file_name()
                .and_then(|name| name.to_str())
                .context("invalid epoch directory name")?;
            let leaf_c = component(leaf)?;
            // SAFETY: parent is held and leaf_c is one checked component. Existing paths refuse.
            ensure!(
                unsafe { libc::mkdirat(parent.as_raw_fd(), leaf_c.as_ptr(), 0o700) } == 0,
                "epoch directory must be fresh: {}",
                io::Error::last_os_error()
            );
            let directory = open_at(&parent, leaf, libc::O_RDONLY | libc::O_DIRECTORY, 0)?;
            private(&directory, true)?;
            let fifo = component(FIFO)?;
            // SAFETY: directory is held and FIFO is a checked single leaf, created exclusively.
            ensure!(
                unsafe { libc::mkfifoat(directory.as_raw_fd(), fifo.as_ptr(), 0o600) } == 0,
                "FIFO creation failed: {}",
                io::Error::last_os_error()
            );
            let check = open_at(&directory, FIFO, libc::O_RDONLY, 0)?;
            let metadata = check.metadata()?;
            ensure!(
                metadata.file_type().is_fifo()
                    && metadata.nlink() == 1
                    && metadata.mode() & 0o077 == 0,
                "invalid private FIFO"
            );
            let identity = Identity::of(&directory)?;
            let fifo = Identity::of(&check)?;
            let client = jobserver::Client::from_fifo(&path.join(FIFO))?;
            directory.sync_all()?;
            parent.sync_all()?;
            let endpoint = Self {
                parent,
                directory,
                path: path.to_owned(),
                identity,
                fifo,
                client: Some(client),
            };
            endpoint.validate()?;
            Ok(endpoint)
        }

        fn validate(&self) -> Result<()> {
            let parent_path = self.path.parent().context("missing epoch parent")?;
            let parent = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(parent_path)?;
            ensure!(
                Identity::of(&parent)? == Identity::of(&self.parent)?,
                "epoch parent identity changed"
            );
            owned_parent(&parent)?;
            owned_parent(&self.parent)?;
            let leaf = self
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .context("invalid epoch leaf")?;
            let directory = open_at(&self.parent, leaf, libc::O_RDONLY | libc::O_DIRECTORY, 0)?;
            private(&directory, true)?;
            private(&self.directory, true)?;
            ensure!(
                Identity::of(&directory)? == self.identity,
                "epoch directory identity changed"
            );
            let file = open_at(&self.directory, FIFO, libc::O_RDONLY, 0)?;
            let metadata = file.metadata()?;
            // SAFETY: geteuid reads the current account only.
            ensure!(
                Identity::of(&file)? == self.fifo
                    && metadata.file_type().is_fifo()
                    && metadata.nlink() == 1
                    && metadata.mode() & 0o077 == 0
                    && metadata.uid() == unsafe { libc::geteuid() },
                "epoch FIFO identity, type or privacy changed"
            );
            Ok(())
        }

        fn log(&self, id: u32, side: &str) -> Result<File> {
            let file = open_at(
                &self.directory,
                &format!("root-{id}.{side}"),
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL,
                0o600,
            )?;
            // This call exclusively created the file. Normalize only its held
            // inode so a restrictive inherited umask cannot break read pinning.
            file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
            private(&file, false)?;
            Ok(file)
        }

        fn retire(&mut self) -> Result<()> {
            self.validate()?;
            // Retirement relinquishes only our endpoint handles. The named FIFO
            // stays empty for late same-cohort importers. Only the original
            // controller can later prove whole-cohort drain and unlink it.
            drop(self.client.take());
            Ok(())
        }
    }

    struct Target {
        path: PathBuf,
        parent: File,
        directory: File,
        identity: Identity,
        ancestors: Vec<Identity>,
    }

    fn ancestry(path: &Path) -> Result<Vec<Identity>> {
        path.ancestors()
            .map(|ancestor| {
                let metadata = std::fs::metadata(ancestor)?;
                Ok(Identity(metadata.dev(), metadata.ino()))
            })
            .collect()
    }

    fn paths_overlap(left: &Path, right: &Path) -> bool {
        left.starts_with(right) || right.starts_with(left)
    }

    impl Target {
        fn prepare(requested: &Path, endpoint: &Endpoint, roots: &[Option<Root>]) -> Result<Self> {
            ensure!(
                requested.is_absolute()
                    && !requested
                        .components()
                        .any(|part| matches!(part, Component::ParentDir)),
                "private root target must be absolute and contain no parent traversal"
            );
            // Resolve existing ancestors before comparing reservations. Never
            // follow a target leaf symlink; missing descendants are opened or
            // created relative to the validated owned ancestor below.
            let mut ancestor = requested;
            let mut missing = Vec::new();
            loop {
                match std::fs::symlink_metadata(ancestor) {
                    Ok(metadata) => {
                        ensure!(
                            ancestor != requested || !metadata.file_type().is_symlink(),
                            "private root target leaf must not be a symlink"
                        );
                        break;
                    }
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {
                        missing.push(
                            ancestor
                                .file_name()
                                .context("invalid target component")?
                                .to_owned(),
                        );
                        ancestor = ancestor
                            .parent()
                            .context("target has no existing ancestor")?;
                    }
                    Err(error) => return Err(error.into()),
                }
            }
            let canonical = ancestor
                .canonicalize()
                .context("target ancestor cannot be resolved")?;
            let mut directory = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(&canonical)?;
            owned_parent(&directory)?;
            let path = missing
                .iter()
                .rev()
                .fold(canonical.clone(), |path, leaf| path.join(leaf));
            endpoint.validate()?;
            let transport = endpoint.path.canonicalize()?;
            ensure!(
                !paths_overlap(&path, &transport),
                "cache target overlaps transport directory"
            );
            let anchor_ancestors = ancestry(&canonical)?;
            ensure!(
                !anchor_ancestors.contains(&endpoint.identity),
                "cache target ancestor aliases transport directory"
            );
            for root in roots.iter().flatten() {
                ensure!(
                    !paths_overlap(&path, &root.target.path),
                    "root cache targets overlap"
                );
                ensure!(
                    !anchor_ancestors.contains(&root.target.identity)
                        && (!missing.is_empty()
                            || !root.target.ancestors.contains(&Identity::of(&directory)?)),
                    "root cache target ancestor physically overlaps a reserved target"
                );
            }
            for leaf in missing.iter().rev() {
                let leaf = leaf.to_str().context("target component is not UTF-8")?;
                let name = component(leaf)?;
                // SAFETY: directory is held and name is one checked component.
                let created = unsafe { libc::mkdirat(directory.as_raw_fd(), name.as_ptr(), 0o700) };
                if created != 0 {
                    let error = io::Error::last_os_error();
                    ensure!(
                        error.kind() == io::ErrorKind::AlreadyExists,
                        "target directory creation failed: {error}"
                    );
                }
                directory = open_at(&directory, leaf, libc::O_RDONLY | libc::O_DIRECTORY, 0)?;
                owned_parent(&directory)?;
            }
            let identity = Identity::of(&directory)?;
            let parent = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(path.parent().context("cache target has no parent")?)?;
            owned_parent(&parent)?;
            let ancestors = ancestry(&path)?;
            ensure!(
                ancestors.first() == Some(&identity),
                "cache target identity changed"
            );
            let transport_ancestors = ancestry(&transport)?;
            ensure!(
                !ancestors.contains(&endpoint.identity) && !transport_ancestors.contains(&identity),
                "cache target physically overlaps transport directory"
            );
            for root in roots.iter().flatten() {
                ensure!(
                    !ancestors.contains(&root.target.identity)
                        && !root.target.ancestors.contains(&identity),
                    "root cache targets physically overlap"
                );
            }
            Ok(Self {
                path,
                parent,
                directory,
                identity,
                ancestors,
            })
        }

        fn validate(&self) -> Result<()> {
            owned_parent(&self.directory)?;
            owned_parent(&self.parent)?;
            let parent = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(self.path.parent().context("cache target has no parent")?)?;
            owned_parent(&parent)?;
            ensure!(
                Identity::of(&parent)? == Identity::of(&self.parent)?,
                "cache target parent identity changed"
            );
            let current = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(&self.path)?;
            owned_parent(&current)?;
            ensure!(
                Identity::of(&current)? == self.identity,
                "cache target identity changed before launch"
            );
            Ok(())
        }
    }

    #[derive(Deserialize)]
    #[serde(tag = "op", rename_all = "kebab-case", deny_unknown_fields)]
    enum Input {
        Spawn {
            v: u32,
            epoch: String,
            id: u32,
            manifest: PathBuf,
            target: PathBuf,
        },
        Cancel {
            v: u32,
            epoch: String,
            id: u32,
        },
        Close {
            v: u32,
            epoch: String,
        },
        Finalize {
            v: u32,
            epoch: String,
            finalization: String,
        },
    }

    struct Root {
        child: Child,
        pid: u32,
        reaped: bool,
        control: UnixStream,
        cancellation: Cancellation,
        // Reserved through the whole epoch, including after root exit: a
        // descendant may still write it until the controller establishes drain.
        target: Target,
    }

    struct RecipeRoot {
        recipe: Recipe,
        // Precreated before Opened; the controller can pin these exact writer
        // inodes before any root birth. Descendant exit is still required for
        // complete output, independently of the root's own exit observation.
        stdout: File,
        stderr: File,
    }

    // Trust: a request is not an acknowledgement, and peer closure is not exit.
    enum Cancellation {
        None,
        Pending { sent: bool, disconnected: bool },
        Reported,
    }

    impl Root {
        fn request_cancel(&mut self) {
            if matches!(self.cancellation, Cancellation::None) {
                self.cancellation = Cancellation::Pending {
                    sent: false,
                    disconnected: false,
                };
            }
        }

        fn cancellation_pending(&self) -> bool {
            matches!(self.cancellation, Cancellation::Pending { .. })
        }

        fn cancellation_interest(&self) -> i16 {
            match self.cancellation {
                Cancellation::Pending {
                    sent,
                    disconnected: false,
                } if !self.reaped => {
                    if sent {
                        libc::POLLIN
                    } else {
                        libc::POLLOUT
                    }
                }
                _ => 0,
            }
        }

        // One byte in each direction per poll keeps reconciliation bounded.
        // Only the actual root's A proves its sticky stop-dispatch latch.
        fn progress_cancel(&mut self) -> Result<Option<&'static str>> {
            if !self.cancellation_pending() {
                return Ok(None);
            }
            if self.reaped {
                self.cancellation = Cancellation::Reported;
                return Ok(Some("already-exited"));
            }
            let Cancellation::Pending { sent, disconnected } = &mut self.cancellation else {
                unreachable!("pending cancellation checked above")
            };
            if *disconnected {
                return Ok(None);
            }
            if !*sent {
                match self.control.write(b"C") {
                    Ok(1) => *sent = true,
                    Ok(_) => *disconnected = true,
                    Err(error) if peer_finished(&error) => *disconnected = true,
                    Err(error) if would_wait(&error) => return Ok(None),
                    Err(error) => return Err(error).context("private root cancel write failed"),
                }
            }
            if *disconnected {
                return Ok(None);
            }
            let mut bytes = [0u8; 2];
            match self.control.read(&mut bytes) {
                Ok(0) => *disconnected = true,
                Ok(count) => {
                    ensure!(
                        count == 1 && bytes[0] == b'A',
                        "invalid private root cancellation acknowledgement"
                    );
                    self.cancellation = Cancellation::Reported;
                    return Ok(Some("stopped"));
                }
                Err(error) if peer_finished(&error) => *disconnected = true,
                Err(error) if would_wait(&error) => {}
                Err(error) => return Err(error).context("private root cancel read failed"),
            }
            Ok(None)
        }
    }

    fn would_wait(error: &io::Error) -> bool {
        matches!(
            error.kind(),
            io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
        )
    }

    fn peer_finished(error: &io::Error) -> bool {
        matches!(
            error.kind(),
            io::ErrorKind::BrokenPipe
                | io::ErrorKind::ConnectionReset
                | io::ErrorKind::NotConnected
        )
    }

    fn root_control_pair() -> Result<(UnixStream, UnixStream)> {
        let (controller, root) = UnixStream::pair()?;
        controller.set_nonblocking(true)?;
        for stream in [&controller, &root] {
            // SAFETY: both descriptors are held private sockets. CLOEXEC keeps
            // every root's parent endpoint out of later root descendants.
            let flags = unsafe { libc::fcntl(stream.as_raw_fd(), libc::F_GETFD) };
            ensure!(
                flags >= 0
                    && unsafe {
                        libc::fcntl(stream.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC)
                    } >= 0,
                "cannot contain private root control descriptor"
            );
        }
        Ok((controller, root))
    }

    struct Epoch {
        endpoint: Endpoint,
        epoch: String,
        published: u32,
        withdrawn: u32,
        roots: Vec<Option<Root>>,
        recipes: Vec<Option<RecipeRoot>>,
        closing: bool,
        finalization: Option<String>,
        retired: bool,
        input: Vec<u8>,
        frames: VecDeque<Vec<u8>>,
        output: Vec<u8>,
    }

    fn nonblocking_pipe(fd: RawFd) -> Result<()> {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: stat points to writable storage and fd is a process stdio descriptor.
        ensure!(
            unsafe { libc::fstat(fd, stat.as_mut_ptr()) } == 0,
            "private control descriptor missing"
        );
        // SAFETY: fstat succeeded and initialized stat.
        let stat = unsafe { stat.assume_init() };
        ensure!(
            stat.st_mode & libc::S_IFMT == libc::S_IFIFO,
            "private epoch control requires pipes, not terminal stdio"
        );
        // SAFETY: F_GETFL reads fd flags; the endpoint is this helper's exclusively supplied pipe.
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        ensure!(flags >= 0, "cannot inspect private control pipe");
        // SAFETY: only this owned stdio pipe description changes, never an inherited GNU pipe.
        ensure!(
            unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } >= 0,
            "cannot make private control nonblocking"
        );
        // SAFETY: prevent the control endpoint escaping through any future exec.
        ensure!(
            unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } >= 0,
            "cannot contain private control descriptor"
        );
        Ok(())
    }

    // Trust: a blocked inherited diagnostic pipe must not prevent root reaping.
    // Never change its shared flags or acquire stdio's process-global lock.
    fn report_refusal(error: &anyhow::Error) {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: stat is writable storage; fstat only inspects stderr.
        if unsafe { libc::fstat(2, stat.as_mut_ptr()) } != 0 {
            return;
        }
        // SAFETY: successful fstat initialized stat.
        let regular = unsafe { stat.assume_init() }.st_mode & libc::S_IFMT == libc::S_IFREG;
        // SAFETY: F_GETFL only inspects the inherited descriptor's current flags.
        let flags = unsafe { libc::fcntl(2, libc::F_GETFL) };
        if !regular && (flags < 0 || flags & libc::O_NONBLOCK == 0) {
            return;
        }
        let diagnostic = format!("private epoch refused before root drain: {error:#}\n");
        let bytes = diagnostic.as_bytes();
        // SAFETY: bytes stays live for this one bounded write. A diagnostic I/O
        // failure grants nothing. Regular files retain ordinary disk latency.
        let _ = unsafe { libc::write(2, bytes.as_ptr().cast(), bytes.len().min(MAX_FRAME)) };
    }

    impl Epoch {
        fn emit(&mut self, event: &str, fields: Value) -> Result<()> {
            let mut frame = fields
                .as_object()
                .context("event fields must be an object")?
                .clone();
            frame.insert("v".into(), json!(4));
            frame.insert("epoch".into(), json!(self.epoch));
            frame.insert("event".into(), json!(event));
            let mut bytes = serde_json::to_vec(&frame)?;
            bytes.push(b'\n');
            ensure!(
                bytes.len() <= MAX_FRAME && self.output.len() + bytes.len() <= MAX_OUTPUT,
                "private control output exceeded bound"
            );
            self.output.extend_from_slice(&bytes);
            Ok(())
        }

        fn flush(&mut self) -> Result<()> {
            if self.output.is_empty() {
                return Ok(());
            }
            // SAFETY: output is live initialized storage; stdout is the private write pipe.
            let written = unsafe { libc::write(1, self.output.as_ptr().cast(), self.output.len()) };
            if written < 0 {
                let error = io::Error::last_os_error();
                if matches!(
                    error.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                ) {
                    return Ok(());
                }
                return Err(error.into());
            }
            ensure!(written != 0, "private control output made no progress");
            self.output.drain(..written as usize);
            Ok(())
        }

        fn read(&mut self) -> Result<()> {
            let mut bytes = [0u8; 4096];
            // SAFETY: bytes is writable for the supplied length; stdin is the owned read pipe.
            let count = unsafe { libc::read(0, bytes.as_mut_ptr().cast(), bytes.len()) };
            if count < 0 {
                let error = io::Error::last_os_error();
                if matches!(
                    error.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                ) {
                    return Ok(());
                }
                return Err(error.into());
            }
            ensure!(
                count != 0,
                "private epoch controller closed before completion"
            );
            self.input.extend_from_slice(&bytes[..count as usize]);
            while let Some(end) = self.input.iter().position(|byte| *byte == b'\n') {
                ensure!(
                    end > 0 && end < MAX_FRAME && self.frames.len() < MAX_COMMANDS,
                    "private control frame exceeded bound"
                );
                self.frames.push_back(self.input.drain(..=end).collect());
            }
            ensure!(
                self.input.len() < MAX_FRAME,
                "unterminated private control frame exceeded bound"
            );
            Ok(())
        }

        fn command(&mut self, frame: &[u8]) -> Result<()> {
            let command: Input =
                serde_json::from_slice(frame).context("invalid private control frame")?;
            let (version, epoch) = match &command {
                Input::Spawn { v, epoch, .. }
                | Input::Cancel { v, epoch, .. }
                | Input::Close { v, epoch }
                | Input::Finalize { v, epoch, .. } => (*v, epoch),
            };
            ensure!(
                version == 4 && epoch == &self.epoch,
                "foreign private control version or epoch"
            );
            // Trust: Finalize is the explicit end of this controller's command
            // stream. Close only seals births; it must not race later controls.
            ensure!(
                self.finalization.is_none(),
                "private epoch finalize is one-use; no later commands are accepted"
            );
            match command {
                Input::Cancel { id, .. } => {
                    let root = self
                        .roots
                        .get_mut(id as usize)
                        .and_then(Option::as_mut)
                        .context("private cancel root ID is unavailable")?;
                    root.request_cancel();
                }
                Input::Close { .. } => {
                    ensure!(!self.closing, "private epoch close is one-use");
                    self.closing = true;
                    self.emit("closing", json!({}))?;
                }
                Input::Finalize { finalization, .. } => {
                    ensure!(
                        self.closing && self.roots.iter().flatten().all(|root| root.reaped),
                        "private epoch finalize requires Close and all owned roots reaped"
                    );
                    ensure!(
                        self.roots
                            .iter()
                            .flatten()
                            .all(|root| !root.cancellation_pending()),
                        "private epoch finalize requires all cancellation outcomes"
                    );
                    ensure!(
                        finalization.len() == 32
                            && finalization.bytes().all(|byte| {
                                byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)
                            }),
                        "private epoch finalization must be 32 lowercase hexadecimal digits"
                    );
                    // Trust: echo only this actual request's challenge. The
                    // controller chooses it after observing all root exits, so
                    // an earlier buffered Retired cannot satisfy the handshake.
                    self.finalization = Some(finalization);
                }
                Input::Spawn {
                    id,
                    manifest,
                    target,
                    ..
                } => {
                    ensure!(
                        !self.closing
                            && (id as usize) < self.roots.len()
                            && self.roots[id as usize].is_none(),
                        "private root ID is unavailable or epoch is closing"
                    );
                    ensure!(
                        manifest.is_absolute(),
                        "private root manifest must be absolute"
                    );
                    self.endpoint.validate()?;
                    let target = Target::prepare(&target, &self.endpoint, &self.roots)
                        .context("invalid private root target")?;
                    let (stdout, stderr) = if let Some(recipe) = &self.recipes[id as usize] {
                        (recipe.stdout.try_clone()?, recipe.stderr.try_clone()?)
                    } else {
                        (
                            self.endpoint.log(id, "stdout")?,
                            self.endpoint.log(id, "stderr")?,
                        )
                    };
                    target
                        .validate()
                        .context("private root target changed before launch")?;
                    let (control, root_control) = root_control_pair()?;
                    // Trust: fixed analysis recipes execute their pinned SDK
                    // Targo, whose original session the owner later queries.
                    let program = if let Some(program) = self.recipes[id as usize]
                        .as_ref()
                        .and_then(|root| root.recipe.program())
                    {
                        program.to_owned()
                    } else {
                        std::env::current_exe()?
                    };
                    let mut command = Command::new(program);
                    command.args(["--unverified", "build", "--__resource-root-control"]);
                    if let Some(recipe) = &self.recipes[id as usize] {
                        recipe.recipe.configure(&mut command)?;
                        // Cargo discovers project configuration from cwd, not
                        // from --manifest-path. Preserve the checked plan's
                        // checkout, which the controller binds to this manifest.
                        command.current_dir(
                            manifest.parent().context("recipe manifest has no parent")?,
                        );
                    } else {
                        command.arg("--offline");
                    }
                    command
                        .arg("--manifest-path")
                        .arg(&manifest)
                        .arg("--target-dir")
                        .arg(&target.path)
                        .stdin(Stdio::from(OwnedFd::from(root_control)))
                        .stdout(Stdio::from(stdout))
                        .stderr(Stdio::from(stderr));
                    command
                        .env_remove("CARGO_MAKEFLAGS")
                        .env_remove("MAKEFLAGS")
                        .env_remove("MFLAGS");
                    self.endpoint
                        .client
                        .as_ref()
                        .context("sealed endpoint")?
                        .configure_make(&mut command);
                    let child = command.spawn().context("private Targo root spawn failed")?;
                    drop(command);
                    let pid = child.id();
                    self.roots[id as usize] = Some(Root {
                        child,
                        pid,
                        reaped: false,
                        control,
                        cancellation: Cancellation::None,
                        target,
                    });
                    self.emit("spawned", json!({"id":id,"pid":pid}))?;
                }
            }
            Ok(())
        }

        fn children(&mut self) -> Result<()> {
            for id in 0..self.roots.len() {
                let ended = if let Some(root) = &mut self.roots[id] {
                    if root.reaped {
                        None
                    } else {
                        root.child.try_wait()?.map(|status| {
                            root.reaped = true;
                            (root.pid, status)
                        })
                    }
                } else {
                    None
                };
                if let Some((pid, status)) = ended {
                    self.emit(
                        "root-exit",
                        json!({"id":id,"pid":pid,"code":status.code(),"success":status.success()}),
                    )?;
                }
            }
            Ok(())
        }

        fn cancellations(&mut self) -> Result<()> {
            for id in 0..self.roots.len() {
                let acknowledgement = if let Some(root) = &mut self.roots[id] {
                    root.progress_cancel()?.map(|state| (root.pid, state))
                } else {
                    None
                };
                if let Some((pid, state)) = acknowledgement {
                    self.emit("cancelled", json!({"id":id,"pid":pid,"state":state}))?;
                }
            }
            Ok(())
        }

        fn done(&self) -> bool {
            self.retired
                && self.output.is_empty()
                && self.roots.iter().flatten().all(|root| root.reaped)
        }

        fn step_close(&mut self) -> Result<()> {
            if !self.closing || self.retired {
                return Ok(());
            }
            self.endpoint.validate()?;
            // Trust: preserve Close's existing nonblocking withdrawal. Holding
            // returned credits stops new borrowing without inventing retirement;
            // Finalize, exact inventory and the original drain checks still gate it.
            if self.withdrawn < self.published {
                if let Some(token) = self
                    .endpoint
                    .client
                    .as_ref()
                    .context("sealed endpoint")?
                    .try_acquire()?
                {
                    token.drop_without_releasing();
                    self.withdrawn += 1;
                }
            }
            if self.finalization.is_some()
                && self.withdrawn == self.published
                && self.roots.iter().flatten().all(|root| root.reaped)
            {
                // Process all already queued control first. Finalize followed by
                // malformed/obsolete input, or observed EOF, cannot manufacture
                // retirement merely because no root is currently running.
                if !self.frames.is_empty() || !self.input.is_empty() {
                    return Ok(());
                }
                let mut control = libc::pollfd {
                    fd: 0,
                    events: libc::POLLIN,
                    revents: 0,
                };
                // SAFETY: control is one initialized private input descriptor.
                let ready = unsafe { libc::poll(&raw mut control, 1, 0) };
                if ready < 0 {
                    let error = io::Error::last_os_error();
                    if error.kind() == io::ErrorKind::Interrupted {
                        return Ok(());
                    }
                    return Err(error.into());
                }
                ensure!(
                    control.revents & (libc::POLLHUP | libc::POLLERR | libc::POLLNVAL) == 0,
                    "private controller closed before retirement"
                );
                if control.revents & libc::POLLIN != 0 {
                    self.read()?;
                    return Ok(());
                }
                if let Some(extra) = self
                    .endpoint
                    .client
                    .as_ref()
                    .context("retired endpoint")?
                    .try_acquire()?
                {
                    extra.drop_without_releasing();
                    anyhow::bail!("private epoch has unexpected surplus credits");
                }
                self.endpoint.retire()?;
                self.retired = true;
                self.emit(
                    "retired",
                    json!({"withdrawn":self.withdrawn,"fifo":self.endpoint.path.join(FIFO),"scope":"owned-roots-and-explicit-tokens","finalization":self.finalization}),
                )?;
            }
            Ok(())
        }

        fn drive(&mut self) -> Result<()> {
            loop {
                if self.done() {
                    return Ok(());
                }
                self.flush()?;
                self.children()?;
                // Actual root-exit is emitted before an already-exited receipt.
                self.cancellations()?;
                if !self.retired {
                    self.endpoint.validate()?;
                }
                if !self.retired {
                    if let Some(frame) = self.frames.pop_front() {
                        self.command(&frame)?;
                    }
                }
                self.step_close()?;
                let mut descriptors = vec![
                    libc::pollfd {
                        fd: if self.retired { -1 } else { 0 },
                        events: libc::POLLIN,
                        revents: 0,
                    },
                    libc::pollfd {
                        fd: 1,
                        events: if self.output.is_empty() {
                            0
                        } else {
                            libc::POLLOUT
                        },
                        revents: 0,
                    },
                ];
                for root in self.roots.iter().flatten() {
                    let events = root.cancellation_interest();
                    if events != 0 {
                        descriptors.push(libc::pollfd {
                            fd: root.control.as_raw_fd(),
                            events,
                            revents: 0,
                        });
                    }
                }
                // SAFETY: descriptors contains at most 2 + MAX_ROOTS initialized pollfd values.
                let result = unsafe {
                    libc::poll(
                        descriptors.as_mut_ptr(),
                        descriptors.len() as _,
                        if self.frames.is_empty() { 10 } else { 0 },
                    )
                };
                if result < 0 {
                    let error = io::Error::last_os_error();
                    if error.kind() == io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(error.into());
                }
                if descriptors[0].revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0 {
                    self.read()?;
                }
                ensure!(
                    descriptors[1].revents & (libc::POLLHUP | libc::POLLERR | libc::POLLNVAL) == 0,
                    "private control reader disappeared"
                );
            }
        }

        // Refusal never fabricates Retired or kills a child whose work may survive.
        // Keep the actual receipts and reap controlled roots as they finish; the
        // controller still needs whole-cohort drain and retains every CPU unit.
        fn reap_after_refusal(&mut self) {
            while self.roots.iter().flatten().any(|root| !root.reaped) {
                for root in self.roots.iter_mut().flatten() {
                    if !root.reaped {
                        match root.child.try_wait() {
                            Ok(Some(_)) => root.reaped = true,
                            Ok(None) => {}
                            Err(_) => return,
                        }
                    }
                }
                // SAFETY: a zero-length descriptor set is valid; this is a bounded idle wait.
                unsafe {
                    libc::poll(std::ptr::null_mut(), 0, 10);
                }
            }
        }
    }

    pub(super) fn run(
        path: &Path,
        epoch: &str,
        backing: u32,
        roots: u32,
        rows: &[String],
    ) -> Result<()> {
        ensure!(
            epoch.len() == 32
                && epoch
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
            "private epoch must be 32 lowercase hexadecimal digits"
        );
        ensure!(
            (1..=MAX_BACKING).contains(&backing)
                && (1..=MAX_ROOTS).contains(&roots)
                && roots <= backing,
            "private epoch requires 1 <= roots <= backing <= 256 and roots <= 64"
        );
        // Parse all recipes and pin the selected SDK drivers before publishing
        // any endpoint or credit. Startup data is not a capacity capability.
        let recipes = Recipe::parse_all(rows, roots)?;
        nonblocking_pipe(0)?;
        nonblocking_pipe(1)?;
        let endpoint = Endpoint::create(path)?;
        let recipes = recipes
            .into_iter()
            .enumerate()
            .map(|(id, recipe)| {
                recipe
                    .map(|recipe| -> Result<_> {
                        Ok(RecipeRoot {
                            recipe,
                            stdout: endpoint.log(id as u32, "stdout")?,
                            stderr: endpoint.log(id as u32, "stderr")?,
                        })
                    })
                    .transpose()
            })
            .collect::<Result<Vec<_>>>()?;
        let published = backing - roots;
        for _ in 0..published {
            endpoint
                .client
                .as_ref()
                .expect("new endpoint")
                .release_raw()?;
        }
        let mut state = Epoch {
            endpoint,
            epoch: epoch.to_owned(),
            published,
            withdrawn: 0,
            roots: (0..roots).map(|_| None).collect(),
            recipes,
            closing: false,
            finalization: None,
            retired: false,
            input: Vec::new(),
            frames: VecDeque::new(),
            output: Vec::new(),
        };
        state.emit(
            "opened",
            json!({"fifo":path.join(FIFO),"backing":backing,"roots":roots,"published":published}),
        )?;
        let result = state.drive();
        if let Err(error) = &result {
            // Trust: fatal refusal accepts no more commands. This is our
            // validated private stdin pipe; CLOEXEC and private root sockets leave
            // no child readers. Closing it promptly exposes EPIPE while roots
            // still drain. Never retry close after EINTR: the descriptor may
            // already be closed and reused, so retrying could close another FD.
            // SAFETY: fd 0 is this helper's exclusively owned control reader.
            let _ = unsafe { libc::close(0) };
            // Trust: expose the actual refusal while blocked roots still drain.
            // Root logs remain separate, and diagnostic failure grants nothing.
            report_refusal(error);
            state.reap_after_refusal();
        }
        result
    }
}
