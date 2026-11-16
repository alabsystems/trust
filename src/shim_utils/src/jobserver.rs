// Trust: SP-1 keeps every other nonstdio descriptor out of compiler children.
use std::process::Command;

/// A jobserver adopted once, before a compiler shim opens unrelated files.
pub struct InheritedJobserver {
    #[cfg(unix)]
    transport: Option<unix::Transport>,
    #[cfg(not(unix))]
    client: Option<::jobserver::Client>,
}

impl InheritedJobserver {
    /// Validate the parent's jobserver without acquiring or releasing a token.
    /// Invalid or absent metadata is left intact for the real driver's diagnostics.
    ///
    /// # Safety
    /// Call during single-threaded shim startup, before opening unrelated files:
    /// the parent's advertised descriptors must not be closed or reused while
    /// `jobserver` validates and duplicates them.
    pub unsafe fn from_env() -> Self {
        // SAFETY: the caller owns the startup boundary described above. Requiring
        // pipes rejects an environment string naming an unrelated regular file.
        let client = unsafe { ::jobserver::Client::from_env_ext(true) }.client.ok();
        #[cfg(unix)]
        {
            Self {
                transport: client
                    .and_then(|client| unsafe { unix::Transport::from_client(&client) }),
            }
        }
        #[cfg(not(unix))]
        {
            Self { client }
        }
    }

    /// Hand this jobserver to one compiler command; no other descriptor is opted in.
    pub fn configure(&self, command: &mut Command) {
        #[cfg(unix)]
        if let Some(transport) = &self.transport {
            transport.configure(command);
        }
        #[cfg(not(unix))]
        if let Some(client) = &self.client {
            client.configure(command);
        }
    }
}

#[cfg(unix)]
mod unix {
    use std::ffi::OsString;
    use std::io;
    use std::os::fd::{AsRawFd, BorrowedFd, OwnedFd, RawFd};
    use std::os::unix::process::CommandExt;
    use std::process::Command;
    use std::sync::Arc;

    pub(super) enum Transport {
        Pipe { descriptors: Arc<[OwnedFd; 2]>, makeflags: OsString },
        Named { makeflags: OsString },
    }

    impl Transport {
        // SAFETY: the caller keeps the validated originals live during startup.
        pub(super) unsafe fn from_client(client: &::jobserver::Client) -> Option<Self> {
            // Read the validated library's canonical protocol, never raw MAKEFLAGS.
            // jobserver 0.1.34 advertises the original R,W, while its pre_exec
            // hook clears CLOEXEC on internal duplicates. Under SP-1 those are
            // different descriptors, so configure alone cannot forward R,W.
            let mut metadata = Command::new("bootstrap-jobserver-metadata");
            client.configure(&mut metadata); // This command is never executed.
            let makeflags =
                metadata.get_envs().find(|(key, _)| *key == "CARGO_MAKEFLAGS")?.1?.to_owned();
            let auth = makeflags
                .to_str()?
                .split_whitespace()
                .find_map(|part| part.strip_prefix("--jobserver-auth="))?;
            if auth.starts_with("fifo:") {
                // The child opens a named FIFO itself; no descriptor is inherited.
                return Some(Self::Named { makeflags });
            }
            let (read, write) = auth.split_once(',')?;
            let read: RawFd = read.parse().ok()?;
            let write: RawFd = write.parse().ok()?;
            // SAFETY: from_env_ext(true) validated these inherited pipes, and the
            // startup caller keeps them open until these owned copies are made.
            let read = unsafe { BorrowedFd::borrow_raw(read) }.try_clone_to_owned().ok()?;
            // SAFETY: the same startup guarantee applies to the write endpoint.
            let write = unsafe { BorrowedFd::borrow_raw(write) }.try_clone_to_owned().ok()?;
            let makeflags = format!(
                "-j --jobserver-fds={},{} --jobserver-auth={},{}",
                read.as_raw_fd(),
                write.as_raw_fd(),
                read.as_raw_fd(),
                write.as_raw_fd(),
            )
            .into();
            Some(Self::Pipe { descriptors: Arc::new([read, write]), makeflags })
        }

        pub(super) fn configure(&self, command: &mut Command) {
            match self {
                Self::Named { makeflags } => {
                    command.env("CARGO_MAKEFLAGS", makeflags);
                }
                Self::Pipe { descriptors, makeflags } => {
                    command.env("CARGO_MAKEFLAGS", makeflags);
                    // Keep the exact owned descriptors alive as long as the
                    // command, even if the startup adapter is dropped first.
                    let descriptors = Arc::clone(descriptors);
                    // SAFETY: after std's strip, the child only calls async-signal-
                    // safe fcntl on these two pinned descriptors. No global opt-out.
                    unsafe {
                        command.pre_exec(move || {
                            for descriptor in descriptors.iter() {
                                let fd = descriptor.as_raw_fd();
                                let flags = libc::fcntl(fd, libc::F_GETFD);
                                if flags == -1
                                    || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC)
                                        == -1
                                {
                                    return Err(io::Error::last_os_error());
                                }
                            }
                            Ok(())
                        });
                    }
                }
            }
        }
    }
}
