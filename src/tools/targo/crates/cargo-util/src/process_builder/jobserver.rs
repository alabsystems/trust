// Trust: exact shared jobserver custody, compatible with stock std and SP-1.
use std::ffi::{OsStr, OsString};
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::{Arc, Mutex, Weak};

#[derive(Clone, Copy, PartialEq, Eq)]
struct PipeIdentity {
    device: u64,
    inode: u64,
    access: libc::c_int,
}

type SharedPipe = Arc<[OwnedFd; 2]>;
type CachedPipe = ([PipeIdentity; 2], Weak<[OwnedFd; 2]>);

// Queued compiler units can retain thousands of distinct ProcessBuilders for
// one client. Keep two descriptors per live transport, not two per queued unit.
// Weak entries never keep a pipe alive after its last builder/command drops.
static PIPES: Mutex<Vec<CachedPipe>> = Mutex::new(Vec::new());

#[derive(Clone, Debug)]
pub(super) enum JobserverTransport {
    Pipe {
        endpoints: Arc<[OwnedFd; 2]>,
        makeflags: OsString,
    },
    Named {
        makeflags: OsString,
    },
    Invalid {
        errno: i32,
        kind: io::ErrorKind,
        message: Arc<str>,
    },
}

impl JobserverTransport {
    pub(super) fn capture(client: &jobserver::Client) -> Self {
        Self::try_capture(client).unwrap_or_else(|error| Self::Invalid {
            errno: error.raw_os_error().unwrap_or(libc::EINVAL),
            kind: error.kind(),
            message: error.to_string().into(),
        })
    }

    fn try_capture(client: &jobserver::Client) -> io::Result<Self> {
        // Read only the client's canonical protocol. This command is never
        // executed; ambient MAKEFLAGS never grants descriptor authority here.
        let mut metadata = Command::new("__cargo_jobserver_metadata_only__");
        client.configure(&mut metadata);
        let makeflags = metadata
            .get_envs()
            .find(|(key, _)| *key == "CARGO_MAKEFLAGS")
            .and_then(|(_, value)| value)
            .ok_or_else(|| invalid("jobserver client supplied no canonical metadata"))?;
        let auth = makeflags
            .to_str()
            .and_then(|flags| {
                flags
                    .split_whitespace()
                    .find_map(|part| part.strip_prefix("--jobserver-auth="))
            })
            .ok_or_else(|| invalid("jobserver client supplied no canonical transport"))?;
        if auth.starts_with("fifo:") {
            // The child opens a named FIFO; no descriptor handoff is needed.
            return Ok(Self::Named {
                makeflags: makeflags.to_owned(),
            });
        }
        let (read, write) = auth
            .split_once(',')
            .ok_or_else(|| invalid("jobserver client supplied no numeric pipe pair"))?;
        let read = read
            .parse()
            .map_err(|_| invalid("invalid jobserver read descriptor"))?;
        let write = write
            .parse()
            .map_err(|_| invalid("invalid jobserver write descriptor"))?;
        // Validate and duplicate before looking in the registry. A previously
        // captured pipe never makes closed or reused source numbers valid.
        let endpoints = shared_pipe(duplicate_pipe(read)?, duplicate_pipe(write)?)?;
        let makeflags = format!(
            "-j --jobserver-fds={},{} --jobserver-auth={},{}",
            endpoints[0].as_raw_fd(),
            endpoints[1].as_raw_fd(),
            endpoints[0].as_raw_fd(),
            endpoints[1].as_raw_fd()
        )
        .into();
        Ok(Self::Pipe {
            endpoints,
            makeflags,
        })
    }

    pub(super) fn makeflags(&self) -> io::Result<&OsStr> {
        match self {
            Self::Pipe { makeflags, .. } | Self::Named { makeflags } => Ok(makeflags),
            Self::Invalid { kind, message, .. } => Err(io::Error::new(*kind, message.to_string())),
        }
    }

    pub(super) fn configure(&self, command: &mut Command) {
        match self {
            Self::Named { makeflags } => {
                command.env("CARGO_MAKEFLAGS", makeflags);
            }
            Self::Pipe {
                endpoints,
                makeflags,
            } => {
                command.env("CARGO_MAKEFLAGS", makeflags);
                let endpoints = Arc::clone(endpoints);
                // SAFETY: keep precisely these owned copies live through fork.
                // After std's strip, only async-signal-safe fcntl calls run.
                unsafe {
                    command.pre_exec(move || {
                        for endpoint in endpoints.iter() {
                            let fd = endpoint.as_raw_fd();
                            let flags = libc::fcntl(fd, libc::F_GETFD);
                            if flags == -1
                                || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) == -1
                            {
                                return Err(io::Error::last_os_error());
                            }
                        }
                        Ok(())
                    });
                }
            }
            Self::Invalid { errno, .. } => {
                let errno = *errno;
                // SAFETY: refuse before exec without allocation, env mutation,
                // token acquisition or falling back to an unrelated jobserver.
                unsafe {
                    command.pre_exec(move || Err(io::Error::from_raw_os_error(errno)));
                }
            }
        }
    }
}

fn shared_pipe(read: OwnedFd, write: OwnedFd) -> io::Result<SharedPipe> {
    let identities = [pipe_identity(&read)?, pipe_identity(&write)?];
    let mut pipes = PIPES
        .lock()
        .map_err(|_| io::Error::other("jobserver transport registry poisoned"))?;
    pipes.retain(|(_, pipe)| pipe.strong_count() != 0);
    if let Some(pipe) = pipes
        .iter()
        .find_map(|(identity, pipe)| (*identity == identities).then(|| pipe.upgrade()).flatten())
    {
        return Ok(pipe);
    }
    let pipe = Arc::new([read, write]);
    pipes.push((identities, Arc::downgrade(&pipe)));
    Ok(pipe)
}

fn pipe_identity(fd: &OwnedFd) -> io::Result<PipeIdentity> {
    let mut info = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: the owned descriptor stays live and stat has writable storage.
    if unsafe { libc::fstat(fd.as_raw_fd(), info.as_mut_ptr()) } == -1 {
        return Err(io::Error::last_os_error());
    }
    let info = unsafe { info.assume_init() };
    // SAFETY: F_GETFL only queries the live descriptor. Access mode distinguishes
    // the read/write ends on systems whose pipe stat identities are identical.
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    if flags == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(PipeIdentity {
        device: info.st_dev as u64,
        inode: info.st_ino as u64,
        access: flags & libc::O_ACCMODE,
    })
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn duplicate_pipe(fd: RawFd) -> io::Result<OwnedFd> {
    // SAFETY: fcntl validates the integer; do not borrow an unchecked raw FD.
    // Its successful result is a fresh, uniquely owned CLOEXEC descriptor.
    let copy = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if copy == -1 {
        return Err(io::Error::last_os_error());
    }
    let copy = unsafe { OwnedFd::from_raw_fd(copy) };
    let mut info = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: the owned descriptor stays live and stat has writable storage.
    if unsafe { libc::fstat(copy.as_raw_fd(), info.as_mut_ptr()) } == -1 {
        return Err(io::Error::last_os_error());
    }
    let info = unsafe { info.assume_init() };
    if info.st_mode & libc::S_IFMT != libc::S_IFIFO {
        return Err(invalid("jobserver descriptor is not a pipe"));
    }
    Ok(copy)
}
