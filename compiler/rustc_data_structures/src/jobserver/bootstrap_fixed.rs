// Trust: actual private Bootstrap compiler custody. Distinct from cooperative
// NativeV3: no WorkerClient, CPU Lease, private pool or fresh implicit is made.
use std::fs::File;
use std::io::{self, Read};
use std::os::fd::{AsFd, OwnedFd};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::MetadataExt as _;
use std::sync::Arc;
use std::time::{Duration, Instant};

use trust_resource_controller::bootstrap_graph::GnuIdentity;
use trust_resource_controller::bootstrap_graph::compilation::compiler::AdoptRequest;
use trust_resource_controller::bootstrap_graph::transport::check_gnu_identity;
use trust_resource_controller::client::bootstrap_graph::CompilerMember;
use trust_resource_controller::{BirthKind, ContextQuery, FileIdentity, Identity, JobBinding};
use trust_resource_provenance::process;

use super::admission::Client;

pub struct BootstrapFixed {
    member: Arc<CompilerMember>,
    registry: Arc<super::native_park::Registry>,
    extras: jobserver_utils::quiescence::Client,
}
impl BootstrapFixed {
    pub(super) fn registry(&self) -> &Arc<super::native_park::Registry> {
        &self.registry
    }
    pub(super) fn extras(&self) -> &jobserver_utils::quiescence::Client {
        &self.extras
    }
    pub fn member(&self) -> &Arc<CompilerMember> {
        &self.member
    }
    pub fn try_pause(self: &Arc<Self>) -> io::Result<Option<super::BootstrapCompilerPause>> {
        super::BootstrapCompilerPause::acquire(self)
    }
}
fn refused(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message)
}
fn witnesses(local: &jobserver_crate::Client) -> io::Result<([OwnedFd; 2], GnuIdentity)> {
    let (read, write, path) = match local.transport_witnesses()? {
        jobserver_crate::TransportWitnesses::NumericPipe { read, write } => (read, write, None),
        jobserver_crate::TransportWitnesses::NamedFifo { read, write, path } => {
            (read, write, Some(path))
        }
    };
    let identity = |fd: &OwnedFd| -> io::Result<FileIdentity> {
        let meta = File::from(fd.try_clone()?).metadata()?;
        Ok(FileIdentity { device: meta.dev(), inode: meta.ino() })
    };
    let (a, b) = (identity(&read)?, identity(&write)?);
    let gnu = match path {
        Some(path) if a == b => {
            GnuIdentity::NamedFifo { path: path.as_os_str().as_bytes().to_vec(), backing: a }
        }
        Some(_) => return Err(refused("private compiler GNU FIFO witnesses differ")),
        None => GnuIdentity::NumericPipe { read: a, write: b },
    };
    let fds = [read, write];
    check_gnu_identity(&gnu, &fds.each_ref().map(AsFd::as_fd))?;
    Ok((fds, gnu))
}
pub(super) fn activate(local: jobserver_crate::Client) -> io::Result<Client> {
    // This protocol carries the SAME queued Fixed primary, never a cooperative
    // workload CPU FD. A conflicting early advertisement cannot be promoted.
    if super::early::take_workload_cpu().map_err(io::Error::other)?.is_some() {
        return Err(refused("private Fixed compiler cannot adopt a cooperative CPU handoff"));
    }
    let locator = std::env::var_os("ATERM_RESOURCE_JOB_V3")
        .ok_or_else(|| refused("private Fixed compiler has no original job locator"))?;
    let binding = JobBinding::from_locator(
        locator.to_str().ok_or_else(|| refused("private Fixed compiler locator is not UTF-8"))?,
    )?;
    let mut nonce = [0; 16];
    let mut random = File::open("/dev/urandom")?;
    while nonce == [0; 16] || nonce == binding.root_attempt {
        random.read_exact(&mut nonce)?;
    }
    let at = Instant::now() + Duration::from_secs(8);
    let controller = super::early::take_host_controller(at).map_err(io::Error::other)?;
    let actual = process::read_identity(std::process::id())?;
    let compiler = Identity {
        pid: actual.pid,
        birth: actual.birth,
        #[cfg(target_os = "macos")]
        birth_kind: BirthKind::MacosWallMicroseconds,
        #[cfg(target_os = "linux")]
        birth_kind: BirthKind::LinuxStartTicks,
    };
    let (gnu, identity) = witnesses(&local)?;
    // The flag/locator are DATA only. This private native issuer must validate
    // the actual registered compiler/NoFork target/held runtime/Root+GNU owner.
    let member = controller
        .adopt_bootstrap_fixed_compiler(
            AdoptRequest {
                query: ContextQuery { binding, call_attempt: nonce },
                compiler,
                gnu: identity,
            },
            gnu,
            at,
        )
        .map_err(io::Error::other)?;
    member.check_current(at)?;
    let custody = Arc::new(BootstrapFixed {
        member,
        registry: super::native_park::Registry::new(),
        extras: jobserver_utils::quiescence::Client::new(local.clone()),
    });
    Ok(Client::with_bootstrap_fixed(local, custody))
}

// Trust: actual GNU transport controls only, never native adoption/CPU fixtures.
#[cfg(test)]
#[path = "bootstrap_fixed/tests.rs"]
mod tests;
