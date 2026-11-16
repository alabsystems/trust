//! Ordinary native child ownership inside an already owned fixed group.
//! The outer launcher alone owns group signals and retirement. This owner
//! never constructs a fixed claim, SDK, completed runtime or ClosedRoot.

#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
use std::ffi::OsStr;
use std::ffi::OsString;
use std::io;
#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
use std::path::PathBuf;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use std::process::{Command, ExitStatus};
#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
use std::time::Duration;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use std::time::Instant;

use jobserver_utils::Jobserver;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use trust_resource_provenance::program::HeldSystemCommand;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use super::{Acquire, Lease, LeaseAcquisition, Manager};
#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
use super::{Kind, invalid};
use crate::admission::EarlyFixedClaim;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use crate::admission::InheritedFixedClaim;

pub const PROTOCOL: &str = "trust-build-tree-exec-v1";
pub const USAGE: &str = "Usage: targo --unverified resource fixed [sizing] -- repo-lock-exec [--kind build|measurement] [--repo-root DIR] [--purpose TEXT] [--wait SECONDS] -- ABSOLUTE_NATIVE_PROGRAM [args...]\nOriginal fixed/GNU custody and console streams are retained through the actual child wait. Native system libraries only. This is ordinary execution, not a completed runtime, SDK or hosted-root settlement. Runtime sessions are unavailable until authenticated original Host custody exists.\n";

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) mod native;

#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
struct Options {
    root: Option<PathBuf>,
    kind: Kind,
    purpose: String,
    wait: Duration,
    command: Vec<OsString>,
}

#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
fn parse(args: &[OsString]) -> io::Result<Options> {
    if args.len() > 1024
        || args.iter().map(|arg| arg.as_encoded_bytes().len()).sum::<usize>() > 1024 * 1024
    {
        return Err(invalid("native exec argument population exceeds bound"));
    }
    // Never start a costly producer by treating a missing Host profile as an
    // ordinary child. The flag is a route selector, not a capability.
    if args.iter().take_while(|arg| *arg != "--").any(|arg| arg == "--runtime-session") {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "runtime session requires authenticated original Host input and release custody; no command started",
        ));
    }
    let split = args
        .iter()
        .position(|arg| arg == "--")
        .ok_or_else(|| invalid("native exec requires -- before its exact program"))?;
    let command = args[split + 1..].to_vec();
    if command.is_empty() || !std::path::Path::new(&command[0]).is_absolute() {
        return Err(invalid("native exec requires an absolute program; no PATH or shell fallback"));
    }
    let mut values = std::collections::BTreeMap::new();
    let mut index = 0;
    while index < split {
        let key = args[index].to_str().ok_or_else(|| invalid("native exec option must be UTF8"))?;
        if !matches!(key, "--repo-root" | "--kind" | "--purpose" | "--wait") || index + 1 >= split {
            return Err(invalid("unknown or incomplete native exec option"));
        }
        if values.insert(key, args[index + 1].clone()).is_some() {
            return Err(invalid("duplicate native exec option"));
        }
        index += 2;
    }
    let kind = match values.remove("--kind").as_deref().and_then(OsStr::to_str) {
        None | Some("build") => Kind::Build,
        Some("measurement") => Kind::Measurement,
        _ => return Err(invalid("native exec kind must be build or measurement")),
    };
    let wait = match values.remove("--wait") {
        None => 0,
        Some(value) => value
            .to_str()
            .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
            .and_then(|text| text.parse::<u64>().ok())
            .filter(|seconds| *seconds <= 7 * 24 * 3600)
            .ok_or_else(|| invalid("native exec wait exceeds its seven-day bound"))?,
    };
    let purpose = values
        .remove("--purpose")
        .map(|value| value.into_string().map_err(|_| invalid("native exec purpose must be UTF8")))
        .transpose()?
        .unwrap_or_else(|| "native held child".into());
    Ok(Options {
        root: values.remove("--repo-root").map(PathBuf::from),
        kind,
        purpose,
        wait: Duration::from_secs(wait),
        command,
    })
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn input_deadline() -> io::Result<Instant> {
    Instant::now()
        .checked_add(Duration::from_secs(30))
        .ok_or_else(|| invalid("native input deadline overflows"))
}

/// Called only with the native CLI's already captured original scheduler and
/// the fixed originals snapshotted before its first descriptor allocation.
/// Neither an environment locator nor these observations creates a new grant.
pub fn run(
    args: &[OsString],
    scheduler: Option<&Jobserver>,
    early: Option<EarlyFixedClaim>,
) -> io::Result<i32> {
    if args == [OsString::from("--help")] {
        print!("{USAGE}");
        return Ok(0);
    }
    if args == [OsString::from("--protocol")] {
        println!("{PROTOCOL}");
        return Ok(0);
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        let _ = (scheduler, early);
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "native held command profile is unavailable",
        ));
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        let options = parse(args)?;
        for (name, _) in std::env::vars_os() {
            if name.as_encoded_bytes().starts_with(b"DYLD_")
                || name.as_encoded_bytes().starts_with(b"LD_")
            {
                return Err(invalid("native exec refuses ambient loader overrides"));
            }
        }
        let fixed = early
            .ok_or_else(|| invalid("native exec requires the original outer fixed admission"))?
            .capture()?;
        let mut scheduler = scheduler
            .ok_or_else(|| invalid("native exec requires its original outer GNU transport"))?
            .clone();
        scheduler.enable_descendant_handoff()?;
        let image =
            HeldSystemCommand::open(std::path::Path::new(&options.command[0]), input_deadline()?)?;
        // Initial supported exec profile is the checked Bootstrap producer.
        // An older/unaware image cannot silently ignore its original ceiling.
        image.require_bootstrap_fixed_protocol(
            &crate::bootstrap_protocol::BOOTSTRAP_FIXED_PROTOCOL_MARKER,
            input_deadline()?,
        )?;
        let mut environment = super::cli::Environment::default();
        environment.root = std::env::var_os("TRUST_REPO");
        let root =
            options.root.map(Ok).unwrap_or_else(|| super::cli::default_root(&environment))?;
        let manager = Manager::open(&root)?;
        let lease = match manager.acquire_lease(&Acquire {
            kind: options.kind,
            owner_pid: std::process::id(),
            purpose: options.purpose,
            contract:
                "original native child and independently observed surviving writers retain the tree"
                    .into(),
            wait: options.wait,
            inherited_token: std::env::var("TRUST_BUILD_LOCK_TOKEN").ok(),
            break_reason: None,
        })? {
            LeaseAcquisition::Granted(lease) => lease,
            LeaseAcquisition::Busy(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::WouldBlock,
                    "native build-tree owner is busy; no child started",
                ));
            }
        };
        let mut command = Command::new(image.program());
        command.args(&options.command[1..]);
        lease.configure_child(&mut command)?;
        scheduler.configure_make(&mut command);
        command.env(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV, fixed.descendant_advertisement()?);
        // Raw inherited numbers cannot survive unaware spawns. Older readers
        // must refuse rather than ignore the new original-rights courier.
        command.env(crate::admission::FIXED_HANDOFF_ENV, "requires-live-ancestor-v1");
        fixed.check_current()?;
        lease.check_current()?;
        image.validate(input_deadline()?)?;
        let launch_deadline = input_deadline()?;
        let child = native::Child::spawn_suspended(&command, &scheduler, launch_deadline)?;
        let mut owner = Running { child, image, fixed, scheduler, lease, finished: false };
        // posix_spawn has loaded the image but has not allowed its user entry.
        // A pathname replacement must be refused and reaped before it can
        // consume the original scheduling/Manager handoff.
        let identity = owner.child.stopped_identity(launch_deadline)?;
        owner.image.validate_loaded(identity, launch_deadline)?;
        owner.fixed.check_current()?;
        owner.lease.check_current()?;
        owner.child.resume(identity, launch_deadline)?;
        let status = owner.wait()?;
        use std::os::unix::process::ExitStatusExt as _;
        Ok(status.code().unwrap_or_else(|| 128 + status.signal().unwrap_or(1)))
    }
}

/// Only the original Child's owning wait can finish this direct-child owner.
/// Kept private: a PID or saved terminal cannot manufacture it.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
struct Running {
    child: native::Child,
    image: HeldSystemCommand,
    fixed: InheritedFixedClaim,
    scheduler: Jobserver,
    lease: Lease,
    finished: bool,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl Running {
    fn wait(&mut self) -> io::Result<ExitStatus> {
        loop {
            if let Some(status) = self.child.try_wait()? {
                self.finished = true;
                self.fixed.check_current()?;
                self.lease.check_current()?;
                self.image.validate(input_deadline()?).map_err(|error| {
                    io::Error::new(
                        error.kind(),
                        format!("actual child {status}; original input recheck failed: {error}"),
                    )
                })?;
                return Ok(status);
            }
            self.fixed.check_current()?;
            self.lease.check_current()?;
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl Drop for Running {
    fn drop(&mut self) {
        // Errors/unwind cancel only OUR original direct child, never the
        // ancestor's group. Keep every actual owner alive until its own wait.
        while !self.finished {
            let _ = self.child.kill();
            match self.child.wait() {
                Ok(_) => self.finished = true,
                Err(_) => std::thread::sleep(Duration::from_millis(100)),
            }
        }
        let _ = &self.scheduler;
    }
}

#[cfg(test)]
mod tests;
