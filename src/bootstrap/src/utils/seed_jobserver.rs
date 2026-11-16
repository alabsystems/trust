//! Trust: the named jobserver Bootstrap gives a seed Cargo (BOOTSTRAP-JOBSERVER-PROBE-1).
//!
//! A seed Cargo without `CARGO_JOBSERVER_HANDOFF` gives its build scripts a numeric
//! `--jobserver-auth=R,W` pipe. Trust std gives a spawned child only its stdio, so a
//! build script's compiler probe (rustix's `can_compile`, autocfg) reaches the
//! Bootstrap shim advertising closed descriptors, and the shim refuses, as it must:
//! an advertised server it cannot import is never a private budget. The probe's cfg
//! is then lost, or the build script dies writing to the refused probe.
//!
//! A named FIFO is opened by its path, so it survives that strip. When no FIFO is
//! inherited, Bootstrap makes one the way GNU make 4.4 does for its children: a
//! private directory under the build's `tmp`, holding a mode-0600 FIFO with
//! `jobs - 1` tokens (every client already holds one implicit token). Its owner, the
//! `Builder` that composes seed Cargo commands, keeps the FIFO open for reading and
//! writing while it lives, so no reader sees EOF and no writer EPIPE between Cargo
//! runs, and removes it when it is dropped. An exit handler removes the names of
//! servers still live when the process exits without dropping them (`exit!`,
//! `std::process::exit`); a later Bootstrap holding the build lock removes the ones a
//! signal left, once no process holds them open.
//!
//! The FIFO carries the configured job count and nothing more. It grants no proof
//! or compiler authority, and the shim's refusal of an invalid server is unchanged.

use std::ffi::CString;
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{
    FileTypeExt as _, MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _,
};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};
use std::{fs, io};

use jobserver_utils::Jobserver;

use crate::utils::exec::BootstrapCommand;

pub(crate) const FIFO_NAME: &str = "jobserver.fifo";
pub(crate) const DIRECTORY_PREFIX: &str = "seed-jobserver-";

/// One owned named jobserver. Dropping it removes its FIFO and directory.
pub(crate) struct SeedJobserver {
    directory: PathBuf,
    path: PathBuf,
    jobs: u32,
    // Holds the FIFO's read and write descriptions for this owner's lifetime. Outside the
    // tests it is never read: holding it is its whole purpose.
    #[cfg_attr(not(test), allow(dead_code))]
    server: Jobserver,
}

impl SeedJobserver {
    /// The seed jobserver of one build: under `parent` (the build's `tmp`), or in
    /// the system temporary directory when GNU flags cannot carry a path under
    /// `parent` (relative, not UTF-8, whitespace), as GNU make 4.4 makes its own.
    /// That choice is made before anything is created; every error after it
    /// stops, so a refused node is never retried elsewhere. With `remove_stale`
    /// (the caller holds the build lock), servers a killed Bootstrap left under
    /// `parent` are removed first; never in the shared system directory.
    pub(crate) fn for_build(parent: &Path, jobs: u32, remove_stale: bool) -> io::Result<Self> {
        let requested = advertisable(parent);
        let parent = if requested { parent.to_owned() } else { std::env::temp_dir() };
        let _creating = creation_lock();
        if remove_stale && requested {
            remove_stale_servers(&parent);
        }
        Self::create_locked(&parent, jobs)
    }

    /// Make a private directory under `parent`, a mode-0600 FIFO in it, open
    /// the FIFO and put `jobs - 1` tokens in it. Nothing is left behind on error.
    /// Builds reach it through `for_build`; only the tests call it directly.
    #[cfg(test)]
    pub(crate) fn create(parent: &Path, jobs: u32) -> io::Result<Self> {
        let _creating = creation_lock();
        Self::create_locked(parent, jobs)
    }

    fn create_locked(parent: &Path, jobs: u32) -> io::Result<Self> {
        if !advertisable(parent) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "GNU flags cannot carry a seed jobserver under {} (relative, not UTF-8 or \
                     whitespace)",
                    parent.display()
                ),
            ));
        }
        fs::create_dir_all(parent)?;
        // A fresh private directory: no other user can replace the FIFO's name.
        let directory = tempfile::Builder::new()
            .prefix(DIRECTORY_PREFIX)
            .permissions(fs::Permissions::from_mode(0o700))
            .tempdir_in(parent)?;
        // mkdir's and mkfifo's modes pass through the umask, which can only
        // remove bits; set both exactly, so the owner can always use them.
        fs::set_permissions(directory.path(), fs::Permissions::from_mode(0o700))?;
        let path = directory.path().join(FIFO_NAME);
        let name = CString::new(path.as_os_str().as_bytes())
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
        // SAFETY: `name` is a valid C string naming a new entry in our private directory.
        if unsafe { libc::mkfifo(name.as_ptr(), 0o600) } != 0 {
            return Err(io::Error::last_os_error());
        }
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600))?;
        // The library also refuses a symlink or a non-FIFO, and a node
        // replaced between its two opens.
        let server = Jobserver::from_fifo(&path)?;
        for _ in 1..jobs {
            server.client().release_raw()?;
        }
        register_exit_removal()?;
        let directory = directory.keep();
        live_names().push((directory.clone(), path.clone()));
        Ok(Self { directory, path, jobs, server })
    }

    /// The GNU make 4.4 spelling: Cargo's jobserver crate reads it, and every
    /// Cargo hands the same `fifo:` path on to build scripts and compilers.
    pub(crate) fn makeflags(&self) -> String {
        // `create` accepted the path, so it is UTF-8.
        format!("-j{} --jobserver-auth=fifo:{}", self.jobs, self.path.to_str().unwrap())
    }

    /// Hand this jobserver to a seed Cargo, replacing every other GNU advertisement.
    pub(crate) fn configure(&self, cargo: &mut BootstrapCommand) {
        cargo.env("MAKEFLAGS", self.makeflags());
        cargo.env_remove("MFLAGS");
        // The jobserver crate reads CARGO_MAKEFLAGS before MAKEFLAGS.
        cargo.env_remove("CARGO_MAKEFLAGS");
        // An inherited handoff names another pool's witnesses. Beside this FIFO
        // the shim would try to authenticate them against it, and refuse.
        cargo.env_remove(jobserver_utils::DESCENDANT_HANDOFF_ENV);
    }
}

impl Drop for SeedJobserver {
    fn drop(&mut self) {
        live_names().retain(|(directory, _)| *directory != self.directory);
        let _ = fs::remove_file(&self.path);
        let _ = fs::remove_dir(&self.directory);
    }
}

/// Whether GNU flags can carry a FIFO path under `parent`: the same test
/// `Jobserver::from_fifo` applies (the directory and FIFO names this module
/// adds are alphanumeric).
fn advertisable(parent: &Path) -> bool {
    parent.is_absolute()
        && parent.to_str().is_some_and(|text| !text.chars().any(char::is_whitespace))
}

// The directory and FIFO of every live server, for the exit handler.
static LIVE_NAMES: Mutex<Vec<(PathBuf, PathBuf)>> = Mutex::new(Vec::new());
static EXIT_HANDLER: OnceLock<bool> = OnceLock::new();
// A server is registered only once its FIFO is open, so this process never
// removes a directory one of its own threads is still filling.
static CREATION: Mutex<()> = Mutex::new(());

fn creation_lock() -> std::sync::MutexGuard<'static, ()> {
    CREATION.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn live_names() -> std::sync::MutexGuard<'static, Vec<(PathBuf, PathBuf)>> {
    // The registry holds plain paths; a panic elsewhere cannot leave it inconsistent.
    LIVE_NAMES.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn register_exit_removal() -> io::Result<()> {
    // SAFETY: registers a plain function; it runs once, when the process exits.
    if *EXIT_HANDLER.get_or_init(|| unsafe { libc::atexit(remove_at_exit) } == 0) {
        Ok(())
    } else {
        Err(io::Error::other("cannot register the seed jobserver's removal at exit"))
    }
}

// `std::process::exit` and a return from `main` both run this; a signal does not.
extern "C" fn remove_at_exit() {
    // Never block an exiting process on a thread that holds the registry.
    if let Ok(live) = LIVE_NAMES.try_lock() {
        for (directory, path) in live.iter() {
            let _ = fs::remove_file(path);
            let _ = fs::remove_dir(directory);
        }
    }
}

/// Remove the seed jobservers under `parent` that no process holds open: a
/// directory named by this module, owned by this user and not a live server of
/// this process, holding nothing but a FIFO with no reader (or nothing). A
/// directory with anything else in it, or a FIFO some process still holds (a
/// live Bootstrap, or a Cargo that outlived a killed one), is left alone. Best
/// effort: what cannot be judged stays.
fn remove_stale_servers(parent: &Path) {
    let Ok(entries) = fs::read_dir(parent) else { return };
    // SAFETY: getuid has no preconditions.
    let uid = unsafe { libc::getuid() };
    for entry in entries.flatten() {
        if !entry.file_name().as_bytes().starts_with(DIRECTORY_PREFIX.as_bytes()) {
            continue;
        }
        let directory = entry.path();
        if live_names().iter().any(|(live, _)| *live == directory) {
            continue;
        }
        match fs::symlink_metadata(&directory) {
            Ok(metadata) if metadata.is_dir() && metadata.uid() == uid => {}
            _ => continue,
        }
        let Ok(names) = fs::read_dir(&directory) else { continue };
        let names: Result<Vec<_>, _> =
            names.map(|name| name.map(|name| name.file_name())).collect();
        if !names.is_ok_and(|names| names.iter().all(|name| name == FIFO_NAME)) {
            continue;
        }
        let fifo = directory.join(FIFO_NAME);
        match fs::symlink_metadata(&fifo) {
            Ok(metadata) if metadata.file_type().is_fifo() => {
                if !unread(&fifo) {
                    continue;
                }
                let _ = fs::remove_file(&fifo);
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            _ => continue,
        }
        // Only an empty directory goes.
        let _ = fs::remove_dir(&directory);
    }
}

/// A FIFO no process has open for reading: a nonblocking open for writing
/// fails with ENXIO (POSIX). A live server holds a reader for its lifetime.
fn unread(fifo: &Path) -> bool {
    match fs::OpenOptions::new()
        .write(true)
        .custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(fifo)
    {
        Ok(_) => false,
        Err(error) => error.raw_os_error() == Some(libc::ENXIO),
    }
}

/// Whether `directory` is a live server's, for the exit handler.
#[cfg(test)]
pub(crate) fn is_live(directory: &Path) -> bool {
    live_names().iter().any(|(live, _)| live == directory)
}

#[cfg(test)]
impl SeedJobserver {
    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn directory(&self) -> &Path {
        &self.directory
    }
}

#[cfg(test)]
mod tests;
