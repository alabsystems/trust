//! Trust (DC-24a): a unit source, a program the build names that may hold a
//! shared dependency unit staged elsewhere.
//!
//! With [`UNIT_SOURCE_ENV`] naming a program, a native unverified build that
//! shares dependencies asks it for a shared unit whose check under the unit's
//! lock missed. Targo starts the program once per build at its first ask, as a
//! child it talks to over pipes, and sends one JSON line: the version, the
//! unit's key (the SHA-256 of the fingerprint record this build computed) and a
//! new staging folder inside the store, private as the store is. The program
//! may send `working` lines while it stages, and then answers with one line,
//! `staged` or `none`. A staged unit is laid out as the unit's own directory
//! (`fingerprint/` and `out/`), each file a copy or clone the source owns
//! alone (never a hard link to its own cache). Targo takes only the unit's
//! planned files from it, and only when the staged fingerprint record is the
//! computed one; then it asks for the check again, and the unit is taken when
//! that check passes (the fingerprint, and the outputs against their receipt),
//! and refused with a reason otherwise, in which case the files it placed are
//! removed and it compiles.
//!
//! A program that is silent for [`SILENCE`] (including a write to it that does
//! not complete), does not answer an ask within [`ASK_LIMIT`], exits, answers
//! anything else (a line before it is asked included) or cannot be started is
//! passed over for the rest of the build and killed. When the build ends its
//! input is closed, it has [`SILENCE`] to exit before it is killed, and the
//! build's staging folder is removed. With no program named, builds run as
//! before, and the verified lane never asks (it never shares). The ask runs on
//! the unit's worker, never on the coordinator.

use std::fs;
use std::io::{BufRead as _, BufReader, Read as _, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Child, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender, TryRecvError, TrySendError};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use cargo_util::{ProcessBuilder, Sha256};
use tracing::{debug, warn};

use super::job_queue::JobState;
use super::{BuildRunner, Unit, UnitIndex};
use crate::CargoResult;
use crate::GlobalContext;
use crate::util::log_message::{LogMessage, SharedDependencyDecision, UnitSourceRefusal};
use crate::util::machine_message::UnitRebuildCause;

/// The variable that names the unit source. It is Targo-internal: no process
/// the build starts (compiler, build script, test or run) sees it.
pub(crate) const UNIT_SOURCE_ENV: &str = "TRUST_TARGO_UNIT_SOURCE";

/// How long the source may stay silent before it is passed over: a write to
/// it must complete, and a line (`working` or the answer) must come, within
/// this. It is also how long the source has to exit when the build ends.
pub(crate) const SILENCE: Duration = Duration::from_secs(2);

/// How long one ask may last however often the source says it is `working`.
/// Every other ask of the build waits behind it, so it bounds that wait too.
pub(crate) const ASK_LIMIT: Duration = Duration::from_secs(120);

/// The longest reply line read (`staged`, `none` or `working` and a newline).
const REPLY_LIMIT: u64 = 64;

/// The mode a placed file gets: written by this user alone, as the store's
/// own files are, so a later compile of the unit can rewrite it in place.
#[cfg(unix)]
const PLACED_MODE: u32 = 0o644;

const PROTOCOL_VERSION: u32 = 1;

/// The build's unit source, started at its first ask.
pub(crate) struct UnitSource {
    program: PathBuf,
    /// `<store>/staging/<build>`, made at the first ask and removed with the
    /// source when the build ends.
    staging: PathBuf,
    state: Mutex<State>,
    /// Set once the source is passed over. The coordinator reads it without
    /// the lock, which an ask on a worker may hold for up to [`ASK_LIMIT`].
    passed_over: AtomicBool,
}

enum State {
    Unstarted,
    Running(Running),
    PassedOver,
}

struct Running {
    child: Child,
    /// The asks, written to the source's input by a thread of their own, so
    /// a source that stops reading cannot block the asking worker. Holds at
    /// most one ask: a second finds it full while the first is unwritten.
    asks: SyncSender<Vec<u8>>,
    /// The source's lines. Holds at most one, so a source that writes without
    /// being asked cannot grow Targo's memory.
    replies: Receiver<Result<String, String>>,
    count: u64,
}

impl Running {
    /// Closes the source's input, gives it `grace` to exit, then kills it.
    fn stop(self, grace: Duration) {
        let Running {
            mut child, asks, ..
        } = self;
        // The writer thread ends with its channel and drops the source's input.
        drop(asks);
        let deadline = Instant::now() + grace;
        while Instant::now() < deadline {
            match child.try_wait() {
                Ok(Some(_)) => return,
                Ok(None) => std::thread::sleep(Duration::from_millis(10)),
                Err(_) => break,
            }
        }
        let _ = child.kill();
        let _ = child.wait();
    }
}

/// What the build asks with after a miss of a shared unit under its lock.
pub(crate) struct SharedMiss {
    pub(crate) index: UnitIndex,
    /// The SHA-256 of the fingerprint record this build computed, the bytes a
    /// published record of the same unit holds.
    pub(crate) key: String,
    /// The unit's directory in the store.
    pub(crate) directory: PathBuf,
    /// The fingerprint record, relative to the unit's directory.
    pub(crate) record: PathBuf,
    /// The record's short hash file, relative to the unit's directory.
    pub(crate) short_hash: PathBuf,
    /// Every planned fingerprint-folder and `out/` file, relative.
    pub(crate) planned: Vec<PathBuf>,
    /// Why this check missed.
    pub(crate) cause: UnitRebuildCause,
}

/// Which check under a unit's lock the worker asks for.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Check {
    /// The check after the lock is taken.
    AfterLock,
    /// The check of a unit a source staged and the worker placed, and
    /// whether this build compiled (rather than used) any of its dependencies,
    /// in which case the unit compiles as it would with no source.
    Staged { dependency_compiled: bool },
}

/// The verdict of one check under the unit's lock, and the miss's key where
/// the build has a source to ask.
pub(crate) struct Recheck {
    pub(crate) fresh: bool,
    pub(crate) miss: Option<SharedMiss>,
}

impl UnitSource {
    /// The build's source, where one is named and the build shares into
    /// `store`. Verified Targo never shares, so it never gets one.
    pub(crate) fn named(gctx: &GlobalContext, store: Option<&Path>) -> Option<Arc<UnitSource>> {
        let store = store?;
        if crate::trust_verified_targo() {
            return None;
        }
        let program = gctx.get_env_os(UNIT_SOURCE_ENV)?;
        if program.is_empty() {
            return None;
        }
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |time| time.as_nanos());
        Some(Arc::new(UnitSource::new(
            PathBuf::from(program),
            store
                .join("staging")
                .join(format!("{}-{nonce}", std::process::id())),
        )))
    }

    fn new(program: PathBuf, staging: PathBuf) -> UnitSource {
        UnitSource {
            program,
            staging,
            state: Mutex::new(State::Unstarted),
            passed_over: AtomicBool::new(false),
        }
    }

    /// Whether the source may still be asked. Once it is passed over, a miss
    /// computes no key for it.
    pub(crate) fn available(&self) -> bool {
        !self.passed_over.load(Ordering::Acquire)
    }

    /// Asks for the unit with `key`. Returns the staging folder the source
    /// says it staged the unit in, or `None` where it holds nothing, or is
    /// (or now becomes) passed over.
    pub(crate) fn ask(&self, key: &str) -> Option<PathBuf> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        if matches!(*state, State::Unstarted) {
            *state = match self.start() {
                Ok(running) => State::Running(running),
                Err(error) => {
                    warn!(%error, program = %self.program.display(), "unit source passed over: it did not start");
                    self.passed_over.store(true, Ordering::Release);
                    State::PassedOver
                }
            };
        }
        let State::Running(running) = &mut *state else {
            return None;
        };
        match self.exchange(running, key) {
            Ok(staged) => staged,
            Err(error) => {
                warn!(%error, program = %self.program.display(), "unit source passed over");
                self.passed_over.store(true, Ordering::Release);
                if let State::Running(running) = std::mem::replace(&mut *state, State::PassedOver) {
                    running.stop(Duration::ZERO);
                }
                None
            }
        }
    }

    fn start(&self) -> CargoResult<Running> {
        // The store's staging folder is kept across builds; the build's own
        // folder is new.
        private_directory(
            self.staging.parent().expect("staging has a parent"),
            Existing::Accepted,
        )?;
        private_directory(&self.staging, Existing::Refused)?;
        let mut process = ProcessBuilder::new(&self.program);
        crate::util::rustc::scrub_trust_targo_internal_env(&mut process);
        process.env_remove(UNIT_SOURCE_ENV);
        let mut command = process.build_command();
        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        let mut child = command.spawn()?;
        let mut stdin = child.stdin.take().expect("piped stdin");
        let stdout = child.stdout.take().expect("piped stdout");
        let (asks, written) = std::sync::mpsc::sync_channel::<Vec<u8>>(1);
        let writer = std::thread::Builder::new()
            .name("targo-unit-source-asks".into())
            .spawn(move || {
                for line in written {
                    if stdin.write_all(&line).and_then(|()| stdin.flush()).is_err() {
                        return;
                    }
                }
            });
        let (sender, replies) = std::sync::mpsc::sync_channel(1);
        let reader = std::thread::Builder::new()
            .name("targo-unit-source".into())
            .spawn(move || {
                let mut reader = BufReader::new(stdout);
                loop {
                    let mut line = Vec::new();
                    let reply = match (&mut reader).take(REPLY_LIMIT).read_until(b'\n', &mut line) {
                        Ok(0) => Err("the unit source exited".to_owned()),
                        Ok(_) if line.last() != Some(&b'\n') => {
                            Err("the unit source sent an unterminated or overlong line".to_owned())
                        }
                        Ok(_) => String::from_utf8(line)
                            .map(|line| line.trim_end_matches('\n').to_owned())
                            .map_err(|_| {
                                "the unit source sent a line that is not UTF-8".to_owned()
                            }),
                        Err(error) => Err(format!("reading the unit source failed: {error}")),
                    };
                    let last = reply.is_err();
                    if sender.send(reply).is_err() || last {
                        return;
                    }
                }
            });
        let running = Running {
            child,
            asks,
            replies,
            count: 0,
        };
        if let Err(error) = writer.and(reader) {
            running.stop(Duration::ZERO);
            return Err(error.into());
        }
        Ok(running)
    }

    fn exchange(&self, running: &mut Running, key: &str) -> CargoResult<Option<PathBuf>> {
        // Every line answers the ask before it: one already waiting was sent
        // unasked, or is a second answer to an earlier ask.
        match running.replies.try_recv() {
            Ok(Ok(reply)) => anyhow::bail!("the unit source sent {reply:?} before it was asked"),
            Ok(Err(error)) => anyhow::bail!(error),
            Err(TryRecvError::Disconnected) => anyhow::bail!("the unit source exited"),
            Err(TryRecvError::Empty) => {}
        }
        running.count += 1;
        let folder = self.staging.join(running.count.to_string());
        private_directory(&folder, Existing::Refused)?;
        let mut line = serde_json::to_string(&serde_json::json!({
            "version": PROTOCOL_VERSION,
            "key": key,
            "staging": folder,
        }))?;
        line.push('\n');
        match running.asks.try_send(line.into_bytes()) {
            Ok(()) => {}
            Err(TrySendError::Full(_)) => {
                anyhow::bail!("the unit source did not read the ask before this one")
            }
            Err(TrySendError::Disconnected(_)) => {
                anyhow::bail!("writing to the unit source failed")
            }
        }
        // An unwritten ask gets no line, so silence covers the write too.
        let limit = Instant::now() + ASK_LIMIT;
        loop {
            let left = limit.saturating_duration_since(Instant::now());
            match running.replies.recv_timeout(left.min(SILENCE)) {
                Ok(Ok(reply)) if reply == "working" => {}
                Ok(Ok(reply)) if reply == "staged" => return Ok(Some(folder)),
                Ok(Ok(reply)) if reply == "none" => return Ok(None),
                Ok(Ok(reply)) => anyhow::bail!("the unit source answered {reply:?}"),
                Ok(Err(error)) => anyhow::bail!(error),
                Err(RecvTimeoutError::Timeout) if left <= SILENCE => {
                    anyhow::bail!("the unit source did not answer within {ASK_LIMIT:?}")
                }
                Err(RecvTimeoutError::Timeout) => {
                    anyhow::bail!("the unit source was silent for {SILENCE:?}")
                }
                Err(RecvTimeoutError::Disconnected) => anyhow::bail!("the unit source exited"),
            }
        }
    }
}

impl Drop for UnitSource {
    /// The build ends: close the source's input, give it [`SILENCE`] to exit,
    /// and remove the build's staging folder.
    fn drop(&mut self) {
        let state = std::mem::replace(
            self.state
                .get_mut()
                .unwrap_or_else(|poison| poison.into_inner()),
            State::PassedOver,
        );
        if let State::Running(running) = state {
            running.stop(SILENCE);
        }
        match fs::remove_dir_all(&self.staging) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                warn!(%error, staging = %self.staging.display(), "unit source staging was not emptied")
            }
        }
    }
}

/// Whether [`private_directory`] accepts a directory that is already there.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Existing {
    /// The store's staging folder, kept across builds.
    Accepted,
    /// A build's or an ask's folder, which must be new.
    Refused,
}

/// Creates `path` private to this user (0700), or, where `existing` accepts
/// it, takes it where it already is a plain directory (the store's own checks
/// cover its owner and mode).
fn private_directory(path: &Path, existing: Existing) -> CargoResult<()> {
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt as _;
        builder.mode(0o700);
    }
    match builder.create(path) {
        Ok(()) => Ok(()),
        Err(error)
            if error.kind() == std::io::ErrorKind::AlreadyExists
                && existing == Existing::Accepted =>
        {
            let metadata = fs::symlink_metadata(path)?;
            anyhow::ensure!(
                metadata.is_dir() && !metadata.file_type().is_symlink(),
                "unit source staging is not a plain directory: {}",
                path.display()
            );
            Ok(())
        }
        Err(error) => Err(anyhow::Error::from(error).context(format!(
            "unit source staging {} was not made new",
            path.display()
        ))),
    }
}

/// The SHA-256 of a fingerprint record's bytes: the key of a unit.
pub(crate) fn key(record: &str) -> String {
    let mut hash = Sha256::new();
    hash.update(record.as_bytes());
    hash.finish_hex()
}

/// The miss a source is asked about: the unit's key and its planned files.
pub(crate) fn miss(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    record: &str,
    cause: UnitRebuildCause,
) -> CargoResult<SharedMiss> {
    let short_hash = build_runner.files().fingerprint_file_path(unit, "");
    let fingerprint_dir = build_runner.files().fingerprint_dir(unit);
    let directory = fingerprint_dir
        .parent()
        .ok_or_else(|| anyhow::anyhow!("shared unit has no directory"))?
        .to_path_buf();
    let out = build_runner.files().deps_dir(unit);
    let relative = |path: &Path| -> CargoResult<PathBuf> {
        Ok(path
            .strip_prefix(&directory)
            .map_err(|_| anyhow::anyhow!("planned file outside its unit: {}", path.display()))?
            .to_path_buf())
    };
    let mut planned = vec![
        relative(&short_hash)?,
        relative(&short_hash.with_extension("json"))?,
        relative(&build_runner.files().fingerprint_file_path(unit, "dep-"))?,
        relative(&build_runner.files().message_cache_path(unit))?,
        relative(
            &build_runner
                .files()
                .fingerprint_file_path(unit, "outputs-")
                .with_extension("json"),
        )?,
    ];
    for output in build_runner.outputs(unit)?.iter() {
        if output.path.parent() == Some(out.as_path()) {
            planned.push(relative(&output.path)?);
        }
    }
    planned.sort();
    planned.dedup();
    Ok(SharedMiss {
        index: build_runner.bcx.unit_to_index[unit],
        key: key(record),
        record: relative(&short_hash.with_extension("json"))?,
        short_hash: relative(&short_hash)?,
        directory,
        planned,
        cause,
    })
}

/// On the unit's worker, holding its lock, after the check missed: ask the
/// source, place what it staged, and ask for the check again. Returns whether
/// the unit was taken; a refused or absent one compiles, and a refused one
/// leaves none of the files placed for it behind.
pub(crate) fn offer(
    state: &JobState<'_, '_>,
    source: &UnitSource,
    miss: &SharedMiss,
    force: bool,
) -> CargoResult<bool> {
    let Some(staged) = source.ask(&miss.key) else {
        return Ok(false);
    };
    let decision = match place(&staged, miss) {
        Err(reason) => SharedDependencyDecision::Refused { reason },
        Ok(placed) => {
            let again = state.recheck_freshness(force, true);
            let decision = match &again {
                Ok(again) if again.fresh => SharedDependencyDecision::Taken {},
                Ok(again) => SharedDependencyDecision::Refused {
                    reason: if again.miss.as_ref().map(|miss| miss.cause)
                        == Some(UnitRebuildCause::OutputIntegrity)
                    {
                        UnitSourceRefusal::OutputIntegrity
                    } else {
                        UnitSourceRefusal::Stale
                    },
                },
                Err(_) => SharedDependencyDecision::Refused {
                    reason: UnitSourceRefusal::Stale,
                },
            };
            if decision != (SharedDependencyDecision::Taken {}) {
                // A short hash and receipt that pass would stand until the
                // compile clears them; a build killed before that must not
                // leave a refused unit in the store.
                remove_placed(&placed);
            }
            again?;
            decision
        }
    };
    debug!(key = %miss.key, ?decision, "unit source decision");
    let taken = decision == SharedDependencyDecision::Taken {};
    state.input_work(LogMessage::SharedDependencyDecision {
        index: miss.index,
        decision,
    });
    Ok(taken)
}

/// Renames the planned files of a staged unit into the unit's directory,
/// where its fingerprint record is the one this build computed, and returns
/// what it placed. Nothing else in the staging folder is read, and nothing is
/// read through a link: the staged folder and every folder under it on the
/// way to a planned file must be plain directories, and every planned file
/// present a plain file with one link (a hard link would let the store's
/// later in-place writes reach the source's own copy). A placed file gets
/// the store's mode. On a refusal nothing stays placed.
fn place(staged: &Path, miss: &SharedMiss) -> Result<Vec<PathBuf>, UnitSourceRefusal> {
    let directory = |path: &Path| match fs::symlink_metadata(path) {
        Ok(metadata) if metadata.is_dir() => Ok(()),
        _ => Err(UnitSourceRefusal::Incomplete),
    };
    let lone = |metadata: &fs::Metadata| {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            metadata.nlink() == 1
        }
        #[cfg(not(unix))]
        {
            let _ = metadata;
            true
        }
    };
    // Whether a planned file is present, through plain directories only.
    let present = |relative: &Path| -> Result<bool, UnitSourceRefusal> {
        let mut folder = staged.to_path_buf();
        directory(&folder)?;
        if let Some(parent) = relative.parent() {
            for component in parent.components() {
                folder.push(component);
                match fs::symlink_metadata(&folder) {
                    Ok(metadata) if metadata.is_dir() => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                        return Ok(false);
                    }
                    _ => return Err(UnitSourceRefusal::Incomplete),
                }
            }
        }
        match fs::symlink_metadata(staged.join(relative)) {
            Ok(metadata) if metadata.is_file() && lone(&metadata) => Ok(true),
            Ok(_) => Err(UnitSourceRefusal::Incomplete),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
            Err(_) => Err(UnitSourceRefusal::Incomplete),
        }
    };
    if !present(&miss.record)? || !present(&miss.short_hash)? {
        return Err(UnitSourceRefusal::Incomplete);
    }
    let bytes = fs::read(staged.join(&miss.record)).map_err(|_| UnitSourceRefusal::Incomplete)?;
    let mut hash = Sha256::new();
    hash.update(&bytes);
    if hash.finish_hex() != miss.key {
        return Err(UnitSourceRefusal::FingerprintDiffers);
    }
    let mut taking = Vec::new();
    for relative in &miss.planned {
        if present(relative)? {
            taking.push(relative);
        }
    }
    let mut placed = Vec::new();
    for relative in taking {
        let to = miss.directory.join(relative);
        let moved = (|| -> std::io::Result<bool> {
            if let Some(parent) = to.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::rename(staged.join(relative), &to)?;
            placed.push(to.clone());
            // What arrived is judged again: the source could have changed the
            // file between the check above and the rename.
            let metadata = fs::symlink_metadata(&to)?;
            if !metadata.is_file() || !lone(&metadata) {
                return Ok(false);
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;
                fs::set_permissions(&to, fs::Permissions::from_mode(PLACED_MODE))?;
            }
            Ok(true)
        })();
        if !matches!(moved, Ok(true)) {
            remove_placed(&placed);
            return Err(UnitSourceRefusal::Incomplete);
        }
    }
    Ok(placed)
}

/// Removes the files placed for a refused unit.
fn remove_placed(placed: &[PathBuf]) {
    for path in placed {
        match fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                warn!(%error, path = %path.display(), "a refused unit's placed file was not removed")
            }
        }
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt as _;

    fn source(dir: &Path, script: &str) -> UnitSource {
        let program = dir.join("source");
        fs::write(&program, format!("#!/bin/sh\n{script}\n")).unwrap();
        fs::set_permissions(&program, fs::Permissions::from_mode(0o755)).unwrap();
        let store = dir.join("store");
        fs::create_dir(&store).unwrap();
        UnitSource::new(program, store.join("staging").join("build"))
    }

    fn passed_over(source: &UnitSource) -> bool {
        matches!(*source.state.lock().unwrap(), State::PassedOver) && !source.available()
    }

    #[test]
    fn a_silent_source_is_passed_over_for_the_rest_of_the_build() {
        let dir = tempfile::tempdir().unwrap();
        let log = dir.path().join("asked");
        let source = source(
            dir.path(),
            &format!("while read line; do echo \"$line\" >> {log:?}; exec sleep 30; done"),
        );
        let started = Instant::now();
        assert_eq!(source.ask("a"), None);
        assert!(started.elapsed() >= SILENCE);
        assert!(passed_over(&source));
        assert_eq!(source.ask("b"), None);
        assert_eq!(fs::read_to_string(&log).unwrap().lines().count(), 1);
    }

    #[test]
    fn a_source_that_exits_is_passed_over() {
        let dir = tempfile::tempdir().unwrap();
        let source = source(dir.path(), "read line; exit 0");
        assert!(source.available());
        assert_eq!(source.ask("a"), None);
        assert!(passed_over(&source));
    }

    #[test]
    fn an_unknown_answer_is_passed_over_and_staging_is_emptied() {
        let dir = tempfile::tempdir().unwrap();
        let source = source(dir.path(), "read line; echo maybe");
        let staging = source.staging.clone();
        assert_eq!(source.ask("a"), None);
        assert!(passed_over(&source));
        assert!(staging.is_dir());
        drop(source);
        assert!(!staging.exists());
    }

    /// One process answers every ask of the build, each in a new folder that
    /// is private (0700) and inside the store's staging folder.
    #[test]
    fn staged_and_none_answers_keep_the_one_source() {
        let dir = tempfile::tempdir().unwrap();
        let started = dir.path().join("started");
        let source = source(
            dir.path(),
            &format!(
                "echo $$ >> {started:?}; read line; echo staged; read line; echo none; read line; echo staged"
            ),
        );
        let first = source.ask("a").unwrap();
        assert!(first.is_dir() && first.starts_with(&source.staging));
        assert!(source.staging.starts_with(dir.path().join("store/staging")));
        for folder in [&first, &source.staging] {
            let mode = fs::metadata(folder).unwrap().permissions().mode();
            assert_eq!(mode & 0o777, 0o700, "{}", folder.display());
        }
        assert_eq!(source.ask("b"), None);
        let third = source.ask("c").unwrap();
        assert_ne!(first, third);
        assert!(source.available());
        assert_eq!(fs::read_to_string(&started).unwrap().lines().count(), 1);
    }

    /// The build's folder must be new: one already there is not reused.
    #[test]
    fn a_build_folder_already_there_is_not_reused() {
        let dir = tempfile::tempdir().unwrap();
        let source = source(dir.path(), "read line; echo none");
        fs::create_dir_all(&source.staging).unwrap();
        assert_eq!(source.ask("a"), None);
        assert!(passed_over(&source));
    }

    /// A source the test feeds by hand: its replies come from `replies`.
    fn running(replies: Receiver<Result<String, String>>) -> (Running, Receiver<Vec<u8>>) {
        let child = std::process::Command::new("/bin/sleep")
            .arg("30")
            .spawn()
            .unwrap();
        let (asks, written) = std::sync::mpsc::sync_channel(1);
        (
            Running {
                child,
                asks,
                replies,
                count: 0,
            },
            written,
        )
    }

    #[test]
    fn a_line_waiting_before_the_ask_passes_the_source_over() {
        let dir = tempfile::tempdir().unwrap();
        let source = source(dir.path(), "");
        let (sender, replies) = std::sync::mpsc::sync_channel(1);
        sender.send(Ok("none".to_owned())).unwrap();
        let (mut running, _written) = running(replies);
        let error = source.exchange(&mut running, "a").unwrap_err();
        assert!(error.to_string().contains("before it was asked"), "{error}");
        running.stop(Duration::ZERO);
    }

    #[test]
    fn an_ask_left_unread_passes_the_source_over() {
        let dir = tempfile::tempdir().unwrap();
        let source = source(dir.path(), "");
        fs::create_dir_all(&source.staging).unwrap();
        let (_sender, replies) = std::sync::mpsc::sync_channel(1);
        let (mut running, _written) = running(replies);
        running.asks.try_send(b"unread\n".to_vec()).unwrap();
        let error = source.exchange(&mut running, "a").unwrap_err();
        assert!(error.to_string().contains("did not read"), "{error}");
        running.stop(Duration::ZERO);
    }

    #[test]
    fn working_lines_come_before_the_answer() {
        let dir = tempfile::tempdir().unwrap();
        let source = source(dir.path(), "");
        fs::create_dir_all(&source.staging).unwrap();
        let (sender, replies) = std::sync::mpsc::sync_channel(1);
        let (mut running, written) = running(replies);
        // The source answers once it has the ask, as a real one does.
        let feeder = std::thread::spawn(move || {
            let ask = written.recv().unwrap();
            for line in ["working", "working", "staged"] {
                sender.send(Ok(line.to_owned())).unwrap();
            }
            ask
        });
        let staged = source.exchange(&mut running, "a").unwrap().unwrap();
        assert!(staged.starts_with(&source.staging));
        let ask: serde_json::Value = serde_json::from_slice(&feeder.join().unwrap()).unwrap();
        assert_eq!(ask["key"], "a");
        assert_eq!(ask["version"], PROTOCOL_VERSION);
        running.stop(Duration::ZERO);
    }

    fn staged_miss(dir: &Path, record: &[u8]) -> (PathBuf, SharedMiss) {
        let staged = dir.join("staged");
        fs::create_dir_all(staged.join("fingerprint")).unwrap();
        fs::create_dir_all(staged.join("out")).unwrap();
        fs::write(staged.join("fingerprint/lib-leaf.json"), record).unwrap();
        fs::write(staged.join("fingerprint/lib-leaf"), "0123").unwrap();
        fs::write(staged.join("out/libleaf.rlib"), "archive").unwrap();
        fs::write(staged.join("out/unplanned"), "x").unwrap();
        let miss = SharedMiss {
            index: UnitIndex(0),
            key: key("{\"record\":1}"),
            directory: dir.join("unit"),
            record: "fingerprint/lib-leaf.json".into(),
            short_hash: "fingerprint/lib-leaf".into(),
            planned: vec![
                "fingerprint/lib-leaf".into(),
                "fingerprint/lib-leaf.json".into(),
                "fingerprint/dep-lib-leaf".into(),
                "out/libleaf.rlib".into(),
            ],
            cause: UnitRebuildCause::FreshBuild,
        };
        (staged, miss)
    }

    #[test]
    fn only_planned_files_of_the_computed_record_are_placed() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":1}");
        let placed = place(&staged, &miss).unwrap();
        let unit = dir.path().join("unit");
        assert_eq!(placed.len(), 3);
        assert!(unit.join("fingerprint/lib-leaf.json").is_file());
        assert!(unit.join("out/libleaf.rlib").is_file());
        assert!(!unit.join("out/unplanned").exists());
        assert!(staged.join("out/unplanned").exists());
        remove_placed(&placed);
        assert!(placed.iter().all(|path| !path.exists()));
    }

    /// A read-only staged file (as a content-addressed cache keeps it) gets the
    /// store's mode, so a later compile of the unit can rewrite it in place.
    #[test]
    fn a_read_only_staged_file_is_placed_writable() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":1}");
        for file in ["fingerprint/lib-leaf", "out/libleaf.rlib"] {
            fs::set_permissions(staged.join(file), fs::Permissions::from_mode(0o444)).unwrap();
        }
        place(&staged, &miss).unwrap();
        for file in ["fingerprint/lib-leaf", "out/libleaf.rlib"] {
            let placed = dir.path().join("unit").join(file);
            let mode = fs::metadata(&placed).unwrap().permissions().mode();
            assert_eq!(mode & 0o777, PLACED_MODE, "{file}");
            fs::write(&placed, b"").unwrap();
        }
    }

    #[test]
    fn a_record_for_other_inputs_places_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":2}");
        assert_eq!(
            place(&staged, &miss),
            Err(UnitSourceRefusal::FingerprintDiffers)
        );
        assert!(!dir.path().join("unit").exists());
    }

    #[test]
    fn a_linked_planned_file_places_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":1}");
        std::os::unix::fs::symlink("/etc/hosts", staged.join("fingerprint/dep-lib-leaf")).unwrap();
        assert_eq!(place(&staged, &miss), Err(UnitSourceRefusal::Incomplete));
        assert!(!dir.path().join("unit").exists());
    }

    /// A hard link would let the store's in-place writes reach the source's
    /// own copy.
    #[test]
    fn a_hard_linked_planned_file_places_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":1}");
        let cached = dir.path().join("cache-copy");
        fs::hard_link(staged.join("out/libleaf.rlib"), &cached).unwrap();
        assert_eq!(place(&staged, &miss), Err(UnitSourceRefusal::Incomplete));
        assert!(!dir.path().join("unit").exists());
        assert_eq!(fs::read(&cached).unwrap(), b"archive");
    }

    /// A linked folder would bring files from outside the store.
    #[test]
    fn a_linked_planned_folder_places_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":1}");
        let outside = dir.path().join("outside");
        fs::rename(staged.join("out"), &outside).unwrap();
        std::os::unix::fs::symlink(&outside, staged.join("out")).unwrap();
        assert_eq!(place(&staged, &miss), Err(UnitSourceRefusal::Incomplete));
        assert!(!dir.path().join("unit").exists());
        assert!(outside.join("libleaf.rlib").is_file());
    }

    #[test]
    fn a_linked_staging_folder_places_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let (staged, miss) = staged_miss(dir.path(), b"{\"record\":1}");
        let outside = dir.path().join("outside");
        fs::rename(&staged, &outside).unwrap();
        std::os::unix::fs::symlink(&outside, &staged).unwrap();
        assert_eq!(place(&staged, &miss), Err(UnitSourceRefusal::Incomplete));
        assert!(!dir.path().join("unit").exists());
    }
}
