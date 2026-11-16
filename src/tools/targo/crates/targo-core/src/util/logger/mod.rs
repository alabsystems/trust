//! Build analysis logging infrastructure.

use std::cell::RefCell;
use std::hash::Hash;
use std::io::{BufWriter, Write};
use std::mem::ManuallyDrop;
use std::path::Path;
use std::sync::mpsc::{self, Sender};
use std::thread::JoinHandle;

use anyhow::Context as _;
use cargo_util::paths;

use crate::CargoResult;
use crate::compiler::BuildConfig;
use crate::util::flock::{FileLock, Filesystem};
use crate::util::log_message::INPUT_WORK_VERSION;
use crate::util::log_message::LogMessage;
use crate::util::short_hash;
use crate::workspace::Workspace;

pub(crate) mod native;

// for newer `cargo report` commands
struct FileLogger {
    tx: ManuallyDrop<Sender<LogMessage>>,
    handle: Option<JoinHandle<()>>,
}

impl FileLogger {
    /// Creates a logger if `-Zbuild-analysis` is enabled
    fn maybe_new(ws: &Workspace<'_>, run_id: &mut RunId) -> CargoResult<Option<FileLogger>> {
        let analysis = ws.gctx().build_config()?.analysis.as_ref();
        match (analysis, ws.gctx().cli_unstable().build_analysis) {
            (Some(analysis), true) if analysis.enabled => {
                let log_dir = ws.gctx().home().join("log");
                paths::create_dir_all(log_dir.as_path_unlocked())?;

                // Trust: distinct invocations may have the same workspace and
                // millisecond timestamp. Reserve a fresh file atomically; never
                // wait on, overwrite or append to a retained session's log.
                let log_file = reserve_analysis_log(&log_dir, run_id)?;

                let (tx, rx) = mpsc::channel::<LogMessage>();

                let run_id_str = run_id.to_string();
                let handle = std::thread::spawn(move || {
                    let mut writer = BufWriter::new(log_file);
                    // Trust: incomplete diagnostic evidence must not receive a
                    // closing marker after an earlier write/flush failure.
                    if let Err(error) = write_analysis_log(&mut writer, &run_id_str, rx) {
                        tracing::warn!("build analysis log was not completed: {error}");
                    }
                });

                Ok(Some(Self {
                    tx: ManuallyDrop::new(tx),
                    handle: Some(handle),
                }))
            }
            (Some(_), false) => {
                ws.gctx().shell().warn(
                    "ignoring 'build.analysis' config, pass `-Zbuild-analysis` to enable it",
                )?;
                Ok(None)
            }
            _ => Ok(None),
        }
    }
}

// Trust: the chosen identity belongs to this logger and is shared by every
// sink/phase. generate_run_id remains deterministic for invocation correlation
// and report workspace grouping; only an actual filename collision changes it.
fn reserve_analysis_log(log_dir: &Filesystem, run_id: &mut RunId) -> CargoResult<FileLock> {
    loop {
        let filename = format!("{run_id}.jsonl");
        if let Some(file) = log_dir.create_rw_exclusive_new(Path::new(&filename))? {
            return Ok(file);
        }
        run_id.next_collision()?;
    }
}

// Trust: a scoped terminal record permits strict readers to distinguish a
// supported zero-attempt run from legacy, killed or truncated evidence. This
// covers the actual serialized records, not durable storage or build success.
fn write_analysis_log<W: Write>(
    writer: &mut W,
    run_id: &str,
    messages: impl IntoIterator<Item = LogMessage>,
) -> std::io::Result<()> {
    LogMessage::InputWorkEnabled {
        version: INPUT_WORK_VERSION,
    }
    .write_json_log(writer, run_id)?;
    let mut started = 0u64;
    let mut finished = 0u64;
    for message in messages {
        let counter = match &message {
            LogMessage::InputWorkStarted { .. } => Some(&mut started),
            LogMessage::InputWorkFinished { .. } => Some(&mut finished),
            _ => None,
        };
        if let Some(counter) = counter {
            *counter = counter
                .checked_add(1)
                .ok_or_else(|| std::io::Error::other("input work event count overflow"))?;
        }
        message.write_json_log(writer, run_id)?;
    }
    // Flush the entire body before authoring a terminal record. A partial body
    // cannot be mistaken for complete, cheap work by a later strict reader.
    writer.flush()?;
    LogMessage::InputWorkClosed {
        version: INPUT_WORK_VERSION,
        started,
        finished,
    }
    .write_json_log(writer, run_id)?;
    writer.flush()
}

impl Drop for FileLogger {
    fn drop(&mut self) {
        // SAFETY: tx is dropped exactly once here to signal thread shutdown.
        // ManuallyDrop prevents automatic drop after this impl runs.
        unsafe {
            ManuallyDrop::drop(&mut self.tx);
        }

        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

/// For legacy `cargo build --timings` flag
struct InMemoryLogger {
    // using mutex to hide mutability
    logs: RefCell<Vec<LogMessage>>,
}

impl InMemoryLogger {
    fn maybe_new(options: &BuildConfig) -> Option<Self> {
        if options.timing_report {
            Some(Self {
                logs: RefCell::new(Vec::new()),
            })
        } else {
            None
        }
    }
}

/// Logger for `-Zbuild-analysis`.
pub struct BuildLogger {
    run_id: RunId,
    file_logger: Option<FileLogger>,
    in_memory_logger: Option<InMemoryLogger>,
    native_logger: Option<native::NativeLogger>,
}

impl BuildLogger {
    pub fn maybe_new(ws: &Workspace<'_>, options: &BuildConfig) -> CargoResult<Option<Self>> {
        let mut run_id = Self::generate_run_id(ws);
        let file_logger = FileLogger::maybe_new(ws, &mut run_id)?;
        let in_memory_logger = InMemoryLogger::maybe_new(options);

        if file_logger.is_none() && in_memory_logger.is_none() {
            return Ok(None);
        }

        Ok(Some(Self {
            run_id,
            file_logger,
            in_memory_logger,
            native_logger: None,
        }))
    }

    /// An explicit paired caller supplies the original bounded observer. This
    /// does not enable project-selected analysis files or in-memory timings.
    pub(crate) fn observed(
        ws: &Workspace<'_>,
        options: &BuildConfig,
        observer: std::sync::Arc<dyn native::Observer>,
    ) -> CargoResult<Self> {
        let mut logger = Self::maybe_new(ws, options)?.unwrap_or_else(|| Self {
            run_id: Self::generate_run_id(ws),
            file_logger: None,
            in_memory_logger: None,
            native_logger: None,
        });
        logger.native_logger = Some(native::NativeLogger::new(
            observer,
            &logger.run_id.to_string(),
        )?);
        Ok(logger)
    }
    pub(crate) fn finish_native(&self) -> CargoResult<()> {
        if let Some(logger) = &self.native_logger {
            logger.finish(&self.run_id.to_string())?;
        }
        Ok(())
    }

    /// Generates the stable invocation/workspace run ID candidate.
    /// Trust: file-backed logging reserves its final identity atomically.
    pub fn generate_run_id(ws: &Workspace<'_>) -> RunId {
        RunId::new(&ws.root(), ws.gctx().invocation_time())
    }

    /// Returns the run ID for this build session.
    pub fn run_id(&self) -> &RunId {
        &self.run_id
    }

    /// Trust: a real file-backed analysis session, not in-memory timings alone.
    pub fn has_file_analysis(&self) -> bool {
        self.file_logger.is_some()
    }

    /// Logs a message.
    pub fn log(&self, msg: LogMessage) {
        if let Some(logger) = &self.native_logger {
            logger.log(&self.run_id.to_string(), &msg);
        }
        if let Some(ref logger) = self.in_memory_logger {
            let mut borrowed = logger.logs.try_borrow_mut().expect(
                "Unable to get a mutable reference to in-memory logger; please file a bug report",
            );
            borrowed.push(msg.clone());
        };

        if let Some(ref logger) = self.file_logger {
            let _ = logger.tx.send(msg);
        };
    }

    pub fn get_logs(&self) -> Option<Vec<LogMessage>> {
        self.in_memory_logger.as_ref().map(|l| {
            l.logs
                .try_borrow()
                .expect("Unable to get a reference to in-memory logger; please file a bug report")
                .clone()
        })
    }
}

/// A Cargo invocation/workspace identifier, disambiguated on log reservation.
#[derive(Clone)]
pub struct RunId {
    timestamp: jiff::Timestamp,
    hash: String,
    // Trust: optional log-name reservation ordinal. It is not a time, a proof
    // token or workspace identity. None preserves all retained legacy IDs.
    collision: Option<u64>,
}

impl RunId {
    const FORMAT: &str = "%Y%m%dT%H%M%S%3fZ";

    pub fn new<H: Hash>(h: &H, timestamp: jiff::Timestamp) -> RunId {
        RunId {
            timestamp,
            hash: short_hash(h),
            collision: None,
        }
    }

    // Trust: use a fixed-width suffix whose lexical order follows reservation
    // order, including the unsuffixed legacy/base name in session listings.
    fn next_collision(&mut self) -> CargoResult<()> {
        self.collision = Some(
            self.collision
                .unwrap_or(0)
                .checked_add(1)
                .context("build-analysis run ID collision counter exhausted")?,
        );
        Ok(())
    }

    pub fn timestamp(&self) -> &jiff::Timestamp {
        &self.timestamp
    }

    /// Checks whether ID was generated from the same workspace.
    pub fn same_workspace(&self, other: &RunId) -> bool {
        self.hash == other.hash
    }
}

impl std::fmt::Display for RunId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let hash = &self.hash;
        let timestamp = self.timestamp.strftime(Self::FORMAT);
        write!(f, "{timestamp}-{hash}")?;
        // Trust: '~' sorts after the base filename's '.' separator.
        if let Some(collision) = self.collision {
            write!(f, "~{collision:016x}")?;
        }
        Ok(())
    }
}

impl std::str::FromStr for RunId {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let msg = || {
            format!(
                "expect run ID in format `20060724T012128000Z-<16-char-hex>[~<16-char-lower-hex>]`, got `{s}`"
            )
        };
        // Trust: accept retained unsuffixed IDs and preserve exact canonical
        // spelling of new IDs for --id lookup. No case-folded suffix aliases.
        let (base, collision) = if let Some((base, suffix)) = s.rsplit_once('~') {
            let value = u64::from_str_radix(suffix, 16).with_context(msg)?;
            if suffix != format!("{value:016x}") {
                anyhow::bail!(msg());
            }
            (base, Some(value))
        } else {
            (s, None)
        };
        let Some((timestamp, hash)) = base.rsplit_once('-') else {
            anyhow::bail!(msg());
        };

        if hash.len() != 16 || !hash.chars().all(|c| c.is_ascii_hexdigit()) {
            anyhow::bail!(msg());
        }
        let timestamp = jiff::civil::DateTime::strptime(Self::FORMAT, timestamp)
            .and_then(|dt| dt.to_zoned(jiff::tz::TimeZone::UTC))
            .map(|zoned| zoned.timestamp())
            .with_context(msg)?;

        Ok(RunId {
            timestamp,
            hash: hash.into(),
            collision,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::UnitIndex;
    use crate::util::log_message::{InputWork, InputWorkOutcome, InputWorkPhase};

    #[test]
    fn input_work_log_closes_only_after_recording_the_entire_attempt() {
        let mut bytes = Vec::new();
        write_analysis_log(
            &mut bytes,
            "run",
            [
                LogMessage::InputWorkStarted {
                    capture: 0,
                    index: UnitIndex(7),
                    phase: InputWorkPhase::Freshness,
                },
                LogMessage::InputWorkFinished {
                    capture: 0,
                    index: UnitIndex(7),
                    phase: InputWorkPhase::Freshness,
                    outcome: InputWorkOutcome::Uncacheable,
                    work: InputWork {
                        metadata_reads: 3,
                        ..InputWork::default()
                    },
                },
                LogMessage::InputWorkFinalized { captures: 1 },
            ],
        )
        .unwrap();
        let rows = serde_json::Deserializer::from_slice(&bytes)
            .into_iter::<serde_json::Value>()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(rows.len(), 5);
        assert_eq!(rows[0]["reason"], "input-work-enabled");
        assert_eq!(rows[2]["outcome"], "uncacheable");
        assert_eq!(rows[2]["work"]["metadata_reads"], 3);
        assert_eq!(rows[3]["reason"], "input-work-finalized");
        assert_eq!(rows[3]["captures"], 1);
        assert_eq!(rows[4]["reason"], "input-work-closed");
        assert_eq!(rows[4]["started"], 1);
        assert_eq!(rows[4]["finished"], 1);
    }

    struct FailingWriter {
        bytes: Vec<u8>,
        remaining: usize,
        fail_flush: bool,
    }

    impl Write for FailingWriter {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if self.remaining == 0 {
                return Err(std::io::Error::other("injected write failure"));
            }
            let count = bytes.len().min(self.remaining);
            self.bytes.extend_from_slice(&bytes[..count]);
            self.remaining -= count;
            Ok(count)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            if self.fail_flush {
                Err(std::io::Error::other("injected flush failure"))
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn failed_body_write_or_flush_cannot_author_a_closing_marker() {
        for (remaining, fail_flush) in [(30, false), (usize::MAX, true)] {
            let mut writer = FailingWriter {
                bytes: Vec::new(),
                remaining,
                fail_flush,
            };
            assert!(write_analysis_log(&mut writer, "run", []).is_err());
            assert!(!String::from_utf8_lossy(&writer.bytes).contains("input-work-closed"));
        }
    }

    #[test]
    fn run_id_round_trip() {
        // Trust: exact lookup keeps both retained legacy IDs and newly
        // disambiguated IDs readable without aliases or workspace changes.
        for id in [
            "20060724T012128000Z-b0fd440798ab3cfb",
            "20060724T012128000Z-b0fd440798ab3cfb~0000000000000001",
            "20060724T012128000Z-b0fd440798ab3cfb~00000000000000ff",
        ] {
            assert_eq!(id, id.parse::<RunId>().unwrap().to_string());
        }
    }

    // Trust: malformed/case-folded suffixes cannot alias an exact retained ID.
    #[test]
    fn run_id_collision_preserves_workspace_and_timestamp_without_aliases() {
        let original: RunId = "20060724T012128000Z-b0fd440798ab3cfb".parse().unwrap();
        let mut selected = original.clone();
        selected.next_collision().unwrap();
        let text = selected.to_string();
        assert!(selected.same_workspace(&original));
        assert_eq!(selected.timestamp(), original.timestamp());
        assert!(format!("{text}.jsonl") > format!("{original}.jsonl"));
        assert!(text.parse::<RunId>().unwrap().same_workspace(&original));
        for suffix in [
            "",
            "1",
            "000000000000000A",
            "0000000000000001~0000000000000002",
        ] {
            assert!(format!("{original}~{suffix}").parse::<RunId>().is_err());
        }
        let mut last: RunId = format!("{original}~ffffffffffffffff").parse().unwrap();
        assert!(last.next_collision().is_err());
    }

    // Trust: exercise real concurrent atomic creation while the original
    // retained session's original exclusive lock is STILL held. No sleeps,
    // random IDs or lock release stand in for independently owned log files.
    #[test]
    fn concurrent_log_reservations_preserve_a_locked_retained_session() {
        let directory = tempfile::tempdir().unwrap();
        let filesystem = Filesystem::new(directory.path().to_path_buf());
        let base = RunId::new(
            &"original-workspace",
            "2026-11-08T01:02:03Z".parse().unwrap(),
        );
        let mut retained_id = base.clone();
        let mut retained = reserve_analysis_log(&filesystem, &mut retained_id).unwrap();
        let retained_bytes = b"retained original session bytes\n";
        retained.write_all(retained_bytes).unwrap();
        retained.flush().unwrap();

        let barrier = std::sync::Barrier::new(2);
        let reserved = std::thread::scope(|scope| {
            let handles = (0..2)
                .map(|_| {
                    let filesystem = &filesystem;
                    let barrier = &barrier;
                    let mut id = base.clone();
                    scope.spawn(move || {
                        barrier.wait();
                        let mut file = reserve_analysis_log(filesystem, &mut id).unwrap();
                        write_analysis_log(
                            &mut file,
                            &id.to_string(),
                            [LogMessage::InputWorkFinalized { captures: 0 }],
                        )
                        .unwrap();
                        (id, file)
                    })
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect::<Vec<_>>()
        });

        assert_ne!(reserved[0].0.to_string(), reserved[1].0.to_string());
        for (id, file) in &reserved {
            assert_ne!(id.to_string(), retained_id.to_string());
            assert!(id.same_workspace(&retained_id));
            assert_eq!(id.timestamp(), retained_id.timestamp());
            let bytes = std::fs::read(file.path()).unwrap();
            let rows = serde_json::Deserializer::from_slice(&bytes)
                .into_iter::<serde_json::Value>()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert!(rows.iter().all(|row| row["run_id"] == id.to_string()));
            assert_eq!(rows.last().unwrap()["reason"], "input-work-closed");
        }
        assert_eq!(std::fs::read(retained.path()).unwrap(), retained_bytes);
    }

    // Trust: a colliding symlink/directory is retained, never followed/opened
    // as a supposedly reusable log. create_new owns only the fresh result.
    #[cfg(unix)]
    #[test]
    fn log_reservation_does_not_follow_or_replace_existing_nonfiles() {
        let directory = tempfile::tempdir().unwrap();
        let filesystem = Filesystem::new(directory.path().to_path_buf());
        let mut id = RunId::new(&"workspace", "2026-11-08T01:02:03Z".parse().unwrap());
        let target = directory.path().join("retained-target");
        std::fs::write(&target, b"retained").unwrap();
        let symlink = directory.path().join(format!("{id}.jsonl"));
        std::os::unix::fs::symlink(&target, &symlink).unwrap();
        let mut collision = id.clone();
        collision.next_collision().unwrap();
        let existing_dir = directory.path().join(format!("{collision}.jsonl"));
        std::fs::create_dir(&existing_dir).unwrap();
        let file = reserve_analysis_log(&filesystem, &mut id).unwrap();
        assert_ne!(file.path(), symlink);
        assert_ne!(file.path(), existing_dir);
        assert!(
            std::fs::symlink_metadata(symlink)
                .unwrap()
                .file_type()
                .is_symlink()
        );
        assert!(existing_dir.is_dir());
        assert_eq!(std::fs::read(target).unwrap(), b"retained");
    }
}
