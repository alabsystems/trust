//! Exact outer read prefixes reach owned create-only files before frame
//! decoding/callback failure. These observations never grant native custody.
use std::fs::{File, OpenOptions};
use std::io::{self, Write as _};
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{SyncSender, TrySendError};
use std::sync::{Arc, Mutex, TryLockError};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};

pub(crate) enum Input {
    Frame(Vec<u8>),
    Eof,
}
struct Raw {
    file: File,
    path: PathBuf,
    seen: u64,
    written: u64,
    hash: Sha256,
    eof: bool,
}
pub(crate) struct Pump {
    raw: [Raw; 2],
    pending: Vec<u8>,
    sender: SyncSender<Input>,
    deadline: Instant,
    cancelled: Arc<AtomicBool>,
    pub failure: Option<String>,
}
impl Pump {
    pub fn new(
        root: &Path,
        sender: SyncSender<Input>,
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
    ) -> io::Result<Arc<Mutex<Self>>> {
        let open = |name: &str| -> io::Result<Raw> {
            let path = root.join(name);
            let file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(&path)?;
            Ok(Raw { file, path, seen: 0, written: 0, hash: Sha256::new(), eof: false })
        };
        Ok(Arc::new(Mutex::new(Self {
            raw: [open("root.stdout.frames.bin")?, open("root.stderr.bin")?],
            pending: Vec::new(),
            sender,
            deadline,
            cancelled,
            failure: None,
        })))
    }
    pub fn accept(&mut self, index: usize, bytes: &[u8]) -> io::Result<()> {
        let result = self.accept_inner(index, bytes);
        if let Err(error) = &result {
            self.failure.get_or_insert_with(|| error.to_string());
        }
        result
    }
    fn accept_inner(&mut self, index: usize, bytes: &[u8]) -> io::Result<()> {
        if index > 1 {
            return Err(io::Error::other("invalid original native stream"));
        }
        let previously_failed = self.failure.is_some();
        let raw = &mut self.raw[index];
        if raw.eof {
            return Err(io::Error::other("native bytes after physical stream EOF"));
        }
        if bytes.is_empty() {
            raw.eof = true;
            if previously_failed {
                return Err(io::Error::other(
                    "original native sink failed; actual other-stream EOF retained",
                ));
            }
            if index == 0 {
                if !self.pending.is_empty() {
                    return Err(io::Error::other(
                        "actual native stdout ended within a partial frame",
                    ));
                }
                self.send(Input::Eof)?;
            }
            return Ok(());
        }
        raw.seen = raw
            .seen
            .checked_add(bytes.len() as u64)
            .ok_or_else(|| io::Error::other("native stream count overflow"))?;
        let cap = if index == 0 { super::RAW_STDOUT_MAX } else { 1024 * 1024 };
        let keep = bytes.len().min((cap as u64).saturating_sub(raw.written) as usize);
        let mut remaining = &bytes[..keep];
        while !remaining.is_empty() {
            if Instant::now() >= self.deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            let n = raw.file.write(remaining)?;
            if n == 0 {
                return Err(io::ErrorKind::WriteZero.into());
            }
            raw.hash.update(&remaining[..n]);
            raw.written += n as u64;
            remaining = &remaining[n..];
        }
        if keep != bytes.len() {
            return Err(io::Error::other(
                "native raw stream exceeds original finite sink bound; prefix retained",
            ));
        }
        if previously_failed {
            return Err(io::Error::other(
                "original native sink failed; actual other-stream prefix retained",
            ));
        }
        if index == 1 {
            return Ok(());
        }
        if self
            .pending
            .len()
            .checked_add(bytes.len())
            .is_none_or(|n| n > trust_resource_controller::MAX_PAYLOAD + 8196)
        {
            return Err(io::Error::other(
                "native framed pending prefix exceeds original finite bound",
            ));
        }
        self.pending.try_reserve(bytes.len()).map_err(io::Error::other)?;
        self.pending.extend_from_slice(bytes);
        while self.pending.len() >= 4 {
            let len = u32::from_be_bytes(self.pending[..4].try_into().unwrap()) as usize;
            if len == 0 || len > trust_resource_controller::MAX_PAYLOAD {
                return Err(io::Error::other(
                    "native service frame exceeds original private bound",
                ));
            }
            if self.pending.len() < 4 + len {
                break;
            }
            let rest = self.pending.split_off(4 + len);
            let mut frame = std::mem::replace(&mut self.pending, rest);
            frame.drain(..4);
            self.send(Input::Frame(frame))?;
        }
        Ok(())
    }
    fn send(&self, mut frame: Input) -> io::Result<()> {
        loop {
            if Instant::now() >= self.deadline || self.cancelled.load(Ordering::Acquire) {
                return Err(io::Error::other(
                    "original native conversation stopped while publishing actual bytes",
                ));
            }
            match self.sender.try_send(frame) {
                Ok(()) => return Ok(()),
                Err(TrySendError::Full(original)) => {
                    frame = original;
                    std::thread::sleep(Duration::from_millis(1));
                }
                Err(TrySendError::Disconnected(_)) => {
                    return Err(io::Error::other("original native frame consumer ended"));
                }
            }
        }
    }
    pub fn finish(&mut self) -> Value {
        for stream in &mut self.raw {
            if Instant::now() >= self.deadline {
                self.failure.get_or_insert("native sink finalization deadline expired".into());
                break;
            }
            if let Err(error) = stream.file.sync_all() {
                self.failure
                    .get_or_insert_with(|| format!("native raw prefix sync failed: {error}"));
            }
        }
        json!({"scope":"actual original outer CLI reads; no hosted admission, process completion or source/proof grant",
            "failure":self.failure,"pending_frame_bytes":self.pending.len(),"streams":self.raw.iter().map(|stream|json!({
                "path":stream.path,"bytes_seen":stream.seen,"bytes_written":stream.written,
                "sha256_of_written_prefix":format!("{:x}",stream.hash.clone().finalize()),"physical_eof":stream.eof,
                "complete_bytes":stream.seen==stream.written && stream.eof && self.failure.is_none(),
            })).collect::<Vec<_>>()})
    }
}
pub(crate) fn lock<'a, T>(
    mutex: &'a Mutex<T>,
    deadline: Instant,
) -> io::Result<std::sync::MutexGuard<'a, T>> {
    loop {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        match mutex.try_lock() {
            Ok(guard) => return Ok(guard),
            Err(TryLockError::Poisoned(_)) => {
                return Err(io::Error::other("original native observation owner poisoned"));
            }
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(1)),
        }
    }
}
