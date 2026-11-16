//! Owned storage for already-prepared publication DATA, never a serialized
//! private proof authority, accepted kernel certificate or selectable grade.
//! A saved record is usable only through its live, private in-process handle.
//! Ordinary write/admission failure leaves the caller's original publisher in
//! charge. A read refusal is not proof and may never omit the recorded debt.

use std::fs::{File, Metadata, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::marker::PhantomData;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use serde::Serialize;
use serde::de::DeserializeOwned;
use sha2::{Digest, Sha256};

const DOMAIN: &[u8] = b"trustc.vf5.prepared-publication-data.v1\0";
static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

fn invalid(message: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.to_string())
}

#[derive(PartialEq, Eq)]
struct Identity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
}

impl Identity {
    fn of(metadata: &Metadata) -> io::Result<Self> {
        if !metadata.is_file() {
            return Err(invalid("publication storage descriptor is not regular"));
        }
        #[cfg(unix)]
        use std::os::unix::fs::MetadataExt;
        Ok(Self {
            #[cfg(unix)]
            device: metadata.dev(),
            #[cfg(unix)]
            inode: metadata.ino(),
        })
    }
}

struct Storage {
    file: File,
    identity: Identity,
    end: u64,
    write_failed: bool,
    #[cfg(test)]
    before_seal: Option<Box<dyn FnOnce(&mut File, u64) -> io::Result<()> + Send>>,
}

/// One descriptor for the compiler session, shared by compact record handles.
/// Its sole filesystem link is removed before a handle can escape. Production
/// exposes no file, pathname, mutable bytes or callback with storage access.
pub(super) struct PublicationSpool(Mutex<Storage>);

pub(super) struct Saved<T> {
    storage: Arc<PublicationSpool>,
    body: String,
    rows: usize,
    offset: u64,
    length: u64,
    digest: String,
    consumed: bool,
    data: PhantomData<fn() -> T>,
}

/// An append commitment, kept private until every requested alternative has
/// sealed. This contains no deserialized data or proof authority.
struct SealedRecord {
    offset: u64,
    length: u64,
    digest: String,
}

impl PublicationSpool {
    pub(super) fn create(configured_root: &Path) -> io::Result<Arc<Self>> {
        let (_, store) = super::super::prepare_private_proof_artifact_store(configured_root)
            .map_err(invalid)?;
        let sequence = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
        let path = store.join(format!(".vf5-publication-{}-{sequence}", std::process::id()));
        let mut options = OpenOptions::new();
        options.read(true).write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600).custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
        }
        let file = options.open(&path)?;
        // No path is reopened after capture. If the platform cannot detach
        // this owned file, refuse admission rather than weaken ownership.
        if let Err(error) = std::fs::remove_file(&path) {
            drop(file);
            let _ = std::fs::remove_file(path);
            return Err(error);
        }
        let identity = Identity::of(&file.metadata()?)?;
        Ok(Arc::new(Self(Mutex::new(Storage {
            file, identity, end: 0, write_failed: false,
            #[cfg(test)]
            before_seal: None,
        }))))
    }

    /// Stream one body's prepared data directly to the owned descriptor.
    /// There is no body-count feature cap or second in-memory bulk buffer.
    /// A failed write poisons future writes; it cannot be retried to green.
    pub(super) fn save<T: Serialize>(
        self: &Arc<Self>,
        body: &str,
        rows: usize,
        value: &T,
    ) -> io::Result<Saved<T>> {
        self.save_record(body, rows, value)
    }

    /// Serialize a borrowed presentation view without retaining its borrow.
    /// `D` is only the owned DATA shape decoded at emission, never a saved
    /// certificate, favorable disposition or proof-authority constructor.
    pub(super) fn save_as<S: Serialize + ?Sized, D: DeserializeOwned>(
        self: &Arc<Self>,
        body: &str,
        rows: usize,
        value: &S,
    ) -> io::Result<Saved<D>> {
        self.save_record(body, rows, value)
    }

    /// Admit both alternatives for the SAME body/row inventory, or neither.
    /// No handle is constructed until both appends independently seal under
    /// one lock. A failed second append leaves its bytes unadmitted, poisons
    /// future writes and preserves every previously returned sealed record.
    pub(super) fn save_pair_as<
        S1: Serialize + ?Sized,
        D1: DeserializeOwned,
        S2: Serialize + ?Sized,
        D2: DeserializeOwned,
    >(
        self: &Arc<Self>,
        body: &str,
        rows: usize,
        first: &S1,
        second: &S2,
    ) -> io::Result<(Saved<D1>, Saved<D2>)> {
        let mut storage = self.0.lock().map_err(|_| invalid("publication storage lock poisoned"))?;
        let first = append(&mut storage, body, rows, first)?;
        let second = append(&mut storage, body, rows, second)?;
        Ok((self.saved(body, rows, first), self.saved(body, rows, second)))
    }

    fn save_record<S: Serialize + ?Sized, D>(
        self: &Arc<Self>,
        body: &str,
        rows: usize,
        value: &S,
    ) -> io::Result<Saved<D>> {
        let mut storage = self.0.lock().map_err(|_| invalid("publication storage lock poisoned"))?;
        let record = append(&mut storage, body, rows, value)?;
        Ok(self.saved(body, rows, record))
    }

    fn saved<D>(self: &Arc<Self>, body: &str, rows: usize, record: SealedRecord) -> Saved<D> {
        Saved {
            storage: Arc::clone(self), body: body.to_owned(), rows,
            offset: record.offset, length: record.length, digest: record.digest,
            consumed: false, data: PhantomData,
        }
    }
}

fn append<S: Serialize + ?Sized>(
    storage: &mut Storage,
    body: &str,
    rows: usize,
    value: &S,
) -> io::Result<SealedRecord> {
    if storage.write_failed {
        return Err(invalid("publication storage previously failed to write"));
    }
    let offset = storage.end;
    let attempt = (|| {
        if Identity::of(&storage.file.metadata()?)? != storage.identity
            || storage.file.metadata()?.len() != offset
        {
            return Err(invalid("publication storage changed before append"));
        }
        storage.file.seek(SeekFrom::Start(offset))?;
        // The commitment starts with bytes actually accepted from the
        // serializer, never whatever a subsequent read happens to return.
        let mut writer = HashingWriter::new(&mut storage.file);
        serde_json::to_writer(&mut writer, value).map_err(invalid)?;
        writer.flush()?;
        let (length, payload) = writer.finish();
        let end = offset.checked_add(length).ok_or_else(|| invalid("record extent overflow"))?;
        let digest = frame_digest(body, rows, offset, length, &payload)?;
        #[cfg(test)]
        if let Some(mutate) = storage.before_seal.take() {
            mutate(&mut storage.file, offset)?;
        }
        if record_digest(storage, body, rows, offset, length)? != digest {
            return Err(invalid("publication storage differs from emitted serialization"));
        }
        Ok((end, length, digest))
    })();
    let (end, length, digest) = match attempt {
        Ok(saved) => saved,
        Err(error) => {
            storage.write_failed = true;
            return Err(error);
        }
    };
    storage.end = end;
    Ok(SealedRecord { offset, length, digest })
}

struct HashingWriter<'a> {
    output: &'a mut File,
    hash: Sha256,
    length: u64,
}

impl<'a> HashingWriter<'a> {
    fn new(output: &'a mut File) -> Self {
        Self { output, hash: Sha256::new(), length: 0 }
    }

    fn finish(self) -> (u64, String) {
        (self.length, trust_types::digest::lowercase_hex(&self.hash.finalize()))
    }
}

impl Write for HashingWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let accepted = self.output.write(bytes)?;
        self.length = self.length.checked_add(u64::try_from(accepted).map_err(invalid)?)
            .ok_or_else(|| invalid("serialized publication length overflow"))?;
        self.hash.update(&bytes[..accepted]);
        Ok(accepted)
    }

    fn flush(&mut self) -> io::Result<()> { self.output.flush() }
}

fn frame_digest(body: &str, rows: usize, offset: u64, length: u64, payload: &str) -> io::Result<String> {
    let mut frame = Vec::new();
    frame.extend_from_slice(DOMAIN);
    frame.extend_from_slice(&u64::try_from(body.len()).map_err(invalid)?.to_be_bytes());
    frame.extend_from_slice(body.as_bytes());
    frame.extend_from_slice(&u64::try_from(rows).map_err(invalid)?.to_be_bytes());
    frame.extend_from_slice(&offset.to_be_bytes());
    frame.extend_from_slice(&length.to_be_bytes());
    // Internally generated lowercase SHA-256 has a fixed 64-byte spelling.
    frame.extend_from_slice(payload.as_bytes());
    Ok(trust_types::stable_sha256_hex(&frame))
}

fn record_digest(
    storage: &mut Storage,
    body: &str,
    rows: usize,
    offset: u64,
    length: u64,
) -> io::Result<String> {
    let metadata = storage.file.metadata()?;
    let end = offset.checked_add(length).ok_or_else(|| invalid("record extent overflow"))?;
    if Identity::of(&metadata)? != storage.identity || metadata.len() < end {
        return Err(invalid("publication record descriptor or extent changed"));
    }
    storage.file.seek(SeekFrom::Start(offset))?;
    let payload = trust_types::digest::stable_sha256_hex_reader((&mut storage.file).take(length))?;
    frame_digest(body, rows, offset, length, &payload)
}

impl<T: DeserializeOwned> Saved<T> {
    /// Exactly one emission attempt. Body/row identity comes from the live
    /// caller's prepared record, not from untrusted serialized fields. The
    /// storage lock spans both commitment validation and decode, so no other
    /// internal append can race that read; no external writer owns its file.
    pub(super) fn consume(&mut self, body: &str, rows: usize) -> io::Result<T> {
        if std::mem::replace(&mut self.consumed, true) {
            return Err(invalid("publication record already consumed"));
        }
        if body != self.body || rows != self.rows {
            return Err(invalid("publication record body or row inventory mismatch"));
        }
        let mut storage = self.storage.0.lock().map_err(|_| invalid("publication storage lock poisoned"))?;
        let digest = record_digest(&mut storage, body, rows, self.offset, self.length)?;
        if digest != self.digest {
            return Err(invalid("publication record content changed"));
        }
        storage.file.seek(SeekFrom::Start(self.offset))?;
        let bounded = (&mut storage.file).take(self.length);
        let mut decoder = serde_json::Deserializer::from_reader(bounded);
        let value = T::deserialize(&mut decoder).map_err(invalid)?;
        decoder.end().map_err(invalid)?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
