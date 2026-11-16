// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LOCAL KERNEL FACTS (Trust TG6, decision `COMPILE-TIME-FACTS-1`): the store,
//! the compiler identity and the per-process context a keyed Clean session
//! ([`crate::clean_island::CleanIslandSession`]) reads and writes facts through.
//!
//! The owner's rule (2026-11-05): "if the functions and proofs don't change,
//! you don't rerun! you already hav facts!". One elaboration of a session (a
//! header-first batch, or one sequential island) is a FACT, keyed by
//! everything it read; a later session that would perform the same
//! elaboration on the same content imports the fact's declarations instead of
//! elaborating and checking them again. What goes into a key, and why that is
//! everything, is [`crate::clean_island`]'s `keyed_env` module's business; this
//! module only stores bytes under keys, safely.
//!
//! # The store
//!
//! `{cargo home}/trust/results/v1/clean-kernel-facts-v1/` (STORE-1's one cache
//! root; the cargo home is `CARGO_HOME`, else `~/.cargo`, resolved here, by the
//! compiler, because every ordinary build reads facts and not every build is
//! driven by Targo). There is no flag that skips, refreshes, disables or
//! relocates it (STORE-1); a test isolates it with a cargo home of its own.
//!
//! * `objects/<ab>/<sha256>`: a fact's bytes, named by their SHA-256. Every
//!   read re-hashes them; a mismatch quarantines the object and is a miss.
//! * `index/<ab>/<key>`: the hex SHA-256 of the object holding the fact for
//!   that key. Keys hold no paths, so every worktree of one cargo home shares
//!   them.
//! * `quarantine/`: what a read or the audit refused, kept for a person to read.
//! * `identity/`: the driver image digests, memoized by the mapped image's
//!   device, inode, size, modification and status-change times.
//!
//! Every directory is `0700` and every file `0600`, this user's, written by a
//! create-new temporary and an atomic rename, and every read checks the open
//! descriptor (a regular file, this user's, private). STORE-1's permission
//! rule holds: the store's path is resolved once, and when any ancestor of it
//! is group- or world-writable, or owned by anyone but this user or root, there
//! is no store and every session checks afresh. Ancestor ACL grants also refuse;
//! store directories and files require no extended ACL entries, observed on
//! their open descriptors. Off unix there is no store.
//!
//! # What a fact is worth
//!
//! A fact read here was written by a process of the same compiler identity
//! (the identity is part of every key) on this machine, under this user's
//! private directory. `COMPILE-TIME-FACTS-1` makes such a fact the discharge of
//! its obligations in every build; `docs/TCB.md`'s TG6 row says what that adds
//! to the trusted base (the store's integrity against a same-user writer is
//! `KNOWN_HAZARDS.md` P-CORESIDENT: SHA-256 detects corruption, not forgery).
//! The defeq faithfulness verdict is never a fact.

use std::fmt::Display;
use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;

use sha2::{Digest, Sha256};

/// The format of a stored fact; part of every key. v4 combines reference-island
/// acceptance and anonymous-judgment dependencies with exact model metadata
/// reads and the prepared continuation's original constant-name set.
pub const FACT_FORMAT: &str = "trust.clean-kernel-fact.v4-reference-islands-model-metadata";
const DIRECTORY: &str = "clean-kernel-facts-v1";
/// A fact holds a batch's whole environment delta and the elaboration log
/// that re-checks it; this bounds what a read will load.
const MAX_FACT_BYTES: u64 = 1024 * 1024 * 1024;
/// One hit in 32, chosen by the key's first byte, is re-elaborated and
/// compared (STORE-1's audit sample, by key prefix).
const AUDIT_ONE_IN: u32 = 32;
/// Set to `1` to print one `TRUST_CLEAN_FACT …` line per event on stderr. A
/// report channel only: it changes no key and no decision.
pub const STATS_ENV: &str = "TRUST_CLEAN_FACT_STATS";

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// A SHA-256 digest.
pub type Digest32 = [u8; 32];

/// SHA-256 over length-prefixed parts, so no two part lists collide.
#[must_use]
pub fn digest_parts(parts: &[&[u8]]) -> Digest32 {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hasher.finalize().into()
}

/// Lower-case hex.
#[must_use]
pub fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn parse_hex32(text: &str) -> Option<Digest32> {
    let text = text.trim();
    if text.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (index, chunk) in text.as_bytes().chunks(2).enumerate() {
        let pair = std::str::from_utf8(chunk).ok()?;
        out[index] = u8::from_str_radix(pair, 16).ok()?;
    }
    Some(out)
}

/// Whether [`STATS_ENV`] asks for event lines.
#[must_use]
pub fn stats_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os(STATS_ENV).is_some_and(|value| value == "1"))
}

/// Print one event line when [`stats_enabled`].
pub(crate) fn stat(event: &str, detail: impl Display) {
    if stats_enabled() {
        eprintln!("TRUST_CLEAN_FACT {event} {detail}");
    }
}

/// The one encoding of everything a fact holds: bincode's default options
/// (variable-length integers, trailing bytes refused), bounded by the largest
/// fact a read loads.
fn codec() -> impl bincode::Options {
    use bincode::Options as _;
    bincode::DefaultOptions::new().with_limit(MAX_FACT_BYTES)
}

/// Encode `value` in the fact codec.
pub(crate) fn encode<T: serde::Serialize + ?Sized>(value: &T) -> Option<Vec<u8>> {
    use bincode::Options as _;
    codec().serialize(value).ok()
}

/// Decode a value of the fact codec, refusing trailing bytes.
pub(crate) fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, String> {
    use bincode::Options as _;
    codec().deserialize(bytes).map_err(|error| error.to_string())
}

// ---------------------------------------------------------------------------
// Private files
// ---------------------------------------------------------------------------

/// Off unix there is no store. STORE-1's permission rule is a rule about owners
/// and mode bits, and nothing here checks what stands for them elsewhere (a
/// Windows folder inherits its parent's access list, so every user may write
/// it), so no fact is read or written and every session checks afresh.
#[cfg(not(unix))]
const NO_STORE_OFF_UNIX: &str =
    "no local kernel fact store off unix: STORE-1's permission rule cannot be checked here";

/// The store's tables, each a directory under its root.
const TABLES: [&str; 4] = ["objects", "index", "quarantine", "identity"];

/// The suffix of a temporary a write renames into place.
const PARTIAL: &str = ".partial";

/// A temporary this old was left by a writer that died before its rename (a
/// live writer renames within seconds: a fact is at most [`MAX_FACT_BYTES`]),
/// and is removed.
const STALE_PARTIAL: Duration = Duration::from_secs(60 * 60);

#[cfg(unix)]
fn euid() -> u32 {
    nix::unistd::geteuid().as_raw()
}

/// Whether `metadata` is of this user's, with none of the `others` mode bits.
#[cfg(unix)]
fn owned_without(metadata: &fs::Metadata, others: u32) -> bool {
    use std::os::unix::fs::MetadataExt;
    metadata.uid() == euid() && metadata.mode() & others == 0
}

/// Observe permissions and ACLs through a real directory descriptor. In
/// particular, following a final symlink cannot turn its target into the
/// directory whose permissions a caller just admitted.
#[cfg(unix)]
fn directory_handle(path: &Path) -> io::Result<fs::File> {
    use nix::fcntl::OFlag;
    nix::fcntl::open(
        path,
        OFlag::O_RDONLY | OFlag::O_DIRECTORY | OFlag::O_NOFOLLOW | OFlag::O_CLOEXEC,
        nix::sys::stat::Mode::empty(),
    )
    .map(fs::File::from)
    .map_err(io::Error::from)
}

/// The store's directory under `cargo_home`, created as needed under STORE-1's
/// permission rule, resolved exactly once.
///
/// The deepest entry on the way that exists (a symlink counts, so a dangling
/// one refuses) is canonicalized, and that path and each of its ancestors must
/// be owned by this user or root and writable by no one else (the rule OpenSSH's
/// `StrictModes` applies: the owner of an ancestor could rename the tree away
/// and plant another). Each missing component is then created beneath it, one
/// at a time, and must be a real directory of this user's that no one else can
/// write; the store's own directory is this user's and private. The path
/// returned has no symlink in it and is never resolved again: a symlink on the
/// way that changes later changes nothing.
#[cfg(unix)]
fn private_root(cargo_home: &Path) -> io::Result<PathBuf> {
    use std::os::unix::fs::{DirBuilderExt, MetadataExt};
    if !cargo_home.is_absolute() {
        return Err(io::Error::other("the cargo home is not an absolute path"));
    }
    let store = cargo_home.join("trust").join("results").join("v1").join(DIRECTORY);
    let mut existing = store.as_path();
    let mut missing = Vec::new();
    while let Err(error) = fs::symlink_metadata(existing) {
        let (io::ErrorKind::NotFound, Some(parent), Some(name)) =
            (error.kind(), existing.parent(), existing.file_name())
        else {
            return Err(error);
        };
        missing.push(name.to_owned());
        existing = parent;
    }
    let mut path = existing.canonicalize()?;
    for ancestor in path.ancestors() {
        let directory = directory_handle(ancestor)?;
        let metadata = directory.metadata()?;
        if !(metadata.uid() == euid() || metadata.uid() == 0) || metadata.mode() & 0o022 != 0 {
            return Err(io::Error::other(
                "a fact store ancestor is group- or world-writable, or another user's",
            ));
        }
        // Deny-only ancestor ACLs grant no access (macOS home directories
        // commonly have one). Any allow entry is outside STORE-1's boundary.
        trust_resource_provenance::require_no_acl_grants(&directory)?;
    }
    // `missing` runs from the store's own directory out; create it inward.
    for (depth, name) in missing.iter().enumerate().rev() {
        path.push(name);
        if depth == 0 {
            break;
        }
        // No wider than 0755 whatever the umask: under a 002 umask a directory
        // created with the default mode was group-writable, so the process that
        // created the store used it and every later one refused it
        // (`tests/clean_fact_umask.rs`).
        match fs::DirBuilder::new().mode(0o755).create(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
        let directory = directory_handle(&path)?;
        let metadata = directory.metadata()?;
        if !metadata.file_type().is_dir() || !owned_without(&metadata, 0o022) {
            return Err(io::Error::other("a fact store ancestor is not this user's directory"));
        }
        trust_resource_provenance::require_no_acl_grants(&directory)?;
    }
    private_dir(&path)?;
    Ok(path)
}

#[cfg(not(unix))]
fn private_root(_cargo_home: &Path) -> io::Result<PathBuf> {
    Err(io::Error::other(NO_STORE_OFF_UNIX))
}

/// Create (or find) a store directory and check that it is private.
///
/// It is created with mode 0700 (less the umask), never created open and
/// narrowed afterwards: between those two calls a concurrent compiler that
/// found it existing would see group bits, refuse the store as not private and
/// check every session afresh (`concurrent_opens_of_a_fresh_store_all_succeed`).
/// The `set_permissions` that follows can only restore owner bits a umask took.
fn private_dir(path: &Path) -> io::Result<()> {
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    match builder.create(path) {
        Ok(()) => {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(path, fs::Permissions::from_mode(0o700))?;
            }
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    check_private_dir(path)
}

/// A store directory is a real directory (never a symlink), this user's, and
/// open to no one else. A directory another account made in the store (a
/// build run under `sudo` that kept `HOME`) is refused by name, not used.
fn check_private_dir(path: &Path) -> io::Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.file_type().is_dir() {
        return Err(io::Error::other("fact store directory is not a real directory"));
    }
    #[cfg(unix)]
    if !owned_without(&metadata, 0o077) {
        return Err(io::Error::other("fact store directory is not this user's private directory"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let directory = directory_handle(path)?;
        let held = directory.metadata()?;
        if (held.dev(), held.ino()) != (metadata.dev(), metadata.ino())
            || !owned_without(&held, 0o077)
        {
            return Err(io::Error::other("fact store directory changed during permission check"));
        }
        trust_resource_provenance::require_no_acl_entries(&directory)?;
    }
    Ok(())
}

/// Read a store file of at most `limit` bytes. It is opened without following
/// a symlink or waiting on a FIFO, and the open descriptor must be a regular
/// file of this user's that no one else can read or write, so what is checked
/// is what is read.
#[cfg(unix)]
fn read_bounded(path: &Path, limit: u64) -> io::Result<Vec<u8>> {
    use nix::fcntl::OFlag;
    if let Some(parent) = path.parent() {
        check_private_dir(parent)?;
    }
    let file = fs::File::from(
        nix::fcntl::open(
            path,
            OFlag::O_RDONLY | OFlag::O_NOFOLLOW | OFlag::O_NONBLOCK | OFlag::O_CLOEXEC,
            nix::sys::stat::Mode::empty(),
        )
        .map_err(io::Error::from)?,
    );
    let metadata = file.metadata()?;
    if !metadata.file_type().is_file() || metadata.len() > limit {
        return Err(io::Error::other("not a bounded regular file"));
    }
    if !owned_without(&metadata, 0o077) {
        return Err(io::Error::other("fact store file is not this user's private file"));
    }
    trust_resource_provenance::require_no_acl_entries(&file)?;
    let mut bytes = Vec::new();
    file.take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(io::Error::other("oversized fact store file"));
    }
    Ok(bytes)
}

#[cfg(not(unix))]
fn read_bounded(_path: &Path, _limit: u64) -> io::Result<Vec<u8>> {
    Err(io::Error::other(NO_STORE_OFF_UNIX))
}

/// A name no other write of this process, or of any other, takes:
/// `{pid}.{nonce}.{n}`. The nonce is drawn once per process from the system's
/// randomness, so a process whose pid a killed writer had (routine on a busy
/// host, near certain in a fresh pid namespace sharing a cargo home) still gets
/// names that writer never used.
fn unique_stamp() -> String {
    static NONCE: OnceLock<u64> = OnceLock::new();
    let nonce = *NONCE.get_or_init(|| {
        use std::hash::BuildHasher as _;
        std::collections::hash_map::RandomState::new().hash_one(std::process::id())
    });
    format!("{}.{nonce:016x}.{}", std::process::id(), NEXT_TEMP.fetch_add(1, Ordering::Relaxed))
}

fn atomic_write(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    private_dir(directory)?;
    reclaim_partials(directory);
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    // A name a dead writer left behind is skipped, never an error.
    let mut attempt = 0;
    let (temporary, mut file) = loop {
        let temporary = directory.join(format!(".{}{PARTIAL}", unique_stamp()));
        match options.open(&temporary) {
            Ok(file) => break (temporary, file),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists && attempt < 8 => {
                attempt += 1;
            }
            Err(error) => return Err(error),
        }
    };
    let result = (|| {
        #[cfg(unix)]
        trust_resource_provenance::require_no_acl_entries(&file)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        fs::rename(&temporary, directory.join(name))
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

/// Remove each temporary in `directory` that a writer killed before its
/// rename left behind (a Ctrl-C, a timeout's SIGKILL, the OOM killer), once it
/// is [`STALE_PARTIAL`] old. Every write sweeps the directory it writes into,
/// and every rescan sweeps the whole store.
fn reclaim_partials(directory: &Path) {
    let Ok(entries) = fs::read_dir(directory) else { return };
    for entry in entries.flatten() {
        let name = entry.file_name();
        if !name.to_str().is_some_and(|name| name.starts_with('.') && name.ends_with(PARTIAL)) {
            continue;
        }
        // `DirEntry::metadata` does not follow a symlink.
        let stale = entry
            .metadata()
            .ok()
            .filter(|metadata| metadata.file_type().is_file())
            .and_then(|metadata| metadata.modified().ok())
            .and_then(|modified| modified.elapsed().ok())
            .is_some_and(|age| age >= STALE_PARTIAL);
        if stale {
            let _ = fs::remove_file(entry.path());
        }
    }
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

/// What [`FactStore::get`] found under a key.
#[derive(Debug)]
pub(crate) enum StoreRead {
    /// No fact for the key.
    Absent,
    /// A fact whose bytes match their content address.
    Present { object: Digest32, bytes: Vec<u8> },
    /// The index or the object was unreadable or did not match its address;
    /// it is quarantined and the read is a miss.
    Quarantined(String),
}

/// The fact store; see the module docs.
#[derive(Debug, Clone)]
pub struct FactStore {
    root: PathBuf,
}

/// What a rescan found.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RescanReport {
    /// Objects whose bytes match their address.
    pub sound: usize,
    /// Objects quarantined because they did not.
    pub quarantined: usize,
    /// Index entries removed because their object is gone or quarantined.
    pub dangling: usize,
    /// Objects removed because no index entry names them (each at least
    /// [`STALE_PARTIAL`] old, so none a writer is about to name).
    pub collected: usize,
}

/// An entry of a table, named by a digest and in that digest's shard.
struct Entry {
    name: Digest32,
    path: PathBuf,
    regular: bool,
}

/// Every entry two levels under `table` (`table/<ab>/<name>`) whose name is a
/// lower-case hex SHA-256 in its own shard: the only names the store reads or
/// writes. Anything else (an editor's autosave, a stray short or non-UTF-8
/// name, a temporary) is never read, so it is left where it is.
fn entries(table: &Path) -> Vec<Entry> {
    let mut out = Vec::new();
    let Ok(shards) = fs::read_dir(table) else { return out };
    for shard in shards.flatten() {
        let shard_name = shard.file_name();
        let Ok(names) = fs::read_dir(shard.path()) else { continue };
        for entry in names.flatten() {
            let Some(name) = entry.file_name().to_str().and_then(parse_canonical_hex32) else {
                continue;
            };
            if shard_name.to_str() != Some(hex(&name[..1]).as_str()) {
                continue;
            }
            let regular = entry.file_type().is_ok_and(|kind| kind.is_file());
            out.push(Entry { name, path: entry.path(), regular });
        }
    }
    out.sort_by_key(|entry| entry.name);
    out
}

/// `text` as a digest when it is exactly a digest's lower-case hex.
fn parse_canonical_hex32(text: &str) -> Option<Digest32> {
    parse_hex32(text).filter(|digest| hex(digest) == text)
}

impl FactStore {
    /// The cargo home the compiler's store lives under: `CARGO_HOME` (against
    /// the working directory when relative), else `~/.cargo` — Cargo's own
    /// resolution, and Targo's (`config::cargo_home`).
    #[must_use]
    pub fn cargo_home() -> Option<PathBuf> {
        if let Some(home) = std::env::var_os("CARGO_HOME").filter(|home| !home.is_empty()) {
            let home = PathBuf::from(home);
            return if home.is_absolute() {
                Some(home)
            } else {
                std::env::current_dir().ok().map(|cwd| cwd.join(home))
            };
        }
        std::env::var_os("HOME")
            .filter(|home| !home.is_empty())
            .map(|home| PathBuf::from(home).join(".cargo"))
    }

    /// Open (creating) the store under `cargo_home`, refusing under STORE-1's
    /// permission rule (see [`private_root`]); off unix there is no store.
    pub fn open(cargo_home: &Path) -> io::Result<Self> {
        let root = private_root(cargo_home)?;
        for table in TABLES {
            private_dir(&root.join(table))?;
        }
        Ok(Self { root })
    }

    /// The store's directory.
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    fn shard(&self, table: &str, name: &Digest32) -> PathBuf {
        self.root.join(table).join(hex(&name[..1]))
    }

    fn path_of(&self, table: &str, name: &Digest32) -> PathBuf {
        self.shard(table, name).join(hex(name))
    }

    /// Read the fact stored for `key`, checking its content address.
    pub(crate) fn get(&self, key: &Digest32) -> StoreRead {
        let pointer = match read_bounded(&self.path_of("index", key), 128) {
            Ok(pointer) => pointer,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return StoreRead::Absent,
            Err(error) => {
                let why = format!("index entry unreadable: {error}");
                self.quarantine_index(key, &why);
                return StoreRead::Quarantined(why);
            }
        };
        let Some(object) = std::str::from_utf8(&pointer).ok().and_then(parse_hex32) else {
            let why = "index entry is not a SHA-256".to_string();
            self.quarantine_index(key, &why);
            return StoreRead::Quarantined(why);
        };
        let object_hex = hex(&object);
        let why = match read_bounded(&self.path_of("objects", &object), MAX_FACT_BYTES) {
            Ok(bytes) if <[u8; 32]>::from(Sha256::digest(&bytes)) == object => {
                return StoreRead::Present { object, bytes };
            }
            Ok(_) => format!("object {object_hex} does not match its SHA-256"),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let why = format!("object {object_hex} is gone");
                self.quarantine_index(key, &why);
                return StoreRead::Quarantined(why);
            }
            Err(error) => format!("object {object_hex} unreadable: {error}"),
        };
        // An object that cannot serve is moved away with its index entry, so
        // the next `put` of the same bytes writes it afresh instead of naming
        // it again.
        self.quarantine_object(&object, &why);
        self.quarantine_index(key, &why);
        StoreRead::Quarantined(why)
    }

    /// Store `bytes` as the fact for `key`: the object first, then the index
    /// entry naming it, each atomically. An object already stored under the
    /// same address is kept only when it holds those bytes.
    pub(crate) fn put(&self, key: &Digest32, bytes: &[u8]) -> io::Result<Digest32> {
        let object: Digest32 = Sha256::digest(bytes).into();
        let path = self.path_of("objects", &object);
        let sound = read_bounded(&path, MAX_FACT_BYTES)
            .is_ok_and(|stored| <[u8; 32]>::from(Sha256::digest(&stored)) == object);
        if !sound {
            if fs::symlink_metadata(&path).is_ok() {
                self.quarantine_object(&object, "the stored object does not hold its bytes");
            }
            atomic_write(&self.shard("objects", &object), &hex(&object), bytes)?;
        }
        atomic_write(&self.shard("index", key), &hex(key), hex(&object).as_bytes())?;
        Ok(object)
    }

    /// Move the fact for `key` (its index entry and its object) to the
    /// quarantine, with the reason, and drop every other index entry that
    /// named the object. The objects are not re-hashed here: every read
    /// re-hashes what it serves, and `targo trust store verify --facts`
    /// re-hashes the whole store; doing it inside the compiler on each
    /// quarantine read every object once per fact a diverging session applied.
    pub(crate) fn quarantine_fact(&self, key: &Digest32, object: &Digest32, why: &str) {
        self.quarantine_object(object, why);
        self.quarantine_index(key, why);
        let mut report = RescanReport::default();
        self.sweep_index(&mut report);
        stat("RESCAN", format_args!("{report:?}"));
    }

    fn quarantine_object(&self, object: &Digest32, why: &str) -> bool {
        let name = format!("object-{}", hex(object));
        self.quarantine_file(&self.path_of("objects", object), &name, why)
    }

    fn quarantine_index(&self, key: &Digest32, why: &str) -> bool {
        let moved =
            self.quarantine_file(&self.path_of("index", key), &format!("index-{}", hex(key)), why);
        if moved {
            stat("QUARANTINE", format_args!("key={} why={why}", hex(key)));
        }
        moved
    }

    /// Move `from` to the quarantine with a record of why, for a person to
    /// read; one that cannot be moved is removed (a refused entry must never be
    /// read again). True when there was an entry and it is gone from its
    /// table: when there was nothing to move, nothing is recorded.
    fn quarantine_file(&self, from: &Path, name: &str, why: &str) -> bool {
        let quarantine = self.root.join("quarantine");
        let kept = format!("{name}.{}", unique_stamp());
        if fs::rename(from, quarantine.join(&kept)).is_ok() {
            let _ = atomic_write(&quarantine, &format!("{kept}.why"), why.as_bytes());
            return true;
        }
        fs::remove_file(from).is_ok()
    }

    /// Re-hash every object; quarantine each one that does not match its
    /// address, drop every index entry whose object is gone, and remove the
    /// objects no index entry names. An entry another process moved away
    /// meanwhile is not counted, and temporaries dead writers left are
    /// removed.
    pub fn rescan(&self) -> RescanReport {
        let mut report = RescanReport::default();
        self.reclaim_all_partials();
        for entry in entries(&self.root.join("objects")) {
            let why = if entry.regular {
                match read_bounded(&entry.path, MAX_FACT_BYTES) {
                    Ok(bytes) if <[u8; 32]>::from(Sha256::digest(&bytes)) == entry.name => {
                        report.sound += 1;
                        continue;
                    }
                    Ok(_) => "rescan: does not match its SHA-256".to_string(),
                    Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                    Err(error) => format!("rescan: unreadable: {error}"),
                }
            } else {
                "rescan: not a regular file".to_string()
            };
            if self.quarantine_object(&entry.name, &why) {
                report.quarantined += 1;
            }
        }
        let named = self.sweep_index(&mut report);
        // An object no index entry names was superseded under its key, or its
        // entry was quarantined. One younger than a temporary's lifetime may be
        // one a writer stored and is about to name, so it is kept; removing one
        // a writer names after all costs a miss, never a wrong hit.
        for entry in entries(&self.root.join("objects")) {
            let old = fs::symlink_metadata(&entry.path)
                .ok()
                .and_then(|metadata| metadata.modified().ok())
                .and_then(|modified| modified.elapsed().ok())
                .is_some_and(|age| age >= STALE_PARTIAL);
            if entry.regular
                && old
                && !named.contains(&entry.name)
                && fs::remove_file(&entry.path).is_ok()
            {
                report.collected += 1;
            }
        }
        report
    }

    /// Drop every index entry whose object is gone or that cannot be read,
    /// counting each in `report`; the objects the remaining entries name.
    fn sweep_index(&self, report: &mut RescanReport) -> std::collections::BTreeSet<Digest32> {
        let mut named = std::collections::BTreeSet::new();
        for entry in entries(&self.root.join("index")) {
            let pointer = if entry.regular {
                read_bounded(&entry.path, 128)
            } else {
                Err(io::Error::other("not a regular file"))
            };
            let why = match pointer {
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => format!("rescan: unreadable: {error}"),
                Ok(pointer) => {
                    let live =
                        std::str::from_utf8(&pointer).ok().and_then(parse_hex32).filter(|object| {
                            fs::symlink_metadata(self.path_of("objects", object))
                                .is_ok_and(|metadata| metadata.file_type().is_file())
                        });
                    if let Some(object) = live {
                        named.insert(object);
                        continue;
                    }
                    "rescan: its object is gone".to_string()
                }
            };
            if self.quarantine_index(&entry.name, &why) {
                report.dangling += 1;
            }
        }
        named
    }

    fn reclaim_all_partials(&self) {
        reclaim_partials(&self.root.join("quarantine"));
        for table in ["objects", "index", "identity"] {
            let Ok(shards) = fs::read_dir(self.root.join(table)) else { continue };
            for shard in shards.flatten() {
                if shard.file_type().is_ok_and(|kind| kind.is_dir()) {
                    reclaim_partials(&shard.path());
                }
            }
        }
    }

    /// Every key with an index entry, sorted.
    #[must_use]
    pub fn keys(&self) -> Vec<Digest32> {
        entries(&self.root.join("index"))
            .into_iter()
            .filter(|entry| entry.regular)
            .map(|entry| entry.name)
            .collect()
    }

    /// The memoized digest of a driver image, keyed by what changes when its
    /// bytes do (never its path).
    fn image_memo(&self, stamp: &str) -> Option<String> {
        let name: Digest32 = Sha256::digest(stamp.as_bytes()).into();
        let bytes = read_bounded(&self.path_of("identity", &name), 4096).ok()?;
        String::from_utf8(bytes).ok()
    }

    fn remember_image(&self, stamp: &str, record: &str) {
        let name: Digest32 = Sha256::digest(stamp.as_bytes()).into();
        let _ = atomic_write(&self.shard("identity", &name), &hex(&name), record.as_bytes());
    }
}

// ---------------------------------------------------------------------------
// The compiler identity
// ---------------------------------------------------------------------------

/// The file a running checker's code is mapped from, as the kernel reports
/// it: its device and inode, in `std::os::unix::fs::MetadataExt`'s terms.
/// The compiler asks for it (`rustc_session::filesearch::current_dll_mapping`),
/// because this crate forbids the `unsafe` a loader query needs.
///
/// The path the checker was loaded from can name another file by the time a
/// compiler first opens its facts: a toolchain rebuilt at the same commit
/// unlinks the old driver and writes the new one under its name while
/// processes that loaded the old one still run. The identity is taken from the
/// file at that path only when it is this mapped file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MappedImage {
    /// `st_dev` of the mapped file.
    pub device: u64,
    /// `st_ino` of the mapped file.
    pub inode: u64,
}

/// Who produced a fact: the trustc commit, the Clean kernel's version and
/// delta format, and the SHA-256 of the image the checking code runs from
/// (the compiler's driver library, which links this crate and Clean). The
/// image digest covers the Clean commit and every other byte of the checker;
/// nothing else is needed for "the same compiler", and nothing less would do.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilerIdentity {
    digest: Digest32,
    prelude: Digest32,
}

impl CompilerIdentity {
    /// The identity digest.
    #[must_use]
    pub fn digest(&self) -> &Digest32 {
        &self.digest
    }

    /// The content digest of Clean's built-in prelude in this image.
    #[must_use]
    pub fn prelude(&self) -> &Digest32 {
        &self.prelude
    }

    fn of_image(
        trustc_commit: &str,
        image: &Path,
        mapped: MappedImage,
        store: &FactStore,
    ) -> Option<Self> {
        let (image, prelude) = image_and_prelude_digest(store, image, mapped)?;
        // v2: the image is the mapped file, never whatever its path names when
        // the store opens. A v1 identity could name a replaced image (TG6
        // review, 2026-11-06), so no v1 fact is reachable.
        let digest = digest_parts(&[
            b"trust.clean-kernel-fact.identity.v2-mapped-image",
            trustc_commit.as_bytes(),
            clean_kernel::VERSION.as_bytes(),
            clean_kernel::env::LOCAL_FACT_DELTA_FORMAT.as_bytes(),
            &image,
        ]);
        Some(Self { digest, prelude })
    }

    /// An identity for unit tests, distinct per `tag`.
    #[cfg(test)]
    pub(crate) fn for_tests(tag: &str) -> Self {
        Self {
            digest: digest_parts(&[b"test identity", tag.as_bytes()]),
            prelude: prelude_content_digest(),
        }
    }
}

fn prelude_content_digest() -> Digest32 {
    let total = clean_kernel::Environment::with_prelude().content_digest().total;
    digest_parts(&[b"prelude", total.as_bytes()])
}

/// The SHA-256 of the image this process runs and its prelude digest.
///
/// The file at `image` is opened, and it is the image only when its device and
/// inode are `mapped`'s: then the descriptor reads the very file the code is
/// mapped from (a mapped file's inode cannot be reused while it is mapped).
/// Its digest is memoized in the store by that file's device, inode, size,
/// modification and status-change times (a status change cannot be set by its
/// owner, so a file rewritten in place always misses the memo), and a read
/// during which those changed is refused. The memo's prelude digest was
/// computed by a process running that same file, so it is this image's.
#[cfg(unix)]
fn image_and_prelude_digest(
    store: &FactStore,
    image: &Path,
    mapped: MappedImage,
) -> Option<(Digest32, Digest32)> {
    use std::os::unix::fs::MetadataExt;
    let stamp = |metadata: &fs::Metadata| {
        format!(
            "v2:{}:{}:{}:{}.{}:{}.{}",
            metadata.dev(),
            metadata.ino(),
            metadata.size(),
            metadata.mtime(),
            metadata.mtime_nsec(),
            metadata.ctime(),
            metadata.ctime_nsec()
        )
    };
    let mut file = fs::File::open(image).ok()?;
    let before = file.metadata().ok()?;
    if !before.file_type().is_file()
        || (before.dev(), before.ino()) != (mapped.device, mapped.inode)
    {
        stat(
            "UNMAPPED",
            format_args!("{} is not the image this process runs; no identity", image.display()),
        );
        return None;
    }
    let stamp_before = stamp(&before);
    if let Some(record) = store.image_memo(&stamp_before) {
        let mut parts = record.split(' ');
        if let (Some(image), Some(prelude), None) =
            (parts.next().and_then(parse_hex32), parts.next().and_then(parse_hex32), parts.next())
        {
            return Some((image, prelude));
        }
    }
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(read) => hasher.update(&buffer[..read]),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(_) => return None,
        }
    }
    if stamp(&file.metadata().ok()?) != stamp_before {
        stat(
            "UNMAPPED",
            format_args!("{} changed while it was read; no identity", image.display()),
        );
        return None;
    }
    let digest: Digest32 = hasher.finalize().into();
    let prelude = prelude_content_digest();
    store.remember_image(&stamp_before, &format!("{} {}", hex(&digest), hex(&prelude)));
    Some((digest, prelude))
}

/// No store opens off unix, so no identity is ever asked for there.
#[cfg(not(unix))]
fn image_and_prelude_digest(
    _store: &FactStore,
    _image: &Path,
    _mapped: MappedImage,
) -> Option<(Digest32, Digest32)> {
    None
}

// ---------------------------------------------------------------------------
// The context a keyed session reads facts through
// ---------------------------------------------------------------------------

/// The Clean-relevant environment of this process: every variable Clean's
/// elaborator or kernel consults (by prefix), name and value, sorted.
fn ambient_digest() -> Digest32 {
    const PREFIXES: &[&str] = &["CLEAN_", "DENY_SORRY", "MATHVERSE_", "LEAN"];
    let mut vars: Vec<(String, String)> = std::env::vars_os()
        .filter_map(|(name, value)| {
            let name = name.into_string().ok()?;
            PREFIXES
                .iter()
                .any(|prefix| name.starts_with(prefix))
                .then(|| (name, value.to_string_lossy().into_owned()))
        })
        .collect();
    vars.sort();
    let mut parts: Vec<&[u8]> = vec![b"ambient"];
    for (name, value) in &vars {
        parts.push(name.as_bytes());
        parts.push(value.as_bytes());
    }
    digest_parts(&parts)
}

/// The store, the identity and the target facts are read under.
#[derive(Debug)]
pub struct FactContext {
    store: FactStore,
    identity: CompilerIdentity,
    pointer_width: u32,
    ambient: Digest32,
    /// `None` in every compiler: one hit in 32 is audited, by key prefix.
    /// Only a unit test sets it (`for_tests`): every hit, or none, so a
    /// test's expectations do not depend on where its keys fall.
    audit_override: Option<bool>,
    /// Every fact written in this process, for a test to count.
    written: Mutex<usize>,
}

impl FactContext {
    /// The context of this compiler process for a target of `pointer_width`
    /// bits, or `None` when there is no usable store (no cargo home, an
    /// ancestor another user could write, a host off unix) or no identity (the
    /// driver's path no longer names the image this process runs, or it cannot
    /// be read), and every session then checks afresh. Opened once per process
    /// and width. `image` is the file the checking code runs from (the driver
    /// library) and the kernel's account of the file it is mapped from;
    /// without one there is no identity, so no facts.
    #[must_use]
    pub fn for_compiler(
        pointer_width: u32,
        trustc_commit: &'static str,
        image: Option<(&Path, MappedImage)>,
    ) -> Option<Arc<Self>> {
        type Opened = Mutex<Vec<(u32, Option<Arc<FactContext>>)>>;
        static OPENED: OnceLock<Opened> = OnceLock::new();
        let opened = OPENED.get_or_init(|| Mutex::new(Vec::new()));
        let mut opened = opened.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some((_, context)) = opened.iter().find(|(width, _)| *width == pointer_width) {
            return context.clone();
        }
        let context = image
            .zip(FactStore::cargo_home())
            .and_then(|((image, mapped), home)| {
                Self::open_in(&home, pointer_width, trustc_commit, image, mapped).ok()
            })
            .map(Arc::new);
        if context.is_none() {
            stat(
                "UNAVAILABLE",
                "no private store or no image identity; every session checks afresh",
            );
        }
        opened.push((pointer_width, context.clone()));
        context
    }

    /// Open the context under an explicit cargo home, for the checker running
    /// from `image`, which the kernel reports mapped from `mapped`.
    pub fn open_in(
        cargo_home: &Path,
        pointer_width: u32,
        trustc_commit: &str,
        image: &Path,
        mapped: MappedImage,
    ) -> io::Result<Self> {
        let store = FactStore::open(cargo_home)?;
        let identity = CompilerIdentity::of_image(trustc_commit, image, mapped, &store)
            .ok_or_else(|| io::Error::other("the checker's image has no identity"))?;
        Ok(Self::with_identity(store, identity, pointer_width))
    }

    fn with_identity(store: FactStore, identity: CompilerIdentity, pointer_width: u32) -> Self {
        Self {
            store,
            identity,
            pointer_width,
            ambient: ambient_digest(),
            audit_override: None,
            written: Mutex::new(0),
        }
    }

    /// A context for unit tests: a store under `cargo_home`, an identity named
    /// by `tag`, and every hit audited when `audit_every_hit`, none otherwise
    /// (the compiler's 1-in-32 sample is pinned by its own test).
    #[cfg(test)]
    pub(crate) fn for_tests(cargo_home: &Path, tag: &str, audit_every_hit: bool) -> Self {
        let store = FactStore::open(cargo_home).expect("test store");
        let mut context = Self::with_identity(store, CompilerIdentity::for_tests(tag), 64);
        context.audit_override = Some(audit_every_hit);
        context
    }

    /// The store.
    #[must_use]
    pub fn store(&self) -> &FactStore {
        &self.store
    }

    /// The identity.
    #[must_use]
    pub fn identity(&self) -> &CompilerIdentity {
        &self.identity
    }

    /// The key material every fact of this process starts from.
    pub(crate) fn key_prefix(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(160);
        out.extend_from_slice(FACT_FORMAT.as_bytes());
        out.extend_from_slice(&self.identity.digest);
        out.extend_from_slice(&self.identity.prelude);
        out.extend_from_slice(&self.ambient);
        out.extend_from_slice(&self.pointer_width.to_le_bytes());
        out
    }

    /// Whether a hit on `key` is re-elaborated and compared.
    pub(crate) fn audits(&self, key: &Digest32) -> bool {
        self.audit_override.unwrap_or(u32::from(key[0]) < 256 / AUDIT_ONE_IN)
    }

    pub(crate) fn note_written(&self) {
        *self.written.lock().unwrap_or_else(std::sync::PoisonError::into_inner) += 1;
    }

    /// How many facts this context wrote.
    #[must_use]
    pub fn written(&self) -> usize {
        *self.written.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

/// A private scratch cargo home for a unit test, beside the test binary (the
/// system temporary directory is world-writable on Linux, and STORE-1 refuses
/// a store under it).
#[cfg(test)]
pub(crate) fn test_scratch(tag: &str) -> PathBuf {
    let base = std::env::current_exe()
        .ok()
        .and_then(|exe| exe.parent().map(Path::to_path_buf))
        .unwrap_or_else(std::env::temp_dir)
        .join("trust-clean-fact-scratch");
    let dir = base.join(format!(
        "{tag}-{}-{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        for path in [&base, &dir] {
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).expect("private");
        }
    }
    dir
}

// The store exists only on unix (STORE-1); so do its tests.
#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn scratch(tag: &str) -> PathBuf {
        test_scratch(&format!("clean-fact-{tag}"))
    }

    #[test]
    fn a_stored_fact_reads_back_by_its_key() {
        let home = scratch("roundtrip");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"k"]);
        assert!(matches!(store.get(&key), StoreRead::Absent));
        let object = store.put(&key, b"fact bytes").expect("put");
        match store.get(&key) {
            StoreRead::Present { object: read, bytes } => {
                assert_eq!(read, object);
                assert_eq!(bytes, b"fact bytes");
            }
            other => panic!("expected the fact, got {other:?}"),
        }
        assert_eq!(store.keys(), vec![key]);
        let _ = fs::remove_dir_all(home);
    }

    /// NEGATIVE CONTROL: a flipped byte in a stored object is quarantined on
    /// read, the read is a miss, and the next read finds nothing.
    #[test]
    fn a_flipped_byte_is_quarantined() {
        let home = scratch("flip");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"k"]);
        let object = store.put(&key, b"fact bytes").expect("put");
        let path = store.path_of("objects", &object);
        let mut bytes = fs::read(&path).expect("object");
        bytes[0] ^= 1;
        fs::write(&path, bytes).expect("flip");
        assert!(matches!(store.get(&key), StoreRead::Quarantined(_)));
        assert!(matches!(store.get(&key), StoreRead::Absent));
        assert!(
            fs::read_dir(store.root().join("quarantine")).expect("quarantine").count() > 0,
            "the refused fact is kept for a person to read"
        );
        let _ = fs::remove_dir_all(home);
    }

    #[test]
    fn a_rescan_quarantines_every_corrupt_object() {
        let home = scratch("rescan");
        let store = FactStore::open(&home).expect("store");
        let good = digest_parts(&[b"good"]);
        let bad = digest_parts(&[b"bad"]);
        store.put(&good, b"good fact").expect("put");
        let object = store.put(&bad, b"bad fact").expect("put");
        fs::write(store.path_of("objects", &object), b"tampered").expect("tamper");
        let report = store.rescan();
        assert_eq!(report, RescanReport { sound: 1, quarantined: 1, dangling: 1, collected: 0 });
        assert_eq!(store.keys(), vec![good]);
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (measured 2026-11-06): compilers that open one fresh store
    /// at once all get it. Cargo starts a workspace's units in parallel, and a
    /// directory created with the umask's mode and narrowed afterwards was,
    /// between the two calls, group-readable to a concurrent compiler, which
    /// refused the store as not private and checked every session afresh
    /// (`TRUST_CLEAN_FACT UNAVAILABLE` on two of three `astream` units).
    #[test]
    fn concurrent_opens_of_a_fresh_store_all_succeed() {
        use std::sync::{Arc, Barrier};
        const OPENERS: usize = 16;
        for round in 0..32 {
            let home = scratch(&format!("race-{round}"));
            let barrier = Arc::new(Barrier::new(OPENERS));
            let openers: Vec<_> = (0..OPENERS)
                .map(|_| {
                    let (home, barrier) = (home.clone(), Arc::clone(&barrier));
                    std::thread::spawn(move || {
                        barrier.wait();
                        FactStore::open(&home).map(drop).map_err(|error| error.to_string())
                    })
                })
                .collect();
            let refused: Vec<String> = openers
                .into_iter()
                .filter_map(|opener| opener.join().expect("opener").err())
                .collect();
            assert!(refused.is_empty(), "round {round}: {refused:?}");
            let _ = fs::remove_dir_all(home);
        }
    }

    /// NEGATIVE CONTROL (STORE-1's permission rule): a world-writable
    /// ancestor means no store.
    #[cfg(unix)]
    #[test]
    fn a_writable_ancestor_refuses_the_store() {
        use std::os::unix::fs::PermissionsExt;
        let home = scratch("writable");
        fs::set_permissions(&home, fs::Permissions::from_mode(0o777)).expect("chmod");
        assert!(FactStore::open(&home).is_err());
        fs::set_permissions(&home, fs::Permissions::from_mode(0o700)).expect("chmod");
        assert!(FactStore::open(&home).is_ok());
        let _ = fs::remove_dir_all(home);
    }

    #[cfg(target_os = "macos")]
    fn chmod_acl(path: &Path, entry: Option<&str>) {
        let mut command = std::process::Command::new("/bin/chmod");
        if let Some(entry) = entry {
            command.args(["+a", entry]);
        } else {
            command.arg("-N");
        }
        let output = command.arg(path).output().expect("chmod ACL");
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    }

    /// Extended ACL inheritance is independent of the POSIX mode bits.
    #[cfg(target_os = "macos")]
    #[test]
    fn inherited_acl_grants_refuse_the_store_even_with_private_mode_bits() {
        use std::os::unix::fs::{DirBuilderExt as _, MetadataExt as _};
        let home = scratch("inherited-acl");
        chmod_acl(&home, Some("everyone allow write,append,file_inherit,directory_inherit"));
        let cargo = home.join("cargo");
        fs::DirBuilder::new().mode(0o700).create(&cargo).expect("inheriting directory");
        assert_eq!(fs::metadata(&cargo).unwrap().mode() & 0o077, 0);
        assert!(FactStore::open(&cargo).is_err(), "mode 0700 must not hide an ACL grant");
        chmod_acl(&cargo, None);
        chmod_acl(&home, None);
        assert!(FactStore::open(&cargo).is_ok(), "an ordinary private home still works");
        fs::remove_dir_all(home).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn store_directories_refuse_even_deny_only_acl_entries() {
        let home = scratch("directory-acl");
        let store = FactStore::open(&home).expect("store");
        chmod_acl(store.root(), Some("everyone deny delete"));
        assert!(FactStore::open(&home).is_err(), "the store uses the strict empty-ACL rule");
        chmod_acl(store.root(), None);
        assert!(FactStore::open(&home).is_ok());
        fs::remove_dir_all(home).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_fact_file_acl_is_rejected_on_the_original_open_descriptor() {
        let home = scratch("file-acl");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"acl-key"]);
        let object = store.put(&key, b"fact bytes").expect("put");
        let path = store.path_of("objects", &object);
        chmod_acl(&path, Some("everyone allow write"));
        assert!(read_bounded(&path, MAX_FACT_BYTES).is_err());
        assert!(
            matches!(store.get(&key), StoreRead::Quarantined(_)),
            "content hashing cannot admit a file with an ACL grant"
        );
        fs::remove_dir_all(home).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_read_refuses_a_shard_that_gained_an_acl_after_open() {
        let home = scratch("shard-acl");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"shard-key"]);
        store.put(&key, b"fact bytes").expect("put");
        let shard = store.shard("index", &key);
        chmod_acl(&shard, Some("everyone allow write"));
        assert!(matches!(store.get(&key), StoreRead::Quarantined(_)));
        chmod_acl(&shard, None);
        fs::remove_dir_all(home).unwrap();
    }

    #[test]
    fn the_audit_sample_is_one_in_thirty_two_by_key_prefix() {
        let home = scratch("audit");
        let store = FactStore::open(&home).expect("store");
        let context = FactContext::with_identity(store, CompilerIdentity::for_tests("audit"), 64);
        let sampled = (0u8..=255).filter(|first| context.audits(&[*first; 32])).count();
        assert_eq!(sampled, 8);
        let _ = fs::remove_dir_all(home);
    }

    fn mapped(path: &Path) -> MappedImage {
        use std::os::unix::fs::MetadataExt;
        let metadata = fs::metadata(path).expect("image");
        MappedImage { device: metadata.dev(), inode: metadata.ino() }
    }

    #[test]
    fn the_image_identity_is_memoized_and_stable() {
        let home = scratch("identity");
        let store = FactStore::open(&home).expect("store");
        let image = home.join("image");
        fs::write(&image, b"a checker image").expect("image");
        let of = |commit: &str| {
            CompilerIdentity::of_image(commit, &image, mapped(&image), &store).expect("identity")
        };
        let first = of("commit");
        assert_eq!(first, of("commit"));
        assert!(fs::read_dir(store.root().join("identity")).expect("memo").count() > 0);
        // NEGATIVE CONTROLS: another trustc commit is another identity, and
        // so is an image rewritten in place to the same size (it misses the
        // memo).
        assert_ne!(first.digest(), of("other commit").digest());
        fs::write(&image, b"A checker image").expect("rewrite");
        assert_ne!(first.digest(), of("commit").digest());
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (TG6 review, 2026-11-06): a process whose image was replaced
    /// under its path (a toolchain rebuilt at the same commit unlinks the old
    /// driver and writes a new one under the same name) has no identity. Before,
    /// it hashed the new file and filed the facts its old checker made under
    /// the new image's identity, and memoized its own prelude digest for it, so
    /// every process of the new image imported them unchecked.
    #[test]
    fn an_image_replaced_under_its_path_gives_its_old_runner_no_identity() {
        let home = scratch("replaced");
        let store = FactStore::open(&home).expect("store");
        let image = home.join("image");
        fs::write(&image, b"the old checker").expect("image");
        // Held open, as a mapping holds it, so its inode is not reused.
        let _old = fs::File::open(&image).expect("old image");
        let old = mapped(&image);
        let old_identity =
            CompilerIdentity::of_image("commit", &image, old, &store).expect("identity");
        fs::remove_file(&image).expect("unlink");
        fs::write(&image, b"the new checker").expect("new image");
        assert!(
            CompilerIdentity::of_image("commit", &image, old, &store).is_none(),
            "the old image's runner must not take the new file's identity"
        );
        let new_identity =
            CompilerIdentity::of_image("commit", &image, mapped(&image), &store).expect("new");
        assert_ne!(old_identity.digest(), new_identity.digest());
        let context = FactContext::open_in(&home, 64, "commit", &image, old);
        assert!(context.is_err(), "no context, so no facts, for the old runner");
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (TG6 review, 2026-11-06): a temporary a killed writer left
    /// is removed once stale, by a write into its directory and by a rescan;
    /// a fresh one (a live writer's) is kept. Before, nothing removed them.
    #[test]
    fn a_dead_writers_temporaries_are_reclaimed_and_a_live_ones_are_kept() {
        let home = scratch("partials");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"k"]);
        let object = store.put(&key, b"fact bytes").expect("put");
        let plant = |directory: &Path, name: &str, age: Duration| {
            let path = directory.join(name);
            let file = fs::File::create(&path).expect("temporary");
            let when = std::time::SystemTime::now() - age;
            file.set_modified(when).expect("mtime");
            path
        };
        let hour = Duration::from_secs(60 * 60);
        let objects = store.shard("objects", &object);
        let index = store.shard("index", &key);
        let dead_object = plant(&objects, ".1.0.partial", 2 * hour);
        let dead_index = plant(&index, ".2.0.partial", 2 * hour);
        let dead_quarantine = plant(&store.root().join("quarantine"), ".3.0.partial", 2 * hour);
        let live = plant(&index, ".4.0.partial", Duration::ZERO);
        // The object is stored already, so this writes the index entry only,
        // and sweeps only the index entry's directory.
        store.put(&key, b"fact bytes").expect("put again");
        assert!(!dead_index.exists(), "a write sweeps its directory");
        assert!(dead_object.exists() && dead_quarantine.exists());
        store.rescan();
        assert!(!dead_object.exists() && !dead_quarantine.exists(), "a rescan sweeps the store");
        assert!(live.exists(), "a live writer's temporary is kept");
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (TG6 review, 2026-11-06): a rescan removes an object no
    /// index entry names once it is old, and keeps every object an entry
    /// names and every young one. Before, a fact superseded under its key
    /// stayed forever.
    #[test]
    fn a_rescan_collects_old_objects_no_entry_names() {
        let home = scratch("collect");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"k"]);
        let superseded = store.put(&key, b"the first elaboration").expect("put");
        let current = store.put(&key, b"the second elaboration").expect("put");
        let age = |object: &Digest32| {
            let file = OpenOptions::new()
                .write(true)
                .open(store.path_of("objects", object))
                .expect("object");
            file.set_modified(std::time::SystemTime::now() - 2 * STALE_PARTIAL).expect("mtime");
        };
        assert_eq!(store.rescan().collected, 0, "a young object is kept");
        age(&superseded);
        age(&current);
        let report = store.rescan();
        assert_eq!(report, RescanReport { sound: 2, quarantined: 0, dangling: 0, collected: 1 });
        assert!(!store.path_of("objects", &superseded).exists());
        assert!(matches!(store.get(&key), StoreRead::Present { object, .. } if object == current));
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (TG6 review, 2026-11-06): an object that cannot be read is
    /// moved away with its index entry, so the next put of the same bytes
    /// writes it afresh and the key hits again. Before, only the index entry
    /// was moved and put kept any existing object, so the key missed on every
    /// build forever and the quarantine grew by two files a build.
    #[test]
    fn an_unreadable_object_is_rewritten_by_the_next_put() {
        use std::os::unix::fs::PermissionsExt;
        let home = scratch("unreadable");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"k"]);
        let object = store.put(&key, b"fact bytes").expect("put");
        let path = store.path_of("objects", &object);
        // Readable by others: no longer private, so no longer served.
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).expect("chmod");
        assert!(matches!(store.get(&key), StoreRead::Quarantined(_)));
        store.put(&key, b"fact bytes").expect("put again");
        assert!(matches!(store.get(&key), StoreRead::Present { .. }), "the key hits again");
        // A directory in the object's place: moved away, then rewritten.
        fs::remove_file(&path).expect("remove");
        fs::create_dir(&path).expect("a directory in its place");
        assert!(matches!(store.get(&key), StoreRead::Quarantined(_)));
        store.put(&key, b"fact bytes").expect("put after a directory");
        assert!(matches!(store.get(&key), StoreRead::Present { .. }));
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (TG6 review, 2026-11-06): names that are not a digest in its
    /// own shard are never read, so a rescan leaves them and counts nothing.
    /// Before, a one-byte name made the rescan panic (`&name[..2]`), inside
    /// the compiler.
    #[test]
    fn stray_names_in_the_tables_are_left_alone() {
        let home = scratch("stray");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"k"]);
        store.put(&key, b"fact bytes").expect("put");
        let index = store.shard("index", &key);
        let misplaced = digest_parts(&[b"misplaced"]);
        for name in ["x", "\u{e9}", &format!("#{}#", hex(&key)), &hex(&misplaced)] {
            fs::write(index.join(name), b"stray").expect("stray");
        }
        assert_eq!(
            store.rescan(),
            RescanReport { sound: 1, quarantined: 0, dangling: 0, collected: 0 }
        );
        assert_eq!(store.keys(), vec![key]);
        assert!(index.join("x").exists());
        let _ = fs::remove_dir_all(home);
    }

    /// REGRESSION (TG6 review, 2026-11-06): quarantining an entry that is
    /// already gone (another process moved it) records nothing. Before, every
    /// such call wrote a `.why` for a move that never happened, and a rescan
    /// racing another process's quarantine counted the object as corrupt.
    #[test]
    fn quarantining_what_is_gone_records_nothing() {
        let home = scratch("gone");
        let store = FactStore::open(&home).expect("store");
        let key = digest_parts(&[b"absent"]);
        assert!(!store.quarantine_index(&key, "nothing to move"));
        assert!(!store.quarantine_object(&key, "nothing to move"));
        let quarantine = fs::read_dir(store.root().join("quarantine")).expect("quarantine");
        assert_eq!(quarantine.count(), 0);
        let _ = fs::remove_dir_all(home);
    }

    /// A symlink on the way to the store that resolves nowhere refuses the
    /// store and creates nothing through it, and one that resolves is followed
    /// once: the root is canonical. This pins the behavior. It does not
    /// reproduce the race the TG6 review found (a symlink made to resolve
    /// between the old ancestor check and `create_dir_all`), which the old
    /// code also refused when run single-threaded.
    #[test]
    fn a_dangling_symlink_on_the_way_refuses_the_store() {
        let home = scratch("dangling");
        let elsewhere = home.join("elsewhere");
        let cargo_home = home.join("cargo");
        std::os::unix::fs::symlink(&elsewhere, &cargo_home).expect("symlink");
        assert!(FactStore::open(&cargo_home).is_err());
        assert!(!elsewhere.exists(), "nothing is created through a dangling symlink");
        // A symlink that resolves is followed once: the store's root is the
        // canonical path, with no symlink in it.
        fs::create_dir(&elsewhere).expect("target");
        let store = FactStore::open(&cargo_home).expect("store");
        assert_eq!(store.root(), store.root().canonicalize().expect("canonical"));
        assert!(store.root().starts_with(elsewhere.canonicalize().expect("canonical")));
        let _ = fs::remove_dir_all(home);
    }
}
