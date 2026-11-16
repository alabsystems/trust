//! Trust: `-Ztrust-carried-times` (EW-9).
//!
//! Bootstrap may seed a fresh tree's build directory by cloning another tree's
//! green build ("the donor"). A cloned unit must then be fresh exactly when it
//! would be in the donor rebuilt in place from this tree's files. Bootstrap
//! runs Targo by its `cargo` name, whose fingerprints decide that by
//! modification times: an input is changed when its time is later than the
//! unit's own record (`rerun-if-changed` paths are always compared so). A
//! content fingerprint (`targo` by its own name, or `-Zchecksum-freshness`)
//! reads no time for its inputs and is unaffected. A fresh checkout's files
//! are all newer than the donor's outputs, so bootstrap compares each input of
//! a cloned unit with the donor's file and, where the two hold the same bytes
//! and the donor's is older, records the donor's time here instead of setting
//! it on this tree's file. Moving a file's time back would make every other
//! time-based cache that reads it (another target directory, an editor's
//! index) take an older content for current; the table is read only by the
//! Targo invocations bootstrap gives it, for the target directories it cloned.
//!
//! An entry names a file by device and inode and holds the size, modification
//! time and status-change time the file had when it was compared. It applies
//! only while all of those are unchanged: any write, rename over, `touch` or
//! `chmod` changes the status-change time, which no program can set, and the
//! file's own (later) time is used from then on. A table can therefore only
//! make a file read as older while its bytes are those the seed compared.
//!
//! Format (bootstrap writes it, `src/bootstrap/src/utils/trust_stage1_seed.rs`):
//! the line [`MAGIC`], then one line per entry of nine decimal integers
//! separated by single spaces: `dev ino size mtime_sec mtime_nsec ctime_sec
//! ctime_nsec carried_sec carried_nsec`. Anything else is an error: the table
//! is refused whole, never read in part.

use std::fs::Metadata;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};
use filetime::FileTime;

use crate::CargoResult;
use crate::util::data_structures::HashMap;

/// The first line of a table.
pub const MAGIC: &str = "trust-carried-times/v1";

/// What a table knows about one file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Entry {
    size: u64,
    mtime: (i64, i64),
    ctime: (i64, i64),
    carried: (i64, u32),
}

/// The carried times in effect for this invocation.
#[derive(Debug, PartialEq, Eq)]
pub struct CarriedTimes {
    path: PathBuf,
    entries: HashMap<(u64, u64), Entry>,
}

impl CarriedTimes {
    /// Reads the table at `path`.
    pub fn load(path: &Path) -> CargoResult<CarriedTimes> {
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("-Ztrust-carried-times: cannot read {}", path.display()))?;
        CarriedTimes::parse(path, &text)
    }

    /// Parses a table; `path` only names it in errors.
    pub fn parse(path: &Path, text: &str) -> CargoResult<CarriedTimes> {
        let mut lines = text.lines();
        if lines.next() != Some(MAGIC) {
            bail!(
                "-Ztrust-carried-times: {} is not a `{MAGIC}` table",
                path.display()
            );
        }
        let mut entries = HashMap::default();
        for (number, line) in lines.enumerate() {
            let fields: Vec<&str> = line.split(' ').collect();
            let numbers: Option<Vec<i128>> = (fields.len() == 9)
                .then(|| fields.iter().map(|field| decimal(field)).collect())
                .flatten();
            let entry = numbers.and_then(|n| {
                Some((
                    (u64::try_from(n[0]).ok()?, u64::try_from(n[1]).ok()?),
                    Entry {
                        size: u64::try_from(n[2]).ok()?,
                        mtime: (i64::try_from(n[3]).ok()?, nanos(n[4])?.into()),
                        ctime: (i64::try_from(n[5]).ok()?, nanos(n[6])?.into()),
                        carried: (i64::try_from(n[7]).ok()?, nanos(n[8])?),
                    },
                ))
            });
            let Some((key, entry)) = entry else {
                bail!(
                    "-Ztrust-carried-times: {} line {} is malformed: `{line}`",
                    path.display(),
                    number + 2
                );
            };
            if entries.insert(key, entry).is_some() {
                bail!(
                    "-Ztrust-carried-times: {} names device {} inode {} twice",
                    path.display(),
                    key.0,
                    key.1
                );
            }
        }
        Ok(CarriedTimes {
            path: path.to_owned(),
            entries,
        })
    }

    /// The modification time to compare for a file whose metadata is `meta`:
    /// the carried time while the file is exactly as it was compared, and its
    /// own time otherwise.
    pub fn mtime(&self, meta: &Metadata) -> FileTime {
        let own = FileTime::from_last_modification_time(meta);
        match self.entry(meta) {
            Some(entry) => FileTime::from_unix_time(entry.carried.0, entry.carried.1),
            None => own,
        }
    }

    #[cfg(unix)]
    fn entry(&self, meta: &Metadata) -> Option<&Entry> {
        use std::os::unix::fs::MetadataExt;
        let entry = self.entries.get(&(meta.dev(), meta.ino()))?;
        (entry.size == meta.len()
            && entry.mtime == (meta.mtime(), meta.mtime_nsec())
            && entry.ctime == (meta.ctime(), meta.ctime_nsec()))
            .then_some(entry)
    }

    #[cfg(not(unix))]
    fn entry(&self, _meta: &Metadata) -> Option<&Entry> {
        None
    }
}

/// A decimal integer as bootstrap writes one: an optional `-`, then digits,
/// with no leading zero.
fn decimal(field: &str) -> Option<i128> {
    let digits = field.strip_prefix('-').unwrap_or(field);
    let canonical = !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && (digits == "0" || !digits.starts_with('0'))
        && !(field.starts_with('-') && digits == "0");
    canonical.then(|| field.parse().ok()).flatten()
}

fn nanos(value: i128) -> Option<u32> {
    u32::try_from(value).ok().filter(|n| *n < 1_000_000_000)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(lines: &[&str]) -> CargoResult<CarriedTimes> {
        let mut text = format!("{MAGIC}\n");
        for line in lines {
            text.push_str(line);
            text.push('\n');
        }
        CarriedTimes::parse(Path::new("t"), &text)
    }

    #[test]
    fn a_table_is_read_whole_or_refused() {
        assert_eq!(table(&[]).unwrap().entries.len(), 0);
        let t = table(&["1 2 3 4 5 -6 7 8 9"]).unwrap();
        assert_eq!(
            t.entries[&(1, 2)],
            Entry {
                size: 3,
                mtime: (4, 5),
                ctime: (-6, 7),
                carried: (8, 9)
            }
        );
        for bad in [
            "1 2 3 4 5 6 7 8",
            "1 2 3 4 5 6 7 8 9 10",
            "1 2 3 4 5 6 7 8 1000000000",
            "1  2 3 4 5 6 7 8 9",
            "1 2 3 4 5 6 7 8 09",
            "1 2 3 4 5 6 7 8 -0",
            "-1 2 3 4 5 6 7 8 9",
            "1 2 3 4 5 6 7 8 +9",
            "1 2 3 4 5 6 7 8 9 ",
        ] {
            assert!(table(&[bad]).is_err(), "{bad}");
        }
        assert!(table(&["1 2 3 4 5 6 7 8 9", "1 2 0 0 0 0 0 0 0"]).is_err());
        assert!(CarriedTimes::parse(Path::new("t"), "trust-carried-times/v2\n").is_err());
        assert!(CarriedTimes::parse(Path::new("t"), "").is_err());
    }

    #[cfg(unix)]
    #[test]
    fn a_carried_time_holds_only_while_the_file_is_as_compared() {
        use std::os::unix::fs::MetadataExt;
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("input.rs");
        std::fs::write(&file, "fn main() {}").unwrap();
        let entry_for = |meta: &Metadata| {
            format!(
                "{} {} {} {} {} {} {} 1000 5",
                meta.dev(),
                meta.ino(),
                meta.len(),
                meta.mtime(),
                meta.mtime_nsec(),
                meta.ctime(),
                meta.ctime_nsec()
            )
        };
        let meta = std::fs::metadata(&file).unwrap();
        let t = table(&[&entry_for(&meta)]).unwrap();
        assert_eq!(t.mtime(&meta), FileTime::from_unix_time(1000, 5));
        let tree = dir.path();
        assert_eq!(
            cargo_util::paths::mtime_recursive_by(&file, |m| t.mtime(m)).unwrap(),
            FileTime::from_unix_time(1000, 5)
        );
        // The directory has no entry: it keeps its own time.
        assert_eq!(
            cargo_util::paths::mtime_recursive_by(tree, |m| t.mtime(m)).unwrap(),
            FileTime::from_last_modification_time(&std::fs::metadata(tree).unwrap())
                .max(FileTime::from_unix_time(1000, 5))
        );

        // Any change to the file ends the entry: here only its time is set back
        // to what it was, which moves its status-change time.
        let before = FileTime::from_last_modification_time(&meta);
        std::thread::sleep(std::time::Duration::from_millis(20));
        filetime::set_file_mtime(&file, before).unwrap();
        let touched = std::fs::metadata(&file).unwrap();
        assert_eq!(FileTime::from_last_modification_time(&touched), before);
        assert_eq!(
            t.mtime(&touched),
            before,
            "a touched file reads its own time"
        );
    }
}
