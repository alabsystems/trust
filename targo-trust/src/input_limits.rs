// Bounded readers for untrusted JSON and proof-report inputs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs::File;
use std::io::{self, BufRead, Read};
use std::path::Path;

/// One Cargo JSON envelope may contain a hex-encoded proof payload. Keep the
/// raw-line ceiling above the schema's largest useful native payload while
/// still preventing `BufRead::lines`/Serde from allocating without a bound.
pub(crate) const MAX_CARGO_JSON_LINE_BYTES: usize = 128 * 1024 * 1024;

/// Direct compiler stderr uses the same transport envelope and therefore the
/// same per-line ceiling.
pub(crate) const MAX_COMPILER_STDERR_LINE_BYTES: usize = MAX_CARGO_JSON_LINE_BYTES;

/// Bound retained authenticated transport across one Cargo invocation. This
/// is deliberately larger than the per-line ceiling but finite, preventing a
/// stream of individually valid messages from exhausting memory.
pub(crate) const MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES: usize = 512 * 1024 * 1024;

/// Saved proof reports are user-controlled inputs to diff/query/self-improve.
pub(crate) const MAX_SAVED_PROOF_REPORT_BYTES: usize = 128 * 1024 * 1024;

/// Release transcript reports contain summaries and digests, not proof blobs.
pub(crate) const MAX_RELEASE_TRANSCRIPT_REPORT_BYTES: usize = 64 * 1024 * 1024;

/// Human-authored release/configuration metadata must stay small enough to
/// inspect and parse deterministically. Large proof artifacts use the
/// purpose-specific limits above instead.
pub(crate) const MAX_RELEASE_METADATA_BYTES: usize = 4 * 1024 * 1024;

/// Executables and selected binary images are proof inputs. They may be much
/// larger than metadata, but reading an attacker-controlled multi-gigabyte
/// sparse file into memory must fail before allocation.
pub(crate) const MAX_BINARY_ARTIFACT_BYTES: usize = 512 * 1024 * 1024;

/// An external checked-certificate checker is an untrusted subprocess. A
/// production run must never inherit the proof driver's lifetime merely
/// because the checker stops making progress.
pub(crate) const EXTERNAL_CHECKER_TIMEOUT_MS: u64 = 5 * 60 * 1000;

/// Read one UTF-8 line without ever allocating past `max_bytes` of raw input.
/// The trailing newline and an optional preceding carriage return are removed.
pub(crate) fn read_bounded_utf8_line<R: BufRead>(
    reader: &mut R,
    max_bytes: usize,
) -> io::Result<Option<String>> {
    let mut bytes = Vec::new();
    loop {
        let available = reader.fill_buf()?;
        if available.is_empty() {
            if bytes.is_empty() {
                return Ok(None);
            }
            break;
        }

        let newline = available.iter().position(|byte| *byte == b'\n');
        let take = newline.unwrap_or(available.len());
        if bytes.len().saturating_add(take) > max_bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("input line exceeds the {max_bytes}-byte safety limit"),
            ));
        }
        bytes.extend_from_slice(&available[..take]);
        reader.consume(take + usize::from(newline.is_some()));
        if newline.is_some() {
            break;
        }
    }

    if bytes.last() == Some(&b'\r') {
        bytes.pop();
    }
    String::from_utf8(bytes).map(Some).map_err(|error| {
        io::Error::new(io::ErrorKind::InvalidData, format!("input line is not UTF-8: {error}"))
    })
}

/// Read a regular file with both pre-read and streaming size checks. The
/// streaming check closes the growth race after metadata is inspected.
pub(crate) fn read_bounded_file(path: &Path, max_bytes: usize) -> io::Result<Vec<u8>> {
    let path_metadata = std::fs::symlink_metadata(path)?;
    if path_metadata.file_type().is_symlink() || !path_metadata.file_type().is_file() {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "input is not a regular file"));
    }
    if path_metadata.len() > max_bytes as u64 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("input exceeds the {max_bytes}-byte safety limit"),
        ));
    }

    let mut file = File::open(path)?;
    let opened_metadata = file.metadata()?;
    if !opened_metadata.file_type().is_file()
        || !same_file_snapshot(&path_metadata, &opened_metadata)
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "input changed while it was opened",
        ));
    }

    let initial_capacity = usize::try_from(path_metadata.len()).unwrap_or(max_bytes).min(max_bytes);
    let mut bytes = Vec::with_capacity(initial_capacity);
    (&mut file).take(max_bytes as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > max_bytes {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("input grew beyond the {max_bytes}-byte safety limit while reading"),
        ));
    }
    if bytes.len() as u64 != path_metadata.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "input size changed while it was read",
        ));
    }
    let handle_metadata = file.metadata()?;
    let after_metadata = std::fs::symlink_metadata(path)?;
    if after_metadata.file_type().is_symlink()
        || !after_metadata.file_type().is_file()
        || !same_file_snapshot(&path_metadata, &handle_metadata)
        || !same_file_snapshot(&path_metadata, &after_metadata)
    {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "input changed while it was read"));
    }
    Ok(bytes)
}

pub(crate) fn read_bounded_utf8_file(path: &Path, max_bytes: usize) -> io::Result<String> {
    let bytes = read_bounded_file(path, max_bytes)?;
    String::from_utf8(bytes).map_err(|error| {
        io::Error::new(io::ErrorKind::InvalidData, format!("input is not UTF-8: {error}"))
    })
}

/// Read a bounded UTF-8 stream whose filesystem metadata cannot describe its
/// eventual contents (for example, a fixed procfs pseudo-file with `st_size ==
/// 0`). Callers remain responsible for selecting and opening the trusted
/// stream path; this helper guarantees allocation and UTF-8 bounds.
#[cfg(any(test, not(target_os = "macos")))]
pub(crate) fn read_bounded_utf8_stream<R: Read>(reader: R, max_bytes: usize) -> io::Result<String> {
    let mut bytes = Vec::new();
    reader.take(max_bytes as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > max_bytes {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("input stream exceeds the {max_bytes}-byte safety limit"),
        ));
    }
    String::from_utf8(bytes).map_err(|error| {
        io::Error::new(io::ErrorKind::InvalidData, format!("input stream is not UTF-8: {error}"))
    })
}

#[cfg(unix)]
fn same_file_snapshot(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt as _;

    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.len() == right.len()
        && left.mode() == right.mode()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
fn same_file_snapshot(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    left.is_file()
        && right.is_file()
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;

    #[test]
    fn bounded_line_rejects_escaped_json_before_deserialization() {
        // A short decoded JSON string can have a much larger escaped wire form.
        // The limit applies to raw bytes, before Serde can allocate its String.
        let input = format!("\"{}\"\n", "\\u0061".repeat(16));
        let error = read_bounded_utf8_line(&mut Cursor::new(input), 32)
            .expect_err("escaped wire input must be capped before JSON parsing");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("32-byte safety limit"));
    }

    #[test]
    fn bounded_line_accepts_exact_limit_and_strips_crlf() {
        let mut input = Cursor::new(b"1234\r\nnext\n".as_slice());
        assert_eq!(
            read_bounded_utf8_line(&mut input, 5).expect("bounded line"),
            Some("1234".to_string())
        );
        assert_eq!(
            read_bounded_utf8_line(&mut input, 4).expect("second line"),
            Some("next".to_string())
        );
    }

    #[test]
    fn bounded_utf8_stream_rejects_oversize_and_invalid_utf8() {
        let oversize = read_bounded_utf8_stream(Cursor::new(b"12345"), 4)
            .expect_err("oversized pseudo-file stream must fail closed");
        assert_eq!(oversize.kind(), io::ErrorKind::InvalidData);
        assert!(oversize.to_string().contains("4-byte safety limit"));

        let invalid = read_bounded_utf8_stream(Cursor::new([0xff]), 4)
            .expect_err("non-UTF-8 pseudo-file stream must fail closed");
        assert_eq!(invalid.kind(), io::ErrorKind::InvalidData);
    }

    #[cfg(unix)]
    #[test]
    fn bounded_file_rejects_a_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("bounded file fixture");
        let target = root.path().join("target.json");
        let linked = root.path().join("linked.json");
        std::fs::write(&target, b"{}\n").expect("write target");
        symlink(&target, &linked).expect("create input symlink");

        let error = read_bounded_file(&linked, 32).expect_err("symlink input must fail closed");
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    }
}
