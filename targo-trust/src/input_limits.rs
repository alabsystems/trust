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

/// The FLOOR of the retained authenticated-transport bound across one Cargo
/// invocation — deliberately larger than the per-line ceiling but finite, so
/// a stream of individually valid messages cannot exhaust memory. The bound
/// actually applied is [`max_authenticated_cargo_transport_bytes`].
pub(crate) const MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES: usize = 512 * 1024 * 1024;

/// The retained authenticated-transport bound for THIS machine: one eighth of
/// its effective memory, never below the floor. A flat 512 MiB refused every
/// large workspace — measured 2026-09-08 on ny (`--all-targets --all-features`,
/// 411 units, zero compiler errors, 128 GiB box): "authenticated Cargo Trust
/// transport exceeds the 536870912-byte aggregate safety limit", exit 2, after
/// 47 minutes of honest evidence. Retained rows parse to a few times their
/// text, so one eighth of RAM as text keeps the whole run well under half of
/// it; a machine whose memory cannot be read gets the floor.
pub(crate) fn max_authenticated_cargo_transport_bytes() -> usize {
    scaled_transport_ceiling(trust_router::effective_physical_memory_bytes())
}

/// The pure rule behind [`max_authenticated_cargo_transport_bytes`].
pub(crate) fn scaled_transport_ceiling(effective_memory_bytes: u64) -> usize {
    let floor = MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES as u64;
    usize::try_from((effective_memory_bytes / 8).max(floor)).unwrap_or(usize::MAX)
}

#[cfg(test)]
mod emitted_report_bound_tests {
    use super::{MAX_SAVED_PROOF_REPORT_BYTES, max_emitted_proof_report_bytes};

    /// The emit bound must never drop BELOW the flat read-side value: on a
    /// machine whose memory cannot be read, or a small one, the old behaviour
    /// is what we keep. It must also be a bound this machine can actually
    /// exceed only by running out of memory, not by verifying a large
    /// workspace — ay's 41,354-obligation gate is the case that motivated it.
    #[test]
    fn the_emitted_bound_never_falls_below_the_read_side_floor() {
        assert!(
            max_emitted_proof_report_bytes() >= MAX_SAVED_PROOF_REPORT_BYTES,
            "the emit bound must never be tighter than the flat read-side limit"
        );
    }

    /// The read-side limit is a defence against a hostile file and must stay
    /// flat. If someone scales it, this fails and says why. (The flat value is
    /// the 2026-09-18 512 MiB, not the 128 MiB this test first pinned.)
    #[test]
    fn the_read_side_limit_stays_flat() {
        assert_eq!(
            MAX_SAVED_PROOF_REPORT_BYTES,
            512 * 1024 * 1024,
            "the saved-report READ limit bounds untrusted input and must not track machine memory"
        );
    }
}

#[cfg(test)]
mod transport_ceiling_tests {
    use super::{MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES, scaled_transport_ceiling};

    #[test]
    fn the_ceiling_is_an_eighth_of_memory_and_never_below_the_floor() {
        const GIB: u64 = 1024 * 1024 * 1024;
        assert_eq!(scaled_transport_ceiling(0), MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES);
        assert_eq!(scaled_transport_ceiling(2 * GIB), MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES);
        assert_eq!(scaled_transport_ceiling(16 * GIB), 2 * GIB as usize);
        assert_eq!(scaled_transport_ceiling(128 * GIB), 16 * GIB as usize);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(scaled_transport_ceiling(u64::MAX), (u64::MAX / 8) as usize);
        #[cfg(target_pointer_width = "32")]
        assert_eq!(scaled_transport_ceiling(u64::MAX), usize::MAX);
    }
}

/// Saved proof reports are user-controlled inputs to diff/query/self-improve.
///
/// This bounds what a READER may slurp: every consumer of a saved report
/// (`read_bounded_file` / `read_bounded_utf8_file`, ~20 call sites across
/// diff, query, self-improve, provenance and the binary-evidence loaders)
/// pulls the whole file into memory, so an unbounded file is an unbounded
/// allocation from user-controlled input.
///
/// This is a READ bound and stays flat: it defends against a hostile or corrupt
/// file, where the only safe answer is a fixed ceiling. It is NOT the right
/// bound for a report this tool is EMITTING — see
/// [`max_emitted_proof_report_bytes`] — and using it as both is what made a
/// workspace-scale run refuse itself.
// Decision (2026-09-18): raised 128 MiB -> 512 MiB, matching the store /
// binary-artifact tier of this family. Same precedent as the 2 GiB NDJSON bound
// below: a legitimate strict proof must not be discarded for a reader-memory
// bound it does not conceptually need. The bit-level UNSAT certificate for a
// constant-scaled 64-bit byte assembler (`trust-endian` `u64_be`) is ~56 MiB and
// serializes to ~130 MiB once hex-encoded into the canonical JSON — real proof,
// over the old 128 MiB reader ceiling. The evidence was ALSO shrunk at the source
// (the trust-mc translator now emits native-width comparisons and shifts for
// constant-factor overflow checks), which reseals the smaller composers; this
// lifts the reader ceiling for the largest. 512 MiB is one whole-file allocation
// on a machine this toolchain already builds on.
pub(crate) const MAX_SAVED_PROOF_REPORT_BYTES: usize = 512 * 1024 * 1024;

/// The bound on a proof report THIS run serializes for itself, scaled to the
/// machine, never below the read-side floor.
///
/// Same rule, same reason, as [`max_authenticated_cargo_transport_bytes`]
/// above: a flat ceiling that was ample for one crate refuses an honest
/// workspace after it has already paid for the verification. Measured
/// 2026-09-12 on the sealed toolchain: ay's release gate compiled its whole
/// `--all-targets --all-features` surface with zero errors and 41,354
/// obligations, then died with no `Gate:` banner because the report exceeded
/// the flat 128 MiB then in force; nn did the same; a synthetic single crate
/// crosses it at 940 verified functions while 930 seals. Proof evidence is ~26
/// KiB per
/// obligation before the transport's hex doubling, so the report tracks the
/// size of the run, not of any one input.
///
/// This bounds bytes we produced and immediately re-read, every artifact of
/// which is digest-checked on decode; it is a memory guard, not a trust
/// boundary, so scaling it weakens no check.
pub(crate) fn max_emitted_proof_report_bytes() -> usize {
    // A QUARTER of the transport ceiling, because this bounds the SERIALIZED
    // size while the process holds several copies of the report at once — the
    // DTO, the serialized bytes, and the encoded form — so peak RSS is a
    // multiple of the number bounded here.
    //
    // MEASURED 2026-09-14, nn's gate (73,780 obligations) under seal 22, by a
    // 30-second sampler running across the kill:
    //
    //     05:24:15  free=68.8GB  targo-trust rss= 4.8GB
    //     05:25:45  free=55.5GB              rss=17.6GB
    //     05:26:15  free=37.8GB              rss=34.7GB
    //     05:26:45  free=12.2GB              rss=58.8GB
    //     05:27:15  free= 6.4GB              rss=64.8GB   <- SIGKILL at 05:27:29
    //
    // No compiler was running (trustc=0): that is all report construction, after
    // a gate that had already finished and printed its census. The ceiling then
    // in force was memory/8 = 16 GiB on this 128 GiB machine, and peak RSS
    // reached ~4x it.
    //
    // The flat 128 MiB cap this replaced refused an honest workspace outright,
    // which is why it was scaled. Scaling it without accounting for the copy
    // multiplier traded a clean refusal for a KILL — strictly worse, because a
    // kill destroys the run, the report, and the diagnosis together, and looks
    // from the outside like a compile failure. A refusal at least says what
    // happened. Neither is a good outcome for a workspace this size; the real
    // fix is to stop materializing the whole report in memory (see the
    // content-addressed-store note in the handoff), and this bound is what keeps
    // the failure honest until then.
    //
    // 2026-09-17: that fix landed. The report builder now swaps inlined rows
    // into place instead of copying them back, charges its inline budget against
    // ENCODED size, and hashes the publication state by STREAMING rather than
    // materializing the encoded form — so the copies the /4 accounted for (DTO,
    // serialized, encoded) are down to two. Measured across an 8h ay gate on seal
    // trust-d75f13f9: the builder held 4.7-7.8 GB where the run above reached
    // 64.8 GB. Meanwhile ay's `--all-targets` report is MEASURED at 5041 MiB of
    // row evidence (415,650 rows, 1% inlined) against this 4 GiB ceiling — a run
    // that finishes its 20h gate then dies at the seal. Decision
    // 2026-09-17: keep test targets in the sealed claim and raise the cap. Half
    // the transport ceiling (8 GiB here) clears the measured report with margin
    // and, at two copies, peaks around 10 GB on a 128 GB machine.
    let ceiling = scaled_transport_ceiling(trust_router::effective_physical_memory_bytes()) / 2;
    ceiling.max(MAX_SAVED_PROOF_REPORT_BYTES)
}

/// The NDJSON report is WRITE-ONLY, and is bounded separately for that reason.
///
/// MEASURED 2026-09-10: `targo trust check -p tla-cli` on first-party/ty
/// verified 316 units with 0 errors and emitted 26,951 obligations — and then
/// the whole run's evidence was DISCARDED, because the NDJSON exceeded
/// `MAX_SAVED_PROOF_REPORT_BYTES` and the artifact gate refused to save
/// anything at all. A successful verification producing no report is the worst
/// available outcome: the work is done and the evidence is thrown away.
///
/// The reader bound was the wrong instrument here. Nothing reads `report.ndjson`
/// back — the bounded readers all consume the canonical `report.json`; the
/// NDJSON is written, staged and published as an artifact for external tools.
/// It is also LINE-ORIENTED by construction (one JSON object per obligation),
/// so a future reader must stream it under `MAX_CARGO_JSON_LINE_BYTES` rather
/// than slurp it, and would gain nothing from a whole-file ceiling.
///
/// What remains worth bounding is the disk a runaway could consume, so this is
/// finite rather than absent: 2 GiB is roughly sixteen times the largest report
/// measured and still far below any disk this toolchain builds on. If a reader
/// of the NDJSON is ever added, bound it per LINE — do not lower this to make
/// a slurping reader safe, because that trades evidence for a bound the format
/// does not need.
///
/// This is the FLOOR of the bound, not the bound: see
/// [`max_saved_ndjson_report_bytes`].
pub(crate) const MAX_SAVED_NDJSON_REPORT_BYTES: usize = 2 * 1024 * 1024 * 1024;

/// The bound on the `report.ndjson` a run writes beside the canonical
/// `report.json` it renders: never tighter than that canonical report.
///
/// The NDJSON is a line-per-function rendering of the SAME `report.functions`
/// (`trust_report::write_ndjson`: a header, one `func.clone()` record per
/// function, a footer with the summary), so its size tracks the canonical
/// report's: MEASURED 2026-10-17 on aterm-serde (candidate trust 7f3690ed73,
/// 5,635 obligations) 288,440,921 NDJSON bytes against 287,533,069 canonical
/// bytes, a ratio of 1.003. A flat 2 GiB therefore refused a run whose canonical
/// report had already sealed under [`max_emitted_proof_report_bytes`]: MEASURED
/// on the 2026-10-16 candidate gate, aterm-gui's complete verification (253,066
/// obligations, coverage 33282/33282) ended `REPORT NOT SAVED: NDJSON report
/// exceeds the 2147483648-byte saved-report limit` and published nothing.
///
/// So the bound is the largest of the flat floor, the canonical bound itself,
/// and twice the canonical bytes this run actually serialized — a rendering more
/// than twice the size of what it renders is a renderer defect, and that is the
/// runaway this still bounds. Crossing it does not discard the run either: the
/// artifact writer omits the NDJSON with a note and keeps `report.json`.
pub(crate) fn max_saved_ndjson_report_bytes(canonical_report_bytes: usize) -> usize {
    MAX_SAVED_NDJSON_REPORT_BYTES
        .max(max_emitted_proof_report_bytes())
        .max(canonical_report_bytes.saturating_mul(2))
}

/// The bound on the rendered `report.html`. HTML is a human rendering of the
/// canonical report; past this bound it is SKIPPED with a note and never
/// discards `report.json` or `report.ndjson`.
pub(crate) const MAX_SAVED_HTML_REPORT_BYTES: usize = MAX_SAVED_PROOF_REPORT_BYTES * 4;

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

fn open_input_file(path: &Path) -> io::Result<File> {
    // Trust: a path can change to a FIFO or symlink after the metadata check.
    // Nonblocking/no-follow open keeps that race a refusal, not an input hang.
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW);
    }
    options.open(path)
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

    let mut file = open_input_file(path)?;
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

    #[cfg(unix)]
    #[test]
    fn raced_input_open_never_waits_for_a_fifo_writer_or_follows_a_symlink() {
        use std::os::unix::fs::{FileTypeExt as _, symlink};
        let root = tempfile::tempdir().unwrap();
        let fifo = root.path().join("raced-input");
        let name = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        let (send, receive) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let opened =
                open_input_file(&fifo).map(|file| file.metadata().unwrap().file_type().is_fifo());
            let _ = send.send(opened);
        });
        assert!(
            receive
                .recv_timeout(std::time::Duration::from_secs(2))
                .expect("opening a FIFO substituted after metadata inspection must not block")
                .unwrap()
        );
        let target = root.path().join("regular");
        std::fs::write(&target, b"held bytes").unwrap();
        let alias = root.path().join("alias");
        symlink(target, &alias).unwrap();
        assert!(open_input_file(&alias).is_err());
    }

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
