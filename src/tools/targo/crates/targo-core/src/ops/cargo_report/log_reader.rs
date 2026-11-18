//! Trust: bounded, identity-checked build-analysis log transport shared by reports.
//! Framing completeness and each report's semantic completeness are separate.

use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::{BufRead, BufReader, Read as _};
use std::path::Path;

use anyhow::{Context as _, bail};
use serde::Deserialize;
use serde::de::{MapAccess, SeqAccess, Visitor};
use serde_json::Value;

use crate::CargoResult;
use crate::compiler::fingerprint::{DepInfoUnavailable, DirtyReason, FsStatus, StaleItem};
use crate::util::file_identity::{
    metadata_is_plain_file, opened_file_identity, paths_refer_to_same_file,
};
use crate::util::log_message::LogMessage;

const MAX_LOG_BYTES: u64 = 256 * 1024 * 1024;
pub(super) const MAX_LINE_BYTES: u64 = 256 * 1024;
const MAX_RECORDS: usize = 1_000_000;
pub(super) const MAX_UNITS: usize = 65_536;

pub(super) fn read_checked<T>(
    path: &Path,
    analyze: impl FnOnce(BufReader<&std::fs::File>) -> CargoResult<T>,
) -> CargoResult<T> {
    let before = fs::symlink_metadata(path)?;
    if !metadata_is_plain_file(&before) || before.len() > MAX_LOG_BYTES {
        bail!("build-analysis log is not a bounded plain file");
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let file = options.open(path)?;
    let identity = opened_file_identity(&file)?;
    let opened = file.metadata()?;
    if !same_log(&before, &opened) {
        bail!("build-analysis log changed before reading");
    }
    let report = analyze(BufReader::new(&file))?;
    if !same_log(&opened, &file.metadata()?)
        || !same_log(&opened, &fs::symlink_metadata(path)?)
        || identity != opened_file_identity(&options.open(path)?)?
    {
        bail!("build-analysis log changed during reading");
    }
    Ok(report)
}

fn same_log(before: &fs::Metadata, after: &fs::Metadata) -> bool {
    if !metadata_is_plain_file(after)
        || before.len() != after.len()
        || !matches!((before.modified(), after.modified()), (Ok(a), Ok(b)) if a == b)
    {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.ctime() == after.ctime()
            && before.ctime_nsec() == after.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        before.permissions().readonly() == after.permissions().readonly()
    }
}

pub(super) fn require_workspace(recorded: Option<&Path>, requested: &Path) -> CargoResult<()> {
    let recorded = recorded.context("build-analysis session has no original workspace root")?;
    if !recorded.is_absolute() || !requested.is_absolute() {
        bail!("build-analysis workspace roots must be absolute");
    }
    // Canonicalization follows directory aliases on every platform; the held
    // opened identities decide equality rather than either lexical spelling.
    let recorded =
        fs::canonicalize(recorded).context("cannot resolve recorded build-analysis workspace")?;
    let requested =
        fs::canonicalize(requested).context("cannot resolve requested build-analysis workspace")?;
    if !fs::metadata(&recorded)?.is_dir()
        || !fs::metadata(&requested)?.is_dir()
        || !paths_refer_to_same_file(&recorded, &requested)?
    {
        bail!("build-analysis session belongs to a different workspace");
    }
    Ok(())
}

pub(super) fn read_records(
    reader: impl BufRead,
    run: &str,
    mut visit: impl FnMut(LogMessage) -> CargoResult<()>,
) -> CargoResult<()> {
    for message in records(reader, run) {
        visit(message?)?;
    }
    Ok(())
}

// Trust: stream checked records into fallible consumers without collecting a
// second log or skipping a damaged frame. Completeness requires full iteration;
// EOF and the first error fuse the stream. Existing callback readers share it.
pub(super) fn records(
    mut reader: impl BufRead,
    run: &str,
) -> impl Iterator<Item = CargoResult<LogMessage>> {
    let run = run.to_owned();
    let mut records = 0usize;
    let mut bytes = 0u64;
    let mut finished = false;
    std::iter::from_fn(move || {
        if finished {
            return None;
        }
        let next: CargoResult<Option<LogMessage>> = (|| {
            let mut line = Vec::new();
            let read = reader
                .by_ref()
                .take(MAX_LINE_BYTES + 1)
                .read_until(b'\n', &mut line)?;
            if read == 0 {
                if records == 0 {
                    bail!("empty build-analysis log");
                }
                return Ok(None);
            }
            bytes = bytes
                .checked_add(read as u64)
                .context("log byte count overflow")?;
            if bytes > MAX_LOG_BYTES || read as u64 > MAX_LINE_BYTES || line.last() != Some(&b'\n')
            {
                bail!("build-analysis log exceeds bounds or has a truncated frame");
            }
            if records >= MAX_RECORDS {
                bail!("log record limit exceeded");
            }
            let mut value = decode_unique_json(&line)?;
            let object = value
                .as_object_mut()
                .context("log record must be an object")?;
            let observed_run = object.remove("run_id").context("log record lacks run_id")?;
            if observed_run.as_str() != Some(run.as_str()) {
                bail!("build-analysis record belongs to another run");
            }
            let timestamp = object
                .remove("timestamp")
                .context("log record lacks timestamp")?;
            timestamp
                .as_str()
                .context("invalid log timestamp")?
                .parse::<jiff::Timestamp>()?;
            check_fields(object)?;
            let message = LogMessage::deserialize(&value)?;
            if let LogMessage::UnitFingerprint {
                cause: Some(cause), ..
            } = &message
            {
                check_cause_fields(value.get("cause").unwrap(), cause)?;
            }
            Ok(Some(message))
        })();
        match next {
            Ok(Some(message)) => {
                records += 1;
                Some(Ok(message))
            }
            Ok(None) => {
                finished = true;
                None
            }
            Err(error) => {
                finished = true;
                Some(Err(error))
            }
        }
    })
}

// Trust: reject unknown envelope fields instead of silently discarding evidence.
fn check_fields(object: &serde_json::Map<String, Value>) -> CargoResult<()> {
    let reason = object
        .get("reason")
        .and_then(Value::as_str)
        .context("log record lacks reason")?;
    let fields: &[&str] = match reason {
        "execution-enabled" => &["reason", "version"],
        "compiler-observations-enabled" => &["reason", "version", "rusage_requested"],
        "shared-dependency-policy" => &["reason", "version", "enabled", "members", "keyed"],
        "shared-dependency-decision" => &["reason", "index", "decision"],
        "test-action-registered" => &["reason", "index", "harness", "prerequisites"],
        "unit-scheduled" => &["reason", "index", "elapsed", "fresh"],
        "unit-outcome" => &["reason", "index", "elapsed", "outcome"],
        "execution-graph-finished" => &[
            "reason",
            "elapsed",
            "outcome",
            "scheduled",
            "completed",
            "not_executed",
        ],
        "input-work-enabled" => &["reason", "version"],
        "input-work-started" => &["reason", "capture", "index", "phase"],
        "input-work-finished" => &["reason", "capture", "index", "phase", "outcome", "work"],
        "input-work-closed" => &["reason", "version", "started", "finished"],
        "input-work-finalized" => &["reason", "captures"],
        "build-started" => &[
            "reason",
            "command",
            "cwd",
            "host",
            "jobs",
            "num_cpus",
            "profile",
            "rustc_version",
            "rustc_version_verbose",
            "target_dir",
            "workspace_root",
        ],
        "resolution-started"
        | "resolution-finished"
        | "unit-graph-started"
        | "unit-graph-finished" => &["reason", "elapsed"],
        "unit-registered" => &[
            "reason",
            "package_id",
            "target",
            "mode",
            "platform",
            "index",
            "features",
            "requested",
            "dependencies",
        ],
        "unit-started" => &["reason", "index", "elapsed"],
        "unit-finished" | "unit-rmeta-finished" => &["reason", "index", "elapsed", "unblocked"],
        "unit-section-started" | "unit-section-finished" => {
            &["reason", "index", "elapsed", "section"]
        }
        "unit-peak-memory" => &["reason", "index", "bytes"],
        "unit-cpu-times" => &["reason", "index", "user_ns", "system_ns"],
        "unit-fingerprint" => &["reason", "index", "status", "cause", "recheck"],
        _ => bail!("unknown build-analysis event schema"),
    };
    if object.keys().any(|key| !fields.contains(&key.as_str())) {
        bail!("unknown log event field");
    }
    if let Some(work) = object.get("work") {
        let work = work.as_object().context("capture work must be an object")?;
        let fields = [
            "entries",
            "input_bytes",
            "bytes_hashed",
            "metadata_reads",
            "resolution_steps",
            "link_reads",
            "observations",
            "revalidations",
        ];
        if work.len() != fields.len() || work.keys().any(|key| !fields.contains(&key.as_str())) {
            bail!("invalid capture work fields");
        }
    }
    if let Some(target) = object.get("target") {
        let target = target
            .as_object()
            .context("unit target must be an object")?;
        if target.len() != 2 || !target.contains_key("name") || !target.contains_key("kind") {
            bail!("invalid unit target fields");
        }
    }
    Ok(())
}

// Trust: internally tagged newtype variants flatten the filesystem/stale-item
// tags into the same cause object. Serde validates required fields and values;
// this exhaustive typed match rejects fields that its enum buffering ignores.
// Adding a producer variant therefore requires updating its report schema here.
fn check_cause_fields(value: &Value, cause: &DirtyReason) -> CargoResult<()> {
    let mut fields = vec!["dirty_reason"];
    let extra: &[&str] = match cause {
        DirtyReason::RustcChanged
        | DirtyReason::TargetConfigurationChanged
        | DirtyReason::PathToSourceChanged
        | DirtyReason::ProfileConfigurationChanged
        | DirtyReason::ConfigSettingsChanged
        | DirtyReason::CompileKindChanged
        | DirtyReason::LocalLengthsChanged
        | DirtyReason::ContentFingerprintChanged
        | DirtyReason::ContentFingerprintUnavailable
        | DirtyReason::FingerprintRecordMismatch
        | DirtyReason::NothingObvious
        | DirtyReason::Forced
        | DirtyReason::FreshBuild => &[][..],
        DirtyReason::FeaturesChanged { .. }
        | DirtyReason::DeclaredFeaturesChanged { .. }
        | DirtyReason::RustflagsChanged { .. }
        | DirtyReason::PrecalculatedComponentsChanged { .. }
        | DirtyReason::FingerprintMethodChanged { .. }
        | DirtyReason::DepInfoOutputChanged { .. }
        | DirtyReason::RerunIfChangedOutputFileChanged { .. }
        | DirtyReason::RerunIfChangedOutputPathsChanged { .. }
        | DirtyReason::EnvVarsChanged { .. }
        | DirtyReason::LocalFingerprintTypeChanged { .. }
        | DirtyReason::NumberOfDependenciesChanged { .. }
        | DirtyReason::UnitDependencyNameChanged { .. } => &["old", "new"],
        DirtyReason::EnvVarChanged { .. } => &["name", "old_value", "new_value"],
        DirtyReason::UnitDependencyInfoChanged { .. } => &["unit"],
        DirtyReason::FsStatusOutdated(status) => {
            fields.push("fs_status");
            match status {
                FsStatus::Stale => &[],
                FsStatus::UpToDate { .. } => {
                    bail!("up-to-date filesystem state is not a logged cause")
                }
                FsStatus::StaleDependency { .. } => &["unit", "dep_mtime", "max_mtime"],
                FsStatus::StaleDepFingerprint { .. } => &["unit"],
                FsStatus::StaleItem(item) => {
                    fields.push("stale_item");
                    match item {
                        StaleItem::DepInfoUnavailable { reason, .. } => {
                            let fields: &[&str] = match reason {
                                DepInfoUnavailable::FormatMismatch { .. } => {
                                    &["kind", "recorded", "current"]
                                }
                                DepInfoUnavailable::Missing
                                | DepInfoUnavailable::Unreadable
                                | DepInfoUnavailable::Malformed
                                | DepInfoUnavailable::RelocationRootUnavailable
                                | DepInfoUnavailable::FilenameInventoryIncomplete => &["kind"],
                            };
                            only_cause_fields(&value["reason"], fields)?;
                            &["path", "reason"]
                        }
                        StaleItem::OutputIntegrity { .. } => &["path", "reason"],
                        // Trust: an output anchor is not an unavailable input path.
                        StaleItem::BuildScriptInputsUnavailable { .. } => &["output_anchor"],
                        StaleItem::MissingFile { .. }
                        | StaleItem::UnableToReadFile { .. }
                        | StaleItem::FailedToReadMetadata { .. }
                        | StaleItem::MissingChecksum { .. } => &["path"],
                        StaleItem::FileSizeChanged { .. } => &["path", "old_size", "new_size"],
                        StaleItem::ChangedFile { .. } => {
                            &["reference", "reference_mtime", "stale", "stale_mtime"]
                        }
                        StaleItem::ChangedChecksum { .. } => {
                            &["source", "stored_checksum", "new_checksum"]
                        }
                        StaleItem::ChangedEnv { .. } => &["var", "previous", "current"],
                        StaleItem::ModuleCandidateChanged { .. } => {
                            &["path", "previous", "current"]
                        }
                    }
                }
            }
        }
    };
    fields.extend(extra);
    only_cause_fields(value, &fields)
}

fn only_cause_fields(value: &Value, fields: &[&str]) -> CargoResult<()> {
    let object = value
        .as_object()
        .context("fingerprint cause must be an object")?;
    if object.keys().any(|key| !fields.contains(&key.as_str())) {
        bail!("unknown fingerprint cause field");
    }
    Ok(())
}

#[cfg(test)]
mod record_stream_tests {
    use super::*;
    use std::io::Cursor;

    fn frame() -> String {
        format!(
            "{}\n",
            serde_json::json!({
                "run_id":"selected", "timestamp":"2026-11-06T00:00:00Z",
                "reason":"resolution-started", "elapsed":0.0,
            })
        )
    }

    #[test]
    fn owning_cpu_event_requires_exact_fields_and_unsigned_integer_components() {
        let frame = "{\"run_id\":\"selected\",\"timestamp\":\"2026-11-06T00:00:00Z\",\"reason\":\"unit-cpu-times\",\"index\":0,\"user_ns\":1,\"system_ns\":0}\n";
        assert!(
            records(Cursor::new(frame), "selected")
                .collect::<CargoResult<Vec<_>>>()
                .is_ok()
        );
        for invalid in [
            frame.replace("\"system_ns\":0", "\"system_ns\":0,\"capacity\":1"),
            frame.replace("\"user_ns\":1", "\"user_ns\":1,\"user_ns\":1"),
            frame.replace("\"user_ns\":1", "\"user_ns\":-1"),
            frame.replace("\"user_ns\":1", "\"user_ns\":1.0"),
            frame.replace("\"user_ns\":1", "\"user_ns\":true"),
            frame.replace("\"user_ns\":1", "\"user_ns\":18446744073709551616"),
            frame.replace(
                "\"user_ns\":1",
                "\"user_ns\":{\"$serde_json::private::Number\":\"1\"}",
            ),
        ] {
            assert!(
                records(Cursor::new(&invalid), "selected")
                    .collect::<CargoResult<Vec<_>>>()
                    .is_err(),
                "{invalid}"
            );
        }
    }

    /// Every float this logger writes reads back as a number, whether or not
    /// serde_json's `arbitrary_precision` is on in the graph; an object that
    /// spells serde_json's number token, plainly or escaped, stays an object.
    #[test]
    fn written_floats_read_back_and_a_spelled_number_token_stays_refused() {
        for elapsed in [0.0, 1.5, 0.000123, 1e-7, 12345.678901] {
            let frame = format!(
                "{}\n",
                serde_json::json!({
                    "run_id":"selected", "timestamp":"2026-11-06T00:00:00Z",
                    "reason":"resolution-started", "elapsed":elapsed,
                })
            );
            let read = records(Cursor::new(&frame), "selected").collect::<CargoResult<Vec<_>>>();
            assert!(read.is_ok(), "{frame}: {:?}", read.err());
        }
        for spelled in [
            "{\"$serde_json::private::Number\":\"1.5\"}",
            "{\"\\u0024serde_json::private::Number\":\"1.5\"}",
        ] {
            let frame = format!(
                "{{\"run_id\":\"selected\",\"timestamp\":\"2026-11-06T00:00:00Z\",\"reason\":\"resolution-started\",\"elapsed\":{spelled}}}\n"
            );
            assert!(
                records(Cursor::new(&frame), "selected")
                    .collect::<CargoResult<Vec<_>>>()
                    .is_err(),
                "{frame}"
            );
        }
    }

    #[test]
    fn empty_or_bad_first_frame_reports_one_error_then_fuses() {
        for input in [String::new(), "{bad}\n".into(), "{}".into()] {
            let mut stream = records(Cursor::new(input), "selected");
            assert!(stream.next().unwrap().is_err());
            assert!(stream.next().is_none());
            assert!(stream.next().is_none());
        }
    }

    #[test]
    fn a_late_error_is_never_skipped_or_resumed() {
        let input = format!("{}{bad}\n{}", frame(), frame(), bad = "{bad}");
        let mut stream = records(Cursor::new(&input), "selected");
        assert!(stream.next().unwrap().is_ok());
        assert!(stream.next().unwrap().is_err());
        assert!(stream.next().is_none());
        drop(stream);
        let mut seen = 0;
        assert!(
            read_records(Cursor::new(input), "selected", |_| {
                seen += 1;
                Ok(())
            })
            .is_err()
        );
        assert_eq!(seen, 1);
    }

    #[test]
    fn complete_frames_require_newlines_and_line_bounds() {
        let valid = frame();
        let truncated = format!("{}{}", valid, valid.trim_end());
        let mut stream = records(Cursor::new(truncated), "selected");
        assert!(stream.next().unwrap().is_ok());
        let Err(error) = stream.next().unwrap() else {
            panic!("accepted a truncated frame")
        };
        assert!(error.to_string().contains("truncated frame"));
        assert!(stream.next().is_none());
        let mut oversized = records(
            Cursor::new(vec![b' '; MAX_LINE_BYTES as usize + 1]),
            "selected",
        );
        assert!(oversized.next().unwrap().is_err());
        assert!(oversized.next().is_none());
        let mut complete = records(Cursor::new(valid), "selected");
        assert!(complete.next().unwrap().is_ok());
        assert!(complete.next().is_none());
        assert!(complete.next().is_none());
    }
}

// Trust: Value alone would silently replace duplicate JSON object keys. This
// bounded-frame decoder rejects duplicates recursively before typed decoding.
//
// The decoder also keeps numbers numbers when serde_json's `arbitrary_precision`
// is on in this graph (trust-ir's `native-transport-json`, through trust-types).
// There `deserialize_any` hands every number that is not a plain `u64`/`i64`
// (each float this logger writes) to `visit_map` as a one-entry map whose key
// serde_json supplies itself, `NUMBER_TOKEN`; read as an object, every `f64`
// field of a record failed ("invalid type: map, expected f64"). That key never
// comes from the line: a key the line spells is borrowed from `input` or, when
// escaped, decoded into a transient buffer. So only a borrowed key outside the
// line is serde_json's number, and a line that spells the token itself stays an
// object, refused by typed decoding as before.
const NUMBER_TOKEN: &str = "$serde_json::private::Number";

fn decode_unique_json(input: &[u8]) -> serde_json::Result<Value> {
    use serde::de::DeserializeSeed as _;
    let mut deserializer = serde_json::Deserializer::from_slice(input);
    let value = UniqueJson { input }.deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

#[derive(Clone, Copy)]
struct UniqueJson<'i> {
    input: &'i [u8],
}

impl<'de> serde::de::DeserializeSeed<'de> for UniqueJson<'_> {
    type Value = Value;
    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Value, D::Error> {
        deserializer.deserialize_any(self)
    }
}

impl<'de> Visitor<'de> for UniqueJson<'_> {
    type Value = Value;
    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("JSON without duplicate fields")
    }
    fn visit_bool<E: serde::de::Error>(self, value: bool) -> Result<Value, E> {
        Ok(Value::Bool(value))
    }
    fn visit_i64<E: serde::de::Error>(self, value: i64) -> Result<Value, E> {
        Ok(Value::Number(value.into()))
    }
    fn visit_u64<E: serde::de::Error>(self, value: u64) -> Result<Value, E> {
        Ok(Value::Number(value.into()))
    }
    fn visit_f64<E: serde::de::Error>(self, value: f64) -> Result<Value, E> {
        Ok(Value::Number(
            serde_json::Number::from_f64(value).ok_or_else(|| E::custom("nonfinite number"))?,
        ))
    }
    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Value, E> {
        Ok(Value::String(value.into()))
    }
    fn visit_string<E: serde::de::Error>(self, value: String) -> Result<Value, E> {
        Ok(Value::String(value))
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }
    fn visit_none<E: serde::de::Error>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Value, A::Error> {
        let mut values = Vec::new();
        while let Some(value) = seq.next_element_seed(self)? {
            values.push(value);
        }
        Ok(Value::Array(values))
    }
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Value, A::Error> {
        let mut values = serde_json::Map::new();
        while let Some(key) = map.next_key_seed(Key { input: self.input })? {
            if key.number_token && values.is_empty() {
                let Value::String(text) = map.next_value_seed(self)? else {
                    return Err(serde::de::Error::custom("serde_json number is not text"));
                };
                if map.next_key_seed(Key { input: self.input })?.is_some() {
                    return Err(serde::de::Error::custom(
                        "serde_json number has another field",
                    ));
                }
                return text
                    .parse::<serde_json::Number>()
                    .map(Value::Number)
                    .map_err(serde::de::Error::custom);
            }
            if key.number_token {
                return Err(serde::de::Error::custom(
                    "serde_json number inside an object",
                ));
            }
            if values.contains_key(&key.text) {
                return Err(serde::de::Error::custom("duplicate JSON field"));
            }
            let value = map.next_value_seed(self)?;
            values.insert(key.text, value);
        }
        Ok(Value::Object(values))
    }
}

/// An object key, and whether serde_json supplied it as its number token.
struct ObjectKey {
    text: String,
    number_token: bool,
}

#[derive(Clone, Copy)]
struct Key<'i> {
    input: &'i [u8],
}

impl<'de> serde::de::DeserializeSeed<'de> for Key<'_> {
    type Value = ObjectKey;
    fn deserialize<D: serde::Deserializer<'de>>(
        self,
        deserializer: D,
    ) -> Result<ObjectKey, D::Error> {
        deserializer.deserialize_str(self)
    }
}

impl<'de> Visitor<'de> for Key<'_> {
    type Value = ObjectKey;
    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON object key")
    }
    fn visit_borrowed_str<E: serde::de::Error>(self, value: &'de str) -> Result<ObjectKey, E> {
        let start = self.input.as_ptr() as usize;
        let at = value.as_ptr() as usize;
        let in_line = at >= start && at < start + self.input.len();
        Ok(ObjectKey {
            text: value.to_owned(),
            number_token: !in_line && value == NUMBER_TOKEN,
        })
    }
    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<ObjectKey, E> {
        Ok(ObjectKey {
            text: value.to_owned(),
            number_token: false,
        })
    }
}

#[cfg(test)]
mod fingerprint_cause_tests {
    use super::*;
    use crate::compiler::UnitIndex;
    use crate::context::FingerprintMethod;

    fn read_cause(cause: Value) -> CargoResult<()> {
        let frame = serde_json::json!({
            "run_id": "selected-run", "timestamp": "2026-11-06T00:00:00Z",
            "reason": "unit-fingerprint", "index": 0, "status": "dirty", "cause": cause,
        });
        let line = format!("{frame}\n");
        read_records(std::io::Cursor::new(line), "selected-run", |_| Ok(()))
    }

    #[test]
    fn producer_cause_shapes_reject_unknown_fields_without_losing_valid_payloads() {
        let mut causes = vec![
            DirtyReason::RustcChanged,
            DirtyReason::FeaturesChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::DeclaredFeaturesChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::TargetConfigurationChanged,
            DirtyReason::PathToSourceChanged,
            DirtyReason::ProfileConfigurationChanged,
            DirtyReason::RustflagsChanged {
                old: vec!["a".into()],
                new: vec!["b".into()],
            },
            DirtyReason::ConfigSettingsChanged,
            DirtyReason::CompileKindChanged,
            DirtyReason::LocalLengthsChanged,
            DirtyReason::PrecalculatedComponentsChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::FingerprintMethodChanged {
                old: FingerprintMethod::Mtime,
                new: FingerprintMethod::Content,
            },
            DirtyReason::DepInfoOutputChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::RerunIfChangedOutputFileChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::RerunIfChangedOutputPathsChanged {
                old: vec!["a".into()],
                new: vec!["b".into()],
            },
            DirtyReason::EnvVarsChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::EnvVarChanged {
                name: "A".into(),
                old_value: None,
                new_value: Some("b".into()),
            },
            DirtyReason::LocalFingerprintTypeChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::NumberOfDependenciesChanged { old: 1, new: 2 },
            DirtyReason::UnitDependencyNameChanged {
                old: "a".into(),
                new: "b".into(),
            },
            DirtyReason::UnitDependencyInfoChanged { unit: UnitIndex(1) },
            DirtyReason::ContentFingerprintChanged,
            DirtyReason::ContentFingerprintUnavailable,
            DirtyReason::FingerprintRecordMismatch,
            DirtyReason::NothingObvious,
            DirtyReason::Forced,
            DirtyReason::FreshBuild,
        ];
        let stale = [
            serde_json::json!({"stale_item":"missing-file", "path":"a"}),
            serde_json::json!({"stale_item":"unable-to-read-file", "path":"a"}),
            serde_json::json!({"stale_item":"output-integrity", "path":"a", "reason":"failed"}),
            serde_json::json!({"stale_item":"failed-to-read-metadata", "path":"a"}),
            serde_json::json!({"stale_item":"file-size-changed", "path":"a", "old_size":1, "new_size":2}),
            serde_json::json!({"stale_item":"changed-file", "reference":"a", "reference_mtime":1.0, "stale":"b", "stale_mtime":2.0}),
            serde_json::json!({"stale_item":"changed-checksum", "source":"a", "stored_checksum":format!("sha256={}", "aa".repeat(32)), "new_checksum":format!("sha256={}", "bb".repeat(32))}),
            serde_json::json!({"stale_item":"missing-checksum", "path":"a"}),
            serde_json::json!({"stale_item":"changed-env", "var":"A", "previous":null, "current":"b"}),
        ];
        for item in stale {
            causes.push(DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                serde_json::from_value(item).unwrap(),
            )));
        }
        for reason in [
            DepInfoUnavailable::Missing,
            DepInfoUnavailable::Unreadable,
            DepInfoUnavailable::Malformed,
            DepInfoUnavailable::FormatMismatch {
                recorded: 2,
                current: 3,
            },
            DepInfoUnavailable::RelocationRootUnavailable,
            DepInfoUnavailable::FilenameInventoryIncomplete,
        ] {
            causes.push(DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                StaleItem::DepInfoUnavailable {
                    path: "a".into(),
                    reason,
                },
            )));
        }
        causes.extend([
            DirtyReason::FsStatusOutdated(FsStatus::Stale),
            DirtyReason::FsStatusOutdated(FsStatus::StaleDependency {
                unit: UnitIndex(1),
                dep_mtime: filetime::FileTime::from_unix_time(1, 0),
                max_mtime: filetime::FileTime::from_unix_time(2, 0),
            }),
            DirtyReason::FsStatusOutdated(FsStatus::StaleDepFingerprint { unit: UnitIndex(1) }),
        ]);
        for cause in causes {
            let mut value = serde_json::to_value(&cause).unwrap();
            read_cause(value.clone()).unwrap();
            value["extra"] = true.into();
            assert!(
                read_cause(value).is_err(),
                "accepted extra field: {cause:?}"
            );
        }
        // Absent optional fields remain legal; round-trip equality is not the schema.
        read_cause(serde_json::json!({"dirty_reason":"env-var-changed", "name":"A"})).unwrap();
    }

    #[test]
    fn nested_dependency_rejection_fields_are_checked_before_delivery() {
        let original = serde_json::json!({
            "dirty_reason":"fs-status-outdated", "fs_status":"stale-item",
            "stale_item":"dep-info-unavailable", "path":"a",
            "reason":{"kind":"format-mismatch", "recorded":2, "current":3},
        });
        read_cause(original.clone()).unwrap();
        for fault in ["missing", "extra", "unknown-kind", "wrong-type"] {
            let mut cause = original.clone();
            match fault {
                "missing" => {
                    cause["reason"].as_object_mut().unwrap().remove("current");
                }
                "extra" => {
                    cause["reason"]["extra"] = true.into();
                }
                "unknown-kind" => {
                    cause["reason"]["kind"] = "future".into();
                }
                "wrong-type" => {
                    cause["reason"]["current"] = "3".into();
                }
                _ => unreachable!(),
            }
            assert!(read_cause(cause).is_err(), "accepted {fault}");
        }
    }

    #[test]
    fn module_candidate_cause_preserves_presence_and_refuses_unknown_fields_or_wrong_types() {
        for (previous, current) in [
            (Some(false), Some(true)),
            (None, Some(false)),
            (Some(true), None),
        ] {
            let original = serde_json::json!({
                "dirty_reason":"fs-status-outdated", "fs_status":"stale-item",
                "stale_item":"module-candidate-changed", "path":"src/foo/mod.rs",
                "previous":previous, "current":current,
            });
            read_cause(original.clone()).unwrap();
            let mut extra = original.clone();
            extra["extra"] = true.into();
            assert!(read_cause(extra).is_err());
            let mut wrong = original;
            wrong["current"] = "present".into();
            assert!(read_cause(wrong).is_err());
        }
    }

    // Trust: admit exactly the producer's new diagnostic shape, with no aliases.
    #[test]
    fn build_script_inputs_unavailable_cause_preserves_anchor_and_refuses_extra_fields() {
        let original = serde_json::json!({
            "dirty_reason":"fs-status-outdated", "fs_status":"stale-item",
            "stale_item":"build-script-inputs-unavailable",
            "output_anchor":"build/script/run/stdout",
        });
        read_cause(original.clone()).unwrap();
        let mut extra = original.clone();
        extra["path"] = "purported-input".into();
        assert!(read_cause(extra).is_err());
        let mut wrong = original;
        wrong["output_anchor"] = true.into();
        assert!(read_cause(wrong).is_err());
    }
}
