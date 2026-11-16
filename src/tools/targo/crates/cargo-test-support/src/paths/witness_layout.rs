//! Trust: an explicit upstream layout adapter for WITNESS-STORE-FLAT-1.
//!
//! Validate the additional cache objects before comparing the original,
//! unchanged non-witness snapshot. This checks store framing/integrity, not
//! typeck replay validity or proof authority. No compiler mode is changed.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::Deserialize;
use snapbox::IntoData;
use walkdir::WalkDir;

use crate::compare::{assert_e2e, match_contains};

const LEDGER: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../../../tests/upstream-rust/targo-witness-layout.json"
));

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Policy {
    schema_version: u32,
    id: String,
    owner: String,
    status: String,
    reviewed_on: String,
    expires_on: String,
    store_magic: String,
    stem_hex_digits: usize,
    modules: Vec<String>,
    reason: String,
}

fn date_day(date: &str) -> Result<u64, String> {
    let parts = date.split('-').collect::<Vec<_>>();
    if parts.len() != 3 || parts[0].len() != 4 || parts[1].len() != 2 || parts[2].len() != 2 {
        return Err(format!("invalid adapter date {date:?}"));
    }
    let numbers = parts
        .iter()
        .map(|part| part.parse::<u64>())
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| format!("invalid adapter date {date:?}"))?;
    let (year, month, day) = (numbers[0], numbers[1], numbers[2]);
    let leap = |year| year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    if !(1970..=9999).contains(&year) || !(1..=12).contains(&month) {
        return Err(format!("invalid adapter date {date:?}"));
    }
    let months = [
        31,
        if leap(year) { 29 } else { 28 },
        31,
        30,
        31,
        30,
        31,
        31,
        30,
        31,
        30,
        31,
    ];
    if day == 0 || day > months[month as usize - 1] {
        return Err(format!("invalid adapter date {date:?}"));
    }
    let years = (1970..year)
        .map(|y| if leap(y) { 366 } else { 365 })
        .sum::<u64>();
    Ok(years + months[..month as usize - 1].iter().sum::<u64>() + day - 1)
}

fn policy(caller: &str, today: u64) -> Result<(), String> {
    policy_from(LEDGER, caller, today)
}

fn policy_from(ledger: &str, caller: &str, today: u64) -> Result<(), String> {
    let value: Policy =
        serde_json::from_str(ledger).map_err(|error| format!("invalid witness ledger: {error}"))?;
    let expected_modules = [
        "tests/testsuite/build_dir.rs",
        "tests/testsuite/build_dir_fine_grain_locking.rs",
        "tests/testsuite/build_dir_legacy.rs",
    ];
    let caller = caller.replace('\\', "/");
    if value.schema_version != 1
        || value.id != "trust.vanilla.targo-managed-witness-layout"
        || value.owner != "@trust-release"
        || value.status != "active"
        || value.store_magic != "TWSTORE2"
        || value.stem_hex_digits != 16
        || value.modules != expected_modules
        || value.reason.is_empty()
        || Path::new(&caller)
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
        || !expected_modules.iter().any(|file| {
            caller == *file
                || caller == format!("src/tools/targo/{file}")
                || caller.ends_with(&format!("/src/tools/targo/{file}"))
        })
    {
        return Err(format!(
            "witness layout adapter has unsupported policy or caller {caller:?}"
        ));
    }
    let reviewed = date_day(&value.reviewed_on)?;
    let expires = date_day(&value.expires_on)?;
    if expires < reviewed || expires - reviewed > 31 || today < reviewed || today > expires {
        return Err(
            "witness layout adapter is unreviewed, expired, or has an excessive review interval"
                .into(),
        );
    }
    Ok(())
}

fn take<'a>(bytes: &'a [u8], cursor: &mut usize, count: usize) -> Result<&'a [u8], String> {
    let end = cursor.checked_add(count).ok_or("witness length overflow")?;
    let result = bytes.get(*cursor..end).ok_or("truncated witness store")?;
    *cursor = end;
    Ok(result)
}

fn envelope(bytes: &[u8]) -> Result<u32, String> {
    let mut cursor = 0;
    if take(bytes, &mut cursor, 8)? != b"TWSTORE2" {
        return Err("unsupported witness store magic".into());
    }
    let count = u32::from_le_bytes(take(bytes, &mut cursor, 4)?.try_into().unwrap());
    if count as usize > bytes.len().saturating_sub(cursor) / 14 {
        return Err("witness entry count exceeds framing".into());
    }
    let mut previous = None;
    for _ in 0..count {
        let size = u16::from_le_bytes(take(bytes, &mut cursor, 2)?.try_into().unwrap()) as usize;
        let key = take(bytes, &mut cursor, size)?;
        if key.is_empty()
            || std::str::from_utf8(key).is_err()
            || previous.is_some_and(|old| old >= key)
        {
            return Err("witness keys must be nonempty UTF-8 in unique sorted order".into());
        }
        previous = Some(key);
        let size = u32::from_le_bytes(take(bytes, &mut cursor, 4)?.try_into().unwrap()) as usize;
        let payload = take(bytes, &mut cursor, size)?;
        if !payload.starts_with(b"TWV1") {
            return Err("unsupported witness payload magic".into());
        }
        let expected = u64::from_le_bytes(take(bytes, &mut cursor, 8)?.try_into().unwrap());
        let actual = key
            .iter()
            .chain(payload)
            .fold(0xcbf2_9ce4_8422_2325u64, |hash, byte| {
                (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
            });
        // Production unpack turns a corrupt entry into a cache miss. A layout
        // assertion is stricter: it must not hide a malformed emitted file.
        if expected != actual {
            return Err("witness entry integrity mismatch".into());
        }
    }
    if cursor != bytes.len() {
        return Err("trailing witness store bytes".into());
    }
    Ok(count)
}

fn witness_name(path: &Path) -> bool {
    let Some(stem) = path.file_stem().and_then(|value| value.to_str()) else {
        return false;
    };
    stem.len() == 16
        && stem
            .bytes()
            .all(|value| value.is_ascii_digit() || (b'a'..=b'f').contains(&value))
}

fn validate_stores(
    root: &Path,
    expected: &[(&str, usize)],
    trust_compiler: bool,
    matches: impl Fn(&str, &str) -> bool,
) -> Result<BTreeSet<PathBuf>, String> {
    let mut counts = vec![0; expected.len()];
    let mut found = BTreeSet::new();
    let mut unit_directories = BTreeMap::new();
    for (pattern, count) in expected {
        if *count == 0
            || pattern.contains("[..]")
            || pattern.contains('\n')
            || !pattern.starts_with("[ROOT]/")
        {
            return Err("witness locations need explicit bounded compiler out-dir patterns and positive counts".into());
        }
    }
    for entry in WalkDir::new(root).sort_by_file_name() {
        let entry =
            entry.map_err(|error| format!("could not inspect full witness layout: {error}"))?;
        let path = entry.path();
        if entry.file_type().is_dir() && entry.file_name() == "trust-witness" {
            return Err(format!(
                "managed witness directory violates flat-store contract: {}",
                path.display()
            ));
        }
        if path.extension().is_none_or(|value| value != "twit") {
            continue;
        }
        if !entry.file_type().is_file() || !witness_name(path) {
            return Err(format!(
                "witness must be a regular <16-lowercase-hex>.twit file: {}",
                path.display()
            ));
        }
        let parent = path
            .parent()
            .unwrap()
            .to_str()
            .ok_or("non-UTF8 witness directory")?;
        let locations = expected
            .iter()
            .enumerate()
            .filter(|(_, (pattern, _))| matches(pattern, parent))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if !trust_compiler || locations.len() != 1 {
            return Err(format!(
                "unexpected or ambiguous witness location: {}",
                path.display()
            ));
        }
        envelope(&fs::read(path).map_err(|error| format!("could not read witness: {error}"))?)?;
        let pattern = expected[locations[0]].0;
        if pattern.ends_with("/out") || pattern.ends_with("/artifact/bin") {
            let count = unit_directories
                .entry(path.parent().unwrap().to_owned())
                .or_insert(0);
            *count += 1;
            if *count != 1 {
                return Err(format!(
                    "multiple crate stores in one dedicated compiler unit out-dir: {parent}"
                ));
            }
        }
        counts[locations[0]] += 1;
        found.insert(path.to_owned());
    }
    for (index, (pattern, count)) in expected.iter().enumerate() {
        let required = if trust_compiler { *count } else { 0 };
        if counts[index] != required {
            return Err(format!(
                "witness count at {pattern}: expected {required}, found {}",
                counts[index]
            ));
        }
    }
    Ok(found)
}

/// The explicit adapter is available only to the three ledgered modules.
/// Each count/location is authored beside the unchanged upstream snapshot.
pub trait TrustWitnessLayout {
    #[track_caller]
    fn assert_build_dir_layout_with_witnesses(
        &self,
        expected: impl IntoData,
        stores: &[(&str, usize)],
    );
}

impl TrustWitnessLayout for Path {
    #[track_caller]
    fn assert_build_dir_layout_with_witnesses(
        &self,
        expected: impl IntoData,
        stores: &[(&str, usize)],
    ) {
        let today = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("UTC clock predates epoch")
            .as_secs()
            / 86400;
        policy(std::panic::Location::caller().file(), today)
            .unwrap_or_else(|error| panic!("{error}"));
        let trust_version = crate::rustc_info()
            .verbose_version
            .lines()
            .find_map(|line| line.strip_prefix("trust: "));
        assert!(
            trust_version.is_none_or(|value| !value.is_empty() && value != "unknown"),
            "unbound Trust compiler identity"
        );
        let assert = assert_e2e().action(snapbox::assert::Action::Verify);
        let witnesses =
            validate_stores(self, stores, trust_version.is_some(), |pattern, actual| {
                match_contains(pattern, actual, &assert.redactions()).is_ok()
            })
            .unwrap_or_else(|error| panic!("{error}"));
        let mut actual = Vec::new();
        for entry in WalkDir::new(self).sort_by_file_name() {
            let entry = entry.expect("all layout entries must be readable");
            if !entry.file_type().is_file() || witnesses.contains(entry.path()) {
                continue;
            }
            let path = entry.path().to_string_lossy().into_owned();
            if super::build_dir_ignored_path_patterns()
                .iter()
                .any(|pattern| match_contains(pattern, &path, &assert.redactions()).is_ok())
            {
                continue;
            }
            actual.push(path);
        }
        // Preserve every original non-witness assertion and upstream dSYM/PDB
        // rule. Only the exact independently validated witness set is projected.
        assert.eq(format!("{}\n", actual.join("\n")), expected.unordered());
    }
}

impl TrustWitnessLayout for PathBuf {
    #[track_caller]
    fn assert_build_dir_layout_with_witnesses(
        &self,
        expected: impl IntoData,
        stores: &[(&str, usize)],
    ) {
        self.as_path()
            .assert_build_dir_layout_with_witnesses(expected, stores);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct OwnedDirectory(PathBuf);

    impl OwnedDirectory {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            for _ in 0..100 {
                let path = std::env::temp_dir().join(format!(
                    "trust-targo-witness-layout-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed),
                ));
                let mut builder = fs::DirBuilder::new();
                #[cfg(unix)]
                {
                    use std::os::unix::fs::DirBuilderExt;
                    builder.mode(0o700);
                }
                match builder.create(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("could not create owned test directory: {error}"),
                }
            }
            panic!("could not reserve unique test directory");
        }
    }

    impl Drop for OwnedDirectory {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).expect("remove only this test's owned directory");
        }
    }

    fn empty_store(directory: &Path, name: &str) -> PathBuf {
        fs::create_dir_all(directory).unwrap();
        let path = directory.join(name);
        fs::write(&path, b"TWSTORE2\0\0\0\0").unwrap();
        path
    }

    fn validate(root: &Path, count: usize, trust: bool) -> Result<BTreeSet<PathBuf>, String> {
        validate_stores(
            root,
            &[("[ROOT]/unit/out", count)],
            trust,
            |pattern, actual| pattern == "[ROOT]/unit/out" && Path::new(actual) == root.join("out"),
        )
    }

    #[test]
    fn exact_declared_store_is_required_and_unrelated_files_stay_visible() {
        let root = OwnedDirectory::new();
        assert!(
            validate(&root.0, 1, true).is_err(),
            "missing witness was accepted"
        );
        let file = empty_store(&root.0.join("out"), "0123456789abcdef.twit");
        fs::write(
            root.0.join("out/unexpected.txt"),
            b"keep this in the original snapshot",
        )
        .unwrap();
        let found = validate(&root.0, 1, true).unwrap();
        assert_eq!(found, BTreeSet::from([file]));
        assert!(!found.contains(&root.0.join("out/unexpected.txt")));
        empty_store(&root.0.join("out"), "1123456789abcdef.twit");
        assert!(
            validate(&root.0, 1, true).is_err(),
            "extra store was accepted"
        );
        assert!(
            validate(&root.0, 2, true).is_err(),
            "multiple stores in a dedicated unit out-dir were accepted"
        );
    }

    #[test]
    fn names_locations_regularity_and_flatness_refuse_unexpected_objects() {
        for (directory, name) in [
            ("wrong", "0123456789abcdef.twit"),
            ("out/nested", "0123456789abcdef.twit"),
            ("out", "0123456789abcdeF.twit"),
            ("out", "extra.twit"),
            ("out/trust-witness", "0123456789abcdef.twit"),
        ] {
            let root = OwnedDirectory::new();
            empty_store(&root.0.join(directory), name);
            assert!(
                validate(&root.0, 1, true).is_err(),
                "accepted {directory}/{name}"
            );
        }
        let root = OwnedDirectory::new();
        fs::create_dir_all(root.0.join("out/0123456789abcdef.twit")).unwrap();
        assert!(validate(&root.0, 1, true).is_err());
        #[cfg(unix)]
        {
            let root = OwnedDirectory::new();
            fs::create_dir(root.0.join("out")).unwrap();
            fs::write(root.0.join("target"), b"TWSTORE2\0\0\0\0").unwrap();
            std::os::unix::fs::symlink(
                root.0.join("target"),
                root.0.join("out/0123456789abcdef.twit"),
            )
            .unwrap();
            assert!(
                validate(&root.0, 1, true).is_err(),
                "symlink store was accepted"
            );
        }
    }

    #[test]
    fn stock_compiler_keeps_the_pristine_no_witness_layout() {
        let root = OwnedDirectory::new();
        assert!(validate(&root.0, 1, false).unwrap().is_empty());
        empty_store(&root.0.join("out"), "0123456789abcdef.twit");
        assert!(
            validate(&root.0, 1, false).is_err(),
            "stock mode hid a witness"
        );
    }

    #[test]
    fn corrupt_truncated_and_trailing_store_bytes_refuse() {
        assert_eq!(envelope(b"TWSTORE2\0\0\0\0").unwrap(), 0);
        for invalid in [
            b"".as_slice(),
            b"TWSTORE1\0\0\0\0",
            b"TWSTORE2\0\0\0",
            b"TWSTORE2\0\0\0\0trailing",
            b"TWSTORE2\xff\xff\xff\xff",
        ] {
            assert!(envelope(invalid).is_err());
        }
        let root = OwnedDirectory::new();
        let file = empty_store(&root.0.join("out"), "0123456789abcdef.twit");
        fs::write(file, b"TWSTORE1\0\0\0\0").unwrap();
        assert!(
            validate(&root.0, 1, true).is_err(),
            "corrupt regular store was accepted"
        );
    }

    #[test]
    fn payload_integrity_and_unique_key_census_are_checked() {
        // Independent fixed framing/FNV vector for key `root`, payload
        // `TWV1\0`: this is a format fixture, not a replayable typeck claim.
        let valid = [
            84, 87, 83, 84, 79, 82, 69, 50, 1, 0, 0, 0, 4, 0, 114, 111, 111, 116, 5, 0, 0, 0, 84,
            87, 86, 49, 0, 39, 49, 224, 202, 121, 43, 198, 194,
        ];
        assert_eq!(envelope(&valid).unwrap(), 1);
        for byte in [14, 22, 26, 27, 34] {
            let mut corrupt = valid;
            corrupt[byte] ^= 1;
            assert!(envelope(&corrupt).is_err(), "accepted corrupt byte {byte}");
        }
        let mut duplicate = valid.to_vec();
        duplicate[8..12].copy_from_slice(&2u32.to_le_bytes());
        duplicate.extend_from_slice(&valid[12..]);
        assert!(envelope(&duplicate).unwrap_err().contains("unique sorted"));
    }

    #[test]
    fn adapter_enforces_source_scope_review_expiry_and_known_schema() {
        let today = date_day("2026-10-24").unwrap();
        assert_eq!(date_day("1970-01-01").unwrap(), 0);
        assert!(date_day("2026-02-29").is_err());
        assert!(policy("tests/testsuite/build_dir.rs", today).is_ok());
        assert!(policy("src/tools/targo/tests/testsuite/build_dir.rs", today).is_ok());
        assert!(policy("tests/testsuite/foreign.rs", today).is_err());
        assert!(
            policy(
                "tests/testsuite/build_dir.rs",
                date_day("2026-11-24").unwrap()
            )
            .is_err()
        );
        assert!(policy("tests/testsuite/build_dir.rs", today - 1).is_err());
        assert!(
            policy_from(
                &LEDGER.replace("TWSTORE2", "TWSTORE3"),
                "tests/testsuite/build_dir.rs",
                today
            )
            .is_err()
        );
        let mut unknown: serde_json::Value = serde_json::from_str(LEDGER).unwrap();
        unknown
            .as_object_mut()
            .unwrap()
            .insert("allow_missing".into(), true.into());
        assert!(
            policy_from(
                &serde_json::to_string(&unknown).unwrap(),
                "tests/testsuite/build_dir.rs",
                today
            )
            .is_err()
        );
        assert!(
            policy_from(
                &LEDGER.replace("2026-11-23", "2027-11-23"),
                "tests/testsuite/build_dir.rs",
                today
            )
            .is_err()
        );
    }
}
