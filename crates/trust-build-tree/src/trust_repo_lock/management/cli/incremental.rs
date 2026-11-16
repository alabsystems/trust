//! Shared native CLI over the incremental cache owner, used by both genuine
//! Targo and Bootstrap. This does not spawn Python, shell, or another manager.
use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::path::PathBuf;

use super::{Environment, default_root};
use crate::trust_repo_lock::incremental::{Outcome, Thresholds, reclaim};

const PROTOCOL: &str = "trust-incremental-reclamation-v1";
const USAGE: &str = "Usage: targo trust repo lock reclaim-incremental [--apply] [--quiet] [--max-gib N] [--min-free-gib N] [--repo-root DIR]\n\nOnly crates/target*/debug/incremental is eligible. Default: report only; retain\nunder50GiB unless volume free space is below100GiB and cache is at least1GiB.\nBusy Cargo profiles are skipped. Unknown facts and escaping paths refuse.\nTRUST_INCREMENTAL_MAX_GIB and TRUST_INCREMENTAL_MIN_FREE_GIB supply defaults.\n";

/// Optional, bounded maintenance under the newly acquired native owner. A
/// refused cache remains untouched and cannot change the tree's ownership.
pub(super) fn on_acquired(
    root: &std::path::Path,
    environment: &Environment,
    diagnostics: &mut dyn Write,
) {
    let arguments = [
        OsString::from("--apply"),
        OsString::from("--quiet"),
        OsString::from("--repo-root"),
        root.as_os_str().to_owned(),
    ];
    if let Err(error) = checked(&arguments, environment, &mut std::io::sink(), diagnostics) {
        let _ = writeln!(diagnostics, "trust incremental cache: maintenance refused: {error}");
    }
}

fn gib(value: &OsStr) -> Result<u64, String> {
    let value: f64 = value
        .to_str()
        .ok_or("threshold must be UTF-8")?
        .parse()
        .map_err(|_| "threshold must be a finite nonnegative GiB number")?;
    let bytes = value * (1024u64 * 1024 * 1024) as f64;
    if !value.is_finite() || value < 0.0 || !bytes.is_finite() || bytes >= u64::MAX as f64 {
        return Err("threshold must be finite, nonnegative and representable in bytes".into());
    }
    // Integral observations satisfy x>=threshold / x<threshold exactly when
    // compared with ceil(threshold), including fractional-byte thresholds.
    Ok(bytes.ceil() as u64)
}

pub(super) fn checked(
    args: &[OsString],
    environment: &Environment,
    output: &mut dyn Write,
    diagnostics: &mut dyn Write,
) -> Result<u8, String> {
    if args.len() > 32 || args.iter().any(|arg| arg.as_encoded_bytes().len() > 32768) {
        return Err("incremental request exceeds its argument bound".into());
    }
    if args == [OsString::from("--protocol")] {
        writeln!(output, "{PROTOCOL}").map_err(|error| error.to_string())?;
        return Ok(0);
    }
    if args == [OsString::from("--help")] || args == [OsString::from("-h")] {
        output.write_all(USAGE.as_bytes()).map_err(|error| error.to_string())?;
        return Ok(0);
    }
    let mut values = BTreeMap::new();
    let mut apply = false;
    let mut quiet = false;
    let mut index = 0;
    while index < args.len() {
        let key = args[index].to_str().ok_or("option must be UTF-8")?;
        if key == "--apply" && !apply {
            apply = true;
        } else if key == "--quiet" && !quiet {
            quiet = true;
        } else if matches!(key, "--repo-root" | "--max-gib" | "--min-free-gib") {
            let value = args.get(index + 1).ok_or_else(|| format!("{key} requires a value"))?;
            if values.insert(key, value).is_some() {
                return Err(format!("duplicate incremental option {key}"));
            }
            index += 1;
        } else {
            return Err(format!("unexpected incremental option {key}"));
        }
        index += 1;
    }
    let defaults = Thresholds::default();
    let threshold = |flag, configured: Option<&OsStr>, fallback| {
        if let Some(value) = values.get(flag) {
            gib(value)
        } else {
            configured.map(gib).unwrap_or(Ok(fallback))
        }
    };
    let thresholds = Thresholds {
        max_cache_bytes: threshold(
            "--max-gib",
            environment.incremental_max.as_deref(),
            defaults.max_cache_bytes,
        )?,
        min_free_bytes: threshold(
            "--min-free-gib",
            environment.incremental_min_free.as_deref(),
            defaults.min_free_bytes,
        )?,
    };
    let root = values
        .get("--repo-root")
        .map(|path| Ok(PathBuf::from(*path)))
        .unwrap_or_else(|| default_root(environment))
        .map_err(|error| error.to_string())?;
    let rows = reclaim(&root, thresholds, apply).map_err(|error| error.to_string())?;
    let mut code = 0;
    if rows.is_empty() && !quiet {
        writeln!(output, "trust incremental cache: no eligible cache")
            .map_err(|error| error.to_string())?;
    }
    for row in rows {
        let loud = matches!(row.outcome, Outcome::Busy | Outcome::Reclaimed | Outcome::Refused(_))
            || row.removed_interrupted_reclaims != 0;
        code |= u8::from(matches!(row.outcome, Outcome::Refused(_)));
        if quiet && !loud {
            continue;
        }
        let writer: &mut dyn Write = if loud { &mut *diagnostics } else { &mut *output };
        writeln!(writer,
            "trust incremental cache: {}: {:?}; allocated_bytes={:?}; free_bytes={:?}; interrupted_removed={}",
            row.cache.display(), row.outcome, row.allocated_bytes, row.free_bytes, row.removed_interrupted_reclaims
        ).map_err(|error| error.to_string())?;
    }
    Ok(code)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn invoke(root: &std::path::Path, words: &[&str]) -> (u8, String, String) {
        let args: Vec<_> = words.iter().map(OsString::from).collect();
        let environment =
            Environment { root: Some(root.as_os_str().to_owned()), ..Environment::default() };
        let mut output = Vec::new();
        let mut diagnostics = Vec::new();
        let code = super::super::execute(&args, &environment, &mut output, &mut diagnostics);
        (code, String::from_utf8(output).unwrap(), String::from_utf8(diagnostics).unwrap())
    }

    #[test]
    fn native_reclaim_entry_reports_and_applies_actual_cache_without_creating_build_holder() {
        let root = tempfile::tempdir().unwrap();
        let cache = root.path().join("crates/target.noindex/debug/incremental");
        std::fs::create_dir_all(&cache).unwrap();
        std::fs::write(cache.join("state"), b"incremental cache").unwrap();
        let words = ["reclaim-incremental", "--max-gib", "0", "--min-free-gib", "0"];
        let (code, output, error) = invoke(root.path(), &words);
        assert_eq!(code, 0, "{error}");
        assert!(output.contains("WouldReclaim"));
        assert!(cache.exists());
        let mut apply = words.to_vec();
        apply.extend(["--apply", "--quiet"]);
        let (code, output, error) = invoke(root.path(), &apply);
        assert_eq!(code, 0, "{error}");
        assert!(output.is_empty());
        assert!(error.contains("Reclaimed"));
        assert!(!cache.exists());
        assert!(!root.path().join(".trust-build-lock").exists());
    }

    #[test]
    fn native_reclaim_protocol_and_help_need_no_root_or_ambient_policy() {
        let invalid = std::path::Path::new("/nonexistent/incremental/native/root");
        assert_eq!(
            invoke(invalid, &["reclaim-incremental", "--protocol"]),
            (0, format!("{PROTOCOL}\n"), String::new())
        );
        let (code, output, error) = invoke(invalid, &["reclaim-incremental", "--help"]);
        assert_eq!(code, 0, "{error}");
        assert!(output.contains("report only"));
    }

    #[test]
    fn native_reclaim_invalid_policy_refuses_before_deleting() {
        let root = tempfile::tempdir().unwrap();
        let cache = root.path().join("crates/target/debug/incremental");
        std::fs::create_dir_all(&cache).unwrap();
        for words in [
            vec!["reclaim-incremental", "--apply", "--max-gib", "NaN"],
            vec!["reclaim-incremental", "--apply", "--apply"],
            vec!["reclaim-incremental", "--max-gib"],
            vec!["reclaim-incremental", "--min-free-gib", "-1"],
        ] {
            let (code, _, _) = invoke(root.path(), &words);
            assert_eq!(code, 2, "{words:?}");
            assert!(cache.exists());
        }
    }

    #[test]
    fn fractional_gib_thresholds_preserve_integral_comparisons_and_refuse_nonfinite_values() {
        assert_eq!(gib(OsStr::new("0")), Ok(0));
        assert_eq!(gib(OsStr::new("0.5")), Ok(512 * 1024 * 1024));
        assert_eq!(gib(OsStr::new("0.0000000005")), Ok(1));
        for value in ["NaN", "inf", "-1", "1e100", "garbage"] {
            assert!(gib(OsStr::new(value)).is_err(), "{value}");
        }
    }
}
