//! Small diagnostic protocol helpers; no compiler proof authority.

use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::{Value, json};
use trust_types::{stable_sha256_hex, stable_sha256_hex_reader};

pub fn reject_response_files(args: &[String]) -> Result<(), String> {
    if args.iter().any(|arg| arg.starts_with('@')) {
        Err("response files are outside this bounded diagnostic; refusing uninspected arguments"
            .into())
    } else {
        Ok(())
    }
}

pub fn single_option(args: &[String], name: &str) -> Result<Option<String>, String> {
    let mut result = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let value = if arg == name {
            Some(args.next().ok_or_else(|| format!("missing value for {name}"))?.clone())
        } else {
            arg.strip_prefix(&format!("{name}=")).map(str::to_owned)
        };
        if let Some(value) = value {
            if result.replace(value).is_some() {
                return Err(format!("duplicate {name} is outside this diagnostic"));
            }
        }
    }
    Ok(result)
}

pub fn select_primary(
    args: &[String],
    manifest: Option<&Path>,
    root: Option<&Path>,
) -> Result<bool, String> {
    if single_option(args, "--crate-name")?.as_deref() != Some("clean_kernel") {
        return Ok(false);
    }
    let (Some(manifest), Some(root)) = (manifest, root) else { return Ok(false) };
    let expected =
        fs::canonicalize(root.join("crates/clean-kernel")).map_err(|error| error.to_string())?;
    if fs::canonicalize(manifest).map_err(|error| error.to_string())? != expected {
        return Ok(false);
    }
    let source = expected.join("src/lib.rs");
    let inputs: Vec<_> = args.iter().filter(|arg| arg.ends_with(".rs")).collect();
    if inputs.len() != 1
        || fs::canonicalize(inputs[0]).map_err(|error| error.to_string())? != source
    {
        return Err("clean-kernel primary must name exactly its actual src/lib.rs".into());
    }
    if args.iter().any(|arg| arg == "--test")
        || !matches!(single_option(args, "--crate-type")?.as_deref(), Some("lib" | "rlib"))
    {
        return Err(
            "capture selects only the real clean-kernel library, not test/harness units".into()
        );
    }
    Ok(true)
}

pub fn bind_sysroot(mut args: Vec<String>, sysroot: &Path) -> Result<Vec<String>, String> {
    if let Some(selected) = single_option(&args, "--sysroot")? {
        if fs::canonicalize(selected).map_err(|error| error.to_string())? != sysroot {
            return Err("compiler arguments select a different sysroot".into());
        }
    } else {
        args.push("--sysroot".into());
        args.push(sysroot.to_str().ok_or("non-UTF-8 sysroot")?.to_owned());
    }
    Ok(args)
}

pub fn require_one_owner(count: usize) -> Result<(), String> {
    if count == 1 {
        Ok(())
    } else {
        Err(format!("expected exactly one production helper owner, found {count}"))
    }
}

pub fn require_fresh_output(path: &Path) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error.to_string()),
        Ok(_) => Err(format!("capture output already exists: {}", path.display())),
    }
}

pub fn file_digest(path: &Path) -> Result<String, String> {
    stable_sha256_hex_reader(
        File::open(path).map_err(|error| format!("{}: {error}", path.display()))?,
    )
    .map_err(|error| error.to_string())
}

pub fn record_read(
    reads: &mut BTreeMap<PathBuf, String>,
    path: &Path,
    bytes: &[u8],
) -> Result<(), String> {
    let path = fs::canonicalize(path).map_err(|error| error.to_string())?;
    let digest = stable_sha256_hex(bytes);
    if reads.get(&path).is_some_and(|prior| prior != &digest) {
        return Err(format!("input changed between reads: {}", path.display()));
    }
    reads.insert(path, digest);
    Ok(())
}

pub fn check_observed_reads(reads: &BTreeMap<PathBuf, String>) -> Result<(), String> {
    for (path, expected) in reads {
        if file_digest(path)? != *expected {
            return Err(format!("compiler-read input changed: {}", path.display()));
        }
    }
    Ok(())
}

pub fn json_digest(value: &Value) -> Result<String, String> {
    let bytes = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    Ok(stable_sha256_hex(&bytes))
}

pub fn snapshot_paths(paths: &[PathBuf]) -> Result<Value, String> {
    let mut rows = Vec::new();
    for path in paths {
        let path =
            fs::canonicalize(path).map_err(|error| format!("{}: {error}", path.display()))?;
        rows.push(json!({"path": path, "sha256": file_digest(&path)?}));
    }
    Ok(Value::Array(rows))
}

pub fn git_snapshot(root: &Path) -> Result<Value, String> {
    let output = |args: &[&str]| -> Result<Vec<u8>, String> {
        let out = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(args)
            .output()
            .map_err(|error| error.to_string())?;
        if !out.status.success() {
            return Err(format!("git {args:?} failed: {}", String::from_utf8_lossy(&out.stderr)));
        }
        Ok(out.stdout)
    };
    let head = output(&["rev-parse", "HEAD"])?;
    let status = output(&["status", "--porcelain=v1", "--untracked-files=all"])?;
    let diff = output(&["diff", "--binary", "HEAD", "--"])?;
    Ok(json!({
        "root": root,
        "head": String::from_utf8(head).map_err(|error| error.to_string())?.trim(),
        "status": String::from_utf8(status).map_err(|error| error.to_string())?,
        "tracked_diff_sha256": stable_sha256_hex(&diff),
        "untracked_contents_bound": false,
    }))
}

pub fn publish_new(path: &Path, report: &Value) -> Result<(), String> {
    // Serialize before acquiring the output, so serialization failure cannot
    // leave a success-shaped artifact. create_new also protects against races.
    let bytes = serde_json::to_vec_pretty(report).map_err(|error| error.to_string())?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(&bytes)
        .and_then(|()| file.write_all(b"\n"))
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("incomplete diagnostic output {}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    static NEXT: AtomicU64 = AtomicU64::new(0);

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "faithful-capture-test-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).expect("fresh test directory");
            Self(path)
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).into()).collect()
    }

    #[test]
    fn option_protocol_rejects_duplicate_missing_and_response_file_arguments() {
        assert_eq!(
            single_option(&args(&["--crate-name=clean_kernel"]), "--crate-name").unwrap(),
            Some("clean_kernel".into())
        );
        assert!(single_option(&args(&["--crate-name"]), "--crate-name").is_err());
        assert!(
            single_option(&args(&["--crate-name=x", "--crate-name", "y"]), "--crate-name").is_err()
        );
        assert!(reject_response_files(&args(&["@arguments"])).is_err());
        assert!(reject_response_files(&args(&["-vV"])).is_ok());
    }

    #[test]
    fn queries_and_unrelated_crates_delegate_without_capture_configuration() {
        assert!(!select_primary(&args(&["-vV"]), None, None).unwrap());
        assert!(!select_primary(&args(&["--crate-name", "dependency"]), None, None).unwrap());
        assert!(!select_primary(&args(&["--crate-name", "clean_kernel"]), None, None).unwrap());
    }

    #[test]
    fn selection_binds_manifest_actual_source_and_library_kind() {
        let scratch = Scratch::new();
        let manifest = scratch.0.join("crates/clean-kernel");
        fs::create_dir_all(manifest.join("src")).unwrap();
        let source = manifest.join("src/lib.rs");
        fs::write(&source, b"// selection fixture only").unwrap();
        let mut argv = args(&["--crate-name", "clean_kernel", "--crate-type=lib"]);
        argv.push(source.to_str().unwrap().into());
        assert!(select_primary(&argv, Some(&manifest), Some(&scratch.0)).unwrap());
        assert!(!select_primary(&argv, Some(&scratch.0), Some(&scratch.0)).unwrap());
        argv.push("--test".into());
        assert!(select_primary(&argv, Some(&manifest), Some(&scratch.0)).is_err());
        argv.pop();
        argv.push(source.to_str().unwrap().into());
        assert!(select_primary(&argv, Some(&manifest), Some(&scratch.0)).is_err());
    }

    #[test]
    fn sysroot_is_explicit_and_cannot_switch_to_another_directory() {
        let a = Scratch::new();
        let b = Scratch::new();
        let a = fs::canonicalize(&a.0).unwrap();
        let added = bind_sysroot(vec![], &a).unwrap();
        assert_eq!(single_option(&added, "--sysroot").unwrap().as_deref(), a.to_str());
        assert_eq!(bind_sysroot(added.clone(), &a).unwrap(), added);
        assert!(bind_sysroot(args(&["--sysroot", b.0.to_str().unwrap()]), &a).is_err());
    }

    #[test]
    fn missing_and_duplicate_owners_refuse() {
        assert!(require_one_owner(0).is_err());
        assert!(require_one_owner(1).is_ok());
        assert!(require_one_owner(2).is_err());
    }

    #[test]
    fn publication_is_parseable_and_never_overwrites_an_existing_result() {
        let scratch = Scratch::new();
        let path = scratch.0.join("capture.json");
        require_fresh_output(&path).unwrap();
        publish_new(&path, &json!({"diagnostic": true})).unwrap();
        let before = fs::read(&path).unwrap();
        assert_eq!(serde_json::from_slice::<Value>(&before).unwrap(), json!({"diagnostic": true}));
        assert!(require_fresh_output(&path).is_err());
        assert!(publish_new(&path, &json!({"replacement": true})).is_err());
        assert_eq!(fs::read(path).unwrap(), before);
    }

    #[test]
    fn recorded_reads_reject_changes_during_or_after_compiler_reads() {
        let scratch = Scratch::new();
        let source = scratch.0.join("input.rs");
        fs::write(&source, b"original compiler input").unwrap();
        let mut reads = BTreeMap::new();
        record_read(&mut reads, &source, &fs::read(&source).unwrap()).unwrap();
        record_read(&mut reads, &source, &fs::read(&source).unwrap()).unwrap();
        check_observed_reads(&reads).unwrap();
        fs::write(&source, b"changed compiler input").unwrap();
        assert!(check_observed_reads(&reads).unwrap_err().contains("compiler-read input changed"));
        assert!(
            record_read(&mut reads, &source, &fs::read(&source).unwrap())
                .unwrap_err()
                .contains("input changed between reads")
        );
        fs::remove_file(&source).unwrap();
        assert!(check_observed_reads(&reads).is_err());
    }

    #[test]
    fn full_function_json_digest_survives_publication_and_binds_owner_and_span() {
        let scratch = Scratch::new();
        let path = scratch.0.join("capture.json");
        let function = json!({
            "name": "helper", "def_path": "crate::helper", "span": {"file": "actual.rs"},
            "body": {"datatype_defs": {"Actual": {"fields": ["preserved"]}}}
        });
        let digest = json_digest(&function).unwrap();
        publish_new(&path, &json!({"function": function, "function_json_sha256": digest})).unwrap();
        let parsed: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(json_digest(&parsed["function"]).unwrap(), parsed["function_json_sha256"]);
        for field in ["name", "def_path", "span"] {
            let mut changed = parsed["function"].clone();
            changed[field] = json!("changed provenance");
            assert_ne!(json_digest(&changed).unwrap(), digest, "{field} must be bound");
        }
    }
}
