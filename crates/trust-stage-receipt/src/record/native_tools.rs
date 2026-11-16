//! The native stage tools a receipt binds beside its Rust tools: today only rust-lld,
//! which must be the bytes of the lld that the in-tree LLVM the receipt states built.
//!
//! The twin of the `native_stage_tools` branch of `_recorded_files` in
//! scripts/lib/stage_receipt_provenance.py, with the same words. A bound row adds its
//! file to the files the reader hashes, so it is counted in
//! `stage_receipt_files_verified`. tests/data/fixed-point-cases.json holds both readers
//! to the same verdicts on the same receipts. Nothing here reads a file.

use std::collections::BTreeSet;

use crate::{Refusal, Result, Value, digest, repr};

const NAME: &str = "rust-lld";

/// `files` (what, recorded path, recorded sha256) after the receipt's native stage tools.
/// `names` holds the names of the receipt's `tools` rows, which no native tool may repeat.
pub(super) fn recorded<'a>(
    receipt: &'a Value,
    mut names: BTreeSet<&'a str>,
    mut files: Vec<(String, Value, String)>,
) -> Result<Vec<(String, Value, String)>> {
    // An absent key binds no native tool; a present one, null included, must be a list.
    let Some(rows) = receipt.get("native_stage_tools") else {
        return Ok(files);
    };
    let rows = rows.as_array().ok_or_else(|| Refusal("native_stage_tools is not a list".into()))?;
    let stage = receipt["stage_root"].as_str().expect("validated receipt stage root");
    let llvm = &receipt["llvm_identity"];
    let suffix = if names_windows(&receipt["host"]) { ".exe" } else { "" };
    let prefix = lld_prefix(stage);
    for row in rows {
        if !row.is_object() || row["name"] != NAME || !names.insert(NAME) {
            return Err(Refusal("native_stage_tools has an unknown or duplicate tool".into()));
        }
        let sha = digest(row, "sha256", "native_stage_tools.rust-lld.")?;
        if row["status"] != "bound"
            || row["producer_sha256"] != sha.as_str()
            || row["producer_kind"] != "in-tree-llvm-project"
            || row["version_probe_ok"] != true
            || !llvm.is_object()
            || llvm["mode"] != "in-tree"
            || llvm["identity_stated"] != true
            || !python_equal(&row["llvm_source_identity_sha256"], &llvm["source_identity_sha256"])
            || !python_equal(
                &row["llvm_output_fingerprint_sha256"],
                &llvm["output_fingerprint_sha256"],
            )
            || row["path"] != format!("{stage}/bin/{NAME}{suffix}").as_str()
            || row["producer_path"] != format!("{prefix}/bin/lld{suffix}").as_str()
            || !llvm["output_dirs"]
                .as_array()
                .is_some_and(|dirs| dirs.iter().any(|dir| *dir == prefix.as_str()))
        {
            return Err(Refusal(
                "native stage tool rust-lld is not bound to its stated LLVM producer".into(),
            ));
        }
        files.push((format!("native tool {NAME}"), row["path"].clone(), sha));
    }
    Ok(files)
}

/// `"windows" in str(host)`: a string is itself, any other value its repr.
fn names_windows(host: &Value) -> bool {
    match host.as_str() {
        Some(host) => host.contains("windows"),
        None => repr(host).contains("windows"),
    }
}

/// `str(PurePosixPath(stage).parent / "lld")` for a stage root the reader accepted: a
/// relative path whose components are not empty. PurePosixPath drops a `.` component
/// and keeps a `..` one.
fn lld_prefix(stage: &str) -> String {
    let mut parts =
        stage.split('/').filter(|part| !part.is_empty() && *part != ".").collect::<Vec<_>>();
    parts.pop();
    parts.push("lld");
    parts.join("/")
}

/// Python's `==` on two decoded JSON values, which the reference applies to the LLVM
/// identities a row repeats before anything checks what they are: `true` is the
/// integer 1 and `false` is 0, an integer and a float are equal when their values are,
/// and objects compare without order.
fn python_equal(left: &Value, right: &Value) -> bool {
    let mut pending = vec![(left, right)];
    while let Some(pair) = pending.pop() {
        match pair {
            (Value::Null, Value::Null) => {}
            (Value::String(a), Value::String(b)) if a == b => {}
            (Value::Array(a), Value::Array(b)) if a.len() == b.len() => {
                pending.extend(a.iter().zip(b));
            }
            (Value::Object(a), Value::Object(b)) if a.len() == b.len() => {
                for (key, value) in a {
                    let Some(other) = b.get(key) else { return false };
                    pending.push((value, other));
                }
            }
            (left, right) => match (Numeric::of(left), Numeric::of(right)) {
                (Some(a), Some(b)) if a.equals(&b) => {}
                _ => return false,
            },
        }
    }
    true
}

/// A JSON scalar as Python's `json` module decodes it for a comparison.
enum Numeric {
    /// An integer's decimal digits and sign, the token `-0` read as `0`.
    Integer(String),
    Float(f64),
}

impl Numeric {
    fn of(value: &Value) -> Option<Self> {
        match value {
            Value::Bool(value) => Some(Self::Integer(if *value { "1" } else { "0" }.into())),
            Value::Number(number) if number.is_integer() => Some(Self::Integer(
                if number.as_str() == "-0" { "0" } else { number.as_str() }.into(),
            )),
            // Correctly rounded, as Python's float(); an exponent past the range is inf.
            Value::Number(number) => number.as_str().parse().ok().map(Self::Float),
            _ => None,
        }
    }

    fn equals(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(a), Self::Integer(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => a == b,
            (Self::Integer(digits), Self::Float(value))
            | (Self::Float(value), Self::Integer(digits)) => {
                // Python compares an int with a float by exact value, never by rounding
                // the int; a float that is integral prints its exact digits at `.0`.
                value.is_finite()
                    && value.fract() == 0.0
                    && *digits == if *value == 0.0 { "0".into() } else { format!("{value:.0}") }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json;

    fn equal(left: &str, right: &str) -> bool {
        python_equal(
            &json::parse(left.as_bytes()).unwrap(),
            &json::parse(right.as_bytes()).unwrap(),
        )
    }

    #[test]
    fn comparisons_are_python_equality_of_the_decoded_values() {
        // Each verdict is Python's `json.loads(left) == json.loads(right)`.
        for (left, right, python) in [
            ("1", "1.0", true),
            ("1", "1e0", true),
            ("true", "1", true),
            ("true", "1.0", true),
            ("false", "0", true),
            ("0", "-0.0", true),
            ("-0", "0", true),
            ("-5", "-5.0", true),
            ("9007199254740992", "9007199254740992.0", true),
            ("9007199254740993", "9007199254740992.0", false),
            ("1e400", "1e400", true),
            ("1e400", "1", false),
            ("1.5", "1", false),
            ("null", "null", true),
            ("null", "0", false),
            ("\"1\"", "1", false),
            ("[1, true]", "[1.0, 1]", true),
            ("[1]", "[1, 1]", false),
            (r#"{"a": 1, "b": [false]}"#, r#"{"b": [0.0], "a": 1.0}"#, true),
            (r#"{"a": 1}"#, r#"{"b": 1}"#, false),
            ("{}", "[]", false),
        ] {
            assert_eq!(equal(left, right), python, "{left} == {right}");
            assert_eq!(equal(right, left), python, "{right} == {left}");
        }
        // int(1e300) in Python: the exact value of the float, not its shortest spelling.
        let exact = "1000000000000000052504760255204420248704468581108159154915854115511802457988908195786371375080447864043704443832883878176942523235360430575644792184786706982848387200926575803737830233794788090059368953234970799945081119038967640880074652742780142494579258788820056842838115669472196386865459400540160";
        assert!(equal(exact, "1e300"));
        assert!(!equal(&format!("1{}", "0".repeat(300)), "1e300"));
    }

    #[test]
    fn the_lld_prefix_is_the_stage_roots_pure_posix_parent() {
        // str(PurePosixPath(stage).parent / "lld") in Python, for each.
        for (stage, python) in [
            ("b/host/s9", "b/host/lld"),
            ("b/./s9", "b/lld"),
            ("b/mint/./s9", "b/mint/lld"),
            ("b/mint/host/s9", "b/mint/host/lld"),
            ("s9", "lld"),
        ] {
            assert_eq!(lld_prefix(stage), python, "{stage}");
        }
    }

    #[test]
    fn a_host_names_windows_as_its_python_str_does() {
        for (host, python) in [
            (r#""x86_64-pc-windows-msvc""#, true),
            (r#""test-host""#, false),
            (r#"["x86_64-pc-windows-msvc"]"#, true),
            (r#"{"windows": 1}"#, true),
            ("null", false),
            ("1", false),
        ] {
            assert_eq!(names_windows(&json::parse(host.as_bytes()).unwrap()), python, "{host}");
        }
    }
}
