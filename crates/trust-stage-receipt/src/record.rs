use std::collections::BTreeSet;
use std::path::Path;

use crate::{
    RECEIPT_NAME, RECEIPT_SCHEMA, Refusal, Result, Value, digest, files, is_hex, llvm, object,
    release_status_holds, repr, unrecordable_character,
};

pub fn invocation_errors(value: &Value) -> Vec<String> {
    if !value.is_object() {
        return vec!["recreator_invocation is not an object".into()];
    }
    let mut errors = Vec::new();
    if !crate::exact_keys(value, &["schema", "scope", "argv"]) {
        errors
            .push("recreator_invocation does not hold exactly the keys argv, schema, scope".into());
    }
    if value["schema"] != "trust.recreator-invocation.v1" {
        errors.push("recreator_invocation.schema is not trust.recreator-invocation.v1".into());
    }
    if value["scope"] != "self-reported" {
        errors.push("recreator_invocation.scope is not self-reported".into());
    }
    match value["argv"].as_array() {
        Some(argv) if argv.iter().all(Value::is_string) => {
            if argv.iter().any(|arg| unrecordable_character(arg.as_str().unwrap())) {
                errors.push(
                    "recreator_invocation.argv holds a control or unprintable character".into(),
                );
            }
        }
        _ => errors.push("recreator_invocation.argv is not a list of strings".into()),
    }
    errors
}

fn quoted_argument(argument: &str) -> String {
    if argument.is_ascii() {
        if argument.is_empty() {
            return "''".into();
        }
        if argument.bytes().all(|b| b.is_ascii_alphanumeric() || b"_@%+=:,./-".contains(&b)) {
            return argument.into();
        }
        return format!("'{}'", argument.replace('\'', "'\"'\"'"));
    }
    let mut word = String::from("$'");
    for c in argument.chars() {
        if c == '\\' || c == '\'' {
            word.push('\\');
            word.push(c);
        } else if c.is_ascii() {
            word.push(c);
        } else {
            use std::fmt::Write as _;
            let mut buffer = [0; 4];
            for byte in c.encode_utf8(&mut buffer).as_bytes() {
                write!(word, "\\x{byte:02x}").expect("String writes cannot fail");
            }
        }
    }
    word.push('\'');
    word
}

pub fn quoted_arguments(argv: &[String]) -> String {
    if argv.is_empty() {
        return "(no arguments)".into();
    }
    let quoted = argv.iter().map(|arg| quoted_argument(arg)).collect::<Vec<_>>().join(" ");
    let quoted = if quoted == "not-recorded" { "'not-recorded'".into() } else { quoted };
    if quoted.len() > 4096 {
        format!(
            "(not quoted here: {} characters when quoted, more than 4096; read recreator_invocation.argv in {RECEIPT_NAME})",
            quoted.len()
        )
    } else {
        quoted
    }
}

fn valid_stage_root(stage: &str, mint: bool) -> bool {
    let parts = stage.split('/').collect::<Vec<_>>();
    let host = |s: &str| {
        !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
    };
    if parts.len() == 3 && parts[0] == "build" && host(parts[1]) {
        return parts[2]
            .strip_prefix("stage")
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()));
    }
    mint && parts.len() == 4
        && parts[0] == "build"
        && parts[3] == "stage2"
        && host(parts[2])
        && parts[1].strip_prefix("pack-mint-").is_some_and(|s| {
            !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b"_.+-".contains(&b))
        })
}

fn recorded_files(receipt: &Value) -> Result<Vec<(String, Value, String)>> {
    let rows = receipt["tools"]
        .as_array()
        .filter(|rows| !rows.is_empty())
        .ok_or_else(|| Refusal("tools is not a non-empty list".into()))?;
    let mut names = BTreeSet::new();
    let mut files = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        let name = row["name"]
            .as_str()
            .filter(|name| !name.is_empty())
            .ok_or_else(|| Refusal(format!("tools[{index}] is not a named tool row")))?;
        if !names.insert(name) {
            return Err(Refusal(format!("tools names {name} twice")));
        }
        let where_ = format!("tools[{name}].");
        let sha = digest(row, "sha256", &where_)?;
        if row["status"] != "bound" || row["producer_sha256"].as_str() != Some(&sha) {
            return Err(Refusal(format!(
                "{where_}status is {} with producer_sha256 {}: not a tool bound to its producer",
                repr(&row["status"]),
                repr(&row["producer_sha256"])
            )));
        }
        files.push((format!("tool {name}"), row["path"].clone(), sha));
    }
    object(receipt, "compiler", "")?;
    let compiler = &receipt["compiler"];
    files.push((
        "the compiler".into(),
        compiler["path"].clone(),
        digest(compiler, "compiler_sha256", "compiler.")?,
    ));
    files.push((
        "the compiler's rustc name".into(),
        compiler["compatibility_alias"].clone(),
        digest(compiler, "compatibility_alias_sha256", "compiler.")?,
    ));
    for (section, what) in
        [("rustdoc_alias", "the rustdoc name"), ("proc_macro_helper", "the proc-macro helper")]
    {
        object(receipt, section, "")?;
        files.push((
            what.into(),
            receipt[section]["path"].clone(),
            digest(&receipt[section], "sha256", &format!("{section}."))?,
        ));
    }
    native_tools::recorded(receipt, names, files)
}

fn relative_file<'a>(stage: &str, what: &str, recorded: &'a Value) -> Result<&'a str> {
    let prefix = format!("{stage}/");
    let tail = recorded.as_str().and_then(|s| s.strip_prefix(&prefix)).ok_or_else(|| {
        Refusal(format!(
            "the path of {what} is not under the receipt's stage_root {stage}: {}",
            repr(recorded)
        ))
    })?;
    if tail.is_empty()
        || tail.contains('\\')
        || unrecordable_character(tail)
        || tail.split('/').any(|part| matches!(part, "" | "." | ".."))
    {
        return Err(Refusal(format!(
            "the path of {what} is not a plain relative path: {}",
            repr(recorded)
        )));
    }
    Ok(tail)
}

pub(crate) fn validate(
    toolchain: &Path,
    commit: &str,
    receipt: &Value,
) -> Result<(Vec<String>, usize)> {
    if receipt["schema"] != RECEIPT_SCHEMA {
        return Err(Refusal(format!(
            "schema is {}, not {RECEIPT_SCHEMA}",
            repr(&receipt["schema"])
        )));
    }
    let status = receipt["status"].as_str().unwrap_or_default();
    if status == "rejected" {
        let first = receipt["errors"]
            .as_array()
            .and_then(|v| v.first())
            .and_then(Value::as_str)
            .map(|s| format!(": {s}"))
            .unwrap_or_default();
        let first = first.chars().take(200).collect::<String>();
        return Err(Refusal(format!(
            "its own writer rejected this stage (status rejected{first}); a rejected receipt is not recorded as provenance"
        )));
    }
    if !seed_host::ACCEPTED_STATUSES.contains(&status) {
        return Err(Refusal(format!(
            "status is {}, not one of candidate-ready, internal-release-ready, release-ready, unpinned-root-seed-ready",
            repr(&receipt["status"])
        )));
    }
    if receipt["tool_binding_status"] != "ready" {
        return Err(Refusal(format!(
            "status is {status} while tool_binding_status is {}",
            repr(&receipt["tool_binding_status"])
        )));
    }
    if !receipt["errors"].is_empty_array() {
        return Err(Refusal(format!("status is {status} while errors is not the empty list")));
    }
    if receipt["path_scope"] != "repository-root-relative" {
        return Err(Refusal("path_scope is not repository-root-relative".into()));
    }
    let mint = receipt["writer"] == "scripts/mint_and_prove_seed.sh";
    let stage =
        receipt["stage_root"].as_str().filter(|s| valid_stage_root(s, mint)).ok_or_else(|| {
            Refusal(format!(
                "stage_root is not build/<host>/stage<N>: {}",
                repr(&receipt["stage_root"])
            ))
        })?;
    object(receipt, "bootstrap_lineage", "")?;
    let lineage = &receipt["bootstrap_lineage"];
    if lineage["schema"] != "trust.bootstrap-lineage.v1" {
        return Err(Refusal("bootstrap_lineage.schema is not trust.bootstrap-lineage.v1".into()));
    }
    let mode = lineage["mode"].as_str().unwrap_or_default();
    let (wanted_status, wanted_trust) = match mode {
        "seed" => ("trust_from_trust", true),
        "atpkg" => ("local_atpkg", true),
        "genesis" => ("local_genesis", false),
        _ => {
            return Err(Refusal(format!(
                "bootstrap_lineage.mode is {}, not one of seed, atpkg, genesis",
                repr(&lineage["mode"])
            )));
        }
    };
    if lineage["trust_from_trust"].as_bool() != Some(wanted_trust)
        || lineage["status"] != wanted_status
    {
        return Err(Refusal(format!(
            "bootstrap_lineage says mode {mode} with status {} and trust_from_trust {}; a {mode} lineage is {wanted_status} with trust_from_trust {}",
            repr(&lineage["status"]),
            repr(&lineage["trust_from_trust"]),
            if wanted_trust { "True" } else { "False" }
        )));
    }
    if !lineage["errors"].is_empty_array() {
        return Err(Refusal("bootstrap_lineage.errors is not the empty list".into()));
    }
    if receipt["trust_from_trust"] != lineage["trust_from_trust"] {
        return Err(Refusal(
            "trust_from_trust disagrees with bootstrap_lineage.trust_from_trust".into(),
        ));
    }
    let materialization = if mode == "seed" {
        let value = &lineage["validated_seed"]["materialization_status"];
        match value.as_str() {
            Some("fresh-from-validated-archives" | "preexisting-unproven") => value.clone(),
            _ => {
                return Err(Refusal(format!(
                    "bootstrap_lineage.validated_seed.materialization_status is {}, not one of fresh-from-validated-archives, preexisting-unproven",
                    repr(value)
                )));
            }
        }
    } else if !lineage["validated_seed"].is_null() {
        return Err(Refusal(format!("a {mode} bootstrap_lineage carries a validated_seed")));
    } else {
        Value::String("not-applicable".into())
    };
    if ["internal-release-ready", "release-ready"].contains(&status)
        && !release_status_holds(&lineage["mode"], &lineage["trust_from_trust"], &materialization)
    {
        return Err(Refusal(format!(
            "status is {status}, which needs a freshly materialized Trust seed, while its lineage says mode {mode}, trust_from_trust {wanted_trust}, seed materialization {}",
            materialization.as_str().unwrap()
        )));
    }
    let seed_admission = seed_host::admission_lines(receipt, mode, status, &materialization)?;
    if !is_hex(&Value::String(commit.into()), &[40, 64]) {
        return Err(Refusal(format!(
            "the commit this tree's compiler reports is not a full object id: {}",
            repr(&Value::String(commit.into()))
        )));
    }
    object(receipt, "compiler", "")?;
    if receipt["compiler"]["source_commit"].as_str() != Some(commit) {
        return Err(Refusal(format!(
            "it names source commit {}; this tree's compiler reports {commit}",
            repr(&receipt["compiler"]["source_commit"])
        )));
    }
    let files = recorded_files(receipt)?;
    for (what, recorded, sha) in &files {
        let path = toolchain.join(relative_file(stage, what, recorded)?);
        let actual = files::hash_file(&path).map_err(|error| {
            if std::fs::metadata(&path).is_ok_and(|m| !m.is_file()) {
                Refusal(format!(
                    "{what} ({}) is not a regular file in {}",
                    recorded.as_str().unwrap(),
                    toolchain.display()
                ))
            } else {
                Refusal(format!(
                    "{what} ({}) cannot be read in {}: {}",
                    recorded.as_str().unwrap(),
                    toolchain.display(),
                    strerror(&error.0)
                ))
            }
        })?;
        if actual != *sha {
            return Err(Refusal(format!(
                "it records sha256 {sha} for {what} ({}); the file in {} has {actual}",
                recorded.as_str().unwrap(),
                toolchain.display()
            )));
        }
    }
    let argv = if receipt.get("recreator_invocation").is_some() {
        let invocation = &receipt["recreator_invocation"];
        let errors = invocation_errors(invocation);
        if !errors.is_empty() {
            return Err(Refusal(errors.join("; ")));
        }
        let argv = invocation["argv"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        quoted_arguments(&argv)
    } else {
        "not-recorded".into()
    };
    let mut lines = vec![
        format!("stage_receipt={RECEIPT_NAME}"),
        format!("stage_receipt_schema={RECEIPT_SCHEMA}"),
        format!("stage_receipt_status={status}"),
        format!("stage_receipt_lineage_mode={mode}"),
        format!("stage_receipt_trust_from_trust={wanted_trust}"),
        format!("stage_receipt_seed_materialization={}", materialization.as_str().unwrap()),
    ];
    lines.extend(seed_admission);
    lines.push(format!("stage_receipt_files_verified={}", files.len()));
    lines.extend(llvm::lines(receipt)?);
    lines.push(format!("stage_receipt_recreator_argv={argv}"));
    if mint {
        lines.push("stage_receipt_writer=scripts/mint_and_prove_seed.sh".into());
    }
    Ok((lines, files.len()))
}

/// Python's `error.strerror or error` for why `files::hash_file` could not read a file:
/// an OS error's own words, without the ` (os error N)` Rust's `io::Error` adds to them.
/// Any other reason is unchanged.
fn strerror(reason: &str) -> &str {
    reason
        .strip_suffix(')')
        .and_then(|rest| rest.rsplit_once(" (os error "))
        .filter(|(words, code)| !words.is_empty() && code.parse::<i32>().is_ok())
        .map_or(reason, |(words, _)| words)
}

// Declared last so the line numbers above, which the escape-audit rows of
// scripts/gates/land-escape-audits.toml cite, move as little as possible.
mod native_tools;
mod seed_host;

#[cfg(test)]
mod tests {
    use super::strerror;
    use crate::Refusal;

    #[cfg(unix)]
    #[test]
    fn a_read_failure_is_worded_as_python_words_it() {
        // Python's OSError.strerror for each, on the same C library.
        for (code, python) in [
            (libc::ENOENT, "No such file or directory"),
            (libc::EACCES, "Permission denied"),
            (libc::ELOOP, "Too many levels of symbolic links"),
        ] {
            // How files::hash_file's `?` turns an io::Error into a refusal.
            let refusal = Refusal::from(std::io::Error::from_raw_os_error(code));
            assert_ne!(refusal.0, python, "Rust adds the code to the OS's words");
            assert_eq!(strerror(&refusal.0), python);
        }
    }

    #[test]
    fn a_reason_that_is_not_an_os_error_is_kept() {
        for reason in [
            "recorded stage file changed before opening",
            "recorded stage file grew while hashing",
            "(os error 2)",
            "words (os error two)",
            "words (os error 2) and more",
        ] {
            assert_eq!(strerror(reason), reason);
        }
    }
}
