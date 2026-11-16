//! Native form of the pinned AY gate's lexical AND decoded TOML boundary.
//! Matching this posture is not a successful verify/whole-build verdict.
use crate::util::CargoResult;
use anyhow::ensure;
use regex::Regex;
use toml::Value;

const POLICY: [&str; 6] = [
    "-Ztrust-verify=on",
    "-Ztrust-policy=certify",
    "-Ztrust-verify-level=2",
    "-Ztrust-verify-profile=unix_hardened",
    "-Ztrust-verify-include-dependencies=yes",
    "-Ztrust-ir-lower=strict",
];
fn policy(value: &Value) -> bool {
    value.as_array().is_some_and(|values| {
        values.len() == POLICY.len()
            && values
                .iter()
                .zip(POLICY)
                .all(|(value, expected)| value.as_str() == Some(expected))
    })
}
fn decoded_flags(
    table: &toml::map::Map<String, Value>,
    path: &mut Vec<String>,
    cpu: &Regex,
) -> CargoResult<()> {
    for (name, value) in table {
        if matches!(
            name.to_ascii_lowercase().as_str(),
            "rustflags" | "rustdocflags"
        ) {
            let canonical =
                path.as_slice() == ["host"] || path.as_slice() == ["target", "cfg(all())"];
            let tuning = path.len() == 2
                && path[0] == "target"
                && name == "rustflags"
                && value.as_array().is_some_and(|values| {
                    values.len() == 2
                        && values[0].as_str() == Some("-C")
                        && values[1].as_str().is_some_and(|value| cpu.is_match(value))
                });
            ensure!(
                matches!(name.as_str(), "rustflags" | "rustdocflags")
                    && ((canonical && policy(value)) || tuning),
                "decoded AY Cargo flag {:?} is outside complete required policy",
                path.iter()
                    .map(String::as_str)
                    .chain([name.as_str()])
                    .collect::<Vec<_>>()
            );
        }
        if let Some(table) = value.as_table() {
            path.push(name.clone());
            decoded_flags(table, path, cpu)?;
            path.pop();
        }
    }
    Ok(())
}
pub(super) fn validate(config: &str, toolchain: &str) -> CargoResult<()> {
    ensure!(
        !config.contains('\r') && !toolchain.contains('\r'),
        "AY canonical policy requires literal LF lines"
    );
    let pin: Value = toml::from_str(toolchain)?;
    ensure!(
        toolchain
            .lines()
            .filter(|line| *line == "[toolchain]")
            .count()
            == 1
            && toolchain
                .lines()
                .filter(|line| *line == "channel = \"trust\"")
                .count()
                == 1
            && toolchain
                .lines()
                .filter(|line| line.starts_with("channel"))
                .count()
                == 1
            && pin
                .get("toolchain")
                .and_then(|value| value.get("channel"))
                .and_then(Value::as_str)
                == Some("trust"),
        "AY default toolchain must be exactly canonical Trust channel"
    );
    let document: Value = toml::from_str(config)?;
    let table = document
        .as_table()
        .ok_or_else(|| anyhow::anyhow!("AY Cargo config is not a table"))?;
    ensure!(
        !table.contains_key("include")
            && !table
                .get("unstable")
                .and_then(Value::as_table)
                .is_some_and(|table| table.contains_key("config-include")),
        "AY Cargo includes are outside original default policy boundary"
    );
    let overrides = Regex::new(r"(?i)rust(?:doc)?flags|trust[-_](?:verify|policy|ir[-_]lower)")?;
    if let Some(environment) = table.get("env") {
        let environment = environment
            .as_table()
            .ok_or_else(|| anyhow::anyhow!("AY Cargo env must be a table"))?;
        for (name, entry) in environment {
            let value = match entry {
                Value::String(value) => value.as_str(),
                Value::Table(entry) => {
                    ensure!(
                        entry
                            .keys()
                            .all(|name| matches!(name.as_str(), "value" | "force" | "relative"))
                            && ["force", "relative"]
                                .into_iter()
                                .all(|name| entry.get(name).is_none_or(|value| value.is_bool())),
                        "unsupported AY Cargo env shape for {name}"
                    );
                    entry.get("value").and_then(Value::as_str).ok_or_else(|| {
                        anyhow::anyhow!("AY Cargo env {name} lacks a string value")
                    })?
                }
                _ => anyhow::bail!("unsupported AY Cargo env shape for {name}"),
            };
            ensure!(
                !overrides.is_match(name) && !overrides.is_match(value),
                "decoded AY Cargo env {name} carries a forbidden compiler-policy override"
            );
        }
    }
    let cpu = Regex::new(r"^target-cpu=[a-zA-Z0-9_.+-]+$")?;
    decoded_flags(table, &mut Vec::new(), &cpu)?;
    let flags = Regex::new(r"^(rustflags|rustdocflags) = (.*)$")?;
    let flag_name = Regex::new(r"(?i)rust(?:doc)?flags")?;
    let verifier = Regex::new(r"trust[-_]verify|trust[-_]policy|trust[-_]ir[-_]lower")?;
    let tuning = Regex::new(r#"^rustflags = \["-C", "target-cpu=[a-zA-Z0-9_.+-]+"\]$"#)?;
    let canonical = format!(
        "[{}]",
        POLICY.map(|value| format!("\"{value}\"")).join(", ")
    );
    let mut section = "";
    let mut root_gate = 0;
    let mut host_gate = 0;
    let mut host_config = 0;
    let mut sections = std::collections::BTreeMap::<&str, usize>::new();
    let mut lanes = std::collections::BTreeMap::<(&str, &str), usize>::new();
    for line in config
        .lines()
        .filter(|line| !line.trim_start().starts_with('#'))
    {
        if line.starts_with('[') {
            section = line;
            *sections.entry(section).or_default() += 1;
            continue;
        }
        if line == "target-applies-to-host = true" {
            if section.is_empty() {
                root_gate += 1
            } else if section == "[unstable]" {
                host_gate += 1
            }
        }
        if line == "host-config = true" && section == "[unstable]" {
            host_config += 1
        }
        if let Some(capture) = flags.captures(line) {
            let name = capture.get(1).unwrap().as_str();
            let value = capture.get(2).unwrap().as_str();
            if matches!(section, "[host]" | "[target.'cfg(all())']") {
                *lanes.entry((section, name)).or_default() += 1;
                ensure!(
                    value == canonical,
                    "AY canonical host/common target requires complete verifier argv"
                );
            } else {
                ensure!(
                    section.starts_with("[target.") && name == "rustflags" && tuning.is_match(line),
                    "unlicensed AY Cargo flag override outside verified lanes"
                );
            }
            continue;
        }
        ensure!(
            !flag_name.is_match(line),
            "noncanonical AY Cargo flag syntax/environment override"
        );
        ensure!(
            !verifier.is_match(line),
            "AY verifier setting outside canonical flag arrays"
        );
    }
    ensure!(
        root_gate == 1 && host_gate == 1 && host_config == 1,
        "AY certify default requires enabled host config/native inheritance"
    );
    ensure!(
        sections.get("[host]") == Some(&1) && lanes.get(&("[host]", "rustflags")) == Some(&1),
        "AY certify default requires verified host rustflags"
    );
    ensure!(
        sections.get("[target.'cfg(all())']") == Some(&1)
            && lanes.get(&("[target.'cfg(all())']", "rustflags")) == Some(&1)
            && lanes.get(&("[target.'cfg(all())']", "rustdocflags")) == Some(&1),
        "AY certify default requires verified compiler/rustdoc flags for every target"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn actual() -> (String, String) {
        let root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../../first-party/ay");
        (
            std::fs::read_to_string(root.join(".cargo/config.toml")).unwrap(),
            std::fs::read_to_string(root.join("rust-toolchain.toml")).unwrap(),
        )
    }
    #[test]
    fn actual_pinned_ay_policy_and_decoded_override_controls() {
        let (config, pin) = actual();
        validate(&config, &pin).unwrap();
        let environment = |entry: &str| config.replacen("[env]\n", &format!("[env]\n{entry}\n"), 1);
        for mutation in [
            config.replace("-Ztrust-verify-level=2", "-Ztrust-verify-level=1"),
            config.replace("-Ztrust-ir-lower=strict", "-Ztrust-ir-lower=off"),
            format!("include = ['other.toml']\n{config}"),
            environment("\"RUST\\u0046LAGS\" = 'plain'"),
            environment("INNOCENT = { value = \"\\u0074rust-policy=advisory\", force = true }"),
            environment("INNOCENT = { value = 'plain', force = 1 }"),
            config.replace("rustflags = [", "RUSTFLAGS = ["),
        ] {
            toml::from_str::<Value>(&mutation).expect("negative fixture must remain valid TOML");
            assert!(
                validate(&mutation, &pin).is_err(),
                "mutated pinned policy accepted"
            );
        }
        assert!(
            validate(
                &config,
                &pin.replace("channel = \"trust\"", "channel = \"stable\"")
            )
            .is_err()
        );
    }
    #[test]
    fn lexical_guard_still_rejects_equivalent_noncanonical_arrays_and_partial_lane() {
        let (config, pin) = actual();
        let crlf = config.replace('\n', "\r\n");
        toml::from_str::<Value>(&crlf).unwrap();
        assert!(validate(&crlf, &pin).is_err());
        assert!(
            validate(
                &config.replace(", \"-Ztrust-policy", ",\"-Ztrust-policy"),
                &pin
            )
            .is_err()
        );
        assert!(
            validate(
                &config.replace("host-config = true", "host-config = false"),
                &pin
            )
            .is_err()
        );
        assert!(validate(&config.replace("rustdocflags = [", "ignored = ["), &pin).is_err());
    }
}
