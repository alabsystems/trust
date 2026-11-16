// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Native source and cache guards remain below Git and TLS transport. An
//! optional dependency still counts when any consumer enables it. A gix edge
//! from provenance formerly reached curl/OpenSSL and returned through the native
//! OpenSSL source cache, closing Targo's package graph. The committed reader now
//! lives in a separate higher crate used by Bootstrap and native hosts, while
//! the OpenSSL cache uses the libc-only ACL foundation.
//!
//! The dependency set is therefore closed. The admitted path crates are
//! trust-sha2 (no dependencies) and trust-fs-acl (libc only). To add a package, confirm that the
//! stage0 seed targo still resolves targo's workspace:
//! `targo metadata --frozen --format-version 1 --manifest-path src/tools/targo/Cargo.toml`.
//! Then add the package to `ADMITTED`.

const MANIFEST: &str = include_str!("../Cargo.toml");
const SHA2_MANIFEST: &str = include_str!("../../trust-sha2/Cargo.toml");
const ACL_MANIFEST: &str = include_str!("../../trust-fs-acl/Cargo.toml");

/// The packages this crate may depend on. The registry crates' own dependency
/// trees stay out of targo's crates; trust-sha2 is checked to have none.
const ADMITTED: [&str; 5] = ["libc", "serde", "serde_json", "trust-sha2", "trust-fs-acl"];

/// Strips a `#` comment that is not inside a string.
fn strip_comment(line: &str) -> &str {
    let (mut basic, mut literal, mut escaped) = (false, false, false);
    for (at, c) in line.char_indices() {
        match c {
            _ if escaped => escaped = false,
            '\\' if basic => escaped = true,
            '"' if !literal => basic = !basic,
            '\'' if !basic => literal = !literal,
            '#' if !basic && !literal => return &line[..at],
            _ => {}
        }
    }
    line
}

/// Splits on `separator` outside strings, brackets and braces.
fn split_top(text: &str, separator: char) -> Vec<&str> {
    let (mut parts, mut start, mut depth) = (Vec::new(), 0, 0i32);
    let (mut basic, mut literal, mut escaped) = (false, false, false);
    for (at, c) in text.char_indices() {
        match c {
            _ if escaped => escaped = false,
            '\\' if basic => escaped = true,
            '"' if !literal => basic = !basic,
            '\'' if !basic => literal = !literal,
            '[' | '{' if !basic && !literal => depth += 1,
            ']' | '}' if !basic && !literal => depth -= 1,
            _ if c == separator && depth == 0 && !basic && !literal => {
                parts.push(&text[start..at]);
                start = at + c.len_utf8();
            }
            _ => {}
        }
    }
    parts.push(&text[start..]);
    parts
}

/// Bracket depth a logical line still leaves open, outside strings.
fn open_depth(text: &str) -> i32 {
    let (mut depth, mut basic, mut literal, mut escaped) = (0, false, false, false);
    for c in text.chars() {
        match c {
            _ if escaped => escaped = false,
            '\\' if basic => escaped = true,
            '"' if !literal => basic = !basic,
            '\'' if !basic => literal = !literal,
            '[' | '{' if !basic && !literal => depth += 1,
            ']' | '}' if !basic && !literal => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// A bare, basic-quoted or literal-quoted key or string, without its quotes.
fn unquote(text: &str) -> String {
    let text = text.trim();
    for quote in ['"', '\''] {
        if text.len() >= 2 && text.starts_with(quote) && text.ends_with(quote) {
            return text[1..text.len() - 1].to_string();
        }
    }
    text.to_string()
}

fn is_dependency_kind(segment: &str) -> bool {
    matches!(segment, "dependencies" | "build-dependencies" | "build_dependencies")
}

fn is_dev_kind(segment: &str) -> bool {
    matches!(segment, "dev-dependencies" | "dev_dependencies")
}

/// Every package a non-dev dependency table names; for a `package = …` rename,
/// the package rather than the key. Dev-dependencies are left out because Cargo
/// admits dev-dependency cycles. Any dependency declaration in a shape this
/// reader does not know panics instead of being skipped.
fn dependency_packages(manifest: &str) -> Vec<String> {
    let unknown = |what: &str| -> ! { panic!("unrecognized dependency declaration: {what}") };
    // Join the physical lines of a multi-line array into one logical line.
    let mut lines = Vec::new();
    let mut pending = String::new();
    for raw in manifest.lines() {
        assert!(
            !raw.contains("\"\"\"") && !raw.contains("'''"),
            "multi-line strings are not read: {raw}"
        );
        pending.push_str(strip_comment(raw));
        pending.push(' ');
        if open_depth(&pending) <= 0 {
            lines.push(std::mem::take(&mut pending));
        }
    }
    assert!(pending.trim().is_empty(), "unterminated array or inline table");

    // Section: None outside dependency tables; Some(None) in a dependency
    // table; Some(Some(name)) in a dotted `[dependencies.<name>]` table.
    let mut section: Option<Option<String>> = None;
    let mut packages = Vec::new();
    for line in lines.iter().map(|l| l.trim()).filter(|l| !l.is_empty()) {
        if line.starts_with('[') {
            section = None;
            if line.starts_with("[[") {
                if line.contains("dependencies") {
                    unknown(line);
                }
                continue;
            }
            let body = line
                .strip_prefix('[')
                .and_then(|l| l.strip_suffix(']'))
                .unwrap_or_else(|| unknown(line));
            let segments: Vec<String> = split_top(body, '.').into_iter().map(unquote).collect();
            let at = match segments.first().map(String::as_str) {
                Some("target") if segments.len() >= 3 => 2,
                _ => 0,
            };
            match (segments.get(at).map(String::as_str), segments.len() - at) {
                (Some(kind), 1) if is_dependency_kind(kind) => section = Some(None),
                (Some(kind), 2) if is_dependency_kind(kind) => {
                    packages.push(segments[at + 1].clone());
                    section = Some(Some(segments[at + 1].clone()));
                }
                (Some(kind), 1 | 2) if is_dev_kind(kind) => {}
                _ if segments.iter().any(|s| s.contains("dependencies")) => unknown(line),
                _ => {}
            }
            continue;
        }
        let (key, value) = line.split_once('=').unwrap_or_else(|| unknown(line));
        let key: Vec<String> = split_top(key, '.').into_iter().map(unquote).collect();
        match &section {
            None => {
                if key.iter().any(|k| k.contains("dependencies")) {
                    unknown(line);
                }
            }
            Some(Some(name)) => {
                if key == ["package"] {
                    let last = packages.iter().rposition(|p| p == name).unwrap();
                    packages[last] = unquote(value);
                }
            }
            Some(None) => {
                let value = value.trim();
                let renamed = if key.len() == 2 && key[1] == "package" {
                    Some(unquote(value))
                } else if key.len() == 1 && value.starts_with('{') && value.ends_with('}') {
                    split_top(&value[1..value.len() - 1], ',')
                        .into_iter()
                        .filter_map(|entry| entry.split_once('='))
                        .find(|(k, _)| unquote(k) == "package")
                        .map(|(_, v)| unquote(v))
                } else if key.len() == 2
                    || (key.len() == 1 && (value.starts_with('"') || value.starts_with('\'')))
                {
                    // A version string, or a dotted key other than `package`.
                    None
                } else {
                    unknown(line)
                };
                if let Some(at) =
                    packages.iter().rposition(|p| *p == key[0]).filter(|_| key.len() == 2)
                {
                    // A later dotted key of a dependency already named.
                    if let Some(package) = renamed {
                        packages[at] = package;
                    }
                } else {
                    packages.push(renamed.unwrap_or_else(|| key[0].clone()));
                }
            }
        }
    }
    packages
}

fn unadmitted(manifest: &str) -> Vec<String> {
    dependency_packages(manifest).into_iter().filter(|p| !ADMITTED.contains(&p.as_str())).collect()
}

#[test]
fn every_dependency_is_admitted_so_none_reaches_targos_crates() {
    let unadmitted = unadmitted(MANIFEST);
    assert!(
        unadmitted.is_empty(),
        "unadmitted dependencies {unadmitted:?}: confirm targo's workspace still resolves \
         without a cycle (see this file's header), then admit them"
    );
}

#[test]
fn the_admitted_path_crates_keep_their_closed_dependencies() {
    assert_eq!(dependency_packages(SHA2_MANIFEST), Vec::<String>::new());
    assert_eq!(dependency_packages(ACL_MANIFEST), ["libc"]);
}

#[test]
fn the_reader_refuses_the_manifest_that_made_targos_workspace_cyclic() {
    // crates/trust-resource-provenance/Cargo.toml at e6613f79644d, verbatim.
    let cyclic = r#"[workspace]

[package]
name = "trust-resource-provenance"
version = "0.13.0"
edition = "2024"
license = "Apache-2.0 OR MIT"
publish = false
description = "Read-only native provenance for retained resource custodians"

[features]
committed-git = ["dep:gix"]

[dependencies]
gix = { version = "=0.85.0", optional = true, default-features = false, features = ["sha1"] }
libc = "0.2"
serde = { version = "1", default-features = false, features = ["std"] }
serde_json = "1"
sha2 = { package = "trust-sha2", path = "../trust-sha2", default-features = false }

[dev-dependencies]
tempfile = "3"
"#;
    assert_eq!(dependency_packages(cyclic), ["gix", "libc", "serde", "serde_json", "trust-sha2"]);
    assert_eq!(unadmitted(cyclic), ["gix"]);
}

#[test]
fn the_reader_resolves_every_known_shape_to_its_package() {
    let shapes = r#"
[package]
name = "x" # a [dependencies] comment
include = [
  "src/**",
]

[dependencies]
a = { package = 'gix', version = "1" }
b = { path = "../package-x", package = "curl" }
c = { git = "https://example.invalid/r#x", package = "git2" }
d.workspace = true
e.version = "1"
e.package = "openssl-sys"
"quoted" = "1"
'literal' = { version = "1", features = [
  "std",
] }

[target.'cfg(all(unix, target_os = "macos"))'.build-dependencies]
f = "1"

[target."cfg(unix)" . dependencies . g]
version = "1"
package = 'reqwest'

[dev-dependencies]
tempfile = "3"

[target.'cfg(unix)'.dev-dependencies.h]
version = "1"
"#;
    assert_eq!(
        dependency_packages(shapes),
        ["gix", "curl", "git2", "d", "openssl-sys", "quoted", "literal", "f", "reqwest"]
    );
}

#[test]
fn the_reader_refuses_dependency_shapes_it_does_not_know() {
    for manifest in [
        "dependencies.gix = \"1\"\n[package]\nname = \"x\"\n",
        "[target.'cfg(unix)']\ndependencies.gix = \"1\"\n",
        "[target.'cfg(unix)']\ndependencies = { gix = \"1\" }\n",
        "[dependencies]\ngix\n",
        "[dependencies]\ngix = [\"1\"]\n",
        "[dependencies]\ngix = { version = \"1\"\n",
        "[package]\ndescription = \"\"\"\nx\n\"\"\"\n",
    ] {
        let read = std::panic::catch_unwind(|| dependency_packages(manifest));
        assert!(read.is_err(), "read {manifest:?} as {:?}", read.unwrap());
    }
}
