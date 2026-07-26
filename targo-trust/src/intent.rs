// Intent-input resolution for `targo trust` (Slice 2).
//
// Intent is a first-class compilation input: a markdown design document or a
// captured chat conversation describing what the author *meant*, fed alongside
// the source so AI-in-the-loop repair aims at the intended program rather than
// only the literal one. On the authority ladder it sits below a formal contract
// but above code-abduced guesses. It is an untrusted guide — it shapes which
// repair to attempt, never whether the proof holds.
//
// Resolution precedence (highest first):
//   1. an explicit `--intent <path>` flag,
//   2. `[trust] intent = "<path>"` in the project manifest,
//   3. `[package.metadata.trust] intent = "<path>"`, the retired spelling,
//      readable for one more release.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::path::Component;
use std::path::{Path, PathBuf};

use crate::config::{ConfiguredIntent, TRUST_TABLE};
use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};

/// Where a resolved intent document came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IntentSource {
    /// Supplied directly via `--intent <path>`.
    Flag,
    /// Declared in the `[trust]` table of the named manifest or config file.
    TrustTable(PathBuf),
    /// Declared in `[package.metadata.trust] intent` in the named manifest.
    Metadata(PathBuf),
}

impl IntentSource {
    pub(crate) fn label(&self) -> String {
        match self {
            IntentSource::Flag => "--intent flag".to_string(),
            IntentSource::TrustTable(path) => {
                format!("[{TRUST_TABLE}] intent in {}", path.display())
            }
            IntentSource::Metadata(path) => {
                format!("[package.metadata.trust] intent in {}", path.display())
            }
        }
    }
}

/// The one sentence that names where an intent declaration now belongs.
pub(crate) fn legacy_metadata_intent_deprecation_notice() -> String {
    format!(
        "`[package.metadata.trust] intent` is deprecated and is read for one more release; \
         move it to `intent` in the `[{TRUST_TABLE}]` table"
    )
}

/// A loaded intent document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedIntent {
    /// The intent document path that was read.
    pub(crate) path: PathBuf,
    /// Full document text.
    pub(crate) text: String,
    /// How the path was discovered.
    pub(crate) source: IntentSource,
}

impl ResolvedIntent {
    /// A bounded excerpt suitable for embedding in an AI repair prompt. Keeps
    /// the prompt focused: the first `max_chars` characters, truncated on a
    /// line boundary where possible.
    pub(crate) fn excerpt(&self, max_chars: usize) -> String {
        excerpt(&self.text, max_chars)
    }
}

fn excerpt(text: &str, max_chars: usize) -> String {
    let trimmed = text.trim();
    if trimmed.chars().count() <= max_chars {
        return trimmed.to_string();
    }
    let mut out = String::new();
    for ch in trimmed.chars() {
        if out.chars().count() >= max_chars {
            break;
        }
        out.push(ch);
    }
    // Prefer to cut at the last newline so we don't truncate mid-line.
    if let Some(last_newline) = out.rfind('\n') {
        out.truncate(last_newline);
    }
    out.push_str("\n… [intent truncated]");
    out
}

/// Resolve and load the intent document, if any. Returns `Ok(None)` when no
/// intent is configured. Returns `Err` only when a configured intent path
/// cannot be read (a configured-but-missing intent is a user error, not a
/// silent skip).
pub(crate) fn resolve_intent(
    flag: Option<&str>,
    configured: Option<&ConfiguredIntent>,
    manifest_path: Option<&Path>,
) -> Result<Option<ResolvedIntent>, String> {
    if let Some(flag) = flag {
        let path = PathBuf::from(flag);
        let text = read_intent(&path)?;
        return Ok(Some(ResolvedIntent { path, text, source: IntentSource::Flag }));
    }

    if let Some(configured) = configured {
        let text = read_intent(&configured.path)?;
        return Ok(Some(ResolvedIntent {
            path: configured.path.clone(),
            text,
            source: IntentSource::TrustTable(configured.declared_in.clone()),
        }));
    }

    if let Some(manifest_path) = manifest_path {
        if let Some(relative) = intent_path_from_manifest(manifest_path)? {
            let base = manifest_path.parent().unwrap_or(Path::new("."));
            reject_symlinked_manifest_intent_components(base, &relative)?;
            let path = base.join(relative);
            let text = read_intent(&path)?;
            eprintln!("targo trust: warning: {}", legacy_metadata_intent_deprecation_notice());
            return Ok(Some(ResolvedIntent {
                path,
                text,
                source: IntentSource::Metadata(manifest_path.to_path_buf()),
            }));
        }
    }

    Ok(None)
}

/// Validate a manifest-declared relative path and reject anything that could
/// leave the declaring directory.
///
/// A manifest-controlled path must not use a symlink below the manifest
/// directory to escape that directory or race a different document into an AI
/// repair prompt. An explicit `--intent` remains the user's authority to name a
/// file elsewhere, but it is still subject to the bounded regular-file read.
/// An empty string means "not declared".
pub(crate) fn contained_manifest_relative_path(
    base: &Path,
    raw: &str,
) -> Result<Option<PathBuf>, String> {
    if raw.trim().is_empty() {
        return Ok(None);
    }
    let relative = PathBuf::from(raw.trim());
    if relative.is_absolute()
        || relative.components().any(|component| {
            matches!(component, Component::ParentDir | Component::RootDir | Component::Prefix(_))
        })
    {
        return Err("must be a contained relative path without `..`".to_string());
    }
    reject_symlinked_manifest_intent_components(base, &relative)?;
    Ok(Some(relative))
}

fn read_intent(path: &Path) -> Result<String, String> {
    read_bounded_utf8_file(path, MAX_RELEASE_METADATA_BYTES)
        .map_err(|error| format!("reading intent document {}: {error}", path.display()))
}

/// Extract `package.metadata.trust.intent` from a manifest, if present.
fn intent_path_from_manifest(manifest_path: &Path) -> Result<Option<PathBuf>, String> {
    let text = read_bounded_utf8_file(manifest_path, MAX_RELEASE_METADATA_BYTES)
        .map_err(|error| format!("reading {}: {error}", manifest_path.display()))?;
    intent_path_from_manifest_str(&text)
}

fn intent_path_from_manifest_str(manifest: &str) -> Result<Option<PathBuf>, String> {
    let value: toml::Value =
        manifest.parse().map_err(|error| format!("parsing manifest TOML: {error}"))?;
    let intent = value
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("trust"))
        .and_then(|t| t.get("intent"));
    match intent {
        None => Ok(None),
        Some(toml::Value::String(path)) if !path.trim().is_empty() => {
            let path = PathBuf::from(path.trim());
            if path.is_absolute()
                || path.components().any(|component| {
                    matches!(
                        component,
                        Component::ParentDir | Component::RootDir | Component::Prefix(_)
                    )
                })
            {
                return Err(
                    "[package.metadata.trust] intent must be a contained relative path without `..`"
                        .to_string(),
                );
            }
            Ok(Some(path))
        }
        Some(toml::Value::String(_)) => Ok(None),
        Some(_) => Err("[package.metadata.trust] intent must be a string path".to_string()),
    }
}

/// Walk the declared path one component at a time so a symlink anywhere along
/// it is caught, not just at the leaf. Checking only the final resolved path
/// would let `docs -> /elsewhere` redirect the whole subtree.
fn reject_symlinked_manifest_intent_components(base: &Path, relative: &Path) -> Result<(), String> {
    let mut candidate = base.to_path_buf();
    for component in relative.components() {
        match component {
            Component::CurDir => continue,
            Component::Normal(part) => candidate.push(part),
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(format!(
                    "manifest intent path {} is not contained beneath {}",
                    relative.display(),
                    base.display()
                ));
            }
        }
        match fs::symlink_metadata(&candidate) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(format!(
                    "manifest intent path {} contains symlink component {}",
                    relative.display(),
                    candidate.display()
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => break,
            Err(error) => {
                return Err(format!(
                    "inspecting manifest intent path component {}: {error}",
                    candidate.display()
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::*;

    fn temp_dir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("trust-intent-test-{tag}"));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    fn write(path: &Path, contents: &str) {
        let mut file = fs::File::create(path).expect("create file");
        file.write_all(contents.as_bytes()).expect("write file");
    }

    #[test]
    fn manifest_intent_path_is_extracted() {
        let manifest = r#"
            [package]
            name = "demo"
            version = "0.1.0"

            [package.metadata.trust]
            intent = "docs/intent.md"
        "#;
        let path = intent_path_from_manifest_str(manifest).expect("parse");
        assert_eq!(path, Some(PathBuf::from("docs/intent.md")));
    }

    #[test]
    fn manifest_without_intent_returns_none() {
        let manifest = r#"
            [package]
            name = "demo"
            version = "0.1.0"
        "#;
        assert_eq!(intent_path_from_manifest_str(manifest).expect("parse"), None);
    }

    #[test]
    fn manifest_non_string_intent_is_an_error() {
        let manifest = r#"
            [package]
            name = "demo"
            version = "0.1.0"

            [package.metadata.trust]
            intent = 42
        "#;
        assert!(intent_path_from_manifest_str(manifest).is_err());
    }

    #[test]
    fn manifest_intent_rejects_absolute_and_parent_paths() {
        for path in ["../outside.md", "docs/../../outside.md", "/tmp/outside.md"] {
            let manifest = format!(
                "[package]\nname=\"d\"\nversion=\"0.1.0\"\n[package.metadata.trust]\nintent={path:?}\n"
            );
            let error = intent_path_from_manifest_str(&manifest)
                .expect_err("manifest-controlled intent must stay beneath manifest directory");
            assert!(error.contains("contained relative path"), "{error}");
        }
    }

    #[test]
    fn flag_takes_precedence_over_manifest() {
        let dir = temp_dir("precedence");
        let flag_doc = dir.join("flag.md");
        write(&flag_doc, "from the flag");
        let manifest_doc = dir.join("manifest.md");
        write(&manifest_doc, "from the manifest");
        let manifest = dir.join("Cargo.toml");
        write(
            &manifest,
            "[package]\nname=\"d\"\nversion=\"0.1.0\"\n[package.metadata.trust]\nintent=\"manifest.md\"\n",
        );

        let resolved = resolve_intent(flag_doc.to_str(), None, Some(&manifest))
            .expect("resolve")
            .expect("some intent");
        assert_eq!(resolved.text, "from the flag");
        assert_eq!(resolved.source, IntentSource::Flag);
    }

    #[test]
    fn the_trust_table_takes_precedence_over_the_retired_metadata_key() {
        let dir = temp_dir("table-precedence");
        write(&dir.join("table.md"), "from the trust table");
        write(&dir.join("metadata.md"), "from package metadata");
        let manifest = dir.join("Cargo.toml");
        write(
            &manifest,
            "[package]\nname=\"d\"\nversion=\"0.1.0\"\n[package.metadata.trust]\nintent=\"metadata.md\"\n[trust]\nintent=\"table.md\"\n",
        );
        let configured =
            ConfiguredIntent { path: dir.join("table.md"), declared_in: manifest.clone() };

        let resolved = resolve_intent(None, Some(&configured), Some(&manifest))
            .expect("resolve")
            .expect("some intent");
        assert_eq!(resolved.text, "from the trust table");
        assert_eq!(resolved.source, IntentSource::TrustTable(manifest));
    }

    #[test]
    fn manifest_intent_is_resolved_relative_to_manifest_dir() {
        let dir = temp_dir("relative");
        let docs = dir.join("docs");
        fs::create_dir_all(&docs).expect("create docs dir");
        write(&docs.join("intent.md"), "design says saturate");
        let manifest = dir.join("Cargo.toml");
        write(
            &manifest,
            "[package]\nname=\"d\"\nversion=\"0.1.0\"\n[package.metadata.trust]\nintent=\"docs/intent.md\"\n",
        );

        let resolved =
            resolve_intent(None, None, Some(&manifest)).expect("resolve").expect("some intent");
        assert_eq!(resolved.text, "design says saturate");
        assert_eq!(resolved.path, docs.join("intent.md"));
        assert!(matches!(resolved.source, IntentSource::Metadata(_)));
    }

    #[test]
    fn missing_configured_intent_is_an_error_not_a_skip() {
        assert!(resolve_intent(Some("/no/such/intent.md"), None, None).is_err());
    }

    #[test]
    fn oversized_explicit_intent_is_rejected_before_allocation() {
        let dir = temp_dir("oversized");
        let path = dir.join("intent.md");
        let file = fs::File::create(&path).expect("create intent");
        file.set_len(MAX_RELEASE_METADATA_BYTES as u64 + 1).expect("size intent");

        let error =
            resolve_intent(path.to_str(), None, None)
                .expect_err("oversized intent must fail closed");
        assert!(error.contains("safety limit"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn manifest_intent_rejects_symlinked_components() {
        use std::os::unix::fs::symlink;

        let dir = temp_dir("symlink-component");
        let outside = temp_dir("symlink-outside");
        write(&outside.join("intent.md"), "outside instructions");
        symlink(&outside, dir.join("docs")).expect("link manifest intent directory");
        let manifest = dir.join("Cargo.toml");
        write(
            &manifest,
            "[package]\nname=\"d\"\nversion=\"0.1.0\"\n[package.metadata.trust]\nintent=\"docs/intent.md\"\n",
        );

        let error = resolve_intent(None, None, Some(&manifest))
            .expect_err("symlinked manifest intent must fail closed");
        assert!(error.contains("symlink component"), "{error}");
    }

    #[test]
    fn no_intent_configured_returns_none() {
        assert_eq!(resolve_intent(None, None, None).expect("resolve"), None);
    }

    #[test]
    fn excerpt_truncates_long_documents_on_line_boundary() {
        let text = "line one\nline two\nline three\nline four\n";
        let out = excerpt(text, 18);
        assert!(out.contains("line one"));
        assert!(out.contains("intent truncated"));
        assert!(!out.contains("line four"));
    }

    #[test]
    fn excerpt_keeps_short_documents_verbatim() {
        let out = excerpt("  short intent  ", 100);
        assert_eq!(out, "short intent");
    }
}
