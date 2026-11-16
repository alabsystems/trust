//! Trust: attempt-local coverage of planned compiler outputs.
//!
//! Reports are observations, not execution authentication or proof. This module
//! performs no file I/O. Its caller must establish successful execution and all
//! required file/post-execution checks before using a seal for publication.

use std::borrow::Cow;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Deserializer, Serialize};

/// The ordinary fingerprint and the native parent use the SAME planned
/// compiler inventory. Published aliases and Cargo-owned files never cover
/// a compiler artifact slot.
pub(super) fn expected_outputs(
    outputs: &[super::build_runner::OutputFile],
) -> Vec<(PathBuf, Emit)> {
    outputs
        .iter()
        .filter_map(|output| {
            let emit = compiler_emit(&output.flavor)?;
            Some((output.path.clone(), emit))
        })
        .collect()
}

pub(super) fn compiler_emit(flavor: &super::FileFlavor) -> Option<Emit> {
    match flavor {
        super::FileFlavor::Normal | super::FileFlavor::Linkable => Some(Emit::Link),
        super::FileFlavor::Rmeta => Some(Emit::Metadata),
        _ => None,
    }
}

const MAX_OUTPUTS: usize = 4096;
const MAX_PATH_BYTES: usize = 128 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum Emit {
    Link,
    Metadata,
}

impl Emit {
    fn as_str(self) -> &'static str {
        match self {
            Self::Link => "link",
            Self::Metadata => "metadata",
        }
    }
}

pub(super) struct Observer {
    expected: Vec<Expected>,
    cwd: PathBuf,
    rejected: bool,
}

struct Expected {
    path: PathBuf,
    emit: Emit,
    seen: bool,
}

/// Complete report coverage for one observer. It cannot be cloned or decoded
/// from a persisted record; consuming it transfers only the planned inventory.
pub(super) struct Seal {
    outputs: Vec<(PathBuf, Emit)>,
}

impl Seal {
    pub(super) fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = self
            .outputs
            .capacity()
            .checked_mul(std::mem::size_of::<(PathBuf, Emit)>())?;
        for (path, _) in &self.outputs {
            bytes = bytes.checked_add(path.capacity())?;
        }
        Some(bytes)
    }
    pub(super) fn outputs(self) -> Vec<(PathBuf, Emit)> {
        self.outputs
    }
}

impl Observer {
    /// Invalid plans refuse coverage without changing compiler success. Only
    /// compiler-owned outputs belong here; Cargo-owned files are a separate
    /// publication obligation and must never fill compiler coverage slots.
    pub(super) fn new(mut expected: Vec<(PathBuf, Emit)>, cwd: PathBuf) -> Self {
        let valid = !expected.is_empty()
            && expected.len() <= MAX_OUTPUTS
            && bounded_absolute(&cwd)
            && expected.iter().all(|(path, _)| bounded_absolute(path));
        if !valid {
            return Self {
                expected: Vec::new(),
                cwd,
                rejected: true,
            };
        }
        expected.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        let rejected = expected.windows(2).any(|pair| pair[0].0 == pair[1].0);
        Self {
            expected: expected
                .into_iter()
                .map(|(path, emit)| Expected {
                    path,
                    emit,
                    seen: false,
                })
                .collect(),
            cwd,
            rejected,
        }
    }

    /// Observe the original JSON before diagnostic routing or cache replay can
    /// reinterpret it. Rejection is permanent and never fails compilation.
    pub(super) fn observe(&mut self, raw_valid_json: &str) {
        if !self.rejected && self.observe_record(raw_valid_json).is_err() {
            self.rejected = true;
        }
    }

    fn observe_record(&mut self, raw: &str) -> Result<(), ()> {
        #[derive(Deserialize)]
        struct Header<'a> {
            // A missing tag may be an ordinary diagnostic. A present null or
            // non-string tag, like a duplicate tag, is malformed protocol.
            #[serde(rename = "$message_type", borrow, default)]
            message_type: Cow<'a, str>,
            #[serde(default, deserialize_with = "present")]
            artifact: bool,
            #[serde(default, deserialize_with = "present")]
            emit: bool,
        }

        let header: Header<'_> = serde_json::from_str(raw).map_err(|_| ())?;
        if !header.artifact && !header.emit && header.message_type != "artifact" {
            return Ok(());
        }

        #[derive(Deserialize)]
        struct Protocol<'a> {
            #[serde(rename = "$message_type", borrow)]
            message_type: Cow<'a, str>,
            #[serde(borrow)]
            artifact: Cow<'a, str>,
            #[serde(borrow)]
            emit: Cow<'a, str>,
        }

        let protocol: Protocol<'_> = serde_json::from_str(raw).map_err(|_| ())?;
        if protocol.message_type != "artifact"
            || protocol.artifact.is_empty()
            || protocol.artifact.len() > MAX_PATH_BYTES
            || protocol.emit.is_empty()
        {
            return Err(());
        }
        let reported = Path::new(protocol.artifact.as_ref());
        let resolved = if reported.is_absolute() {
            reported.to_path_buf()
        } else {
            self.cwd.join(reported)
        };
        if !bounded_absolute(&resolved) {
            return Err(());
        }

        match self
            .expected
            .binary_search_by(|expected| expected.path.cmp(&resolved))
        {
            Ok(index) => {
                let expected = &mut self.expected[index];
                if protocol.emit != expected.emit.as_str() {
                    return Err(());
                }
                // Exact duplicate reports are idempotent, not extra coverage.
                expected.seen = true;
            }
            Err(_) if matches!(protocol.emit.as_ref(), "link" | "metadata") => {
                // The compiler redirected an output relevant to this policy.
                return Err(());
            }
            // Codegen intermediates and dep-info do not cover the planned
            // link/metadata inventory. Retain no report-selected paths.
            Err(_) => {}
        }
        Ok(())
    }

    pub(super) fn finish(self) -> Option<Seal> {
        if self.rejected || self.expected.is_empty() || self.expected.iter().any(|item| !item.seen)
        {
            return None;
        }
        Some(Seal {
            outputs: self
                .expected
                .into_iter()
                .map(|item| (item.path, item.emit))
                .collect(),
        })
    }
}

fn bounded_absolute(path: &Path) -> bool {
    path.is_absolute() && path.as_os_str().as_encoded_bytes().len() <= MAX_PATH_BYTES
}

fn present<'de, D: Deserializer<'de>>(deserializer: D) -> Result<bool, D::Error> {
    serde::de::IgnoredAny::deserialize(deserializer)?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root() -> PathBuf {
        if cfg!(windows) {
            PathBuf::from(r"C:\output-observation")
        } else {
            PathBuf::from("/output-observation")
        }
    }

    fn notification(emit: &str, artifact: &Path) -> String {
        serde_json::json!({
            "$message_type": "artifact",
            "emit": emit,
            "artifact": artifact,
        })
        .to_string()
    }

    fn metadata_observer() -> Observer {
        Observer::new(vec![(root().join("lib.rmeta"), Emit::Metadata)], root())
    }

    fn observe_metadata(observer: &mut Observer) {
        observer.observe(&notification("metadata", &root().join("lib.rmeta")));
    }

    #[test]
    fn relative_reports_and_exact_duplicates_cover_only_the_planned_inventory() {
        let library = root().join("lib.rlib");
        let metadata = root().join("lib.rmeta");
        let mut observer = Observer::new(
            vec![
                (metadata.clone(), Emit::Metadata),
                (library.clone(), Emit::Link),
            ],
            root(),
        );
        observer.observe(&notification("metadata", Path::new("lib.rmeta")));
        observe_metadata(&mut observer);
        observer.observe(&notification("link", &library));
        observer.observe(&notification("link", &library));
        assert_eq!(
            observer.finish().expect("complete coverage").outputs(),
            vec![(library, Emit::Link), (metadata, Emit::Metadata)]
        );
    }

    #[test]
    fn missing_empty_or_duplicate_inventory_cannot_finish() {
        assert!(metadata_observer().finish().is_none());
        assert!(Observer::new(Vec::new(), root()).finish().is_none());
        for kinds in [
            [Emit::Metadata, Emit::Metadata],
            [Emit::Metadata, Emit::Link],
        ] {
            let mut observer = Observer::new(
                kinds
                    .into_iter()
                    .map(|emit| (root().join("lib.rmeta"), emit))
                    .collect(),
                root(),
            );
            observe_metadata(&mut observer);
            assert!(observer.finish().is_none());
        }
        let mut observer = Observer::new(
            vec![(root().join("lib.rmeta"), Emit::Metadata)],
            PathBuf::from("relative"),
        );
        observe_metadata(&mut observer);
        assert!(observer.finish().is_none());
        let mut observer =
            Observer::new(vec![(PathBuf::from("lib.rmeta"), Emit::Metadata)], root());
        observe_metadata(&mut observer);
        assert!(observer.finish().is_none());
    }

    #[test]
    fn redirects_and_wrong_emit_kinds_are_sticky_before_or_after_coverage() {
        for invalid in [
            notification("metadata", &root().join("redirected.rmeta")),
            notification("link", &root().join("elsewhere.rlib")),
            notification("link", &root().join("lib.rmeta")),
            notification("obj", &root().join("lib.rmeta")),
        ] {
            for complete_first in [false, true] {
                let mut observer = metadata_observer();
                if complete_first {
                    observe_metadata(&mut observer);
                }
                observer.observe(&invalid);
                observe_metadata(&mut observer);
                assert!(observer.finish().is_none(), "accepted {invalid}");
            }
        }
    }

    #[test]
    fn malformed_tagged_records_cannot_be_repaired_by_later_valid_reports() {
        for invalid in [
            r#"{"$message_type":"artifact","emit":"metadata"}"#,
            r#"{"$message_type":"artifact","artifact":"lib.rmeta"}"#,
            r#"{"emit":"metadata","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":null,"emit":"metadata","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":1,"emit":"metadata","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"artifact","emit":null,"artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"artifact","emit":[],"artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"artifact","emit":"metadata","artifact":null}"#,
            r#"{"$message_type":"artifact","emit":"metadata","artifact":{}}"#,
            r#"{"$message_type":"artifact","emit":"metadata","artifact":""}"#,
            r#"{"$message_type":"artifact","emit":"","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"diagnostic","emit":"metadata","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"artifact","$message_type":"artifact","emit":"metadata","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"artifact","emit":"metadata","emit":"metadata","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"artifact","emit":"metadata","artifact":"lib.rmeta","artifact":"lib.rmeta"}"#,
            r#"{"$message_type":"diagnostic","message":"note","artifact":null}"#,
        ] {
            let mut observer = metadata_observer();
            observe_metadata(&mut observer);
            observer.observe(invalid);
            observe_metadata(&mut observer);
            assert!(observer.finish().is_none(), "accepted {invalid}");
        }
    }

    #[test]
    fn diagnostics_and_unrelated_outputs_cannot_supply_missing_coverage() {
        let inert = [
            r#"{"$message_type":"diagnostic","message":"note","level":"note"}"#.to_owned(),
            r#"{"message":"untagged diagnostic","level":"note"}"#.to_owned(),
            notification("dep-info", &root().join("lib.d")),
            notification("obj", &root().join("lib.o")),
            notification("llvm-ir", &root().join("lib.ll")),
        ];
        let mut missing = metadata_observer();
        for raw in &inert {
            missing.observe(raw);
        }
        assert!(missing.finish().is_none());
        let mut covered = metadata_observer();
        for raw in &inert {
            covered.observe(raw);
        }
        observe_metadata(&mut covered);
        assert!(covered.finish().is_some());
    }

    #[test]
    fn inventory_and_path_limits_are_inclusive_and_fail_closed() {
        let inventory = || {
            (0..MAX_OUTPUTS)
                .map(|index| (root().join(format!("lib-{index}")), Emit::Link))
                .collect::<Vec<_>>()
        };
        let mut maximum = Observer::new(inventory(), root());
        for (path, _) in inventory() {
            maximum.observe(&notification("link", &path));
        }
        assert_eq!(maximum.finish().unwrap().outputs().len(), MAX_OUTPUTS);
        let mut excess = inventory();
        excess.push((root().join("one-too-many"), Emit::Link));
        assert!(Observer::new(excess, root()).finish().is_none());

        let prefix = root().as_os_str().as_encoded_bytes().len() + 1;
        let maximum_path = root().join("a".repeat(MAX_PATH_BYTES - prefix));
        assert_eq!(
            maximum_path.as_os_str().as_encoded_bytes().len(),
            MAX_PATH_BYTES
        );
        let mut maximum = Observer::new(vec![(maximum_path.clone(), Emit::Link)], root());
        maximum.observe(&notification("link", &maximum_path));
        assert!(maximum.finish().is_some());
        let oversized = root().join("a".repeat(MAX_PATH_BYTES + 1 - prefix));
        assert!(
            Observer::new(vec![(oversized.clone(), Emit::Link)], root())
                .finish()
                .is_none()
        );
        let mut reported = metadata_observer();
        observe_metadata(&mut reported);
        reported.observe(&notification("obj", &oversized));
        assert!(reported.finish().is_none());
        assert!(
            Observer::new(vec![(root().join("lib"), Emit::Link)], oversized)
                .finish()
                .is_none()
        );
    }

    #[test]
    fn parent_components_are_not_canonicalized_and_emit_wire_names_are_exact() {
        let mut observer = metadata_observer();
        observer.observe(&notification("metadata", Path::new("other/../lib.rmeta")));
        observe_metadata(&mut observer);
        assert!(observer.finish().is_none());
        assert_eq!(serde_json::to_string(&Emit::Link).unwrap(), r#""link""#);
        assert_eq!(
            serde_json::to_string(&Emit::Metadata).unwrap(),
            r#""metadata""#
        );
        assert!(serde_json::from_str::<Emit>(r#""Metadata""#).is_err());
    }
}
