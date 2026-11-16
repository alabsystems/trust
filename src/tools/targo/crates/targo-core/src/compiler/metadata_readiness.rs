//! Trust: live metadata readiness for native dirty pipelining units.
//!
//! A compiler report is an observation, not execution authentication or proof.
//! Never open a path selected by that report: only the planned output is used.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, bail};
use serde::{Deserialize, Deserializer};

use crate::CargoResult;

const MAX_REPORTED_PATH_BYTES: usize = 128 * 1024;

pub(super) struct MetadataReadiness {
    policy: Policy,
}

enum Policy {
    Legacy,
    Unrequired,
    Required {
        expected: PathBuf,
        cwd: PathBuf,
        observation: Observation,
    },
}

enum Observation {
    Missing,
    Seen,
    Rejected,
}

impl MetadataReadiness {
    pub(super) fn without_demand(native: bool) -> Self {
        Self {
            policy: if native {
                Policy::Unrequired
            } else {
                Policy::Legacy
            },
        }
    }

    pub(super) fn required(expected: PathBuf, cwd: PathBuf) -> CargoResult<Self> {
        if !expected.is_absolute() || !cwd.is_absolute() {
            bail!("native pipelined metadata requires absolute planned output and compiler cwd");
        }
        Ok(Self {
            policy: Policy::Required {
                expected,
                cwd,
                observation: Observation::Missing,
            },
        })
    }

    /// Intercept demanded artifact records before any diagnostic shortcuts.
    pub(super) fn intercept(&mut self, line: &str) -> CargoResult<Option<bool>> {
        if !matches!(self.policy, Policy::Required { .. }) {
            return Ok(None);
        }
        #[derive(Deserialize)]
        struct Header<'a> {
            #[serde(rename = "$message_type", borrow)]
            message_type: Option<std::borrow::Cow<'a, str>>,
            #[serde(default, deserialize_with = "present")]
            artifact: bool,
            #[serde(default, deserialize_with = "present")]
            emit: bool,
        }
        let header: Header<'_> = match serde_json::from_str(line) {
            Ok(header) => header,
            Err(error) => {
                if let Policy::Required { observation, .. } = &mut self.policy {
                    *observation = Observation::Rejected;
                }
                return Err(error).context("invalid native pipelined metadata record header");
            }
        };
        if header.artifact || header.emit || header.message_type.as_deref() == Some("artifact") {
            return self.observe(line, "").map(Some);
        }
        Ok(None)
    }

    /// The path parameter preserves only legacy Cargo's permissive protocol.
    /// Required native observations decode their path from the same full record.
    pub(super) fn observe(&mut self, line: &str, artifact: &str) -> CargoResult<bool> {
        let Policy::Required {
            expected,
            cwd,
            observation,
        } = &mut self.policy
        else {
            return Ok(matches!(self.policy, Policy::Legacy) && artifact.ends_with(".rmeta"));
        };

        if matches!(observation, Observation::Rejected) {
            bail!("native pipelined metadata observation was already rejected");
        }
        let result: CargoResult<bool> = (|| {
            #[derive(Deserialize)]
            struct Protocol<'a> {
                #[serde(rename = "$message_type", borrow)]
                message_type: std::borrow::Cow<'a, str>,
                #[serde(borrow)]
                emit: std::borrow::Cow<'a, str>,
                #[serde(borrow)]
                artifact: std::borrow::Cow<'a, str>,
            }

            let protocol: Protocol<'_> = serde_json::from_str(line)
                .context("invalid native pipelined metadata artifact notification")?;
            if protocol.artifact.len() > MAX_REPORTED_PATH_BYTES {
                bail!("native pipelined metadata artifact path exceeds the observation limit");
            }
            if protocol.message_type != "artifact" {
                bail!("native pipelined metadata artifact has an unexpected message type");
            }
            let reported = Path::new(protocol.artifact.as_ref());
            let resolved = if reported.is_absolute() {
                reported.to_path_buf()
            } else {
                cwd.join(reported)
            };
            if protocol.emit != "metadata" {
                if resolved == *expected {
                    bail!(
                        "native pipelined metadata output was reported with a non-metadata emit kind"
                    );
                }
                return Ok(false);
            }
            if resolved != *expected {
                bail!(
                    "native pipelined metadata notification names `{}`, expected `{}`",
                    resolved.display(),
                    expected.display()
                );
            }
            require_regular(expected)?;
            Ok(true)
        })();
        match result {
            Ok(false) => Ok(false),
            // Exact duplicates must not send another Finish.
            Ok(true) => Ok(!matches!(
                std::mem::replace(observation, Observation::Seen),
                Observation::Seen
            )),
            Err(error) => {
                *observation = Observation::Rejected;
                Err(error)
            }
        }
    }

    pub(super) fn finish(&self) -> CargoResult<()> {
        if let Policy::Required {
            expected,
            observation,
            ..
        } = &self.policy
        {
            match observation {
                Observation::Missing => bail!(
                    "missing native pipelined metadata notification for `{}`",
                    expected.display()
                ),
                Observation::Rejected => {
                    bail!("native pipelined metadata observation was rejected")
                }
                Observation::Seen => {}
            }
            require_regular(expected)?;
        }
        Ok(())
    }
}

fn present<'de, D: Deserializer<'de>>(deserializer: D) -> Result<bool, D::Error> {
    serde::de::IgnoredAny::deserialize(deserializer)?;
    Ok(true)
}

fn require_regular(expected: &Path) -> CargoResult<()> {
    let metadata = fs::symlink_metadata(expected).with_context(|| {
        format!(
            "native pipelined metadata output is unavailable: `{}`",
            expected.display()
        )
    })?;
    if !metadata.is_file() {
        bail!(
            "native pipelined metadata output is not a regular file: `{}`",
            expected.display()
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn notification(kind: &str, artifact: &Path) -> String {
        serde_json::json!({
            "$message_type": "artifact",
            "emit": kind,
            "artifact": artifact,
        })
        .to_string()
    }

    #[test]
    fn exact_current_report_releases_once_and_requires_the_file_through_completion() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        fs::write(&expected, b"metadata").unwrap();
        let mut readiness =
            MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
        let line = notification("metadata", &expected);
        assert!(
            readiness
                .observe(&line, expected.to_str().unwrap())
                .unwrap()
        );
        assert!(
            !readiness
                .observe(&line, expected.to_str().unwrap())
                .unwrap()
        );
        readiness.finish().unwrap();
        fs::remove_file(expected).unwrap();
        assert!(readiness.finish().is_err());
    }

    #[test]
    fn relative_report_uses_the_captured_child_cwd() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        fs::write(&expected, b"metadata").unwrap();
        let mut readiness = MetadataReadiness::required(expected, root.path().into()).unwrap();
        assert!(
            readiness
                .observe(
                    &notification("metadata", Path::new("lib.rmeta")),
                    "lib.rmeta"
                )
                .unwrap()
        );
        readiness.finish().unwrap();
    }

    #[test]
    fn surviving_default_file_does_not_substitute_for_the_current_report() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("old.rmeta");
        fs::write(&expected, b"old metadata").unwrap();
        let mut readiness = MetadataReadiness::required(expected, root.path().into()).unwrap();
        assert!(readiness.finish().is_err());
        let redirect = root.path().join("redirect.rmeta");
        fs::write(&redirect, b"current metadata").unwrap();
        assert!(
            readiness
                .observe(
                    &notification("metadata", &redirect),
                    redirect.to_str().unwrap()
                )
                .is_err()
        );
        assert!(readiness.finish().is_err());
    }

    #[test]
    fn suffix_or_malformed_protocol_cannot_grant_readiness() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        fs::write(&expected, b"metadata").unwrap();
        let path = expected.to_str().unwrap();
        let other_type =
            serde_json::json!({"$message_type":"diagnostic","emit":"metadata"}).to_string();
        for invalid in [notification("link", &expected), "{}".into(), other_type] {
            let mut readiness =
                MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
            assert!(readiness.observe(&invalid, path).is_err());
            assert!(readiness.finish().is_err());
        }
        let mut readiness = MetadataReadiness::required(expected, root.path().into()).unwrap();
        assert!(
            readiness
                .observe(
                    &notification(
                        "metadata",
                        Path::new(&"a".repeat(MAX_REPORTED_PATH_BYTES + 1))
                    ),
                    "",
                )
                .is_err()
        );
        assert!(readiness.finish().is_err());
    }

    #[test]
    fn tagged_null_or_duplicate_artifact_after_valid_report_permanently_rejects_completion() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        fs::write(&expected, b"metadata").unwrap();
        let quoted = serde_json::to_string(&expected).unwrap();
        let duplicate = format!(
            "{{\"$message_type\":\"artifact\",\"emit\":\"metadata\",\"artifact\":{quoted},\"artifact\":{quoted}}}"
        );
        for invalid in [
            "{\"$message_type\":\"artifact\",\"emit\":\"metadata\",\"artifact\":null}".to_string(),
            duplicate,
        ] {
            let mut readiness =
                MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
            assert_eq!(
                readiness
                    .intercept(&notification("metadata", &expected))
                    .unwrap(),
                Some(true)
            );
            assert!(readiness.intercept(&invalid).is_err());
            assert!(readiness.finish().is_err());
        }
    }

    #[test]
    fn artifact_ingress_precedes_diagnostic_shape_and_ignores_unrelated_records() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        fs::write(&expected, b"metadata").unwrap();
        let mut readiness =
            MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
        let mut diagnostic = serde_json::json!({
            "$message_type":"diagnostic", "rendered":"warning", "message":"warning",
            "level":"warning", "code":null, "children":[],
        });
        assert_eq!(readiness.intercept(&diagnostic.to_string()).unwrap(), None);
        assert!(readiness.finish().is_err());
        diagnostic["$message_type"] = "artifact".into();
        diagnostic["artifact"] = serde_json::to_value(&expected).unwrap();
        diagnostic["emit"] = "metadata".into();
        assert_eq!(
            readiness.intercept(&diagnostic.to_string()).unwrap(),
            Some(true)
        );
        readiness.finish().unwrap();
    }

    #[test]
    fn rejected_report_cannot_be_replaced_by_a_later_exact_report() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        fs::write(&expected, b"metadata").unwrap();
        let mut readiness =
            MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
        assert!(readiness.observe("{}", expected.to_str().unwrap()).is_err());
        assert!(
            readiness
                .observe(
                    &notification("metadata", &expected),
                    expected.to_str().unwrap()
                )
                .is_err()
        );
        assert!(readiness.finish().is_err());
    }

    #[test]
    fn other_real_artifacts_do_not_signal_metadata() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        let mut readiness = MetadataReadiness::required(expected, root.path().into()).unwrap();
        assert!(
            !readiness
                .observe(&notification("dep-info", Path::new("lib.d")), "lib.d")
                .unwrap()
        );
        assert!(readiness.finish().is_err());
    }

    #[test]
    fn native_without_demand_and_legacy_have_distinct_readiness_policies() {
        let mut native = MetadataReadiness::without_demand(true);
        assert!(!native.observe("{}", "arbitrary.rmeta").unwrap());
        native.finish().unwrap();
        let mut legacy = MetadataReadiness::without_demand(false);
        assert!(legacy.observe("{}", "arbitrary.rmeta").unwrap());
        legacy.finish().unwrap();
        assert!(
            MetadataReadiness::required("relative.rmeta".into(), PathBuf::from("relative"))
                .is_err()
        );
    }

    #[test]
    fn a_report_cannot_release_a_missing_or_nonregular_expected_file() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().join("lib.rmeta");
        let mut readiness =
            MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
        let line = notification("metadata", &expected);
        assert!(
            readiness
                .observe(&line, expected.to_str().unwrap())
                .is_err()
        );
        fs::create_dir(&expected).unwrap();
        let mut readiness =
            MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
        assert!(
            readiness
                .observe(&line, expected.to_str().unwrap())
                .is_err()
        );
        assert!(readiness.finish().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn expected_leaf_symlink_is_not_a_regular_metadata_output() {
        let root = tempfile::tempdir().unwrap();
        let actual = root.path().join("actual.rmeta");
        fs::write(&actual, b"metadata").unwrap();
        let expected = root.path().join("lib.rmeta");
        std::os::unix::fs::symlink(actual, &expected).unwrap();
        let mut readiness =
            MetadataReadiness::required(expected.clone(), root.path().into()).unwrap();
        assert!(
            readiness
                .observe(
                    &notification("metadata", &expected),
                    expected.to_str().unwrap()
                )
                .is_err()
        );
        assert!(readiness.finish().is_err());
    }
}
