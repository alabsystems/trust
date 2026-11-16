//! A completed candidate record's claims, not independently proved build facts.

use crate::{CheckedReceipt, Refusal, Result, is_hex};

/// A borrowed checked receipt whose self-reported completed candidate fields
/// are consistent. Actual compiler probes, full seal identity and supervised
/// workload qualification still belong to the native paired runner.
pub struct CandidateReceipt<'a> {
    receipt: &'a CheckedReceipt,
    declared_source_closure_sha256: &'a str,
}

impl CandidateReceipt<'_> {
    pub fn receipt(&self) -> &CheckedReceipt {
        self.receipt
    }
    pub fn declared_source_closure_sha256(&self) -> &str {
        self.declared_source_closure_sha256
    }
}

impl CheckedReceipt {
    pub fn completed_candidate(&self, expected_commit: &str) -> Result<CandidateReceipt<'_>> {
        let data = self.data();
        if data["compiler"]["source_commit"].as_str() != Some(expected_commit) {
            return Err(Refusal(
                "candidate request does not identify the originally checked compiler commit".into(),
            ));
        }
        let lineage = &data["source_lineage"];
        let closure = &lineage["closure_sha256"];
        if !matches!(data["status"].as_str(), Some("internal-release-ready" | "release-ready"))
            || !integer_stage_at_least_two(&data["stage"])
            || data["source_tree_clean"] != true
            || lineage["schema"] != "trust.source-lineage.v1"
            || lineage["status"] != "immutable_release"
            || lineage["source_tree_clean"] != true
            || !lineage["errors"].is_empty_array()
            || lineage["stable_across_build"] != true
            || !is_hex(closure, &[64])
            || lineage["pre_build_closure_sha256"] != *closure
            || lineage["post_build_closure_sha256"] != *closure
        {
            return Err(Refusal("candidate receipt does not bind a clean, stable, completed Trust-from-Trust source closure".into()));
        }
        let repositories = lineage["repositories"]
            .as_array()
            .filter(|rows| rows.iter().all(crate::Value::is_object))
            .ok_or_else(|| {
                Refusal("candidate source closure repositories are not object rows".into())
            })?;
        let roots = repositories.iter().filter(|row| row["path"] == ".").collect::<Vec<_>>();
        if roots.len() != 1 || roots[0]["head"].as_str() != Some(expected_commit) {
            return Err(Refusal(
                "candidate receipt source closure does not identify the compiler's root commit"
                    .into(),
            ));
        }
        let rows = data["tools"].as_array().expect("validated receipt tool rows");
        let stage = data["stage_root"].as_str().expect("validated receipt stage root");
        for name in ["targo", "targo-trust", "trustd", "ay"] {
            let expected = format!("{stage}/bin/{name}");
            if rows.iter().find(|row| row["name"] == name).and_then(|row| row["path"].as_str())
                != Some(expected.as_str())
            {
                return Err(Refusal(format!("candidate receipt does not bind the shipped {name}")));
            }
        }
        Ok(CandidateReceipt {
            receipt: self,
            declared_source_closure_sha256: closure.as_str().unwrap(),
        })
    }
}

fn integer_stage_at_least_two(value: &crate::Value) -> bool {
    let crate::Value::Number(number) = value else {
        return false;
    };
    let token = number.as_str();
    // Preserve Python's `type(stage) is int`: decimal/exponent literals and
    // booleans are not integer stages, even when their numeric value is two.
    if token.is_empty() || !token.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    token.len() > 1 || token.as_bytes()[0] >= b'2'
}
