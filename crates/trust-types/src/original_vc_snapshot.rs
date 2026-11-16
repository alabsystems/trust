//! Bounded persistence of the ORIGINAL compiler VC, before native lowering.
//!
//! A snapshot is untrusted data, including its hashes and row ID. Decoding it
//! restores neither a live compiler receipt nor source/program proof authority.

use serde::{Deserialize, Serialize};

use crate::VerificationCondition;

pub const ORIGINAL_VC_SNAPSHOT_SCHEMA: &str = "trust.original-vc-snapshot.v1";
pub const EXPANDED_ORIGINAL_VC_SNAPSHOT_SCHEMA: &str = "trust.original-vc-snapshot.v2";
pub const ORIGINAL_VC_SNAPSHOT_MAX_BYTES: usize = 4 * 1024 * 1024;
/// Offline payload availability bounds only; no verifier budget is changed.
pub const ORIGINAL_VC_SNAPSHOT_MAX_DEPTH: usize = 64;
const MAX_SNAPSHOT_NODES: usize = 65_536;
const MAX_SNAPSHOT_JSON_NESTING: usize = 192;
pub const EXACT_VC_CLAIM_SCHEMA_VERSION: &str = "trustc.exact-vc-claim.v3";
const EXACT_VC_CLAIM_DIGEST_DOMAIN: &str = "trustc.transport-exact-vc-claim.v3";
const TYPED_INPUT_CLAIM_DIGEST_DOMAIN: &str = "trustc.transport-exact-vc-claim.typed-input.v1";

/// Correlation-only, independently decodable original typed claim. It is a
/// sidecar field, never another CIC artifact or a source authority capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OriginalVcSnapshot {
    #[serde(deserialize_with = "small_string")]
    pub schema: String,
    #[serde(deserialize_with = "small_string")]
    pub obligation_id: String,
    #[serde(deserialize_with = "small_string")]
    pub claim_digest_sha256: String,
    /// Independently captured original typed inputs, when the source claim
    /// needs more than its VC marker. Part of the outer claim digest, never
    /// inferred from a certificate presented for that claim.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "optional_digest"
    )]
    pub typed_input_digest_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expanded_function_identity:
        Option<crate::expanded_function_identity::ExpandedFunctionIdentity>,
    pub overflow_checks: bool,
    #[serde(deserialize_with = "small_string")]
    pub target: String,
    #[serde(deserialize_with = "small_string")]
    pub payload_sha256: String,
    /// Direct typed JSON retains i128/u128 literals, every VC field, and array
    /// order. Do not route this through serde_json::Value, which loses big ints.
    #[serde(deserialize_with = "payload_string")]
    pub original_vc_json: String,
}

impl OriginalVcSnapshot {
    /// Failure costs offline replay availability, never changes a verdict.
    pub fn capture(
        vc: &VerificationCondition,
        overflow_checks: bool,
        target: &str,
        obligation_id: &str,
        claim_digest_sha256: &str,
    ) -> Option<Self> {
        Self::capture_with_typed_input_digest(
            vc,
            overflow_checks,
            target,
            obligation_id,
            claim_digest_sha256,
            None,
        )
    }

    pub fn capture_with_typed_input_digest(
        vc: &VerificationCondition,
        overflow_checks: bool,
        target: &str,
        obligation_id: &str,
        claim_digest_sha256: &str,
        typed_input_digest_sha256: Option<&str>,
    ) -> Option<Self> {
        Self::capture_with_expanded_identity(
            vc,
            overflow_checks,
            target,
            obligation_id,
            claim_digest_sha256,
            typed_input_digest_sha256,
            None,
        )
    }

    pub fn capture_with_expanded_identity(
        vc: &VerificationCondition,
        overflow_checks: bool,
        target: &str,
        obligation_id: &str,
        claim_digest_sha256: &str,
        typed_input_digest_sha256: Option<&str>,
        expanded_function_identity: Option<
            &crate::expanded_function_identity::ExpandedFunctionIdentity,
        >,
    ) -> Option<Self> {
        if target.is_empty()
            || target.len() > 4096
            || obligation_id.is_empty()
            || obligation_id.len() > 4096
        {
            return None;
        }
        let original_vc_json = bounded_original_vc_json(vc)?;
        if exact_vc_claim_digest_with_expanded_identity(
            vc,
            overflow_checks,
            Some(target),
            typed_input_digest_sha256,
            expanded_function_identity,
        )
        .as_deref()
            != Some(claim_digest_sha256)
        {
            return None;
        }
        Some(Self {
            schema: if expanded_function_identity.is_some() {
                EXPANDED_ORIGINAL_VC_SNAPSHOT_SCHEMA
            } else {
                ORIGINAL_VC_SNAPSHOT_SCHEMA
            }
            .into(),
            obligation_id: obligation_id.into(),
            claim_digest_sha256: claim_digest_sha256.into(),
            typed_input_digest_sha256: typed_input_digest_sha256.map(str::to_owned),
            expanded_function_identity: expanded_function_identity.cloned(),
            overflow_checks,
            target: target.into(),
            payload_sha256: crate::stable_sha256_hex(original_vc_json.as_bytes()),
            original_vc_json,
        })
    }

    /// Decode only after checking the presented row ID/digest and bounded bytes.
    /// The caller must independently supply an expected VC/source to establish
    /// anything beyond self-consistency of this serialized snapshot.
    pub fn decode_for_row(
        &self,
        obligation_id: &str,
        claim_digest_sha256: &str,
    ) -> Result<VerificationCondition, &'static str> {
        if self.schema
            != if self.expanded_function_identity.is_some() {
                EXPANDED_ORIGINAL_VC_SNAPSHOT_SCHEMA
            } else {
                ORIGINAL_VC_SNAPSHOT_SCHEMA
            }
            || self.obligation_id.is_empty()
            || self.obligation_id.len() > 4096
            || self.obligation_id != obligation_id
            || self.target.is_empty()
            || self.target.len() > 4096
            || !crate::digest::is_stable_sha256_hex(&self.claim_digest_sha256)
            || self.claim_digest_sha256 != claim_digest_sha256
        {
            return Err("original VC snapshot schema/row/claim binding mismatch");
        }
        if self.original_vc_json.len() > ORIGINAL_VC_SNAPSHOT_MAX_BYTES
            || crate::json_depth::json_nesting_depth(&self.original_vc_json)
                > MAX_SNAPSHOT_JSON_NESTING
            || crate::stable_sha256_hex(self.original_vc_json.as_bytes()) != self.payload_sha256
        {
            return Err("original VC snapshot payload bound/digest mismatch");
        }
        let vc = crate::json_depth::from_str_deep::<VerificationCondition>(&self.original_vc_json)
            .map_err(|_| "malformed original typed VC snapshot")?;
        if bounded_original_vc_json(&vc).is_none()
            || exact_vc_claim_digest_with_expanded_identity(
                &vc,
                self.overflow_checks,
                Some(&self.target),
                self.typed_input_digest_sha256.as_deref(),
                self.expanded_function_identity.as_ref(),
            )
            .as_deref()
                != Some(claim_digest_sha256)
        {
            return Err("original VC snapshot does not reproduce exact claim digest");
        }
        Ok(vc)
    }
}

/// Bound serialization BEFORE any recursive canonical digest/identity work.
/// Besides the iterative Formula/Sort preflight, the writer limits nesting
/// online, including recursive Ty fields and any other serialized carriers.
/// This is an offline-payload availability bound, never a verifier budget.
pub fn bounded_original_vc_json(vc: &VerificationCondition) -> Option<String> {
    if !snapshot_within_capture_bounds(vc) {
        return None;
    }
    bounded_identity_json(vc)
}

/// Shared bounded typed serialization for source identities. This preserves
/// wide integer values and bounds nesting before recursively hashing inputs.
pub(crate) fn bounded_identity_json(value: &impl Serialize) -> Option<String> {
    let mut writer = SnapshotWriter::default();
    serde_json::to_writer(&mut writer, value).ok()?;
    String::from_utf8(writer.bytes).ok()
}

#[derive(Default)]
struct SnapshotWriter {
    bytes: Vec<u8>,
    depth: usize,
    nodes: usize,
    in_string: bool,
    escaped: bool,
}

impl std::io::Write for SnapshotWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if bytes.len() > ORIGINAL_VC_SNAPSHOT_MAX_BYTES.saturating_sub(self.bytes.len()) {
            return Err(std::io::Error::other("original VC snapshot byte limit"));
        }
        for &byte in bytes {
            if self.in_string {
                if self.escaped {
                    self.escaped = false;
                } else if byte == b'\\' {
                    self.escaped = true;
                } else if byte == b'"' {
                    self.in_string = false;
                }
                continue;
            }
            match byte {
                b'"' => self.in_string = true,
                b'{' | b'[' => {
                    self.depth += 1;
                    self.nodes += 1;
                    if self.depth > MAX_SNAPSHOT_JSON_NESTING || self.nodes > MAX_SNAPSHOT_NODES {
                        return Err(std::io::Error::other(
                            "original VC snapshot nesting/node limit",
                        ));
                    }
                }
                b'}' | b']' => self.depth = self.depth.saturating_sub(1),
                _ => {}
            }
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// No recursion, hashing or serialization before this check. Include every
/// Formula in the full VC, not just its violation, and nested sort carriers.
/// ContractMetadata contains scalar flags/indexes; VcKind contains no Formula.
/// Its recursive Ty fields are bounded by the streaming writer before hashing.
fn snapshot_within_capture_bounds(vc: &VerificationCondition) -> bool {
    use crate::{Formula, ObligationWrapper, PathGuardTerm, Sort};
    let mut pending = vec![(&vc.formula, 1usize)];
    if let Some(record) = &vc.obligation {
        pending.push((&record.body, 1));
        pending.extend(record.subject.iter().map(|f| (f, 1)));
        if record.wrappers.len() > MAX_SNAPSHOT_NODES {
            return false;
        }
        for wrapper in &record.wrappers {
            fn add<'a>(pending: &mut Vec<(&'a Formula, usize)>, facts: &'a [Formula]) -> bool {
                if facts.len() > MAX_SNAPSHOT_NODES.saturating_sub(pending.len()) {
                    return false;
                }
                pending.extend(facts.iter().map(|f| (f, 1)));
                true
            }
            match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => {
                    if !add(&mut pending, facts) {
                        return false;
                    }
                }
                ObligationWrapper::PathGuardOr { paths } => {
                    if paths.len() > MAX_SNAPSHOT_NODES {
                        return false;
                    }
                    for path in paths {
                        match path {
                            // The in-process negative-only marker carries no guards,
                            // and already serializes exactly as Raw.
                            PathGuardTerm::Raw | PathGuardTerm::Collapsed => {}
                            PathGuardTerm::Guarded { guards } => {
                                if !add(&mut pending, guards) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    let mut count = 0usize;
    let mut sorts = Vec::new();
    while let Some((f, depth)) = pending.pop() {
        count += 1;
        if count > MAX_SNAPSHOT_NODES || depth > ORIGINAL_VC_SNAPSHOT_MAX_DEPTH {
            return false;
        }
        match f {
            Formula::Var(_, s)
            | Formula::SymVar(_, s)
            | Formula::Ctor { sort: s, .. }
            | Formula::FnApp { sort: s, .. }
            | Formula::Sel { field_sort: s, .. } => sorts.push((s, depth + 1)),
            Formula::Forall(vars, _) | Formula::Exists(vars, _) => {
                if vars.len() > MAX_SNAPSHOT_NODES {
                    return false;
                }
                sorts.extend(vars.iter().map(|(_, s)| (s, depth + 1)));
            }
            Formula::ConstArray { index_sort, elem_sort, .. } => {
                sorts.push((index_sort, depth + 1));
                sorts.push((elem_sort, depth + 1));
            }
            _ => {}
        }
        let remaining = MAX_SNAPSHOT_NODES.saturating_sub(count + pending.len());
        let mut child_count = 0usize;
        if !crate::all_formula_children(f, |child| {
            child_count += 1;
            if child_count > remaining {
                return false;
            }
            pending.push((child, depth + 1));
            true
        }) {
            return false;
        }
        while let Some((sort, depth)) = sorts.pop() {
            count += 1;
            if count > MAX_SNAPSHOT_NODES || depth > ORIGINAL_VC_SNAPSHOT_MAX_DEPTH {
                return false;
            }
            match sort {
                Sort::Array(a, b) => {
                    sorts.push((a, depth + 1));
                    sorts.push((b, depth + 1));
                }
                Sort::Datatype { constructors, .. } => {
                    if constructors.len() > MAX_SNAPSHOT_NODES {
                        return false;
                    }
                    for (_, fields) in constructors {
                        if fields.len() > MAX_SNAPSHOT_NODES.saturating_sub(count + sorts.len()) {
                            return false;
                        }
                        sorts.extend(fields.iter().map(|(_, s)| (s, depth + 1)));
                    }
                }
                Sort::Bool
                | Sort::Int
                | Sort::BitVec(_)
                | Sort::Float { .. }
                | Sort::RoundingMode
                | Sort::Real => {}
                _ => return false,
            }
        }
    }
    true
}

/// Shared claim v3 encoder for compiler publication and original-VC snapshots.
/// Bind every formula by its Merkle digest, retaining exhaustive field/wrapper
/// matching, big-integer encoding, sorted object keys and ordered arrays.
pub fn canonical_exact_vc_claim_payload(
    vc: &VerificationCondition,
    overflow_checks: bool,
    target: Option<&str>,
) -> Option<String> {
    let VerificationCondition { kind, function, location, formula, contract_metadata, obligation } =
        vc;
    let mut formulas = crate::formula_merkle::FormulaDigester::new();
    let vc = serde_json::json!({
        "kind": crate::canonical_digest_json_value(kind).ok()?,
        "function": crate::canonical_digest_json_value(function).ok()?,
        "location": crate::canonical_digest_json_value(location).ok()?,
        "contract_metadata": crate::canonical_digest_json_value(contract_metadata).ok()?,
        "formula": exact_vc_claim_formula(&mut formulas, formula)?,
        "obligation": match obligation {
            Some(record) => exact_vc_claim_obligation_record(&mut formulas, record)?,
            None => serde_json::Value::Null,
        },
    });
    let mut claim = serde_json::json!({
        "schema": EXACT_VC_CLAIM_SCHEMA_VERSION,
        "semantics": {"overflow_checks": overflow_checks, "target": target},
        "vc": vc,
    });
    // The claim is already a Value: do not materialize a second full copy just
    // to sort its objects. This uses the same shared canonicalization primitive.
    crate::digest::canonicalize_json_in_place(&mut claim);
    serde_json::to_string(&claim).ok()
}

/// A formula of an exact-VC claim v3: its Merkle digest, in lowercase hex.
fn exact_vc_claim_formula(
    formulas: &mut crate::formula_merkle::FormulaDigester,
    formula: &crate::Formula,
) -> Option<serde_json::Value> {
    Some(serde_json::Value::String(formulas.digest(formula).ok()?.to_hex()))
}

/// The formulas of an exact-VC claim v3, each its Merkle digest, in order.
fn exact_vc_claim_formulas(
    formulas: &mut crate::formula_merkle::FormulaDigester,
    list: &[crate::Formula],
) -> Option<serde_json::Value> {
    list.iter()
        .map(|formula| exact_vc_claim_formula(formulas, formula))
        .collect::<Option<Vec<_>>>()
        .map(serde_json::Value::Array)
}

/// Exhaustive matching prevents new fields or wrappers from escaping the claim.
fn exact_vc_claim_obligation_record(
    formulas: &mut crate::formula_merkle::FormulaDigester,
    record: &crate::ObligationRecord,
) -> Option<serde_json::Value> {
    use crate::{ObligationRecord, ObligationWrapper, PathGuardTerm};
    let ObligationRecord { body, wrappers, subject, width } = record;
    let mut bound = Vec::with_capacity(wrappers.len());
    for wrapper in wrappers {
        bound.push(match wrapper {
            ObligationWrapper::ConjoinFactsLast { facts } => serde_json::json!({
                "tag": "conjoin_facts_last",
                "facts": exact_vc_claim_formulas(formulas, facts)?,
            }),
            ObligationWrapper::PathGuardOr { paths } => {
                let mut terms = Vec::with_capacity(paths.len());
                for path in paths {
                    terms.push(match path {
                        // Collapsed serializes as Raw and decodes back to Raw.
                        PathGuardTerm::Raw | PathGuardTerm::Collapsed => {
                            serde_json::json!({ "tag": "raw" })
                        }
                        PathGuardTerm::Guarded { guards } => serde_json::json!({
                            "tag": "guarded",
                            "guards": exact_vc_claim_formulas(formulas, guards)?,
                        }),
                    });
                }
                serde_json::json!({ "tag": "path_guard_or", "paths": terms })
            }
        });
    }
    Some(serde_json::json!({
        "body": exact_vc_claim_formula(formulas, body)?,
        "subject": match subject {
            Some(subject) => exact_vc_claim_formula(formulas, subject)?,
            None => serde_json::Value::Null,
        },
        "width": width,
        "wrappers": bound,
    }))
}

pub fn exact_vc_claim_digest_sha256(
    vc: &VerificationCondition,
    overflow_checks: bool,
    target: Option<&str>,
) -> Option<String> {
    let payload = canonical_exact_vc_claim_payload(vc, overflow_checks, target)?;
    let domain = EXACT_VC_CLAIM_DIGEST_DOMAIN.as_bytes();
    Some(crate::digest::stable_sha256_hex_parts(&[
        b"trustc.digest-frame.v1",
        &(domain.len() as u64).to_be_bytes(),
        domain,
        &(payload.len() as u64).to_be_bytes(),
        payload.as_bytes(),
    ]))
}

/// Bind an independently captured typed-input identity to the original VC.
/// `None` is byte-for-byte the historical v3 claim domain. A present digest
/// uses a distinct domain and cannot be added or removed during replay.
pub fn exact_vc_claim_digest_with_typed_input_sha256(
    vc: &VerificationCondition,
    overflow_checks: bool,
    target: Option<&str>,
    typed_input_digest_sha256: Option<&str>,
) -> Option<String> {
    let original = exact_vc_claim_digest_sha256(vc, overflow_checks, target)?;
    let Some(typed) = typed_input_digest_sha256 else { return Some(original) };
    if !crate::digest::is_stable_sha256_hex(typed) {
        return None;
    }
    let domain = TYPED_INPUT_CLAIM_DIGEST_DOMAIN.as_bytes();
    Some(crate::digest::stable_sha256_hex_parts(&[
        b"trustc.digest-frame.v1",
        &(domain.len() as u64).to_be_bytes(),
        domain,
        &(original.len() as u64).to_be_bytes(),
        original.as_bytes(),
        &(typed.len() as u64).to_be_bytes(),
        typed.as_bytes(),
    ]))
}

/// Expanded identities use a separate domain and require an independently
/// bound full typed question. Ordinary/v1 digests remain byte-for-byte stable.
pub fn exact_vc_claim_digest_with_expanded_identity(
    vc: &VerificationCondition,
    overflow_checks: bool,
    target: Option<&str>,
    typed_input_digest_sha256: Option<&str>,
    expanded: Option<&crate::expanded_function_identity::ExpandedFunctionIdentity>,
) -> Option<String> {
    let original = exact_vc_claim_digest_with_typed_input_sha256(
        vc,
        overflow_checks,
        target,
        typed_input_digest_sha256,
    )?;
    let Some(expanded) = expanded else { return Some(original) };
    typed_input_digest_sha256?;
    let identity = expanded.digest()?;
    let domain = b"trustc.transport-exact-vc-claim.expanded-input.v1";
    Some(crate::digest::stable_sha256_hex_parts(&[
        b"trustc.digest-frame.v1",
        &(domain.len() as u64).to_be_bytes(),
        domain,
        &(original.len() as u64).to_be_bytes(),
        original.as_bytes(),
        &(identity.len() as u64).to_be_bytes(),
        identity.as_bytes(),
    ]))
}

fn bounded_string<'de, D: serde::Deserializer<'de>, const MAX: usize>(
    d: D,
) -> Result<String, D::Error> {
    struct Visitor<const MAX: usize>;
    impl<'de, const MAX: usize> serde::de::Visitor<'de> for Visitor<MAX> {
        type Value = String;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "a string of at most {MAX} bytes")
        }
        fn visit_str<E: serde::de::Error>(self, s: &str) -> Result<String, E> {
            if s.len() > MAX {
                return Err(E::custom("original VC snapshot string byte limit"));
            }
            Ok(s.into())
        }
        fn visit_string<E: serde::de::Error>(self, s: String) -> Result<String, E> {
            if s.len() > MAX {
                return Err(E::custom("original VC snapshot string byte limit"));
            }
            Ok(s)
        }
    }
    d.deserialize_string(Visitor::<MAX>)
}
fn small_string<'de, D: serde::Deserializer<'de>>(d: D) -> Result<String, D::Error> {
    bounded_string::<D, 4096>(d)
}
fn optional_digest<'de, D: serde::Deserializer<'de>>(d: D) -> Result<Option<String>, D::Error> {
    let digest = Option::<String>::deserialize(d)?;
    if digest.as_deref().is_some_and(|digest| !crate::digest::is_stable_sha256_hex(digest)) {
        return Err(serde::de::Error::custom("invalid original typed-input digest"));
    }
    Ok(digest)
}
fn payload_string<'de, D: serde::Deserializer<'de>>(d: D) -> Result<String, D::Error> {
    bounded_string::<D, ORIGINAL_VC_SNAPSHOT_MAX_BYTES>(d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ContractMetadata, Formula, SourceSpan, VcKind};

    fn vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "original".into() },
            function: "fixture::original".into(),
            location: SourceSpan { file: "original.rs".into(), ..SourceSpan::default() },
            formula: Formula::And(vec![Formula::Int(i128::MIN), Formula::UInt(u128::MAX)]),
            contract_metadata: Some(ContractMetadata {
                has_ensures: true,
                source_contract_index: Some(7),
                ..ContractMetadata::default()
            }),
            obligation: None,
        }
    }
    #[test]
    fn original_typed_input_is_part_of_the_outer_claim() {
        let vc = vc();
        let target = "aarch64-apple-darwin;ptr64";
        let original = exact_vc_claim_digest_sha256(&vc, true, Some(target)).unwrap();
        assert_eq!(
            exact_vc_claim_digest_with_typed_input_sha256(&vc, true, Some(target), None),
            Some(original.clone())
        );
        let legacy = OriginalVcSnapshot::capture(&vc, true, target, "row", &original).unwrap();
        assert!(!serde_json::to_string(&legacy).unwrap().contains("typed_input_digest_sha256"));
        let typed = "1".repeat(64);
        let bound =
            exact_vc_claim_digest_with_typed_input_sha256(&vc, true, Some(target), Some(&typed))
                .unwrap();
        assert_ne!(bound, original);
        let snapshot = OriginalVcSnapshot::capture_with_typed_input_digest(
            &vc,
            true,
            target,
            "row",
            &bound,
            Some(&typed),
        )
        .unwrap();
        assert!(snapshot.decode_for_row("row", &bound).is_ok());
        let mut changed = snapshot.clone();
        changed.typed_input_digest_sha256 = Some("2".repeat(64));
        assert!(changed.decode_for_row("row", &bound).is_err());
        changed.typed_input_digest_sha256 = None;
        assert!(changed.decode_for_row("row", &bound).is_err());
        let mut changed = legacy;
        changed.typed_input_digest_sha256 = Some(typed);
        assert!(changed.decode_for_row("row", &original).is_err());
        assert!(
            exact_vc_claim_digest_with_typed_input_sha256(&vc, true, Some(target), Some("bad"))
                .is_none()
        );
    }
    fn snapshot(vc: &VerificationCondition) -> OriginalVcSnapshot {
        let digest =
            exact_vc_claim_digest_sha256(vc, true, Some("aarch64-apple-darwin;ptr64")).unwrap();
        OriginalVcSnapshot::capture(
            vc,
            true,
            "aarch64-apple-darwin;ptr64",
            "vc:original:0",
            &digest,
        )
        .unwrap()
    }

    #[test]
    fn complete_typed_snapshot_roundtrip_preserves_bigints_and_metadata_order() {
        let original = vc();
        let snapshot = snapshot(&original);
        let wire = serde_json::to_string(&snapshot).unwrap();
        let snapshot: OriginalVcSnapshot = serde_json::from_str(&wire).unwrap();
        let decoded =
            snapshot.decode_for_row("vc:original:0", &snapshot.claim_digest_sha256).unwrap();
        assert_eq!(bincode::serialize(&original).unwrap(), bincode::serialize(&decoded).unwrap());
    }

    #[test]
    fn collapsed_path_snapshot_preserves_existing_raw_wire_identity_and_guards() {
        use crate::{ObligationRecord, ObligationWrapper, PathGuardTerm};
        let mut collapsed = vc();
        collapsed.obligation = Some(ObligationRecord {
            body: collapsed.formula.clone(),
            wrappers: vec![ObligationWrapper::PathGuardOr {
                paths: vec![PathGuardTerm::Collapsed],
            }],
            subject: None,
            width: None,
        });
        let captured = snapshot(&collapsed);
        let mut raw = collapsed.clone();
        raw.obligation.as_mut().unwrap().wrappers =
            vec![ObligationWrapper::PathGuardOr { paths: vec![PathGuardTerm::Raw] }];
        assert_eq!(captured, snapshot(&raw));
        let decoded = captured
            .decode_for_row(&captured.obligation_id, &captured.claim_digest_sha256)
            .unwrap();
        assert_eq!(bincode::serialize(&collapsed).unwrap(), bincode::serialize(&decoded).unwrap());
        assert!(matches!(
            decoded.obligation.unwrap().wrappers.as_slice(),
            [ObligationWrapper::PathGuardOr { paths }] if paths == &[PathGuardTerm::Raw]
        ));
        // A real guard still contributes its bytes and exact claim identity.
        let mut guarded = raw;
        guarded.obligation.as_mut().unwrap().wrappers = vec![ObligationWrapper::PathGuardOr {
            paths: vec![PathGuardTerm::Guarded { guards: vec![Formula::Bool(true)] }],
        }];
        assert_ne!(captured.claim_digest_sha256, snapshot(&guarded).claim_digest_sha256);
    }

    #[test]
    fn row_claim_semantics_schema_and_payload_tampering_refuse() {
        let snapshot = snapshot(&vc());
        assert!(snapshot.decode_for_row("other-row", &snapshot.claim_digest_sha256).is_err());
        assert!(snapshot.decode_for_row(&snapshot.obligation_id, &"0".repeat(64)).is_err());
        let mut variants = Vec::new();
        let mut changed = snapshot.clone();
        changed.schema.push_str(".other");
        variants.push(changed);
        let mut changed = snapshot.clone();
        changed.overflow_checks = false;
        variants.push(changed);
        let mut changed = snapshot.clone();
        changed.target.push_str("-other");
        variants.push(changed);
        let mut changed = snapshot.clone();
        changed.original_vc_json.push(' ');
        variants.push(changed);
        let mut changed = snapshot.clone();
        changed.payload_sha256 = "0".repeat(64);
        variants.push(changed);
        for changed in variants {
            assert!(
                changed
                    .decode_for_row(&snapshot.obligation_id, &snapshot.claim_digest_sha256)
                    .is_err()
            );
        }
    }

    #[test]
    fn rehashed_changed_full_vc_cannot_reuse_original_claim_digest() {
        let snapshot = snapshot(&vc());
        let mut changed_vc = vc();
        changed_vc.location.file = "foreign.rs".into();
        let mut changed = snapshot.clone();
        changed.original_vc_json = serde_json::to_string(&changed_vc).unwrap();
        changed.payload_sha256 = crate::stable_sha256_hex(changed.original_vc_json.as_bytes());
        assert!(
            changed.decode_for_row(&snapshot.obligation_id, &snapshot.claim_digest_sha256).is_err()
        );
        assert!(
            OriginalVcSnapshot::capture(
                &changed_vc,
                true,
                &snapshot.target,
                &snapshot.obligation_id,
                &snapshot.claim_digest_sha256
            )
            .is_none()
        );
    }

    #[test]
    fn byte_depth_unknown_field_and_duplicate_field_bounds_refuse() {
        let snapshot = snapshot(&vc());
        let mut changed = snapshot.clone();
        changed.original_vc_json = " ".repeat(ORIGINAL_VC_SNAPSHOT_MAX_BYTES + 1);
        changed.payload_sha256 = crate::stable_sha256_hex(changed.original_vc_json.as_bytes());
        assert!(
            changed.decode_for_row(&snapshot.obligation_id, &snapshot.claim_digest_sha256).is_err()
        );
        assert!(
            serde_json::from_str::<OriginalVcSnapshot>(&serde_json::to_string(&changed).unwrap())
                .is_err()
        );
        changed.original_vc_json = "[".repeat(crate::json_depth::MAX_DEEP_NESTING + 1);
        changed.payload_sha256 = crate::stable_sha256_hex(changed.original_vc_json.as_bytes());
        assert!(
            changed.decode_for_row(&snapshot.obligation_id, &snapshot.claim_digest_sha256).is_err()
        );
        let wire = serde_json::to_string(&snapshot).unwrap();
        assert!(
            serde_json::from_str::<OriginalVcSnapshot>(&wire.replacen('{', "{\"foreign\":0,", 1))
                .is_err()
        );
        assert!(
            serde_json::from_str::<OriginalVcSnapshot>(&wire.replacen(
                '{',
                "{\"schema\":\"duplicate\",",
                1
            ))
            .is_err()
        );
        let mut oversized = vc();
        oversized.function = "x".repeat(ORIGINAL_VC_SNAPSHOT_MAX_BYTES + 1).into();
        let digest =
            exact_vc_claim_digest_sha256(&oversized, true, Some(&snapshot.target)).unwrap();
        assert!(
            OriginalVcSnapshot::capture(
                &oversized,
                true,
                &snapshot.target,
                &snapshot.obligation_id,
                &digest
            )
            .is_none()
        );
    }

    #[test]
    fn shared_claim_digest_uses_compiler_v3_framing() {
        let vc = vc();
        let payload = canonical_exact_vc_claim_payload(&vc, true, Some("target;ptr64")).unwrap();
        let domain = b"trustc.transport-exact-vc-claim.v3";
        let mut framed = b"trustc.digest-frame.v1".to_vec();
        framed.extend_from_slice(&(domain.len() as u64).to_be_bytes());
        framed.extend_from_slice(domain);
        framed.extend_from_slice(&(payload.len() as u64).to_be_bytes());
        framed.extend_from_slice(payload.as_bytes());
        assert_eq!(
            exact_vc_claim_digest_sha256(&vc, true, Some("target;ptr64")).unwrap(),
            crate::stable_sha256_hex(&framed)
        );
        assert_ne!(
            exact_vc_claim_digest_sha256(&vc, false, Some("target;ptr64")),
            exact_vc_claim_digest_sha256(&vc, true, Some("target;ptr64"))
        );
    }

    #[test]
    fn shared_canonical_payload_matches_original_compiler_writer_bytes() {
        // Independent compiler JSON writer, not a call back into canonical
        // sorting. Escaping and Unicode retain their exact bytes while the
        // wide formula literal is bound by the v3 Merkle digest.
        fn original_write(value: &serde_json::Value, out: &mut String) {
            use serde_json::Value;
            match value {
                Value::Null => out.push_str("null"),
                Value::Bool(v) => out.push_str(if *v { "true" } else { "false" }),
                Value::Number(v) => out.push_str(&v.to_string()),
                Value::String(v) => out.push_str(&serde_json::to_string(v).unwrap()),
                Value::Array(values) => {
                    out.push('[');
                    for (i, v) in values.iter().enumerate() {
                        if i != 0 {
                            out.push(',');
                        }
                        original_write(v, out);
                    }
                    out.push(']');
                }
                Value::Object(values) => {
                    let mut entries = values.iter().collect::<Vec<_>>();
                    entries.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));
                    out.push('{');
                    for (i, (key, value)) in entries.into_iter().enumerate() {
                        if i != 0 {
                            out.push(',');
                        }
                        out.push_str(&serde_json::to_string(key).unwrap());
                        out.push(':');
                        original_write(value, out);
                    }
                    out.push('}');
                }
            }
        }
        let mut vc = vc();
        vc.kind = VcKind::Assertion {
            message: "quote\" slash\\ tab\t line\n control\u{0001} 雪🙂".into(),
        };
        vc.location.file = "unicode/é.rs".into();
        for target in [None, Some("aarch64-apple-darwin;ptr64\n\"雪")] {
            assert!(vc.obligation.is_none());
            let mut expected_vc = crate::canonical_digest_json_value(&vc).unwrap();
            expected_vc["formula"] = serde_json::Value::String(
                crate::formula_merkle::formula_digest(&vc.formula).unwrap().to_hex(),
            );
            let claim = serde_json::json!({"schema": "trustc.exact-vc-claim.v3",
                "semantics": {"overflow_checks": true, "target": target},
                "vc": expected_vc});
            let mut original = String::new();
            original_write(&claim, &mut original);
            assert_eq!(
                canonical_exact_vc_claim_payload(&vc, true, target).unwrap().as_bytes(),
                original.as_bytes()
            );
        }
    }

    #[test]
    fn deep_full_vc_and_sorts_refuse_before_recursive_capture_on_default_stack() {
        // No ambient stack override or big-stack worker. Intentionally forget
        // the adversarial inputs after refusal so their derived recursive Drop
        // cannot obscure which preflight this test exercises.
        std::thread::spawn(|| {
            use crate::{ObligationRecord, ObligationWrapper, PathGuardTerm, Sort};
            for role in ["violation", "body", "subject", "facts", "guards", "sort"] {
                let mut vc = vc();
                let deep = if role == "sort" {
                    let mut sort = Sort::Int;
                    for _ in 0..10_000 {
                        sort = Sort::Array(Box::new(Sort::Int), Box::new(sort));
                    }
                    Formula::Var("deep-sort".into(), sort)
                } else {
                    let mut f = Formula::Bool(false);
                    for _ in 0..10_000 {
                        f = Formula::Not(Box::new(f));
                    }
                    f
                };
                let mut record = ObligationRecord {
                    body: Formula::Bool(false),
                    wrappers: vec![],
                    subject: None,
                    width: None,
                };
                match role {
                    "violation" | "sort" => vc.formula = deep,
                    "body" => record.body = deep,
                    "subject" => record.subject = Some(deep),
                    "facts" => record
                        .wrappers
                        .push(ObligationWrapper::ConjoinFactsLast { facts: vec![deep] }),
                    _ => record.wrappers.push(ObligationWrapper::PathGuardOr {
                        paths: vec![PathGuardTerm::Guarded { guards: vec![deep] }],
                    }),
                }
                vc.obligation = Some(record);
                assert!(!snapshot_within_capture_bounds(&vc), "{role}");
                assert!(
                    OriginalVcSnapshot::capture(&vc, true, "target;ptr64", "row", &"0".repeat(64))
                        .is_none(),
                    "{role}"
                );
                std::mem::forget(vc);
            }
            let mut vc = vc();
            let mut ty = crate::Ty::u64();
            for _ in 0..10_000 {
                ty = crate::Ty::Ref { mutable: false, inner: Box::new(ty) };
            }
            vc.kind = VcKind::NegationOverflow { ty };
            assert!(
                bounded_original_vc_json(&vc).is_none(),
                "recursive kind Ty is bounded online before hashing"
            );
            assert!(
                OriginalVcSnapshot::capture(&vc, true, "target;ptr64", "row", &"0".repeat(64))
                    .is_none()
            );
            std::mem::forget(vc);
        })
        .join()
        .unwrap();
    }

    #[test]
    fn streaming_writer_bounds_nesting_nodes_bytes_and_handles_split_escapes() {
        use std::io::Write;
        let json = serde_json::to_vec(
            &serde_json::json!({"text": "quote\" slash\\ {[}] 雪", "array": [true]}),
        )
        .unwrap();
        let mut writer = SnapshotWriter::default();
        for byte in &json {
            writer.write_all(&[*byte]).unwrap();
        }
        assert_eq!(writer.bytes, json);
        assert_eq!(writer.depth, 0);
        assert_eq!(writer.nodes, 2, "braces in strings are not structures");
        let mut writer = SnapshotWriter::default();
        assert!(writer.write_all(&vec![b'['; MAX_SNAPSHOT_JSON_NESTING + 1]).is_err());
        let mut writer = SnapshotWriter::default();
        assert!(writer.write_all(&vec![b' '; ORIGINAL_VC_SNAPSHOT_MAX_BYTES + 1]).is_err());
        assert!(writer.bytes.is_empty());
        let mut writer = SnapshotWriter::default();
        writer.write_all(b"[").unwrap();
        for _ in 1..MAX_SNAPSHOT_NODES {
            writer.write_all(b"[]").unwrap();
        }
        assert!(writer.write_all(b"[]").is_err());
    }
}
