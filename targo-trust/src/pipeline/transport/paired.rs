//! Exact original-Unit replay transport for paired AY qualification. This is
//! deliberately separate from unscoped direct-rustc and Cargo JSON envelopes.
//! The caller must retain the actual admitted action/command/input owner.
use trust_types::{
    CoverageTransportSummary, CrateTransportSummary, FunctionTransportResult, TransportMessage,
};

use super::*;

pub(crate) struct PairedTransport {
    pub parsed: ParsedCompilerOutput,
    pub functions: Vec<FunctionTransportResult>,
    pub coverage: CoverageTransportSummary,
    pub summary: CrateTransportSummary,
}
pub(crate) fn parse(stderr: &[u8], expected_session: &str) -> Result<PairedTransport, String> {
    if stderr.len()
        > trust_resource_controller::paired_qualification::service::MAX_STREAM_BYTES as usize
        || expected_session.is_empty()
        || expected_session.len() > 256
    {
        return Err("paired compiler transport exceeds its finite stream/session bounds".into());
    }
    let text = std::str::from_utf8(stderr).map_err(|_| "paired compiler stderr is not UTF8")?;
    let mut functions = Vec::new();
    let mut summary = None;
    let mut coverage = None;
    for line in text.lines() {
        let Some(payload) = line.strip_prefix(trust_types::TRANSPORT_PREFIX) else { continue };
        // Check every object before the typed decoder ignores unknown fields;
        // decode the ORIGINAL bytes afterward, preserving i128/u128 payloads.
        serde_json::from_str::<unique::Document>(payload)
            .map_err(|error| format!("paired duplicate/malformed JSON: {error}"))?;
        let message = trust_types::parse_transport_payload(payload)
            .map_err(|error| format!("paired typed transport is malformed: {error}"))?;
        match message {
            TransportMessage::FunctionResult(function) => {
                if coverage.is_some() || summary.is_some() {
                    return Err("paired function followed coverage/terminal boundary".into());
                }
                check_scope(
                    function.package_name.as_deref(),
                    function.crate_name.as_deref(),
                    function.primary_package,
                    &function.verification_session,
                    expected_session,
                )?;
                let identities = crate::types::envelope_identities(&function);
                let normalized = function
                    .results
                    .iter()
                    .zip(identities)
                    .map(|(row, identity)| {
                        transport_to_verification_result(
                            &function.function,
                            row,
                            function.runtime_checks,
                            identity,
                        )
                    })
                    .collect::<Vec<_>>();
                if let Some(disclosure) = &function.transport_budget {
                    return Err(format!(
                        "paired function report was reduced by its transport budget: {disclosure:?}"
                    ));
                }
                if let Some(defect) = function_transport_summary_defect(&function, &normalized) {
                    return Err(defect);
                }
                // This new profile requires a current paired-capable SDK;
                // legacy missing split counters cannot stand in for zeros.
                let mut counts = FunctionTransportCounts::default();
                add_raw_transport_result_counts(&mut counts, &function.results);
                if counts.timed_out != function.timed_out || counts.skipped != function.skipped {
                    return Err("paired function lost exact timeout/skipped split counters".into());
                }
                functions.push(function);
            }
            TransportMessage::CoverageSummary(row) => {
                if coverage.is_some() || summary.is_some() {
                    return Err("paired coverage repeated or followed terminal boundary".into());
                }
                check_scope(
                    Some(&row.package_name),
                    Some(&row.crate_name),
                    row.primary_package,
                    &row.verification_session,
                    expected_session,
                )?;
                if !row.is_complete() || row.eligible == 0 {
                    return Err("paired function coverage is empty or incomplete".into());
                }
                coverage = Some(row);
            }
            TransportMessage::CrateSummary(row) => {
                if summary.is_some() || coverage.is_none() {
                    return Err("paired terminal repeated or preceded coverage boundary".into());
                }
                check_scope(
                    row.package_name.as_deref(),
                    Some(&row.crate_name),
                    row.primary_package,
                    &row.verification_session,
                    expected_session,
                )?;
                summary = Some(row);
            }
            // This profile has no lossy or unsupported transport fallback.
            _ => {
                return Err(
                    "paired verifier emitted a transport outside its declared census".into()
                );
            }
        }
    }
    let coverage = coverage.ok_or("paired compiler omitted exact coverage")?;
    let summary = summary.ok_or("paired compiler omitted actual terminal inventory")?;
    let parsed = parse_compiler_stderr(Cursor::new(stderr), false);
    if !parsed.raw_terminal_inventory_complete() {
        return Err("paired compiler transport has incomplete/reordered terminal inventory".into());
    }
    let parsed = parsed.require_coverage_function_identity_authentication(true)?;
    let mut observed = CrateTransportCounts::default();
    for function in &functions {
        observed.functions_analyzed += 1;
        if function.total > 0 && function.proved == function.total {
            observed.functions_verified += 1;
        }
        add_raw_transport_result_counts(&mut observed.obligations, &function.results);
    }
    if let Some(defect) = crate_transport_summary_defect(&summary, &observed) {
        return Err(defect);
    }
    if summary.total_timed_out != observed.obligations.timed_out
        || summary.total_skipped != observed.obligations.skipped
    {
        return Err("paired terminal lost exact timeout/skipped split counters".into());
    }
    if summary.total_obligations == 0 {
        return Err("paired AY obligation denominator is empty".into());
    }
    Ok(PairedTransport { parsed, functions, coverage, summary })
}
fn check_scope(
    package: Option<&str>,
    krate: Option<&str>,
    primary: bool,
    session: &str,
    expected: &str,
) -> Result<(), String> {
    if package != Some("ay-proof-common")
        || krate != Some("ay_proof_common")
        || !primary
        || session != expected
    {
        Err("paired verifier changed its original package/crate/primary/session binding".into())
    } else {
        Ok(())
    }
}

mod unique {
    use std::collections::BTreeSet;
    use std::fmt;

    use serde::de::{self, MapAccess, SeqAccess, Visitor};
    use serde::{Deserialize, Deserializer};
    pub(super) struct Document;
    impl<'de> Deserialize<'de> for Document {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            d.deserialize_any(Unique)
        }
    }
    struct Unique;
    impl<'de> Visitor<'de> for Unique {
        type Value = Document;
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("bounded duplicate-free original JSON")
        }
        fn visit_unit<E: de::Error>(self) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_bool<E: de::Error>(self, _: bool) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_i64<E: de::Error>(self, _: i64) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_u64<E: de::Error>(self, _: u64) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_f64<E: de::Error>(self, value: f64) -> Result<Document, E> {
            if value.is_finite() { Ok(Document) } else { Err(E::custom("nonfinite JSON number")) }
        }
        fn visit_str<E: de::Error>(self, _: &str) -> Result<Document, E> {
            Ok(Document)
        }
        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Document, A::Error> {
            while seq.next_element::<Document>()?.is_some() {}
            Ok(Document)
        }
        fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Document, A::Error> {
            let mut seen = BTreeSet::new();
            while let Some(key) = map.next_key::<String>()? {
                if !seen.insert(key) {
                    return Err(de::Error::custom("duplicate paired transport JSON key"));
                }
                map.next_value::<Document>()?;
            }
            Ok(Document)
        }
    }
}
