//! Source-bound disclosure of runtime work outside the logical bridge.
//!
//! These counters are metadata, never kernel facts or runtime certificates.

use std::collections::BTreeSet;
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

// Actual unsafe metadata from the immutable imported98/IR5e95 predecessor.
// These identities conserve obligations; they certify no runtime implementation.
const BASELINE: &[u8] =
    include_bytes!("../../data/runtime-frontier/runtime-boundary-baseline.json");
const BASELINE_ROOT: &str = "98e439cf1281e226c88448cbb24ebe9fbb07fab5";
const BASELINE_IR: &str = "5e950fbff8b1beb5f0a7388a30a124ab4be3d66a";
const BASELINE_SHA256: &str = "89d0b2f955f0204a4adcab51a305cee0fd20a1e524a9c69c7c8f24feec7493dc";
const COMPLETE_INVENTORY_SHA256: &str =
    "3d329ae9e3287c0a77b17223b7f6df1dbeb6c0ec32ead43c6f34ff9887fb1e6e";

/// The original imported declaration inventory and its open runtime frontier.
/// A successful logical bridge does not discharge any of these runtime rows.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeFrontier {
    pub baseline_imported_declarations: usize,
    pub baseline_logical_declarations: usize,
    pub unproved_runtime_implementations: usize,
    pub unproved_runtime_interfaces: usize,
    pub unproved_native_support_obligations: usize,
    pub source_ledger_schema: u64,
    pub source_ledger_sha256: String,
}

fn require(condition: bool, detail: &str) -> Result<(), String> {
    if condition { Ok(()) } else { Err(detail.to_owned()) }
}

fn text<'a>(row: &'a Value, field: &str) -> Result<&'a str, String> {
    row.get(field)
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty() && !s.chars().any(char::is_control))
        .ok_or_else(|| format!("missing or invalid runtime boundary field {field}"))
}

impl RuntimeFrontier {
    /// Parse an explicitly UNPROVED disclosure. This cannot mint authority.
    /// The baseline is the frozen imported inventory, not a claim that every
    /// Lean source declaration or extension entry was restored by the reader.
    pub fn from_source_bytes(bytes: &[u8]) -> Result<Self, String> {
        let doc: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        let schema = doc["schema"].as_u64().ok_or("missing runtime boundary schema")?;
        require(matches!(schema, 1 | 2), "unsupported runtime boundary schema")?;
        let baseline = &doc["baseline"];
        require(
            text(baseline, "root_subject")? == BASELINE_ROOT
                && text(baseline, "ir_source")? == BASELINE_IR
                && text(baseline, "roster_sha256")? == BASELINE_SHA256
                && format!("{:x}", Sha256::digest(BASELINE)) == BASELINE_SHA256,
            "original imported baseline descriptor was rebound",
        )?;
        require(
            baseline["total_obligations"].as_u64() == Some(7125)
                && baseline["logical_safe_obligations"].as_u64() == Some(7084)
                && baseline["runtime_unproved_obligations"].as_u64() == Some(41),
            "original imported declaration inventory was changed or dropped",
        )?;
        let implementations =
            doc["runtime_obligations"].as_array().ok_or("missing runtime obligations")?;
        let interfaces = doc["interfaces"].as_array().ok_or("missing runtime interfaces")?;
        require(
            implementations.len() == 41 && interfaces.len() == 15,
            "runtime implementation/interface census differs from the frozen baseline",
        )?;
        let mut originals = BTreeSet::new();
        let mut runtime = BTreeSet::new();
        let mut original_names = BTreeSet::new();
        let mut runtime_names = BTreeSet::new();
        for row in implementations {
            require(
                row["state"].as_str() == Some("UNPROVED")
                    && row["certified"].as_bool() == Some(false),
                "runtime metadata cannot certify an implementation",
            )?;
            require(
                text(row, "original_kind")? == "definition"
                    && text(row, "original_safety")? == "unsafe",
                "original runtime declaration kind or safety changed",
            )?;
            require(
                originals.insert((text(row, "original_module")?, text(row, "original_full_name")?)),
                "duplicate original runtime declaration identity",
            )?;
            require(
                runtime.insert((text(row, "runtime_module")?, text(row, "runtime_full_name")?)),
                "duplicate runtime implementation identity",
            )?;
            require(
                original_names.insert(text(row, "original_full_name")?),
                "duplicate original full Name across modules",
            )?;
            require(
                runtime_names.insert(text(row, "runtime_full_name")?),
                "duplicate runtime full Name across modules",
            )?;
        }
        let frozen: Value = serde_json::from_slice(BASELINE).map_err(|e| e.to_string())?;
        let frozen_rows = frozen["unsafe_declarations"]
            .as_array()
            .ok_or("missing frozen original declaration identities")?;
        let expected: BTreeSet<_> = frozen_rows
            .iter()
            .map(|row| Ok((text(row, "module")?, text(row, "name")?)))
            .collect::<Result<_, String>>()?;
        require(
            expected.len() == 41 && originals == expected,
            "original declaration identities differ from the frozen imported baseline",
        )?;
        let mut logical = BTreeSet::new();
        let mut logical_names = BTreeSet::new();
        let mut symbols = BTreeSet::new();
        for row in interfaces {
            require(
                row["correspondence"].as_str() == Some("UNPROVED")
                    && row["certified"].as_bool() == Some(false),
                "ABI metadata cannot certify runtime correspondence",
            )?;
            require(
                logical.insert((text(row, "logical_module")?, text(row, "logical_full_name")?)),
                "duplicate logical runtime interface",
            )?;
            require(
                logical_names.insert(text(row, "logical_full_name")?),
                "duplicate logical interface full Name across modules",
            )?;
            require(symbols.insert(text(row, "symbol")?), "duplicate runtime ABI symbol")?;
            require(
                runtime.contains(&(text(row, "runtime_module")?, text(row, "runtime_full_name")?)),
                "runtime interface provider is absent from the exact implementation census",
            )?;
            let provider = text(row, "runtime_provider")?;
            require(
                text(row, "runtime_full_name")?.rsplit('.').next() == Some(provider),
                "runtime interface provider differs from its exact full name",
            )?;
        }
        let support_count = native_support(&doc, schema)?;
        Ok(Self {
            baseline_imported_declarations: 7125,
            baseline_logical_declarations: 7084,
            unproved_runtime_implementations: implementations.len(),
            unproved_runtime_interfaces: interfaces.len(),
            unproved_native_support_obligations: support_count,
            source_ledger_schema: schema,
            source_ledger_sha256: format!("{:x}", Sha256::digest(bytes)),
        })
    }

    pub(super) fn read(repo: &Path, commit: &str) -> Result<Option<Self>, String> {
        trust_bridge_closure::read_runtime_boundary_input(repo, commit)
            .map_err(|e| e.to_string())?
            .map(|bytes| Self::from_source_bytes(&bytes))
            .transpose()
    }

    pub(crate) fn disclosure(&self) -> String {
        format!(
            "Runtime boundary: the baseline IMPORTED inventory of {} declarations comprises \
             {} logical declarations and {} runtime implementations that remain UNPROVED; \
             {} runtime interface correspondences also remain UNPROVED. Schema {} declares \
             {} additional UNPROVED native initialization/link/evaluation support obligations \
             (source ledger sha256 {}). Logical agreement does not certify these implementations, \
             native support, or emitted bytes.",
            self.baseline_imported_declarations,
            self.baseline_logical_declarations,
            self.unproved_runtime_implementations,
            self.unproved_runtime_interfaces,
            self.source_ledger_schema,
            self.unproved_native_support_obligations,
            self.source_ledger_sha256,
        )
    }
}

// This validates a disclosure, not the implementation or a native certificate.
// Keep each support identity and its source set exact: accepting missing or
// relabelled rows would silently shrink the displayed runtime boundary.
fn native_support(doc: &Value, schema: u64) -> Result<usize, String> {
    if schema == 1 {
        require(
            doc.get("native_attachment").is_none() && doc.get("support_obligations").is_none(),
            "schema 1 cannot hide native support outside its declared census",
        )?;
        return Ok(0);
    }
    require(
        text(&doc["baseline"], "scope")? == "imported_restored_declarations"
            && text(&doc["baseline"], "complete_inventory_sha256")? == COMPLETE_INVENTORY_SHA256,
        "native support baseline inventory was rebound",
    )?;
    let attachment = &doc["native_attachment"];
    for (field, expected) in [
        ("logical_module", "TrustIrNativeLink"),
        ("provider_module", "TrustIrRuntime"),
        ("activation_module", "TrustIr.Semantics.Eval"),
        ("initializer_symbol", "initialize_TrustIrNativeLink"),
        ("provider_initializer_symbol", "initialize_TrustIrRuntime"),
        ("initializer_source", "lean/trust_ir-semantics/native/runtime_init.c"),
    ] {
        require(text(attachment, field)? == expected, "native attachment identity changed")?;
    }
    let fixtures =
        attachment["fixture_modules"].as_array().ok_or("missing native fixture modules")?;
    let fixture_names: BTreeSet<_> = fixtures.iter().filter_map(Value::as_str).collect();
    require(
        fixtures.len() == 2
            && fixture_names
                == BTreeSet::from([
                    "TrustIr.Semantics.ExecutableFixtures",
                    "TrustIr.Semantics.FloatFixtures",
                ]),
        "native fixture module census changed",
    )?;
    // Exact selected IR970 support roster, including the native facet/header inputs.
    // Historical incomplete schema2 profiles are disclosure negatives, not alternatives.
    let expected: [(&str, &[&str]); 3] = [
        (
            "runtime-module-initialization",
            &[
                "lean/trust_ir-semantics/native/runtime_init.c",
                "lean/trust_ir-semantics/TrustIrRuntime.lean",
                "lean/trust_ir-semantics/lakefile.lean",
            ],
        ),
        (
            "native-only-lake-link",
            &[
                "lean/trust_ir-semantics/lakefile.lean",
                "lean/trust_ir-semantics/TrustIrNativeLink.lean",
                "lean/trust_ir-semantics/native/runtime_ffi.h",
            ],
        ),
        (
            "logical-fixture-native-evaluation",
            &["lean/trust_ir-semantics/TrustIr/Semantics/Eval.lean", "scripts/lean_proofs.py"],
        ),
    ];
    let rows = doc["support_obligations"].as_array().ok_or("missing native support obligations")?;
    require(rows.len() == expected.len(), "native support obligation census changed")?;
    let mut ids = BTreeSet::new();
    for row in rows {
        let id = text(row, "id")?;
        require(ids.insert(id), "duplicate native support identity")?;
        require(
            row["state"].as_str() == Some("UNPROVED") && row["certified"].as_bool() == Some(false),
            "native support metadata cannot certify an implementation",
        )?;
        text(row, "role")?;
        let (_, inputs) = expected
            .iter()
            .find(|(name, _)| *name == id)
            .ok_or("unknown native support identity")?;
        let actual =
            row["source_inputs"].as_array().ok_or("missing native support source inputs")?;
        let paths: BTreeSet<_> = actual.iter().filter_map(Value::as_str).collect();
        require(
            actual.len() == inputs.len() && paths == inputs.iter().copied().collect(),
            "native support source inputs changed",
        )?;
    }
    Ok(rows.len())
}
