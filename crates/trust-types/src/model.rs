// trust-types/model.rs: MIR-level verification model
//
// These types represent a function extracted from rustc's MIR, simplified
// for verification. Only trust-mir-extract creates these; everything
// downstream consumes them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, VecDeque};

use serde::{Deserialize, Serialize};

use crate::Formula;
use crate::digest::{stable_sha256_hex, stable_sha256_hex_parts};
use crate::spec::FunctionSpec;

const LOWERED_COMPILER_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";

/// Serialize Trust model material for stable semantic hashing.
///
/// `Ty::Adt::faithful_enum_repr` was added after content-hash pins had already
/// shipped. Its outer `None` carries exactly the historical flattened-struct
/// meaning, so hashing that default would invalidate caches and audited pins
/// without changing semantics. Keep the ordinary Serde wire complete (binary
/// formats require a fixed field sequence) and omit only that default JSON
/// member from hash material. `disc_index_safe` predates these pins and remains
/// hash-visible. JSON string contents cannot collide with this member fragment:
/// embedded quotes are escaped, and the name is reserved to `Ty::Adt`.
fn stable_model_json<T>(value: &T) -> Result<String, serde_json::Error>
where
    T: Serialize + ?Sized,
{
    let json = serde_json::to_string(value)?;
    // Trust (B3-4 T3): `layout` follows the same discipline — its `None` is
    // exactly the pre-T3 semantics, so the default must not perturb shipped
    // content-hash pins. A `Some` layout IS hash-visible (it asserts concrete
    // bytes and belongs in identity).
    // Trust (B3-3): `enum_layout` joins the same rule — `None` is exactly the
    // pre-B3-3 semantics (must not perturb shipped pins); a `Some` IS
    // hash-visible (it asserts concrete bytes and belongs in identity).
    // Trust: W19 — `adt_kind` follows the SAME discipline: its `None` is exactly
    // the pre-W19 (un-migrated) semantics; a `Some(kind)` IS hash-visible.
    Ok(json
        .replace(",\"faithful_enum_repr\":null", "")
        .replace(",\"layout\":null", "")
        .replace(",\"enum_layout\":null", "")
        .replace(",\"adt_kind\":null", ""))
}

/// Legacy formula-only digest. This deliberately omits source variable
/// domains and therefore must never authorize a proof or executable monitor.
/// Use [`typed_contract_proposition_digest`] for compiler propositions.
#[deprecated(
    note = "formula-only and signature-blind; use typed_contract_proposition_digest for authority"
)]
#[must_use]
pub fn typed_contract_formula_digest(formula: &Formula) -> String {
    let bytes = serde_json::to_vec(formula).expect(
        "Formula is the canonical serializable Trust proposition; refusing a debug fallback",
    );
    let mut material = b"trust.compiler-contract.typed-proposition.v1\0".to_vec();
    material.extend_from_slice(&bytes);
    format!("sha256:{}", stable_sha256_hex(&material))
}

/// Structural identity for a compiler proposition including the exact source
/// domain of every free variable.  `Formula` deliberately models primitive
/// integer contracts in mathematical `Int`; the sidecar prevents that useful
/// abstraction from making `u8`, `u16`, and signed signatures monitor-equivalent.
#[must_use]
pub fn typed_contract_proposition_digest(
    formula: &Formula,
    variable_domains: &[CompilerContractVariableDomain],
) -> String {
    let bytes = serde_json::to_vec(&(formula, variable_domains)).expect(
        "compiler proposition identity is canonical serializable Trust data; refusing a debug fallback",
    );
    let mut material = b"trust.compiler-contract.typed-proposition.v2\0".to_vec();
    material.extend_from_slice(&bytes);
    format!("sha256:{}", stable_sha256_hex(&material))
}

/// Compute a stable non-zero 32-bit id over stable byte material.
///
/// This is used at schema boundaries that only expose compact numeric handles
/// while the canonical source/assertion identity remains a string.
#[must_use]
pub fn stable_u32_id(bytes: &[u8]) -> u32 {
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(bytes);
    let value = u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]]);
    if value == 0 { 1 } else { value }
}

const MAX_DIRECT_CONTRACT_FUNCTION_COMPONENT_BYTES: usize = 900;
const MAX_DIRECT_CONTRACT_KIND_COMPONENT_BYTES: usize = 64;
const MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES: usize = 384;

/// Encode an arbitrary logical name as one collision-resistant artifact-ID
/// component while preserving the historical spelling of ordinary Rust paths.
///
/// Ordinary paths made from alphanumerics, unambiguous single underscores,
/// and `::` keep their historical spelling (`::` becomes `__`). Inputs whose
/// old spelling could collide enter the reserved `h0_` escape namespace:
/// `_` becomes `_u` and every other non-alphanumeric UTF-8 byte becomes
/// `_xhh`. Oversized values use the `h1_` domain-separated hash namespace;
/// that fallback is collision-resistant rather than mathematically injective.
#[must_use]
pub fn canonical_artifact_id_component(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    if value.is_empty() {
        return "_e".to_string();
    }

    let bytes = value.as_bytes();
    if bytes.len() <= MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES
        && let Some(legacy) = unambiguous_legacy_artifact_component(bytes)
        && legacy.len() <= MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES
    {
        return legacy;
    }

    if bytes.len() <= MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES {
        let mut encoded = String::with_capacity(bytes.len().saturating_add(3));
        encoded.push_str("h0_");
        let mut index = 0;
        while index < bytes.len() && encoded.len() <= MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES {
            let byte = bytes[index];
            if byte == b':' && bytes.get(index + 1) == Some(&b':') {
                encoded.push_str("__");
                index += 2;
                continue;
            }
            if byte.is_ascii_alphanumeric() {
                encoded.push(char::from(byte));
            } else if byte == b'_' {
                encoded.push_str("_u");
            } else {
                encoded.push_str("_x");
                encoded.push(char::from(HEX[(byte >> 4) as usize]));
                encoded.push(char::from(HEX[(byte & 0x0f) as usize]));
            }
            index += 1;
        }
        if encoded.len() <= MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES {
            return encoded;
        }
    }

    let length = (bytes.len() as u64).to_be_bytes();
    let digest = stable_sha256_hex_parts(&[
        b"trust.artifact-id-component.v1\0",
        &length,
        bytes,
    ]);
    format!("h1_{:016x}_{}", bytes.len(), digest)
}

fn unambiguous_legacy_artifact_component(bytes: &[u8]) -> Option<String> {
    let mut encoded = String::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte.is_ascii_alphanumeric() {
            encoded.push(char::from(byte));
            index += 1;
            continue;
        }
        if byte == b'_' {
            if matches!(bytes.get(index.wrapping_sub(1)).copied(), Some(b'_' | b':'))
                || matches!(bytes.get(index + 1).copied(), Some(b'_' | b':'))
            {
                return None;
            }
            encoded.push('_');
            index += 1;
            continue;
        }
        if byte == b':' && bytes.get(index + 1) == Some(&b':') {
            if matches!(bytes.get(index.wrapping_sub(1)).copied(), Some(b'_' | b':'))
                || matches!(bytes.get(index + 2).copied(), Some(b'_' | b':'))
            {
                return None;
            }
            encoded.push_str("__");
            index += 2;
            continue;
        }
        return None;
    }
    if encoded == "_e" || encoded.starts_with("h0_") || encoded.starts_with("h1_") {
        return None;
    }
    Some(encoded)
}

/// Return the canonical, artifact-safe spelling of a contract's function path.
///
/// Ordinary Rust def-paths remain byte-for-byte unchanged. Bytes that are not
/// accepted by the verifier artifact schema, and `%` itself, use uppercase
/// UTF-8 percent encoding. Escaping `%` makes the representation injective for
/// every directly encoded path. Oversized paths use a domain-separated digest
/// spelling; its `%~` marker cannot be produced by direct percent encoding.
#[must_use]
pub fn canonical_contract_function_component(function_def_path: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(
        function_def_path.len().min(MAX_DIRECT_CONTRACT_FUNCTION_COMPONENT_BYTES + 1),
    );
    for byte in function_def_path.bytes() {
        if byte.is_ascii_graphic() && !matches!(byte, b'%' | b'?' | b'#') {
            encoded.push(char::from(byte));
        } else {
            encoded.push('%');
            encoded.push(char::from(HEX[(byte >> 4) as usize]));
            encoded.push(char::from(HEX[(byte & 0x0f) as usize]));
        }
        if encoded.len() > MAX_DIRECT_CONTRACT_FUNCTION_COMPONENT_BYTES {
            break;
        }
    }
    if encoded.len() <= MAX_DIRECT_CONTRACT_FUNCTION_COMPONENT_BYTES {
        return encoded;
    }

    format!(
        "%~sha256~{}",
        stable_sha256_hex_parts(&[
            b"trust.contract.function-def-path.v1\0",
            function_def_path.as_bytes(),
        ]),
    )
}

fn canonical_contract_kind_component(contract_kind: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(
        contract_kind.len().min(MAX_DIRECT_CONTRACT_KIND_COMPONENT_BYTES + 1),
    );
    for byte in contract_kind.bytes() {
        if byte.is_ascii_alphanumeric() || byte == b'_' {
            encoded.push(char::from(byte));
        } else {
            encoded.push('%');
            encoded.push(char::from(HEX[(byte >> 4) as usize]));
            encoded.push(char::from(HEX[(byte & 0x0f) as usize]));
        }
        if encoded.len() > MAX_DIRECT_CONTRACT_KIND_COMPONENT_BYTES {
            break;
        }
    }
    if encoded.len() <= MAX_DIRECT_CONTRACT_KIND_COMPONENT_BYTES {
        return encoded;
    }

    let length = (contract_kind.len() as u64).to_be_bytes();
    format!(
        "%~sha256~{}",
        stable_sha256_hex_parts(&[
            b"trust.contract.kind.v1\0",
            &length,
            contract_kind.as_bytes(),
        ]),
    )
}

/// Construct the one canonical public source id for a compiler contract.
///
/// Keeping this constructor in `trust-types` makes extraction, lowering, and
/// compiler-private monitor matching share exactly the same path encoding.
#[must_use]
pub fn canonical_contract_source_id(
    function_def_path: &str,
    contract_kind: &str,
    contract_index: usize,
) -> String {
    let encoded_kind = canonical_contract_kind_component(contract_kind);
    format!(
        "trust-contract:{}:{encoded_kind}:{contract_index}",
        canonical_contract_function_component(function_def_path)
    )
}

/// Recover a dense contract index only from a syntactically canonical source
/// ID. This is intentionally stricter than taking the final numeric suffix:
/// malformed public metadata must not poison a compiler monitor's dense-index
/// ambiguity inventory.
#[must_use]
pub fn canonical_contract_source_index(contract_id: &str) -> Option<usize> {
    let rest = contract_id.strip_prefix("trust-contract:")?;
    let (path_and_kind, index_text) = rest.rsplit_once(':')?;
    let index = index_text.parse::<usize>().ok()?;
    if index.to_string() != index_text {
        return None;
    }
    let (path, kind) = path_and_kind.rsplit_once(':')?;
    if !matches!(
        kind,
        "requires"
            | "ensures"
            | "invariant"
            | "loop_invariant"
            | "decreases"
            | "assumes"
            | "asserts"
            | "refine"
            | "temporal"
            | "modifies"
    ) || !canonical_contract_function_component_syntax(path)
    {
        return None;
    }
    Some(index)
}

fn canonical_contract_function_component_syntax(component: &str) -> bool {
    if component.is_empty() || component.len() > MAX_DIRECT_CONTRACT_FUNCTION_COMPONENT_BYTES {
        return false;
    }
    if let Some(digest) = component.strip_prefix("%~sha256~") {
        return digest.len() == 64
            && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte));
    }

    let bytes = component.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte == b'%' {
            let Some(high) = bytes.get(index + 1).copied() else { return false };
            let Some(low) = bytes.get(index + 2).copied() else { return false };
            let Some(high) = uppercase_hex_value(high) else { return false };
            let Some(low) = uppercase_hex_value(low) else { return false };
            decoded.push((high << 4) | low);
            index += 3;
            continue;
        }
        if !byte.is_ascii_graphic() || matches!(byte, b'?' | b'#') {
            return false;
        }
        decoded.push(byte);
        index += 1;
    }
    String::from_utf8(decoded)
        .ok()
        .is_some_and(|decoded| canonical_contract_function_component(&decoded) == component)
}

fn uppercase_hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

/// A function extracted for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiableFunction {
    pub name: String,
    pub def_path: String,
    pub span: SourceSpan,
    pub body: VerifiableBody,
    pub contracts: Vec<Contract>,
    // Parsed spec formulas from #[requires] and #[ensures] attributes.
    // Populated by trust-mir-extract using spec_parse::parse_spec_expr.
    #[serde(default)]
    pub preconditions: Vec<Formula>,
    #[serde(default)]
    pub postconditions: Vec<Formula>,
    // Structured spec representation from #[requires], #[ensures],
    // #[invariant] attributes. Bridges compiler attribute parsing to the
    // verification pipeline's FunctionSpec/ContractMetadata types.
    #[serde(default)]
    pub spec: FunctionSpec,
}

impl VerifiableFunction {
    /// Compute a stable content hash of the function body for caching.
    ///
    /// Uses SHA-256 over the serde_json serialization of the body, contracts,
    /// preconditions, postconditions, and spec. The hash is deterministic across
    /// Rust versions (unlike `DefaultHasher`). Name and span are intentionally
    /// excluded — the cache keys by def_path separately.
    ///
    /// This is the single source of truth for content hashing. The free function
    /// `trust_cache::compute_content_hash()` delegates to this method.
    #[must_use]
    pub fn content_hash(&self) -> String {
        self.try_content_hash().expect(
            "VerifiableFunction contains only the canonical serializable Trust model; \
             refusing to manufacture cache identity after serialization failure",
        )
    }

    /// Fallible form of [`Self::content_hash`].
    ///
    /// Cache and certificate callers that can propagate an error should prefer
    /// this API.  The compatibility wrapper deliberately panics on an internal
    /// serialization bug instead of hashing empty fallback strings: two failed
    /// serializations must never collapse to the same proof/cache identity.
    pub fn try_content_hash(&self) -> Result<String, serde_json::Error> {
        use sha2::{Digest, Sha256};
        let body_json = stable_model_json(&self.body)?;
        let contracts_json = stable_model_json(&self.contracts)?;
        let pre_json = stable_model_json(&self.preconditions)?;
        let post_json = stable_model_json(&self.postconditions)?;
        let spec_json = stable_model_json(&self.spec)?;
        let mut hasher = Sha256::new();
        hasher.update(body_json.as_bytes());
        hasher.update(b":");
        hasher.update(contracts_json.as_bytes());
        hasher.update(b":");
        hasher.update(pre_json.as_bytes());
        hasher.update(b":");
        hasher.update(post_json.as_bytes());
        hasher.update(b":");
        hasher.update(spec_json.as_bytes());
        Ok(format!("{:x}", hasher.finalize()))
    }
}

/// MIR body simplified for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiableBody {
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BasicBlock>,
    pub arg_count: usize,
    pub return_ty: Ty,
}

impl VerifiableBody {
    /// Discover guarded clauses encoded by block terminators.
    pub fn discovered_clauses(&self) -> Vec<DiscoveredClause> {
        self.blocks.iter().flat_map(BasicBlock::discovered_clauses).collect()
    }

    /// Build a bounded path map from the entry block to each reachable block.
    ///
    /// This first slice keeps the first discovered conjunction of guards for
    /// each block instead of a full disjunction of all possible paths. That is
    /// enough to support lightweight reachability queries and proof reporting
    /// without exploding path count.
    pub fn path_map(&self) -> Vec<PathMapEntry> {
        if self.blocks.is_empty() {
            return vec![];
        }

        let mut discovered: Vec<Option<PathMapEntry>> = vec![None; self.blocks.len()];
        let mut queue = VecDeque::from([(BlockId(0), Vec::<GuardCondition>::new())]);

        while let Some((block, guards)) = queue.pop_front() {
            let Some(bb) = self.blocks.get(block.0) else {
                continue;
            };

            if discovered[block.0].is_some() {
                continue;
            }

            discovered[block.0] = Some(PathMapEntry {
                block,
                guards: guards.clone(),
                exits: bb.terminator.exit_targets(),
            });

            for guarded in bb.terminator.discovered_clauses(block) {
                if let ClauseTarget::Block(target) = guarded.target {
                    let mut next_guards = guards.clone();
                    next_guards.push(guarded.guard);
                    queue.push_back((target, next_guards));
                }
            }

            for target in bb.terminator.unguarded_successors() {
                queue.push_back((target, guards.clone()));
            }
        }

        discovered.into_iter().flatten().collect()
    }
}

/// A local variable declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalDecl {
    pub index: usize,
    pub ty: Ty,
    pub name: Option<String>,
}

/// Source location.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: String,
    pub line_start: u32,
    pub col_start: u32,
    pub line_end: u32,
    pub col_end: u32,
}

impl SourceSpan {
    /// Create a compatibility source span for a binary instruction address.
    ///
    /// Binary-mode code also carries typed [`BinaryOrigin`] sidecars. The
    /// `binary:0x...` file form keeps older diagnostics and serializers useful.
    #[must_use]
    pub fn binary_address(address: u64) -> Self {
        Self {
            file: format!("binary:0x{address:x}"),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        }
    }

    /// Extract a binary address from the compatibility `binary:0x...` form.
    #[must_use]
    pub fn binary_address_value(&self) -> Option<u64> {
        self.file.strip_prefix("binary:0x").and_then(|hex| u64::from_str_radix(hex, 16).ok())
    }

    /// True when this span points at binary provenance rather than a source file.
    #[must_use]
    pub fn is_binary(&self) -> bool {
        self.binary_address_value().is_some()
    }
}

/// Proof trust level for generated artifacts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Every instruction in the trusted slice is modeled and required VCs hold.
    ProofGrade,
    /// Useful artifact with explicit unknowns, unsupported pieces, or assumptions.
    #[default]
    Partial,
    /// Human-readable analysis aid only.
    Exploratory,
    /// The requested operation could not be safely performed.
    Rejected,
}

/// A single assumption made by a proof or binary analysis stage.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModelAssumption {
    pub stage: String,
    pub description: String,
}

/// Machine-code origin for a lifted TrustIr artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinaryOrigin {
    pub binary_path: Option<String>,
    pub function_entry: Option<u64>,
    pub instruction_address: u64,
    pub instruction_size: Option<u8>,
    pub encoding: Option<u32>,
    #[serde(default)]
    pub instruction_bytes: Vec<u8>,
    pub source: Option<SourceSpan>,
}

impl BinaryOrigin {
    #[must_use]
    pub fn span(&self) -> SourceSpan {
        self.source.clone().unwrap_or_else(|| SourceSpan::binary_address(self.instruction_address))
    }

    /// Fail-closed blockers for proof-grade instruction-byte provenance.
    ///
    /// Serde still accepts older artifacts that omitted byte identity fields; this
    /// helper gives proof-grade consumers a stable diagnostic surface instead of
    /// treating defaulted fields as exact provenance.
    #[must_use]
    pub fn canonical_provenance_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        if self.binary_path.as_ref().is_none_or(|path| path.trim().is_empty()) {
            blockers.push("missing binary path".to_string());
        }
        if self.function_entry.is_none() {
            blockers.push("missing function entry address".to_string());
        }

        match self.instruction_size {
            Some(0) => blockers.push("instruction size is zero".to_string()),
            Some(size) => {
                let instruction_byte_count = self.instruction_bytes.len();
                if instruction_byte_count == 0 {
                    blockers.push("missing instruction bytes".to_string());
                } else if usize::from(size) != instruction_byte_count {
                    blockers.push(format!(
                        "instruction size {size} does not match {} instruction byte(s)",
                        instruction_byte_count
                    ));
                }
            }
            None => blockers.push("missing instruction size".to_string()),
        }

        if let Some(source) = &self.source
            && source.file.starts_with("binary:")
            && source.binary_address_value() != Some(self.instruction_address)
        {
            blockers.push("binary source span does not match instruction address".to_string());
        }

        blockers
    }

    #[must_use]
    pub fn canonical_provenance_allows_proof_grade(&self) -> bool {
        self.canonical_provenance_blockers().is_empty()
    }
}

/// Unsupported item encountered while lifting, verifying, or decompiling.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UnsupportedRecord {
    pub stage: String,
    pub architecture: Option<String>,
    pub origin: Option<BinaryOrigin>,
    pub opcode: Option<String>,
    pub operand: Option<String>,
    pub feature: String,
}

pub const UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY: &str = "binary.aarch64.exception_boundary";
pub const UNSUPPORTED_FAMILY_AARCH64_CONTROL_FLOW_BOUNDARY: &str =
    "binary.aarch64.control_flow_boundary";
pub const UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY: &str =
    "binary.aarch64.memory_order_boundary";
pub const UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY: &str =
    "binary.replay.instruction_identity";
pub const UNSUPPORTED_FAMILY_BINARY_REPLAY_CONTROL_FLOW: &str = "binary.replay.control_flow";
pub const UNSUPPORTED_FAMILY_BINARY_REPLAY_UNSUPPORTED_MACHINE_SEMANTICS: &str =
    "binary.replay.unsupported_machine_semantics";
pub const UNSUPPORTED_FAMILY_UNCLASSIFIED: &str = "unsupported.unclassified";

impl UnsupportedRecord {
    #[must_use]
    pub fn family_tag(&self) -> &'static str {
        let text = unsupported_record_audit_text(self);
        let is_replay = unsupported_record_stage_is(self, "replay") || text.contains("replay");

        if is_replay && contains_any(&text, &["instruction identity", "instruction bytes"]) {
            return UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY;
        }
        if is_replay
            && contains_any(
                &text,
                &[
                    "unsupported control flow",
                    "direct call",
                    "indirect call",
                    "indirect branch",
                    "return",
                ],
            )
        {
            return UNSUPPORTED_FAMILY_BINARY_REPLAY_CONTROL_FLOW;
        }
        if is_replay
            && contains_any(
                &text,
                &[
                    "unsupported machine semantics",
                    "unsupported_machine_semantics",
                    "unsupported architecture",
                ],
            )
        {
            return UNSUPPORTED_FAMILY_BINARY_REPLAY_UNSUPPORTED_MACHINE_SEMANTICS;
        }

        if unsupported_record_arch_is_aarch64(self, &text) {
            if contains_any(&text, &["exception", "trap", "svc", "hvc", "smc", "brk"]) {
                return UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY;
            }
            if contains_any(
                &text,
                &[
                    "unsupported control flow",
                    "control-flow",
                    "control flow",
                    "direct call",
                    "indirect call",
                    "indirect branch",
                    "non-link register return",
                    "return",
                    " ret",
                    " br",
                    " bl",
                ],
            ) {
                return UNSUPPORTED_FAMILY_AARCH64_CONTROL_FLOW_BOUNDARY;
            }
            if contains_any(
                &text,
                &[
                    "memory-order",
                    "memory order",
                    "ordering boundary",
                    "barrier",
                    "atomic",
                    "exclusive",
                    "dmb",
                    "dsb",
                    "isb",
                    "ldxr",
                    "stxr",
                    "ldaxr",
                    "stlxr",
                ],
            ) {
                return UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY;
            }
        }

        UNSUPPORTED_FAMILY_UNCLASSIFIED
    }

    /// Recover a typed AArch64 atomic/exclusive semantic fact from a fail-closed
    /// unsupported record.
    ///
    /// These facts are a scaffold for downstream proof consumers. Deriving one
    /// from the unsupported ledger does not discharge the ledger item: proof
    /// gates must continue to reject until a consumer models the listed
    /// witnesses and removes or proves the corresponding unsupported record.
    #[must_use]
    pub fn aarch64_atomic_semantic_fact(&self) -> Option<Aarch64AtomicSemanticFact> {
        let audit_text = unsupported_record_audit_text(self);
        if !unsupported_record_arch_is_aarch64(self, &audit_text)
            || self.family_tag() != UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY
        {
            return None;
        }

        let opcode = self.opcode.as_deref()?.to_ascii_lowercase();
        let (access, ordering, exclusive_monitor, reports_status, witnesses) = match opcode.as_str()
        {
            "ldar" => (
                MemoryAccessKind::Read,
                MemoryOrderingSemantics::Acquire,
                Aarch64ExclusiveMonitorSemantics::None,
                false,
                vec![
                    "acquire ordering event",
                    "synchronization edge",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            "stlr" => (
                MemoryAccessKind::Write,
                MemoryOrderingSemantics::Release,
                Aarch64ExclusiveMonitorSemantics::None,
                false,
                vec![
                    "release ordering event",
                    "synchronization edge",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            "ldxr" => (
                MemoryAccessKind::Read,
                MemoryOrderingSemantics::Relaxed,
                Aarch64ExclusiveMonitorSemantics::LoadReserve,
                false,
                vec![
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "thread identity",
                ],
            ),
            "stxr" => (
                MemoryAccessKind::Write,
                MemoryOrderingSemantics::Relaxed,
                Aarch64ExclusiveMonitorSemantics::StoreConditional,
                true,
                vec![
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "store-conditional status result",
                    "thread identity",
                ],
            ),
            "ldaxr" => (
                MemoryAccessKind::Read,
                MemoryOrderingSemantics::Acquire,
                Aarch64ExclusiveMonitorSemantics::LoadReserve,
                false,
                vec![
                    "acquire ordering event",
                    "synchronization edge",
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            "stlxr" => (
                MemoryAccessKind::Write,
                MemoryOrderingSemantics::Release,
                Aarch64ExclusiveMonitorSemantics::StoreConditional,
                true,
                vec![
                    "release ordering event",
                    "synchronization edge",
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "store-conditional status result",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            _ => return None,
        };

        Some(Aarch64AtomicSemanticFact {
            origin: self.origin.clone(),
            opcode: self.opcode.clone().unwrap_or_else(|| opcode.to_ascii_uppercase()),
            operand: self.operand.clone(),
            access,
            ordering,
            exclusive_monitor,
            reports_status,
            missing_witnesses: witnesses.into_iter().map(str::to_string).collect(),
            consumed_by_proof_model: false,
        })
    }

    /// Recover a typed AArch64 barrier/monitor-clear fact from a fail-closed
    /// unsupported record. The recovered fact is evidence for downstream
    /// consumers, not a proof discharge.
    #[must_use]
    pub fn aarch64_sync_boundary_semantic_fact(&self) -> Option<Aarch64SyncBoundarySemanticFact> {
        let audit_text = unsupported_record_audit_text(self);
        if !unsupported_record_arch_is_aarch64(self, &audit_text)
            || self.family_tag() != UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY
        {
            return None;
        }

        let opcode = self.opcode.as_deref()?.to_ascii_lowercase();
        let operand_text = self.operand.as_deref().unwrap_or_default().to_ascii_lowercase();
        let feature_text = self.feature.to_ascii_lowercase();
        let (kind, scope, ordering, clears_exclusive_monitor) = match opcode.as_str() {
            "dmb" => (
                Aarch64SyncBoundaryKind::DataMemoryBarrier,
                aarch64_sync_scope_from_text(&feature_text, &operand_text),
                aarch64_data_sync_ordering_from_text(&feature_text, &operand_text),
                false,
            ),
            "dsb" => (
                Aarch64SyncBoundaryKind::DataSynchronizationBarrier,
                aarch64_sync_scope_from_text(&feature_text, &operand_text),
                aarch64_data_sync_ordering_from_text(&feature_text, &operand_text),
                false,
            ),
            "isb" => (
                Aarch64SyncBoundaryKind::InstructionSynchronizationBarrier,
                aarch64_sync_scope_from_text(&feature_text, &operand_text),
                Aarch64SyncOrdering::InstructionStream,
                false,
            ),
            "clrex" => (
                Aarch64SyncBoundaryKind::ClearExclusiveMonitor,
                Aarch64SyncScope::Local,
                Aarch64SyncOrdering::None,
                true,
            ),
            _ => return None,
        };

        Some(Aarch64SyncBoundarySemanticFact {
            origin: self.origin.clone(),
            opcode: self.opcode.clone().unwrap_or_else(|| opcode.to_ascii_uppercase()),
            operand: self.operand.clone(),
            kind,
            scope,
            ordering,
            clears_exclusive_monitor,
            raw_option: parse_aarch64_raw_option(&self.feature),
            missing_witnesses: aarch64_sync_missing_witnesses(kind),
            consumed_by_proof_model: false,
        })
    }
}

/// Collection of unsupported records for an artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UnsupportedLedger {
    pub records: Vec<UnsupportedRecord>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UnsupportedFamilyCount {
    pub family: String,
    pub count: usize,
}

impl UnsupportedLedger {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    #[must_use]
    pub fn family_counts(&self) -> BTreeMap<String, usize> {
        let mut counts = BTreeMap::new();
        for record in &self.records {
            *counts.entry(record.family_tag().to_string()).or_insert(0) += 1;
        }
        counts
    }

    #[must_use]
    pub fn family_count(&self, family: &str) -> usize {
        self.records.iter().filter(|record| record.family_tag() == family).count()
    }

    #[must_use]
    pub fn family_count_rows(&self) -> Vec<UnsupportedFamilyCount> {
        self.family_counts()
            .into_iter()
            .map(|(family, count)| UnsupportedFamilyCount { family, count })
            .collect()
    }

    /// Typed AArch64 memory-order/exclusive facts derivable from fail-closed
    /// unsupported records in this ledger.
    #[must_use]
    pub fn aarch64_atomic_semantic_facts(&self) -> Vec<Aarch64AtomicSemanticFact> {
        self.records.iter().filter_map(UnsupportedRecord::aarch64_atomic_semantic_fact).collect()
    }

    /// Typed AArch64 synchronization-boundary facts derivable from fail-closed
    /// unsupported records in this ledger.
    #[must_use]
    pub fn aarch64_sync_boundary_semantic_facts(&self) -> Vec<Aarch64SyncBoundarySemanticFact> {
        self.records
            .iter()
            .filter_map(UnsupportedRecord::aarch64_sync_boundary_semantic_fact)
            .collect()
    }
}

fn unsupported_record_stage_is(record: &UnsupportedRecord, stage: &str) -> bool {
    record.stage.eq_ignore_ascii_case(stage)
}

fn unsupported_record_arch_is_aarch64(record: &UnsupportedRecord, audit_text: &str) -> bool {
    record.architecture.as_ref().is_some_and(|architecture| {
        let architecture = architecture.to_ascii_lowercase();
        architecture == "aarch64" || architecture == "arm64" || architecture == "armv8"
    }) || audit_text.contains("aarch64")
}

fn unsupported_record_audit_text(record: &UnsupportedRecord) -> String {
    let mut text = String::new();
    append_audit_text(&mut text, Some(record.stage.as_str()));
    append_audit_text(&mut text, record.architecture.as_deref());
    append_audit_text(&mut text, record.opcode.as_deref());
    append_audit_text(&mut text, record.operand.as_deref());
    append_audit_text(&mut text, Some(record.feature.as_str()));
    text
}

fn append_audit_text(text: &mut String, value: Option<&str>) {
    if let Some(value) = value {
        text.push(' ');
        text.push_str(&value.to_ascii_lowercase());
    }
}

fn contains_any(haystack: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| haystack.contains(needle))
}

fn parse_aarch64_raw_option(feature: &str) -> Option<u8> {
    let start = feature.find("raw_option=")?;
    let rest = &feature[start + "raw_option=".len()..];
    let token = rest
        .split(|ch: char| ch == ';' || ch == ',' || ch.is_whitespace())
        .next()
        .unwrap_or("")
        .trim();
    if token.is_empty() || token.eq_ignore_ascii_case("none") {
        return None;
    }

    token
        .strip_prefix("0x")
        .or_else(|| token.strip_prefix("0X"))
        .map_or_else(|| token.parse::<u8>().ok(), |hex| u8::from_str_radix(hex, 16).ok())
}

fn aarch64_sync_scope_from_text(feature: &str, operand: &str) -> Aarch64SyncScope {
    if feature.contains("scope=outershareable") || operand.contains("osh") {
        Aarch64SyncScope::OuterShareable
    } else if feature.contains("scope=nonshareable") || operand.contains("nsh") {
        Aarch64SyncScope::NonShareable
    } else if feature.contains("scope=innershareable") || operand.contains("ish") {
        Aarch64SyncScope::InnerShareable
    } else if feature.contains("scope=local") {
        Aarch64SyncScope::Local
    } else {
        Aarch64SyncScope::FullSystem
    }
}

fn aarch64_data_sync_ordering_from_text(feature: &str, operand: &str) -> Aarch64SyncOrdering {
    if feature.contains("ordering=loadsandstores") || operand.contains("full") {
        Aarch64SyncOrdering::LoadsAndStores
    } else if feature.contains("ordering=loads") || operand.contains("load") {
        Aarch64SyncOrdering::Loads
    } else if feature.contains("ordering=stores") || operand.contains("store") {
        Aarch64SyncOrdering::Stores
    } else {
        Aarch64SyncOrdering::LoadsAndStores
    }
}

fn aarch64_sync_missing_witnesses(kind: Aarch64SyncBoundaryKind) -> Vec<String> {
    let witnesses: &[&str] = match kind {
        Aarch64SyncBoundaryKind::DataMemoryBarrier
        | Aarch64SyncBoundaryKind::DataSynchronizationBarrier => &[
            "barrier ordering event",
            "shareability scope propagation",
            "memory-system visibility/completion",
            "happens-before witness",
        ],
        Aarch64SyncBoundaryKind::InstructionSynchronizationBarrier => &[
            "instruction-stream synchronization event",
            "context synchronization witness",
            "pipeline flush witness",
        ],
        Aarch64SyncBoundaryKind::ClearExclusiveMonitor => {
            &["exclusive-monitor state", "thread identity", "monitor clear witness"]
        }
    };

    witnesses.iter().map(|witness| (*witness).to_string()).collect()
}

/// Memory access direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryAccessKind {
    Read,
    Write,
}

/// Proof-relevant memory ordering carried by an atomic or barrier operation.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryOrderingSemantics {
    Relaxed,
    Acquire,
    Release,
    AcquireRelease,
    SeqCst,
    #[default]
    Unknown,
}

/// AArch64 exclusive monitor action associated with an atomic access.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Aarch64ExclusiveMonitorSemantics {
    /// No exclusive monitor state is touched.
    #[default]
    None,
    /// Load-exclusive establishes a local reservation.
    LoadReserve,
    /// Store-exclusive conditionally commits if the local reservation still holds.
    StoreConditional,
}

/// AArch64 synchronization-boundary instruction class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Aarch64SyncBoundaryKind {
    DataMemoryBarrier,
    DataSynchronizationBarrier,
    InstructionSynchronizationBarrier,
    ClearExclusiveMonitor,
}

/// AArch64 shareability or locality scope for a synchronization boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Aarch64SyncScope {
    OuterShareable,
    NonShareable,
    InnerShareable,
    FullSystem,
    Local,
}

/// Access class ordered by an AArch64 synchronization boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Aarch64SyncOrdering {
    Loads,
    Stores,
    LoadsAndStores,
    InstructionStream,
    None,
}

/// Typed scaffold fact for AArch64 acquire/release and exclusive-monitor
/// instructions that are still rejected by proof-grade gates.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Aarch64AtomicSemanticFact {
    pub origin: Option<BinaryOrigin>,
    pub opcode: String,
    pub operand: Option<String>,
    pub access: MemoryAccessKind,
    pub ordering: MemoryOrderingSemantics,
    pub exclusive_monitor: Aarch64ExclusiveMonitorSemantics,
    pub reports_status: bool,
    pub missing_witnesses: Vec<String>,
    pub consumed_by_proof_model: bool,
}

impl Aarch64AtomicSemanticFact {
    /// True only after a downstream proof model consumes the fact and accounts
    /// for every witness required by the memory-order or monitor semantics.
    #[must_use]
    pub fn proof_grade_gate_accepted(&self) -> bool {
        self.consumed_by_proof_model && self.missing_witnesses.is_empty()
    }

    /// Conservative diagnostic used by release gates while the scaffold is not
    /// consumed by a proof model.
    #[must_use]
    pub fn proof_grade_rejection_reason(&self) -> Option<String> {
        if self.proof_grade_gate_accepted() {
            return None;
        }

        Some(format!(
            "AArch64 {} semantic fact is present but not proof-consumed; missing witnesses: {}",
            self.opcode,
            if self.missing_witnesses.is_empty() {
                "proof model consumption".to_string()
            } else {
                self.missing_witnesses.join(", ")
            }
        ))
    }
}

/// Typed fail-closed scaffold fact for AArch64 barrier and monitor-clear
/// instructions. These facts make a synchronization boundary explicit without
/// proving that surrounding events satisfy the architecture ordering rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Aarch64SyncBoundarySemanticFact {
    pub origin: Option<BinaryOrigin>,
    pub opcode: String,
    pub operand: Option<String>,
    pub kind: Aarch64SyncBoundaryKind,
    pub scope: Aarch64SyncScope,
    pub ordering: Aarch64SyncOrdering,
    pub clears_exclusive_monitor: bool,
    pub raw_option: Option<u8>,
    pub missing_witnesses: Vec<String>,
    pub consumed_by_proof_model: bool,
}

impl Aarch64SyncBoundarySemanticFact {
    /// True only after a downstream proof model consumes every witness needed
    /// to justify the barrier/monitor-clear boundary.
    #[must_use]
    pub fn proof_grade_gate_accepted(&self) -> bool {
        self.consumed_by_proof_model && self.missing_witnesses.is_empty()
    }

    /// Conservative diagnostic used by proof-grade gates while the boundary is
    /// still explicit but unconsumed.
    #[must_use]
    pub fn proof_grade_rejection_reason(&self) -> Option<String> {
        if self.proof_grade_gate_accepted() {
            return None;
        }

        Some(format!(
            "AArch64 {} sync boundary fact is present but not proof-consumed; missing witnesses: {}",
            self.opcode,
            if self.missing_witnesses.is_empty() {
                "proof model consumption".to_string()
            } else {
                self.missing_witnesses.join(", ")
            }
        ))
    }
}

/// Byte order for a lifted memory access.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Endianness {
    Little,
    Big,
    #[default]
    Unknown,
}

/// Recovered memory region class.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryRegionKind {
    Stack,
    Heap,
    Global,
    Tls,
    Mmio,
    #[default]
    Unknown,
}

/// A proof-relevant binary memory access fact.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MemoryAccessFact {
    pub origin: BinaryOrigin,
    pub kind: MemoryAccessKind,
    pub address: Formula,
    pub width_bytes: u32,
    pub endianness: Endianness,
    pub region: MemoryRegionKind,
    pub base_object: Option<String>,
    pub offset: Option<Formula>,
    pub extent: Option<u64>,
    pub provenance: Option<String>,
    pub taint: Vec<String>,
}

/// Claim made by a compiler, verifier, lifter, or report aggregation stage.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerClaim {
    pub component: String,
    pub claim: String,
    pub location: Option<SourceSpan>,
    pub assumptions: Vec<ModelAssumption>,
}

/// Kind of independent refutation for a claim.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RefutationKind {
    BadStateReachable,
    TranslationMismatch,
    SolverDisagreement,
    ReplayMismatch,
    Unknown,
}

/// Replay status for a solver model or exploit witness.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReplayStatus {
    #[default]
    NotAttempted,
    Replayed,
    Spurious,
    Failed,
}

/// Minimal witness shell for compiler/verifier/lifter exploit reports.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExploitWitness {
    pub claim: CompilerClaim,
    pub refutation: RefutationKind,
    pub function: String,
    pub location: Option<SourceSpan>,
    pub model: Option<crate::Counterexample>,
    pub replay: ReplayStatus,
    pub attribution: Option<String>,
}

/// Current JSON schema version for binary decompilation artifacts.
///
/// Version 2 adds the serialized binary source-provenance summary used to gate
/// source backpropagation. Version 3 adds per-function instruction provenance.
/// Version 4 adds digest-level binary artifact identity. Version 5 threads that
/// identity to solver dispatches so replay can bind solver results to bytes.
pub const DECOMPILATION_ARTIFACT_SCHEMA_VERSION: u32 = 5;

fn default_decompilation_artifact_schema_version() -> u32 {
    DECOMPILATION_ARTIFACT_SCHEMA_VERSION
}

/// Output target requested from the binary decompiler/converter path.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DecompileTarget {
    /// Lifted TrustIr, the semantic hub used for proof obligations.
    #[default]
    TrustIr,
    /// Reconstructed Rust source.
    Rust,
    /// trust-cg-compatible output.
    TrustCg,
    /// WebAssembly output.
    Wasm,
    /// Human-readable pseudo-source with no compilation contract.
    PseudoSource,
    /// Named experimental target.
    Other(String),
}

/// Options that define a binary decompilation request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileOptions {
    #[serde(default)]
    pub target: DecompileTarget,
    /// Fail closed on unsupported instructions, undecodable bytes, or unresolved control flow.
    #[serde(default = "default_true")]
    pub strict: bool,
    /// Validate reconstructed output against lifted binary TrustIr before raising trust.
    #[serde(default = "default_true")]
    pub validate_reconstruction: bool,
    /// Run ABI/type recovery passes when available.
    #[serde(default = "default_true")]
    pub recover_types: bool,
    /// Permit partial artifacts for diagnostics while preserving non-proof trust levels.
    #[serde(default)]
    pub allow_partial: bool,
    /// Permit Rust output that uses explicit unsafe operations to preserve machine behavior.
    #[serde(default)]
    pub emit_unsafe_rust: bool,
    #[serde(default)]
    pub entry_points: Vec<u64>,
    #[serde(default)]
    pub function_names: Vec<String>,
    #[serde(default)]
    pub address_ranges: Vec<BinaryAddressRange>,
    #[serde(default)]
    pub max_functions: Option<usize>,
    #[serde(default)]
    pub timeout_ms: Option<u64>,
}

fn default_true() -> bool {
    true
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            target: DecompileTarget::default(),
            strict: true,
            validate_reconstruction: true,
            recover_types: true,
            allow_partial: false,
            emit_unsafe_rust: false,
            entry_points: vec![],
            function_names: vec![],
            address_ranges: vec![],
            max_functions: None,
            timeout_ms: None,
        }
    }
}

/// Half-open virtual-address interval `[start, end)`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinaryAddressRange {
    pub start: u64,
    pub end: u64,
}

impl BinaryAddressRange {
    #[must_use]
    pub fn len(&self) -> u64 {
        self.end.saturating_sub(self.start)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    #[must_use]
    pub fn contains(&self, address: u64) -> bool {
        self.start <= address && address < self.end
    }
}

/// File container format for the analyzed binary.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryArtifactFormat {
    Elf,
    MachO,
    FatMachO,
    Pe,
    Wasm,
    Raw,
    #[default]
    Unknown,
}

/// Loader-level image class.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryImageKind {
    Executable,
    DynamicLibrary,
    StaticLibrary,
    Object,
    CoreDump,
    Firmware,
    #[default]
    Unknown,
}

/// Segment permissions recovered from the loader image.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinarySegmentPermissions {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

/// Executable image segment or section relevant to lifting/proof reporting.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySegment {
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default)]
    pub virtual_range: BinaryAddressRange,
    #[serde(default)]
    pub file_offset: Option<u64>,
    #[serde(default)]
    pub file_size: Option<u64>,
    #[serde(default)]
    pub permissions: BinarySegmentPermissions,
}

/// Binary symbol category used by the decompilation artifact.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinarySymbolKind {
    Function,
    Object,
    Section,
    Import,
    Export,
    Thunk,
    #[default]
    Unknown,
}

/// Loader or debug symbol attached to an artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySymbol {
    pub name: String,
    pub address: u64,
    #[serde(default)]
    pub size: Option<u64>,
    #[serde(default)]
    pub kind: BinarySymbolKind,
}

/// Content digest for the full root artifact consumed by the binary parser.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinaryArtifactDigest {
    /// Digest algorithm. Proof-grade binary provenance currently requires `sha256`.
    #[serde(default = "default_binary_artifact_digest_algorithm")]
    pub algorithm: String,
    /// Lowercase hex-encoded digest value.
    #[serde(default)]
    pub value: String,
}

fn default_binary_artifact_digest_algorithm() -> String {
    "sha256".to_string()
}

impl Default for BinaryArtifactDigest {
    fn default() -> Self {
        Self { algorithm: default_binary_artifact_digest_algorithm(), value: String::new() }
    }
}

impl BinaryArtifactDigest {
    #[must_use]
    pub fn sha256(value: impl Into<String>) -> Self {
        Self { algorithm: default_binary_artifact_digest_algorithm(), value: value.into() }
    }

    #[must_use]
    pub fn is_canonical_sha256(&self) -> bool {
        self.algorithm == "sha256" && is_canonical_sha256_hex(&self.value)
    }
}

/// Exact file range and digest for the loader image selected for decompilation.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinarySelectedImageIdentity {
    /// Offset of the selected image inside the root artifact.
    pub file_offset: u64,
    /// Number of file bytes covered by the selected image.
    pub file_size: u64,
    /// SHA-256 digest of the selected image bytes.
    #[serde(default)]
    pub sha256: String,
}

impl BinarySelectedImageIdentity {
    #[must_use]
    pub fn is_canonical_sha256(&self) -> bool {
        is_canonical_sha256_hex(&self.sha256)
    }

    #[must_use]
    pub fn end_offset(&self) -> Option<u64> {
        self.file_offset.checked_add(self.file_size)
    }
}

/// Digest identity copied to records that need to replay or attest binary bytes.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinaryArtifactDigestIdentity {
    /// Digest for the full root artifact consumed by the parser.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root_artifact_digest: Option<BinaryArtifactDigest>,
    /// Exact loader image range and digest selected for lifting/decompilation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentity>,
}

impl BinaryArtifactDigestIdentity {
    #[must_use]
    pub fn from_metadata(metadata: &BinaryArtifactMetadata) -> Option<Self> {
        let identity = Self {
            root_artifact_digest: metadata.root_artifact_digest.clone(),
            selected_image: metadata.selected_image.clone(),
        };
        identity.has_any_identity().then_some(identity)
    }

    #[must_use]
    pub fn has_any_identity(&self) -> bool {
        self.root_artifact_digest.is_some() || self.selected_image.is_some()
    }

    /// Fail-closed blockers for dispatch-level digest identity.
    #[must_use]
    pub fn digest_identity_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        match &self.root_artifact_digest {
            Some(root) if root.is_canonical_sha256() => {}
            Some(root) if root.algorithm != "sha256" => {
                blockers.push("root artifact digest algorithm is not sha256".to_string());
            }
            Some(_) => {
                blockers.push("root artifact digest is not canonical SHA-256 hex".to_string());
            }
            None => blockers.push("missing root artifact SHA-256 digest".to_string()),
        }

        match &self.selected_image {
            Some(selected) => {
                if selected.file_size == 0 {
                    blockers.push("selected image file size is zero".to_string());
                }
                if !selected.is_canonical_sha256() {
                    blockers.push("selected image digest is not canonical SHA-256 hex".to_string());
                }
                if selected.end_offset().is_none() {
                    blockers.push("selected image range overflows u64".to_string());
                }
            }
            None => blockers.push("missing selected image digest/range".to_string()),
        }

        blockers
    }

    #[must_use]
    pub fn digest_identity_allows_replay(&self) -> bool {
        self.digest_identity_blockers().is_empty()
    }
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Top-level binary metadata shared by lift, verify, decompile, and convert modes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryArtifactMetadata {
    #[serde(default)]
    pub path: Option<String>,
    #[serde(default)]
    pub format: BinaryArtifactFormat,
    #[serde(default)]
    pub image_kind: BinaryImageKind,
    #[serde(default = "default_unknown_architecture")]
    pub architecture: String,
    #[serde(default)]
    pub base_address: Option<u64>,
    #[serde(default)]
    pub entry_point: Option<u64>,
    #[serde(default)]
    pub byte_len: Option<u64>,
    #[serde(default)]
    pub build_id: Option<String>,
    #[serde(default)]
    pub root_artifact_digest: Option<BinaryArtifactDigest>,
    #[serde(default)]
    pub selected_image: Option<BinarySelectedImageIdentity>,
    #[serde(default)]
    pub segments: Vec<BinarySegment>,
    #[serde(default)]
    pub symbols: Vec<BinarySymbol>,
}

fn default_unknown_architecture() -> String {
    "unknown".to_string()
}

impl Default for BinaryArtifactMetadata {
    fn default() -> Self {
        Self {
            path: None,
            format: BinaryArtifactFormat::Unknown,
            image_kind: BinaryImageKind::Unknown,
            architecture: default_unknown_architecture(),
            base_address: None,
            entry_point: None,
            byte_len: None,
            build_id: None,
            root_artifact_digest: None,
            selected_image: None,
            segments: vec![],
            symbols: vec![],
        }
    }
}

impl BinaryArtifactMetadata {
    /// Fail-closed blockers for digest-level binary artifact identity.
    #[must_use]
    pub fn digest_identity_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        let byte_len = match self.byte_len {
            Some(byte_len) if byte_len > 0 => Some(byte_len),
            Some(_) => {
                blockers.push("root artifact byte length is zero".to_string());
                None
            }
            None => {
                blockers.push("missing root artifact byte length".to_string());
                None
            }
        };

        let root = match &self.root_artifact_digest {
            Some(root) if root.is_canonical_sha256() => Some(root),
            Some(root) if root.algorithm != "sha256" => {
                blockers.push("root artifact digest algorithm is not sha256".to_string());
                None
            }
            Some(_) => {
                blockers.push("root artifact digest is not canonical SHA-256 hex".to_string());
                None
            }
            None => {
                blockers.push("missing root artifact SHA-256 digest".to_string());
                None
            }
        };

        let selected = match &self.selected_image {
            Some(selected) => {
                if selected.file_size == 0 {
                    blockers.push("selected image file size is zero".to_string());
                }
                if !selected.is_canonical_sha256() {
                    blockers.push("selected image digest is not canonical SHA-256 hex".to_string());
                }
                match selected.end_offset() {
                    Some(end) => {
                        if let Some(byte_len) = byte_len
                            && end > byte_len
                        {
                            blockers.push(
                                "selected image range exceeds root artifact byte length"
                                    .to_string(),
                            );
                        }
                    }
                    None => blockers.push("selected image range overflows u64".to_string()),
                }
                Some(selected)
            }
            None => {
                blockers.push("missing selected image digest/range".to_string());
                None
            }
        };

        if let (Some(root), Some(selected), Some(byte_len)) = (root, selected, byte_len)
            && selected.file_offset == 0
            && selected.file_size == byte_len
            && selected.sha256 != root.value
        {
            blockers.push(
                "root artifact digest does not match whole-file selected image digest".to_string(),
            );
        }

        blockers
    }

    #[must_use]
    pub fn digest_identity_allows_proof_grade(&self) -> bool {
        self.digest_identity_blockers().is_empty()
    }
}

/// Instruction/function coverage summary for a lifted or decompiled binary slice.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCoverageSummary {
    pub functions_discovered: usize,
    pub functions_lifted: usize,
    pub instructions_discovered: usize,
    pub instructions_lifted: usize,
    pub unsupported_instructions: usize,
    pub undecoded_bytes: usize,
    pub unresolved_edges: usize,
}

/// Audit summary for binary address-to-source provenance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceProvenanceSummary {
    /// Stable lowercase provenance status reported by the binary lifter.
    #[serde(default = "default_binary_source_provenance_status")]
    pub status: String,
    /// Number of exact address-to-source mappings accepted by the lifter.
    #[serde(default)]
    pub exact_mapping_count: usize,
    /// Number of ambiguous mappings withheld by the lifter.
    #[serde(default)]
    pub ambiguous_mapping_count: usize,
    /// Human-readable diagnostics from provenance recovery.
    #[serde(default)]
    pub diagnostics: Vec<String>,
    /// True only when exact recovered source provenance may be used for source backpropagation.
    #[serde(default)]
    pub source_backpropagation_allowed: bool,
}

/// Typed diagnostic kind for binary debug/source provenance gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinarySourceProvenanceDiagnosticKind {
    /// Exact debug/source provenance was accepted and source backpropagation may use it.
    ExactSourceDebugProvenance,
    /// Diagnostics may identify binary addresses, but source backpropagation must remain disabled.
    BinaryAddressOnly,
    /// A source backpropagation request was rejected because exact source mappings are insufficient.
    SourceBackpropagationRejected,
}

impl BinarySourceProvenanceDiagnosticKind {
    /// Stable lowercase label for text reports.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::ExactSourceDebugProvenance => "exact_source_debug_provenance",
            Self::BinaryAddressOnly => "binary_address_only",
            Self::SourceBackpropagationRejected => "source_backpropagation_rejected",
        }
    }
}

/// Derived diagnostic explaining the effective provenance gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceProvenanceDiagnostic {
    /// Machine-readable diagnostic kind.
    pub kind: BinarySourceProvenanceDiagnosticKind,
    /// Human-readable detail copied from provenance recovery or synthesized from the gate.
    pub message: String,
    /// Effective source-backpropagation decision after fail-closed validation.
    pub source_backpropagation_allowed: bool,
    /// Whether binary-address diagnostics may still be emitted.
    pub binary_address_diagnostics_allowed: bool,
}

fn default_binary_source_provenance_status() -> String {
    "unavailable".to_string()
}

impl Default for BinarySourceProvenanceSummary {
    fn default() -> Self {
        Self {
            status: default_binary_source_provenance_status(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: false,
        }
    }
}

impl BinarySourceProvenanceSummary {
    /// True only when the summary reports accepted exact debug/source mappings.
    #[must_use]
    pub fn has_exact_debug_source_provenance(&self) -> bool {
        self.status == "exact" && self.exact_mapping_count > 0 && self.ambiguous_mapping_count == 0
    }

    /// Effective source-backpropagation gate after validating the producer's gate bit.
    #[must_use]
    pub fn effective_source_backpropagation_allowed(&self) -> bool {
        self.source_backpropagation_allowed && self.has_exact_debug_source_provenance()
    }

    /// Binary-address diagnostics remain available even when source backpropagation is closed.
    #[must_use]
    pub fn binary_address_diagnostics_allowed(&self) -> bool {
        true
    }

    /// Fail-closed blockers for malformed source-provenance summary fields.
    #[must_use]
    pub fn schema_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        match self.status.as_str() {
            "unavailable" => {
                if self.exact_mapping_count > 0 {
                    blockers
                        .push("unavailable source provenance reports exact mappings".to_string());
                }
                if self.ambiguous_mapping_count > 0 {
                    blockers.push(
                        "unavailable source provenance reports ambiguous mappings".to_string(),
                    );
                }
            }
            "exact" => {
                if self.exact_mapping_count == 0 {
                    blockers.push("exact source provenance has no accepted mappings".to_string());
                }
                if self.ambiguous_mapping_count > 0 {
                    blockers
                        .push("exact source provenance includes ambiguous mappings".to_string());
                }
            }
            "ambiguous" => {}
            status => {
                blockers.push(format!("source provenance status `{status}` is not recognized"))
            }
        }

        blockers
    }

    /// Fail-closed blockers for using recovered source mappings for backpropagation.
    #[must_use]
    pub fn source_backpropagation_blockers(&self) -> Vec<String> {
        let mut blockers = self.schema_blockers();

        if self.effective_source_backpropagation_allowed() {
            return blockers;
        }

        if self.source_backpropagation_allowed {
            blockers.push(
                "source backpropagation is enabled without exact debug/source provenance"
                    .to_string(),
            );
        } else if self.has_exact_debug_source_provenance() {
            blockers.push("source backpropagation is disabled by the provenance gate".to_string());
        } else {
            blockers.push("source backpropagation lacks exact debug/source provenance".to_string());
        }

        blockers
    }

    #[must_use]
    pub fn source_backpropagation_allows_proof_grade(&self) -> bool {
        self.source_backpropagation_blockers().is_empty()
    }

    /// Derived typed diagnostics for the provenance gate.
    #[must_use]
    pub fn typed_diagnostics(&self) -> Vec<BinarySourceProvenanceDiagnostic> {
        let source_backpropagation_allowed = self.effective_source_backpropagation_allowed();
        let binary_address_diagnostics_allowed = self.binary_address_diagnostics_allowed();

        if source_backpropagation_allowed {
            return vec![];
        }

        let kind = if self.status == "exact" {
            BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected
        } else {
            BinarySourceProvenanceDiagnosticKind::BinaryAddressOnly
        };

        vec![BinarySourceProvenanceDiagnostic {
            kind,
            message: self.diagnostic_message_for_closed_source_backpropagation(),
            source_backpropagation_allowed,
            binary_address_diagnostics_allowed,
        }]
    }

    fn diagnostic_message_for_closed_source_backpropagation(&self) -> String {
        let diagnostics: Vec<&str> = self
            .diagnostics
            .iter()
            .map(String::as_str)
            .filter(|diagnostic| !diagnostic.trim().is_empty())
            .collect();
        if !diagnostics.is_empty() {
            return diagnostics.join("; ");
        }

        if self.status == "exact" && self.exact_mapping_count == 0 {
            "exact debug/source provenance has no accepted address mappings; source backpropagation rejected"
                .to_string()
        } else if self.status == "exact" {
            "exact debug/source provenance is available, but source backpropagation is disabled by the provenance gate"
                .to_string()
        } else {
            "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                .to_string()
        }
    }
}

/// Known calling convention for a recovered binary function signature.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryCallingConvention {
    SystemV,
    Win64,
    Aapcs64,
    Cdecl,
    Fastcall,
    Thiscall,
    Vectorcall,
    Rust,
    #[default]
    Unknown,
    Other(String),
}

/// Base register convention for stack-relative storage facts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryStackBase {
    StackPointer,
    FramePointer,
    CanonicalFrameAddress,
    #[default]
    Unknown,
}

/// Recovered physical storage for parameters, returns, locals, and globals.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryStorageLocation {
    Register {
        name: String,
        bit_width: Option<u32>,
    },
    RegisterPair {
        high: String,
        low: String,
        bit_width: Option<u32>,
    },
    Stack {
        base: BinaryStackBase,
        offset: i64,
        size_bytes: Option<u32>,
    },
    Memory {
        address: Formula,
        size_bytes: Option<u32>,
    },
    Global {
        name: Option<String>,
        address: Option<u64>,
        size_bytes: Option<u64>,
    },
    Immediate {
        value: u128,
        width_bits: u32,
    },
    Split(Vec<BinaryStorageLocation>),
    #[default]
    Unknown,
}

/// Evidence source for ABI, storage, and type facts.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryFactEvidence {
    DebugInfo,
    AbiDefault,
    SymbolMetadata,
    RegisterUse,
    StackUse,
    DataFlow,
    LibrarySummary,
    UserProvided,
    Validation,
    Assumption,
    Heuristic {
        reason: String,
    },
    #[default]
    Unknown,
}

/// Confidence assigned to a recovered binary fact.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryFactConfidence {
    Validated,
    Inferred,
    Heuristic,
    Assumed,
    #[default]
    Unknown,
}

/// Subject described by an ABI, storage, or type fact.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryFactSubject {
    Function {
        name: String,
        entry: u64,
    },
    Parameter {
        function: String,
        index: usize,
    },
    ReturnValue {
        function: String,
        index: usize,
    },
    Local {
        function: String,
        name: String,
    },
    Register {
        function: String,
        register: String,
    },
    Memory {
        name: Option<String>,
        address: Option<u64>,
    },
    Instruction(BinaryOrigin),
    #[default]
    Unknown,
}

/// ABI fact recovered for a binary function or call site.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryAbiFactKind {
    CallingConvention(BinaryCallingConvention),
    Parameter {
        index: usize,
        location: BinaryStorageLocation,
    },
    Return {
        index: usize,
        location: BinaryStorageLocation,
    },
    StackAlignment {
        bytes: u32,
    },
    StackDelta {
        bytes: i64,
    },
    RedZone {
        bytes: u32,
    },
    CalleeSavedRegister {
        register: String,
    },
    CallerSavedRegister {
        register: String,
    },
    Variadic,
    NoReturn,
    ExternalThunk {
        target: String,
    },
    #[default]
    Unknown,
}

/// Provenanced ABI claim. Unvalidated claims remain Partial or Exploratory.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryAbiFact {
    #[serde(default)]
    pub subject: BinaryFactSubject,
    #[serde(default)]
    pub kind: BinaryAbiFactKind,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub evidence: BinaryFactEvidence,
    #[serde(default)]
    pub confidence: BinaryFactConfidence,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
}

/// Storage claim for a recovered parameter, return value, local, global, or register.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryStorageFact {
    #[serde(default)]
    pub subject: BinaryFactSubject,
    #[serde(default)]
    pub location: BinaryStorageLocation,
    #[serde(default)]
    pub ty: Option<Ty>,
    #[serde(default)]
    pub mutable: Option<bool>,
    #[serde(default)]
    pub alignment_bytes: Option<u32>,
    #[serde(default)]
    pub valid_range: Option<BinaryAddressRange>,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub evidence: BinaryFactEvidence,
    #[serde(default)]
    pub confidence: BinaryFactConfidence,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
}

/// Source-ownership classification for a recovered type fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum BinaryTypeFactSourceOwnership {
    /// The fact is attached to exact debug/source provenance.
    ExactDebugSource,
    /// The fact may be useful for binary-address diagnostics only.
    BinaryAddressOnly,
    /// The fact has no source owner.
    Missing,
    /// A source span exists, but the artifact did not accept exact debug/source provenance.
    Ambiguous,
}

impl BinaryTypeFactSourceOwnership {
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::ExactDebugSource => "exact_debug_source",
            Self::BinaryAddressOnly => "binary_address_only",
            Self::Missing => "missing",
            Self::Ambiguous => "ambiguous",
        }
    }
}

/// Type recovery claim expressed as a provenanced constraint, not a proof by itself.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryTypeFact {
    #[serde(default)]
    pub subject: BinaryFactSubject,
    #[serde(default)]
    pub recovered_ty: Option<Ty>,
    #[serde(default)]
    pub constraints: Vec<Formula>,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub evidence: BinaryFactEvidence,
    #[serde(default)]
    pub confidence: BinaryFactConfidence,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
}

impl BinaryTypeFact {
    /// Fail-closed blockers for malformed type-fact claims.
    #[must_use]
    pub fn schema_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        if self.recovered_ty.is_none() && self.constraints.is_empty() {
            blockers.push("type fact has no recovered type or constraints".to_string());
        }

        blockers
    }

    /// Classify whether this type fact has source ownership strong enough for source rewrites.
    #[must_use]
    pub fn source_ownership(
        &self,
        source_provenance: &BinarySourceProvenanceSummary,
    ) -> BinaryTypeFactSourceOwnership {
        let Some(origin) = &self.origin else {
            return BinaryTypeFactSourceOwnership::Missing;
        };
        let Some(source) = &origin.source else {
            return BinaryTypeFactSourceOwnership::Missing;
        };
        if source.is_binary() {
            return BinaryTypeFactSourceOwnership::BinaryAddressOnly;
        }
        if source_provenance.has_exact_debug_source_provenance() {
            BinaryTypeFactSourceOwnership::ExactDebugSource
        } else {
            BinaryTypeFactSourceOwnership::Ambiguous
        }
    }

    #[must_use]
    pub fn has_exact_debug_source_ownership(
        &self,
        source_provenance: &BinarySourceProvenanceSummary,
    ) -> bool {
        self.source_ownership(source_provenance) == BinaryTypeFactSourceOwnership::ExactDebugSource
    }

    /// Fail-closed blockers for using this type fact during source backpropagation.
    #[must_use]
    pub fn source_backpropagation_blockers(
        &self,
        source_provenance: &BinarySourceProvenanceSummary,
    ) -> Vec<String> {
        let mut blockers = self.schema_blockers();

        match self.source_ownership(source_provenance) {
            BinaryTypeFactSourceOwnership::ExactDebugSource => {
                if !source_provenance.effective_source_backpropagation_allowed() {
                    blockers.push(
                        "type fact exact debug/source ownership is present, but source backpropagation is disabled by the provenance gate"
                            .to_string(),
                    );
                }
            }
            BinaryTypeFactSourceOwnership::BinaryAddressOnly => {
                blockers.push(
                    "type fact source ownership is binary-address-only; source backpropagation rejected"
                        .to_string(),
                );
            }
            BinaryTypeFactSourceOwnership::Missing => {
                blockers.push(
                    "type fact has no exact source ownership origin; source backpropagation rejected"
                        .to_string(),
                );
            }
            BinaryTypeFactSourceOwnership::Ambiguous => {
                blockers.push(
                    "type fact source ownership is ambiguous or not backed by accepted exact debug/source provenance; source backpropagation rejected"
                        .to_string(),
                );
            }
        }

        blockers
    }
}

/// Parameter recovered for a binary function signature.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryParameter {
    pub index: usize,
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default)]
    pub ty: Option<Ty>,
    #[serde(default)]
    pub storage: BinaryStorageLocation,
    #[serde(default)]
    pub evidence: BinaryFactEvidence,
    #[serde(default)]
    pub trust_level: TrustLevel,
}

/// Return slot recovered for a binary function signature.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReturn {
    pub index: usize,
    #[serde(default)]
    pub ty: Option<Ty>,
    #[serde(default)]
    pub storage: BinaryStorageLocation,
    #[serde(default)]
    pub evidence: BinaryFactEvidence,
    #[serde(default)]
    pub trust_level: TrustLevel,
}

/// Function signature recovered from ABI defaults, symbols, debug info, and use analysis.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryFunctionSignature {
    pub name: String,
    pub entry: u64,
    #[serde(default)]
    pub calling_convention: BinaryCallingConvention,
    #[serde(default)]
    pub parameters: Vec<BinaryParameter>,
    #[serde(default)]
    pub returns: Vec<BinaryReturn>,
    #[serde(default)]
    pub variadic: bool,
    #[serde(default)]
    pub no_return: bool,
    #[serde(default)]
    pub stack_delta: Option<i64>,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
}

/// Memory region recovered from loader metadata, debug info, or memory analysis.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryMemoryRegion {
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default)]
    pub kind: MemoryRegionKind,
    #[serde(default)]
    pub range: BinaryAddressRange,
    #[serde(default)]
    pub permissions: BinarySegmentPermissions,
    #[serde(default)]
    pub alignment_bytes: Option<u32>,
    #[serde(default)]
    pub evidence: BinaryFactEvidence,
}

/// Shared binary memory model attached to decompilation and verification artifacts.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct BinaryMemoryModel {
    #[serde(default)]
    pub pointer_width_bits: Option<u32>,
    #[serde(default)]
    pub endianness: Endianness,
    #[serde(default)]
    pub regions: Vec<BinaryMemoryRegion>,
    #[serde(default)]
    pub accesses: Vec<MemoryAccessFact>,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub trust_level: TrustLevel,
}

/// Overall binary verification disposition.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryVerificationStatus {
    #[default]
    NotRun,
    Proved,
    Refuted,
    Unknown,
    Timeout,
    Unsupported,
    Rejected,
    Mixed,
}

/// Normalized solver dispatch status for one binary VC.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SolverDispatchStatus {
    #[default]
    NotDispatched,
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error,
    Unsupported,
    Rejected,
}

/// Meaning assigned to SAT for a dispatched solver query.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SolverQuerySemantics {
    /// SAT is a concrete witness/counterexample; UNSAT means the bad state is unreachable.
    #[default]
    SatIsCounterexample,
    /// SAT is a feasible execution path.
    SatIsFeasiblePath,
    /// SAT is only raw formula satisfiability; consumers must inspect the query.
    SatIsSatisfiableOnly,
    Unknown,
}

/// Proof certificate availability and checking status.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofCertificateStatus {
    #[default]
    NotRequested,
    Unavailable {
        reason: Option<String>,
    },
    Present {
        format: String,
        sha256: Option<String>,
        artifact_path: Option<String>,
    },
    Checked {
        checker: String,
        format: String,
        sha256: Option<String>,
    },
    Rejected {
        checker: Option<String>,
        reason: String,
    },
}

/// Compatibility marker used by legacy checked-certificate status strings.
///
/// The proof-cert crate now parses this into
/// [`ProofCertificateProductionCheckerEvidenceRef`] before counting a checked
/// certificate as production evidence. Keeping the marker here makes the
/// migration explicit without changing the serialized enum layout yet.
pub const PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER: &str =
    ";production_checker_evidence_sha256=";

/// Typed reference to production-checker evidence carried by a checked proof
/// certificate status.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofCertificateProductionCheckerEvidenceRef {
    pub checker: String,
    pub checker_version: String,
    pub production_checker_evidence_sha256: String,
}

/// Fail-closed parse result for the legacy checked-certificate status marker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "status")]
pub enum ProofCertificateProductionCheckerEvidenceStatus {
    Missing,
    Malformed { reason: String },
    Present { evidence: ProofCertificateProductionCheckerEvidenceRef },
}

impl ProofCertificateProductionCheckerEvidenceStatus {
    #[must_use]
    pub fn is_present(&self) -> bool {
        matches!(self, Self::Present { .. })
    }

    #[must_use]
    pub fn into_present(self) -> Option<ProofCertificateProductionCheckerEvidenceRef> {
        match self {
            Self::Present { evidence } => Some(evidence),
            Self::Missing | Self::Malformed { .. } => None,
        }
    }
}

impl ProofCertificateProductionCheckerEvidenceRef {
    pub fn new(
        checker: impl Into<String>,
        checker_version: impl Into<String>,
        production_checker_evidence_sha256: impl Into<String>,
    ) -> Result<Self, String> {
        let checker = checker.into();
        let checker_version = checker_version.into();
        let production_checker_evidence_sha256 = production_checker_evidence_sha256.into();

        if checker.trim().is_empty() {
            return Err("production checked certificate status is missing checker id".to_string());
        }
        if checker_version.trim().is_empty() {
            return Err(
                "production checked certificate status is missing checker version".to_string()
            );
        }
        if checker.contains(PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER)
            || checker_version.contains(PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER)
        {
            return Err(
                "checker id/version must not contain production evidence marker".to_string()
            );
        }
        if !is_canonical_lowercase_sha256(&production_checker_evidence_sha256) {
            return Err("production checker evidence sha256 is not canonical lowercase sha256 hex"
                .to_string());
        }

        Ok(Self {
            checker: checker.trim().to_string(),
            checker_version: checker_version.trim().to_string(),
            production_checker_evidence_sha256,
        })
    }

    #[must_use]
    pub fn legacy_checker_status(&self) -> String {
        format!(
            "{}@{}{}{}",
            self.checker,
            self.checker_version,
            PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER,
            self.production_checker_evidence_sha256
        )
    }

    #[must_use]
    pub fn from_legacy_checker_status(
        checker_status: &str,
    ) -> ProofCertificateProductionCheckerEvidenceStatus {
        if !checker_status.contains(PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER) {
            return ProofCertificateProductionCheckerEvidenceStatus::Missing;
        }
        if checker_status.matches(PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER).count() != 1
        {
            return ProofCertificateProductionCheckerEvidenceStatus::Malformed {
                reason: "checked certificate status contains multiple production evidence markers"
                    .to_string(),
            };
        }

        let Some((checker_label, evidence_sha256)) =
            checker_status.rsplit_once(PROOF_CERTIFICATE_PRODUCTION_CHECKER_EVIDENCE_MARKER)
        else {
            return ProofCertificateProductionCheckerEvidenceStatus::Missing;
        };
        let Some((checker, checker_version)) = checker_label.rsplit_once('@') else {
            return ProofCertificateProductionCheckerEvidenceStatus::Malformed {
                reason: "production checked certificate status is missing checker version"
                    .to_string(),
            };
        };

        match Self::new(checker, checker_version, evidence_sha256) {
            Ok(evidence) => ProofCertificateProductionCheckerEvidenceStatus::Present { evidence },
            Err(reason) => ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason },
        }
    }
}

impl ProofCertificateStatus {
    #[must_use]
    pub fn is_checked(&self) -> bool {
        matches!(self, Self::Checked { .. })
    }

    #[must_use]
    pub fn production_checker_evidence_status(
        &self,
    ) -> ProofCertificateProductionCheckerEvidenceStatus {
        match self {
            Self::Checked { checker, .. } => {
                ProofCertificateProductionCheckerEvidenceRef::from_legacy_checker_status(checker)
            }
            Self::NotRequested
            | Self::Unavailable { .. }
            | Self::Present { .. }
            | Self::Rejected { .. } => ProofCertificateProductionCheckerEvidenceStatus::Missing,
        }
    }

    #[must_use]
    pub fn production_checker_evidence(
        &self,
    ) -> Option<ProofCertificateProductionCheckerEvidenceRef> {
        self.production_checker_evidence_status().into_present()
    }

    #[must_use]
    pub fn is_production_checked(&self) -> bool {
        self.production_checker_evidence_status().is_present()
    }
}

fn is_canonical_lowercase_sha256(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

/// Stable release blocker when a backend reports a timeout without policy evidence.
pub const SOLVER_TIMEOUT_RELEASE_BLOCKER_MISSING_POLICY_ATTESTATION: &str =
    "missing_timeout_policy_attestation";

/// Stable release blocker when a backend timeout does not match the recorded policy.
pub const SOLVER_TIMEOUT_RELEASE_BLOCKER_POLICY_MISMATCH: &str = "timeout_policy_mismatch";

/// Normalized timeout evidence status for one solver dispatch or fallback attempt.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SolverTimeoutEvidenceStatus {
    #[default]
    NotApplicable,
    PolicyRecorded,
    Matched,
    MissingPolicyAttestation,
    PolicyMismatch,
}

/// Timeout evidence attached to a solver dispatch or a fallback attempt.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverTimeoutEvidence {
    #[serde(default)]
    pub planned_timeout_ms: Option<u64>,
    #[serde(default)]
    pub backend_timeout_ms: Option<u64>,
    #[serde(default)]
    pub status: SolverTimeoutEvidenceStatus,
    #[serde(default)]
    pub release_blocker: Option<String>,
}

impl SolverTimeoutEvidence {
    #[must_use]
    pub fn from_timeouts(
        planned_timeout_ms: Option<u64>,
        backend_timeout_ms: Option<u64>,
    ) -> Option<Self> {
        let (status, release_blocker) = match (planned_timeout_ms, backend_timeout_ms) {
            (None, None) => return None,
            (Some(_), None) => (SolverTimeoutEvidenceStatus::PolicyRecorded, None),
            (None, Some(_)) => (
                SolverTimeoutEvidenceStatus::MissingPolicyAttestation,
                Some(SOLVER_TIMEOUT_RELEASE_BLOCKER_MISSING_POLICY_ATTESTATION.to_string()),
            ),
            (Some(planned), Some(actual)) if planned == actual => {
                (SolverTimeoutEvidenceStatus::Matched, None)
            }
            (Some(_), Some(_)) => (
                SolverTimeoutEvidenceStatus::PolicyMismatch,
                Some(SOLVER_TIMEOUT_RELEASE_BLOCKER_POLICY_MISMATCH.to_string()),
            ),
        };

        Some(Self { planned_timeout_ms, backend_timeout_ms, status, release_blocker })
    }

    #[must_use]
    pub fn from_fallback_attempt(attempt: &SolverFallbackAttemptEvidence) -> Option<Self> {
        Self::from_timeouts(attempt.planned_timeout_ms, attempt.backend_timeout_ms).map(
            |mut evidence| {
                if evidence.release_blocker.is_none() {
                    evidence.release_blocker = attempt.release_blocker.clone();
                }
                evidence
            },
        )
    }

    #[must_use]
    pub fn from_fallback_attempts(attempts: &[SolverFallbackAttemptEvidence]) -> Option<Self> {
        let mut first_evidence = None;
        for attempt in attempts {
            let Some(evidence) = Self::from_fallback_attempt(attempt) else {
                continue;
            };
            if evidence.release_blocker.is_some() {
                return Some(evidence);
            }
            first_evidence.get_or_insert(evidence);
        }
        first_evidence
    }
}

/// One backend attempt made by a router fallback chain.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverFallbackAttemptEvidence {
    pub attempt_index: u32,
    #[serde(default)]
    pub retry_index: Option<u32>,
    pub solver: String,
    #[serde(default)]
    pub backend: Option<String>,
    #[serde(default)]
    pub policy: Option<String>,
    #[serde(default)]
    pub status: SolverDispatchStatus,
    #[serde(default)]
    pub planned_timeout_ms: Option<u64>,
    #[serde(default)]
    pub backend_timeout_ms: Option<u64>,
    #[serde(default)]
    pub elapsed_ms: Option<u64>,
    #[serde(default)]
    pub error: Option<String>,
    #[serde(default)]
    pub release_blocker: Option<String>,
}

/// One solver query sent for a binary-derived verification condition.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SolverDispatchRecord {
    pub id: String,
    #[serde(default)]
    pub function: Option<String>,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub vc_kind: Option<crate::formula::VcKind>,
    #[serde(default)]
    pub vc: Option<crate::formula::SerializableVc>,
    pub solver: String,
    #[serde(default)]
    pub backend: Option<String>,
    #[serde(default)]
    pub status: SolverDispatchStatus,
    #[serde(default)]
    pub query_semantics: SolverQuerySemantics,
    #[serde(default)]
    pub result: Option<crate::result::VerificationResult>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    #[serde(default)]
    pub elapsed_ms: Option<u64>,
    #[serde(default)]
    pub timeout_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_evidence: Option<SolverTimeoutEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fallback_attempts: Vec<SolverFallbackAttemptEvidence>,
    #[serde(default)]
    pub replay: ReplayStatus,
    #[serde(default)]
    pub certificate: ProofCertificateStatus,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

impl SolverDispatchRecord {
    #[must_use]
    pub fn replay_artifact_digest_identity(&self) -> Option<&BinaryArtifactDigestIdentity> {
        self.binary_artifact_digest_identity.as_ref()
    }

    #[must_use]
    pub fn replay_digest_identity_blockers(&self) -> Vec<String> {
        match &self.binary_artifact_digest_identity {
            Some(identity) => identity.digest_identity_blockers(),
            None => vec!["missing dispatch binary artifact digest identity".to_string()],
        }
    }

    #[must_use]
    pub fn replay_digest_identity_allows_proof_grade(&self) -> bool {
        self.replay_digest_identity_blockers().is_empty()
    }

    /// Fail-closed blockers for replay records that claim proof-grade binary bytes.
    #[must_use]
    pub fn canonical_replay_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        if self.id.trim().is_empty() {
            blockers.push("solver dispatch id is missing".to_string());
        }
        if self.solver.trim().is_empty() {
            blockers.push("solver dispatch solver is missing".to_string());
        }
        if self.replay != ReplayStatus::Replayed {
            blockers.push("solver dispatch replay was not completed".to_string());
        }

        match &self.origin {
            Some(origin) => {
                for blocker in origin.canonical_provenance_blockers() {
                    blockers.push(format!("solver dispatch origin: {blocker}"));
                }
            }
            None => blockers.push("solver dispatch is missing binary origin".to_string()),
        }

        for blocker in self.replay_digest_identity_blockers() {
            blockers.push(format!("solver dispatch replay identity: {blocker}"));
        }

        blockers
    }

    #[must_use]
    pub fn canonical_replay_allows_proof_grade(&self) -> bool {
        self.canonical_replay_blockers().is_empty()
    }
}

/// Verification summary for a binary artifact or one recovered binary function.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BinaryVerificationSummary {
    #[serde(default)]
    pub status: BinaryVerificationStatus,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub total_vcs: usize,
    #[serde(default)]
    pub proved: usize,
    #[serde(default)]
    pub failed: usize,
    #[serde(default)]
    pub unknown: usize,
    #[serde(default)]
    pub timeout: usize,
    #[serde(default)]
    pub unsupported: usize,
    #[serde(default)]
    pub rejected: usize,
    #[serde(default)]
    pub solver_dispatch: Vec<SolverDispatchRecord>,
    #[serde(default)]
    pub proof_certificate: ProofCertificateStatus,
    #[serde(default)]
    pub replay: ReplayStatus,
    #[serde(default)]
    pub unsupported_ledger: UnsupportedLedger,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub claims: Vec<CompilerClaim>,
    #[serde(default)]
    pub witnesses: Vec<ExploitWitness>,
}

impl BinaryVerificationSummary {
    /// Build a conservative binary verification summary from per-VC solver dispatch records.
    ///
    /// The binary artifact trust level is intentionally capped below
    /// [`TrustLevel::ProofGrade`]. Solver UNSAT/SAT outcomes are reflected in
    /// the count fields, but proof-grade promotion requires a separate,
    /// independently checked proof path.
    #[must_use]
    pub fn from_solver_dispatch(solver_dispatch: Vec<SolverDispatchRecord>) -> Self {
        let mut summary = Self { solver_dispatch, ..Self::default() };
        summary.refresh_from_solver_dispatch();
        summary
    }

    /// Recompute aggregate counts, status, replay, and trust from dispatch records.
    ///
    /// Counts are derived from [`SolverDispatchStatus`]. With the default binary
    /// query semantics, [`SolverDispatchStatus::Unsat`] proves the VC and
    /// [`SolverDispatchStatus::Sat`] refutes it with a counterexample.
    pub fn refresh_from_solver_dispatch(&mut self) {
        self.total_vcs = self.solver_dispatch.len();
        self.proved = 0;
        self.failed = 0;
        self.unknown = 0;
        self.timeout = 0;
        self.unsupported = self.unsupported_ledger.records.len();
        self.rejected = 0;

        for dispatch in &self.solver_dispatch {
            match (dispatch.status, dispatch.query_semantics) {
                (SolverDispatchStatus::Unsat, SolverQuerySemantics::SatIsCounterexample) => {
                    // `status` is authoritative ONLY when no
                    // embedded `result` is present. If a dispatch record carries
                    // a `VerificationResult` (e.g. from a deserialized/forged
                    // record), it must CORROBORATE the Unsat claim at the
                    // reported-proof floor (SmtBacked): a `result` that gates
                    // below the floor (Unchecked — a bare unvalidated solver
                    // "unsat" — or Heuristic) must NOT be counted as proved.
                    // Fail closed to `unknown` (a sound false-FAIL), never a
                    // false-PROVE.
                    let corroborated = match &dispatch.result {
                        None => true,
                        Some(r) => matches!(
                            r.clone().require_assurance(crate::result::AssuranceLevel::SmtBacked),
                            crate::result::VerificationResult::Proved { .. }
                        ),
                    };
                    if corroborated {
                        self.proved += 1;
                    } else {
                        self.unknown += 1;
                    }
                }
                (SolverDispatchStatus::Sat, SolverQuerySemantics::SatIsCounterexample) => {
                    self.failed += 1;
                }
                (SolverDispatchStatus::Unsat | SolverDispatchStatus::Sat, _) => self.unknown += 1,
                (
                    SolverDispatchStatus::Unknown
                    | SolverDispatchStatus::Error
                    | SolverDispatchStatus::NotDispatched,
                    _,
                ) => self.unknown += 1,
                (SolverDispatchStatus::Timeout, _) => self.timeout += 1,
                (SolverDispatchStatus::Unsupported, _) => self.unsupported += 1,
                (SolverDispatchStatus::Rejected, _) => self.rejected += 1,
            }
        }

        self.status = binary_verification_status_from_counts(self);
        self.replay = aggregate_dispatch_replay(&self.solver_dispatch);
        self.trust_level = binary_verification_trust_level(self.status);
    }
}

fn binary_verification_status_from_counts(
    summary: &BinaryVerificationSummary,
) -> BinaryVerificationStatus {
    let total = summary.total_vcs;
    if total == 0 {
        if summary.rejected > 0 {
            return BinaryVerificationStatus::Rejected;
        }
        if summary.unsupported > 0 {
            return BinaryVerificationStatus::Unsupported;
        }
        return BinaryVerificationStatus::NotRun;
    }

    let non_zero_categories = [
        summary.proved,
        summary.failed,
        summary.unknown,
        summary.timeout,
        summary.unsupported,
        summary.rejected,
    ]
    .into_iter()
    .filter(|count| *count > 0)
    .count();

    if non_zero_categories > 1 {
        return BinaryVerificationStatus::Mixed;
    }

    if summary.proved == total {
        BinaryVerificationStatus::Proved
    } else if summary.failed == total {
        BinaryVerificationStatus::Refuted
    } else if summary.timeout == total {
        BinaryVerificationStatus::Timeout
    } else if summary.unsupported == total {
        BinaryVerificationStatus::Unsupported
    } else if summary.rejected == total {
        BinaryVerificationStatus::Rejected
    } else {
        BinaryVerificationStatus::Unknown
    }
}

fn aggregate_dispatch_replay(dispatches: &[SolverDispatchRecord]) -> ReplayStatus {
    if dispatches.is_empty() {
        ReplayStatus::NotAttempted
    } else if dispatches.iter().any(|dispatch| dispatch.replay == ReplayStatus::Failed) {
        ReplayStatus::Failed
    } else if dispatches.iter().any(|dispatch| dispatch.replay == ReplayStatus::Spurious) {
        ReplayStatus::Spurious
    } else if dispatches.iter().any(|dispatch| dispatch.replay == ReplayStatus::NotAttempted) {
        ReplayStatus::NotAttempted
    } else {
        ReplayStatus::Replayed
    }
}

fn binary_verification_trust_level(status: BinaryVerificationStatus) -> TrustLevel {
    match status {
        BinaryVerificationStatus::Rejected => TrustLevel::Rejected,
        BinaryVerificationStatus::NotRun
        | BinaryVerificationStatus::Proved
        | BinaryVerificationStatus::Refuted
        | BinaryVerificationStatus::Unknown
        | BinaryVerificationStatus::Timeout
        | BinaryVerificationStatus::Unsupported
        | BinaryVerificationStatus::Mixed => TrustLevel::Partial,
    }
}

/// Validation state for reconstructed or converted output.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReconstructionValidationStatus {
    #[default]
    NotAttempted,
    Validated,
    Refuted,
    Failed,
    Unknown,
}

/// Kind of reconstructed/conversion candidate available for validation.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReconstructionCandidateKind {
    /// No presentation artifact or comparable TrustIr candidate was supplied.
    #[default]
    Missing,
    /// Only text or an opaque artifact path is available; no semantic validation
    /// can be attempted.
    TextOnly,
    /// A structured TrustIr body is available for semantic comparison.
    StructuredTrustIr,
    /// A future validated Rust reconstruction candidate constrained to a
    /// conservative straight-line subset.
    ValidatedRustStrictSubset,
    /// Named experimental candidate kind.
    Other(String),
}

/// Structured evidence attached to reconstructed-output validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReconstructionValidationEvidence {
    /// Structured output is the lifted binary TrustIr itself.
    TrustIrIdentitySelfCheck,
    /// A comparable structured TrustIr candidate was checked in both directions.
    BidirectionalTrustIrRefinement,
    /// The presentation artifact has no comparable semantic TrustIr body.
    TextOnlyCandidateRejected,
    /// Required lifted or reconstructed TrustIr was missing.
    MissingComparableTrustIr,
    /// No checked proof certificate evidence was produced.
    NoCheckedProofCertificate,
    /// The validation did not discharge binary proof obligations.
    NoBinaryProofObligation,
    /// Candidate passed the conservative Rust reconstruction subset preflight.
    StrictRustSubsetEligible,
    /// Candidate was rejected because control flow is not straight-line.
    RejectedNonStraightLine,
    /// Candidate was rejected because it uses lifted memory semantics.
    RejectedMemoryAccess,
    /// Candidate was rejected because it contains a call.
    RejectedCall,
    /// Candidate was rejected because unsupported lifted features remain.
    RejectedUnsupported,
    /// Named experimental evidence kind.
    Other(String),
}

/// Conservative eligibility reason for future validated Rust reconstruction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RustReconstructionRejectionKind {
    MissingLiftedTrustIr,
    NonStraightLine,
    MemoryAccess,
    Call,
    Unsupported,
    Other(String),
}

/// Per-function strict-subset metadata for a future validated Rust path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RustReconstructionEligibility {
    #[serde(default)]
    pub function: Option<String>,
    #[serde(default)]
    pub eligible: bool,
    #[serde(default)]
    pub subset: String,
    #[serde(default)]
    pub rejections: Vec<RustReconstructionRejectionKind>,
    #[serde(default)]
    pub evidence: Vec<ReconstructionValidationEvidence>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

impl Default for RustReconstructionEligibility {
    fn default() -> Self {
        Self {
            function: None,
            eligible: false,
            subset: "straight-line-no-memory-no-calls".to_string(),
            rejections: vec![],
            evidence: vec![],
            diagnostics: vec![],
        }
    }
}

/// Structured placeholder for a future validated Rust reconstruction.
///
/// This is intentionally separate from [`DecompiledOutput`] text for
/// `RustSkeleton`: it can carry strict eligibility and rejection evidence
/// before compile-back validation exists.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatedRustReconstruction {
    #[serde(default)]
    pub status: ReconstructionValidationStatus,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub eligibility: Vec<RustReconstructionEligibility>,
    #[serde(default)]
    pub validation_records: Vec<ReconstructionValidationRecord>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

impl Default for ValidatedRustReconstruction {
    fn default() -> Self {
        Self {
            status: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            eligibility: vec![],
            validation_records: vec![],
            diagnostics: vec![],
        }
    }
}

/// Direction checked while validating a reconstruction candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReconstructionValidationDirection {
    LiftedToOutput,
    OutputToLifted,
}

/// Per-direction summary for reconstructed-output validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructionValidationDirectionRecord {
    #[serde(default = "default_reconstruction_validation_direction")]
    pub direction: ReconstructionValidationDirection,
    #[serde(default)]
    pub status: ReconstructionValidationStatus,
    #[serde(default)]
    pub vc_count: usize,
    #[serde(default)]
    pub counterexamples: usize,
    #[serde(default)]
    pub proof_certificates: usize,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

fn default_reconstruction_validation_direction() -> ReconstructionValidationDirection {
    ReconstructionValidationDirection::LiftedToOutput
}

impl Default for ReconstructionValidationDirectionRecord {
    fn default() -> Self {
        Self {
            direction: default_reconstruction_validation_direction(),
            status: ReconstructionValidationStatus::NotAttempted,
            vc_count: 0,
            counterexamples: 0,
            proof_certificates: 0,
            diagnostics: vec![],
        }
    }
}

/// Structured validation record for a reconstructed or converted output.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructionValidationRecord {
    #[serde(default)]
    pub target: DecompileTarget,
    #[serde(default)]
    pub function: Option<String>,
    #[serde(default)]
    pub lifted_function: Option<String>,
    #[serde(default)]
    pub reconstructed_function: Option<String>,
    #[serde(default)]
    pub candidate: ReconstructionCandidateKind,
    #[serde(default)]
    pub status: ReconstructionValidationStatus,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub forward: Option<ReconstructionValidationDirectionRecord>,
    #[serde(default)]
    pub reverse: Option<ReconstructionValidationDirectionRecord>,
    #[serde(default)]
    pub evidence: Vec<ReconstructionValidationEvidence>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

impl Default for ReconstructionValidationRecord {
    fn default() -> Self {
        Self {
            target: DecompileTarget::TrustIr,
            function: None,
            lifted_function: None,
            reconstructed_function: None,
            candidate: ReconstructionCandidateKind::Missing,
            status: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            forward: None,
            reverse: None,
            evidence: vec![],
            diagnostics: vec![],
        }
    }
}

/// Structured reason a target output is inspectable only, rejected, or otherwise
/// blocked from validation/proof-grade use.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetValidationBlocker {
    #[serde(default)]
    pub target: DecompileTarget,
    #[serde(default)]
    pub function: Option<String>,
    /// Stable machine-readable identity assigned by the blocker producer.
    ///
    /// This is distinct from `feature` and `reason`: consumers must not have to
    /// recover a blocker identity from human-readable prose. The serde default
    /// keeps artifacts written before this field was introduced readable.
    #[serde(default)]
    pub code: String,
    #[serde(default)]
    pub stage: String,
    #[serde(default)]
    pub feature: String,
    #[serde(default)]
    pub reason: String,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

/// Formula preserved from lifted binary TrustIr for target-output inspection.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreservedSymbolicFormula {
    #[serde(default)]
    pub target: DecompileTarget,
    #[serde(default)]
    pub function: Option<String>,
    #[serde(default)]
    pub block: Option<usize>,
    #[serde(default)]
    pub statement_index: Option<usize>,
    #[serde(default)]
    pub location: String,
    pub formula: Formula,
}

/// Canonical schema string attached to `trust_symbolic.formula` payloads.
pub const TRUST_SYMBOLIC_FORMULA_SCHEMA: &str = "trust-types.Formula@1";

/// Stable identity that a target proof consumer must bind before accepting a
/// preserved `trust_symbolic.formula` payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreservedSymbolicFormulaEvidence {
    pub schema: String,
    pub sort: String,
    pub digest: String,
    pub origin: String,
}

impl Default for PreservedSymbolicFormulaEvidence {
    fn default() -> Self {
        Self {
            schema: TRUST_SYMBOLIC_FORMULA_SCHEMA.to_string(),
            sort: String::new(),
            digest: String::new(),
            origin: String::new(),
        }
    }
}

impl PreservedSymbolicFormula {
    #[must_use]
    pub fn schema(&self) -> &'static str {
        TRUST_SYMBOLIC_FORMULA_SCHEMA
    }

    #[must_use]
    pub fn sort_smtlib(&self) -> String {
        crate::smt_logic::infer_sort(&self.formula).to_smtlib()
    }

    #[must_use]
    pub fn formula_digest(&self) -> String {
        self.try_formula_digest().expect(
            "Formula is the canonical serializable Trust IR; refusing to mint \
             preserved-symbolic evidence after serialization failure",
        )
    }

    /// Fallible digest construction for proof consumers that can propagate an
    /// internal model-serialization failure.
    pub fn try_formula_digest(&self) -> Result<String, serde_json::Error> {
        let formula_json = serde_json::to_string(&self.formula)?;
        Ok(stable_sha256_hex(
            format!(
                "schema={}\nsort={}\nformula_json={formula_json}\n",
                self.schema(),
                self.sort_smtlib()
            )
            .as_bytes(),
        ))
    }

    #[must_use]
    pub fn origin(&self) -> String {
        format!(
            "target={};function={};block={};statement={};location={}",
            decompile_target_evidence_label(&self.target),
            self.function.as_deref().unwrap_or("unknown"),
            self.block.map(|block| format!("bb{block}")).unwrap_or_else(|| "unknown".into()),
            self.statement_index
                .map(|statement| format!("stmt{statement}"))
                .unwrap_or_else(|| "unknown".into()),
            self.location
        )
    }

    #[must_use]
    pub fn evidence(&self) -> PreservedSymbolicFormulaEvidence {
        PreservedSymbolicFormulaEvidence {
            schema: self.schema().to_string(),
            sort: self.sort_smtlib(),
            digest: self.formula_digest(),
            origin: self.origin(),
        }
    }

    /// Build an exact diagnostic accepted by schema-aware proof consumers.
    ///
    /// Generic target-consumer markers are intentionally insufficient for
    /// preserved formulas: the diagnostic must bind the schema, inferred sort,
    /// payload digest, and formula origin.
    #[must_use]
    pub fn schema_aware_consumer_diagnostic(&self) -> String {
        let evidence = self.evidence();
        format!(
            "symbolic-formula-proof-consumer=accepted; trust_symbolic.formula=consumed; formula.schema={}; formula.sort={}; formula.digest={}; formula.origin={}",
            evidence.schema, evidence.sort, evidence.digest, evidence.origin
        )
    }

    #[must_use]
    pub fn matches_schema_aware_consumer_diagnostic(&self, diagnostic: &str) -> bool {
        let evidence = self.evidence();
        (diagnostic.contains("trust_symbolic.formula=consumed")
            || diagnostic.contains("symbolic-formula-proof-consumer=accepted"))
            && diagnostic.contains(&format!("formula.schema={}", evidence.schema))
            && diagnostic.contains(&format!("formula.sort={}", evidence.sort))
            && (diagnostic.contains(&format!("formula.digest={}", evidence.digest))
                || diagnostic.contains(&format!("formula.digest=sha256:{}", evidence.digest)))
            && diagnostic.contains(&format!("formula.origin={}", evidence.origin))
    }
}

fn decompile_target_evidence_label(target: &DecompileTarget) -> String {
    match target {
        DecompileTarget::TrustIr => "trust_ir".to_string(),
        DecompileTarget::Rust => "rust".to_string(),
        DecompileTarget::TrustCg => "trust-cg".to_string(),
        DecompileTarget::Wasm => "wasm".to_string(),
        DecompileTarget::PseudoSource => "pseudo_source".to_string(),
        DecompileTarget::Other(name) => name.to_ascii_lowercase(),
    }
}

/// Concrete decompiler/converter output for a target.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecompiledOutput {
    #[serde(default)]
    pub target: DecompileTarget,
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub artifact_path: Option<String>,
    #[serde(default)]
    pub validation: ReconstructionValidationStatus,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub validation_records: Vec<ReconstructionValidationRecord>,
    #[serde(default)]
    pub validated_rust: Option<ValidatedRustReconstruction>,
    #[serde(default)]
    pub target_validation_blockers: Vec<TargetValidationBlocker>,
    #[serde(default)]
    pub preserved_symbolic_formulas: Vec<PreservedSymbolicFormula>,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

impl Default for DecompiledOutput {
    fn default() -> Self {
        Self {
            target: DecompileTarget::TrustIr,
            text: None,
            artifact_path: None,
            validation: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            validation_records: vec![],
            validated_rust: None,
            target_validation_blockers: vec![],
            preserved_symbolic_formulas: vec![],
            assumptions: vec![],
            diagnostics: vec![],
        }
    }
}

/// Cross-function reconstruction summary for a decompilation artifact.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReconstructionSummary {
    #[serde(default)]
    pub target: DecompileTarget,
    #[serde(default)]
    pub outputs: Vec<DecompiledOutput>,
    #[serde(default)]
    pub validation: ReconstructionValidationStatus,
    #[serde(default)]
    pub trust_level: TrustLevel,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
    #[serde(default)]
    pub validated_rust: Option<ValidatedRustReconstruction>,
}

impl Default for ReconstructionSummary {
    fn default() -> Self {
        Self {
            target: DecompileTarget::TrustIr,
            outputs: vec![],
            validation: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            assumptions: vec![],
            diagnostics: vec![],
            validated_rust: None,
        }
    }
}

/// One recovered function in a binary decompilation artifact.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecompiledFunction {
    pub name: String,
    pub entry: u64,
    #[serde(default)]
    pub address_range: Option<BinaryAddressRange>,
    #[serde(default)]
    pub origin: Option<BinaryOrigin>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub instruction_provenance: Vec<BinaryOrigin>,
    #[serde(default)]
    pub signature: BinaryFunctionSignature,
    #[serde(default)]
    pub lifted: Option<VerifiableFunction>,
    #[serde(default)]
    pub output: Option<DecompiledOutput>,
    #[serde(default)]
    pub abi_facts: Vec<BinaryAbiFact>,
    #[serde(default)]
    pub storage_facts: Vec<BinaryStorageFact>,
    #[serde(default)]
    pub type_facts: Vec<BinaryTypeFact>,
    #[serde(default)]
    pub memory_accesses: Vec<MemoryAccessFact>,
    #[serde(default)]
    pub unsupported: UnsupportedLedger,
    #[serde(default)]
    pub coverage: BinaryCoverageSummary,
    #[serde(default)]
    pub verification: BinaryVerificationSummary,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub trust_level: TrustLevel,
}

impl Default for DecompiledFunction {
    fn default() -> Self {
        Self {
            name: String::new(),
            entry: 0,
            address_range: None,
            origin: None,
            instruction_provenance: vec![],
            signature: BinaryFunctionSignature::default(),
            lifted: None,
            output: None,
            abi_facts: vec![],
            storage_facts: vec![],
            type_facts: vec![],
            memory_accesses: vec![],
            unsupported: UnsupportedLedger::default(),
            coverage: BinaryCoverageSummary::default(),
            verification: BinaryVerificationSummary::default(),
            assumptions: vec![],
            trust_level: TrustLevel::Exploratory,
        }
    }
}

/// Shared artifact produced by binary lift, verification, decompile, and convert modes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecompilationArtifact {
    #[serde(default = "default_decompilation_artifact_schema_version")]
    pub schema_version: u32,
    #[serde(default)]
    pub binary: BinaryArtifactMetadata,
    #[serde(default)]
    pub options: DecompileOptions,
    #[serde(default)]
    pub target: DecompileTarget,
    #[serde(default)]
    pub functions: Vec<DecompiledFunction>,
    #[serde(default)]
    pub call_graph: crate::call_graph::CallGraph,
    #[serde(default)]
    pub abi_facts: Vec<BinaryAbiFact>,
    #[serde(default)]
    pub storage_facts: Vec<BinaryStorageFact>,
    #[serde(default)]
    pub type_facts: Vec<BinaryTypeFact>,
    #[serde(default)]
    pub memory_model: BinaryMemoryModel,
    #[serde(default)]
    pub unsupported: UnsupportedLedger,
    #[serde(default)]
    pub coverage: BinaryCoverageSummary,
    #[serde(default)]
    pub source_provenance: BinarySourceProvenanceSummary,
    #[serde(default)]
    pub verification: BinaryVerificationSummary,
    #[serde(default)]
    pub reconstruction: ReconstructionSummary,
    #[serde(default)]
    pub assumptions: Vec<ModelAssumption>,
    #[serde(default)]
    pub witnesses: Vec<ExploitWitness>,
    #[serde(default)]
    pub trust_level: TrustLevel,
}

impl Default for DecompilationArtifact {
    fn default() -> Self {
        Self {
            schema_version: DECOMPILATION_ARTIFACT_SCHEMA_VERSION,
            binary: BinaryArtifactMetadata::default(),
            options: DecompileOptions::default(),
            target: DecompileTarget::TrustIr,
            functions: vec![],
            call_graph: crate::call_graph::CallGraph::default(),
            abi_facts: vec![],
            storage_facts: vec![],
            type_facts: vec![],
            memory_model: BinaryMemoryModel::default(),
            unsupported: UnsupportedLedger::default(),
            coverage: BinaryCoverageSummary::default(),
            source_provenance: BinarySourceProvenanceSummary::default(),
            verification: BinaryVerificationSummary::default(),
            reconstruction: ReconstructionSummary::default(),
            assumptions: vec![],
            witnesses: vec![],
            trust_level: TrustLevel::Partial,
        }
    }
}

impl DecompilationArtifact {
    /// Fail-closed blockers for proof-grade binary-to-TrustIr provenance and schema.
    ///
    /// This intentionally does not change serde compatibility: legacy artifacts
    /// may still deserialize, but proof-grade consumers can reject missing or
    /// malformed binary identity, origin, replay, and source-provenance fields
    /// with stable diagnostics.
    #[must_use]
    pub fn canonical_binary_to_trust_ir_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        if self.schema_version != DECOMPILATION_ARTIFACT_SCHEMA_VERSION {
            blockers.push(format!(
                "decompilation artifact schema version {} is not supported; expected {}",
                self.schema_version, DECOMPILATION_ARTIFACT_SCHEMA_VERSION
            ));
        }
        if !matches!(&self.target, DecompileTarget::TrustIr) {
            blockers.push("decompilation artifact target is not TrustIr".to_string());
        }

        push_prefixed_blockers(
            &mut blockers,
            "binary metadata",
            self.binary.digest_identity_blockers(),
        );
        push_prefixed_blockers(
            &mut blockers,
            "source provenance",
            self.source_provenance.schema_blockers(),
        );

        if self.functions.is_empty() {
            blockers.push("decompilation artifact contains no functions".to_string());
        }

        for (function_index, function) in self.functions.iter().enumerate() {
            let function_label =
                decompiled_function_validation_label(function_index, &function.name);

            match &function.origin {
                Some(origin) => push_prefixed_blockers(
                    &mut blockers,
                    &format!("{function_label} origin"),
                    origin.canonical_provenance_blockers(),
                ),
                None => blockers.push(format!("{function_label} is missing binary origin")),
            }

            if function.instruction_provenance.is_empty() {
                blockers.push(format!("{function_label} has no instruction provenance"));
            }
            for (instruction_index, origin) in function.instruction_provenance.iter().enumerate() {
                push_prefixed_blockers(
                    &mut blockers,
                    &format!("{function_label} instruction[{instruction_index}]"),
                    origin.canonical_provenance_blockers(),
                );
            }

            if function.lifted.is_none() {
                blockers.push(format!("{function_label} is missing lifted TrustIr body"));
            }

            for (type_fact_index, type_fact) in function.type_facts.iter().enumerate() {
                push_prefixed_blockers(
                    &mut blockers,
                    &format!("{function_label} type_fact[{type_fact_index}]"),
                    type_fact.schema_blockers(),
                );
            }
        }

        for (type_fact_index, type_fact) in self.type_facts.iter().enumerate() {
            push_prefixed_blockers(
                &mut blockers,
                &format!("type_fact[{type_fact_index}]"),
                type_fact.schema_blockers(),
            );
        }

        let mut saw_solver_dispatch = false;
        for (dispatch_index, dispatch) in self.verification.solver_dispatch.iter().enumerate() {
            saw_solver_dispatch = true;
            push_prefixed_blockers(
                &mut blockers,
                &format!("verification dispatch[{dispatch_index}]"),
                dispatch.canonical_replay_blockers(),
            );
        }
        for (function_index, function) in self.functions.iter().enumerate() {
            let function_label =
                decompiled_function_validation_label(function_index, &function.name);
            for (dispatch_index, dispatch) in
                function.verification.solver_dispatch.iter().enumerate()
            {
                saw_solver_dispatch = true;
                push_prefixed_blockers(
                    &mut blockers,
                    &format!("{function_label} dispatch[{dispatch_index}]"),
                    dispatch.canonical_replay_blockers(),
                );
            }
        }
        if !saw_solver_dispatch {
            blockers.push(
                "decompilation artifact contains no solver dispatch replay records".to_string(),
            );
        }

        blockers
    }

    #[must_use]
    pub fn canonical_binary_to_trust_ir_allows_proof_grade(&self) -> bool {
        self.canonical_binary_to_trust_ir_blockers().is_empty()
    }

    /// Fail-closed blockers for using recovered type facts during source rewrites.
    #[must_use]
    pub fn type_fact_source_backpropagation_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        for (type_fact_index, type_fact) in self.type_facts.iter().enumerate() {
            push_prefixed_blockers(
                &mut blockers,
                &format!("type_fact[{type_fact_index}]"),
                type_fact.source_backpropagation_blockers(&self.source_provenance),
            );
        }

        for (function_index, function) in self.functions.iter().enumerate() {
            let function_label =
                decompiled_function_validation_label(function_index, &function.name);
            for (type_fact_index, type_fact) in function.type_facts.iter().enumerate() {
                push_prefixed_blockers(
                    &mut blockers,
                    &format!("{function_label} type_fact[{type_fact_index}]"),
                    type_fact.source_backpropagation_blockers(&self.source_provenance),
                );
            }
        }

        blockers
    }
}

fn push_prefixed_blockers(blockers: &mut Vec<String>, prefix: &str, nested_blockers: Vec<String>) {
    for blocker in nested_blockers {
        blockers.push(format!("{prefix}: {blocker}"));
    }
}

fn decompiled_function_validation_label(index: usize, name: &str) -> String {
    if name.trim().is_empty() {
        format!("function[{index}]")
    } else {
        format!("function[{index}] `{name}`")
    }
}

/// A contract specification (requires/ensures).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Contract {
    pub kind: ContractKind,
    pub span: SourceSpan,
    pub body: String,
}

impl Contract {
    /// Stable, human-auditable source id for this contract within a function.
    ///
    /// `contract_index` is the dense compiler `TrustContractId` slot after
    /// conversion into `trust-types`; callers that recover contracts from source
    /// use the same deterministic order.
    #[must_use]
    pub fn stable_source_id(&self, function_def_path: &str, contract_index: usize) -> String {
        canonical_contract_source_id(function_def_path, self.kind.attr_name(), contract_index)
    }

    /// Stable assertion id string for proof engines that bind diagnostics to a
    /// user-authored contract clause.
    #[must_use]
    pub fn stable_assertion_id(&self, function_def_path: &str, contract_index: usize) -> String {
        format!("trust-assertion:{}", self.stable_source_id(function_def_path, contract_index))
    }

    /// Compact stable assertion id for TrustIr native bundle fields.
    #[must_use]
    pub fn stable_native_assertion_index(
        &self,
        function_def_path: &str,
        contract_index: usize,
    ) -> u32 {
        stable_u32_id(self.stable_assertion_id(function_def_path, contract_index).as_bytes())
    }
}

/// Where a proof item came from before canonical Trust lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustProofItemSource {
    /// Native Trust `proof fn` syntax owned by tRustc.
    NativeProofFn,
    /// Native Trust inline `proof { ... }` block.
    NativeProofBlock,
    /// Native Trust proof harness item.
    NativeHarness,
    /// Compatibility import from `#[trust_vc::proof]`.
    TrustVcProofAttribute,
    /// Compatibility import from trust_vc proof macros such as `assert_by!`.
    TrustVcProofMacro,
    /// Compatibility import from trust_wp `#[law]`.
    TrustWpLawAttribute,
    /// Compatibility import from trust_wp `#[logic]` or `#[predicate]`.
    TrustWpLogicAttribute,
    /// External theorem/proof-term checked by clean.
    LeanExternalProof,
}

impl TrustProofItemSource {
    #[must_use]
    pub fn is_native(self) -> bool {
        matches!(self, Self::NativeProofFn | Self::NativeProofBlock | Self::NativeHarness)
    }

    #[must_use]
    pub fn is_compatibility_import(self) -> bool {
        !self.is_native()
    }
}

/// Preferred engine for a proof item. `Auto` means Trust owns routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustProofEngineHint {
    #[default]
    Auto,
    TrustMc,
    TrustWp,
    TrustVc,
    Clean,
    AY,
    Ty,
}

/// Semantic role of a proof item in the Trust proof graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustProofItemKind {
    /// Symbolic harness executed by trust-mc/Kani-style machinery.
    Harness,
    /// Harness that instantiates a function contract.
    ContractHarness,
    /// Lemma/proof function usable by later obligations.
    Lemma,
    /// Pure specification helper.
    SpecificationFunction,
    /// Inline proof block inside executable code.
    ProofBlock,
    /// Logic law available as a solver axiom only after proof evidence exists.
    LogicLaw,
    /// Imported theorem or proof certificate.
    ExternalTheorem,
}

/// Required verification treatment for a proof item.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustProofExecutionMode {
    /// Required in `full-verify` and eligible to discharge full proof obligations.
    #[default]
    RequiredFullVerify,
    /// Required in `full-verify`, but evidence remains bounded/regression-grade.
    BoundedRegression { depth: Option<u64> },
    /// Run only for diagnostics; cannot satisfy release proof obligations.
    DiagnosticOnly,
}

/// Compiler-owned proof item metadata.
///
/// Native Trust syntax should produce these records directly. Legacy Kani,
/// trust-wp, trust-vc, and Lean-facing surfaces may be imported into this shape
/// during migration, but remain marked by `source` so release gates can
/// distinguish canonical syntax from compatibility shims.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustProofItem {
    pub name: String,
    pub span: SourceSpan,
    pub source: TrustProofItemSource,
    pub kind: TrustProofItemKind,
    #[serde(default)]
    pub engine: TrustProofEngineHint,
    #[serde(default)]
    pub mode: TrustProofExecutionMode,
    /// Function, contract, module, theorem, or obligation this item proves.
    #[serde(default)]
    pub target: Option<String>,
    /// Stable hash of the typed proof body once tRustc provides it.
    #[serde(default)]
    pub body_hash: Option<String>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

impl TrustProofItem {
    #[must_use]
    pub fn native_proof_fn(
        name: impl Into<String>,
        kind: TrustProofItemKind,
        span: SourceSpan,
    ) -> Self {
        Self {
            name: name.into(),
            span,
            source: TrustProofItemSource::NativeProofFn,
            kind,
            engine: TrustProofEngineHint::Auto,
            mode: TrustProofExecutionMode::RequiredFullVerify,
            target: None,
            body_hash: None,
            diagnostics: vec![],
        }
    }

    #[must_use]
    pub fn compatibility_import(
        name: impl Into<String>,
        source: TrustProofItemSource,
        kind: TrustProofItemKind,
        engine: TrustProofEngineHint,
        span: SourceSpan,
    ) -> Self {
        Self {
            name: name.into(),
            span,
            source,
            kind,
            engine,
            mode: TrustProofExecutionMode::RequiredFullVerify,
            target: None,
            body_hash: None,
            diagnostics: vec![],
        }
    }

    #[must_use]
    pub fn is_native_syntax(&self) -> bool {
        self.source.is_native()
    }

    #[must_use]
    pub fn is_compatibility_import(&self) -> bool {
        self.source.is_compatibility_import()
    }

    #[must_use]
    pub fn must_execute_in_full_verify(&self) -> bool {
        !matches!(self.mode, TrustProofExecutionMode::DiagnosticOnly)
    }

    #[must_use]
    pub fn proof_grade_blocker(&self) -> Option<&'static str> {
        match self.mode {
            TrustProofExecutionMode::RequiredFullVerify => None,
            TrustProofExecutionMode::BoundedRegression { .. } => Some(
                "bounded proof item must execute but cannot discharge unbounded proof obligations",
            ),
            TrustProofExecutionMode::DiagnosticOnly => {
                Some("diagnostic proof item cannot discharge release proof obligations")
            }
        }
    }
}

/// Typed compiler contract payload handed to MIR extraction.
///
/// This is intentionally a separate bundle from source-recovered attributes:
/// native extraction should consume compiler-owned contract facts and fail
/// closed when they are unavailable, not scrape Rust source as a substitute.
/// The current payload carries normalized `Contract`s while the compiler query
/// is being wired in; future typed fields can be added with serde defaults.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompilerContractBundle {
    #[serde(default)]
    pub contracts: Vec<Contract>,
    /// Query-owned typed propositions, keyed redundantly by dense source index,
    /// kind, and canonical body. A consumer may use a row only when all three
    /// match the corresponding `contracts` entry exactly; missing/duplicate or
    /// stale rows never fall back to monitor/proof authority.
    #[serde(default)]
    pub typed_propositions: Vec<CompilerContractProposition>,
    /// First-class loop clauses carried next to (not inside) the dense
    /// function-contract vector.  Keeping the lanes separate preserves the
    /// stable `TrustContractId` indexing used by function contracts while still
    /// giving VC generation the loop-head identity needed for E4/E5.
    #[serde(default)]
    pub loop_contracts: Vec<LoopContractSpec>,
    #[serde(default)]
    pub proof_items: Vec<TrustProofItem>,
}

impl CompilerContractBundle {
    #[must_use]
    pub fn new(contracts: Vec<Contract>) -> Self {
        Self { contracts, typed_propositions: vec![], loop_contracts: vec![], proof_items: vec![] }
    }

    #[must_use]
    pub fn with_typed_propositions(
        mut self,
        typed_propositions: Vec<CompilerContractProposition>,
    ) -> Self {
        self.typed_propositions = typed_propositions;
        self
    }

    /// Return the unique structurally typed proposition for one exact dense
    /// contract row. Duplicate or stale provenance, and a formula that does
    /// not reparse exactly from the retained canonical body, are rejected.
    #[must_use]
    pub fn typed_proposition(
        &self,
        source_contract_index: usize,
        contract: &Contract,
    ) -> Option<&CompilerContractProposition> {
        let mut candidates = self
            .typed_propositions
            .iter()
            .filter(|proposition| proposition.source_contract_index == source_contract_index);
        let proposition = candidates.next()?;
        if candidates.next().is_some()
            || proposition.kind != contract.kind
            || proposition.body != contract.body
        {
            return None;
        }
        let source = proposition.body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX)?;
        let parsed = crate::parse_spec_expr(source)?;
        if compiler_contract_formula_with_domains(&parsed, &proposition.variable_domains)
            .as_ref()
            != Some(&proposition.formula)
            || compiler_contract_formula_with_domains(
                &proposition.formula,
                &proposition.variable_domains,
            )
            .as_ref()
                != Some(&proposition.formula)
        {
            return None;
        }
        Some(proposition)
    }

    #[must_use]
    pub fn with_loop_contracts(mut self, loop_contracts: Vec<LoopContractSpec>) -> Self {
        self.loop_contracts = loop_contracts;
        self
    }

    #[must_use]
    pub fn with_proof_items(mut self, proof_items: Vec<TrustProofItem>) -> Self {
        self.proof_items = proof_items;
        self
    }
}

/// A typed proposition and its exact compiler-query provenance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerContractProposition {
    pub source_contract_index: usize,
    pub kind: ContractKind,
    /// Canonical compiler-lowered body including its schema prefix.
    pub body: String,
    /// Structural static proposition consumed without reparsing `body`.
    pub formula: Formula,
    /// Canonically name-sorted exact domains for every free variable in
    /// `formula`. Missing, duplicate, conflicting, or unused rows invalidate
    /// the proposition rather than falling back to mathematical `Int`.
    #[serde(default)]
    pub variable_domains: Vec<CompilerContractVariableDomain>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CompilerContractValueDomain {
    Bool,
    MathematicalInt,
    PointerSizedInt { width: u32, signed: bool },
    MachineInt { width: u32, signed: bool },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CompilerContractVariableDomain {
    pub name: String,
    pub domain: CompilerContractValueDomain,
}

impl CompilerContractValueDomain {
    fn logical_sort(self) -> crate::Sort {
        match self {
            Self::Bool => crate::Sort::Bool,
            Self::MathematicalInt
            | Self::PointerSizedInt { .. }
            | Self::MachineInt { .. } => crate::Sort::Int,
        }
    }
}

/// Rebind the parser's deliberately generic free variables to the exact
/// logical sorts implied by a compiler-domain sidecar. Only the closed query
/// proposition vocabulary is accepted. The sidecar must be strictly sorted,
/// unique, and cover exactly the free variables in the tree.
#[must_use]
pub fn compiler_contract_formula_with_domains(
    formula: &Formula,
    variable_domains: &[CompilerContractVariableDomain],
) -> Option<Formula> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Class {
        Bool,
        Numeric,
    }

    fn class(formula: &Formula) -> Option<Class> {
        Some(match formula {
            Formula::Bool(_) => Class::Bool,
            Formula::Int(_) | Formula::UInt(_) => Class::Numeric,
            Formula::Var(_, sort) | Formula::SymVar(_, sort) => match sort {
                crate::Sort::Bool => Class::Bool,
                crate::Sort::Int => Class::Numeric,
                _ => return None,
            },
            Formula::Not(inner) if class(inner)? == Class::Bool => Class::Bool,
            Formula::And(terms) | Formula::Or(terms)
                if terms.iter().all(|term| class(term) == Some(Class::Bool)) =>
            {
                Class::Bool
            }
            Formula::Implies(lhs, rhs)
                if class(lhs)? == Class::Bool && class(rhs)? == Class::Bool =>
            {
                Class::Bool
            }
            Formula::Eq(lhs, rhs) if class(lhs)? == class(rhs)? => Class::Bool,
            Formula::Lt(lhs, rhs)
            | Formula::Le(lhs, rhs)
            | Formula::Gt(lhs, rhs)
            | Formula::Ge(lhs, rhs)
                if class(lhs)? == Class::Numeric && class(rhs)? == Class::Numeric =>
            {
                Class::Bool
            }
            Formula::Add(lhs, rhs)
            | Formula::Sub(lhs, rhs)
            | Formula::Mul(lhs, rhs)
            | Formula::Div(lhs, rhs)
            | Formula::Rem(lhs, rhs)
                if class(lhs)? == Class::Numeric && class(rhs)? == Class::Numeric =>
            {
                Class::Numeric
            }
            Formula::Neg(inner) if class(inner)? == Class::Numeric => Class::Numeric,
            _ => return None,
        })
    }

    for pair in variable_domains.windows(2) {
        if pair[0].name >= pair[1].name {
            return None;
        }
    }
    let domains: BTreeMap<&str, CompilerContractValueDomain> = variable_domains
        .iter()
        .map(|entry| (entry.name.as_str(), entry.domain))
        .collect();
    if domains.len() != variable_domains.len() {
        return None;
    }
    let mut used = std::collections::BTreeSet::new();

    fn bind(
        formula: &Formula,
        domains: &BTreeMap<&str, CompilerContractValueDomain>,
        used: &mut std::collections::BTreeSet<String>,
    ) -> Option<Formula> {
        let boxed = |formula: &Formula,
                     used: &mut std::collections::BTreeSet<String>| {
            bind(formula, domains, used).map(Box::new)
        };
        Some(match formula {
            Formula::Bool(value) => Formula::Bool(*value),
            Formula::Int(value) => Formula::Int(*value),
            Formula::UInt(value) => Formula::UInt(*value),
            Formula::Var(name, _) => {
                let domain = *domains.get(name.as_str())?;
                used.insert(name.clone());
                Formula::Var(name.clone(), domain.logical_sort())
            }
            Formula::SymVar(name, _) => {
                let text = name.as_str();
                let domain = *domains.get(text)?;
                used.insert(text.to_string());
                Formula::SymVar(*name, domain.logical_sort())
            }
            Formula::Not(inner) => Formula::Not(boxed(inner, used)?),
            Formula::And(terms) => Formula::And(
                terms.iter().map(|term| bind(term, domains, used)).collect::<Option<Vec<_>>>()?,
            ),
            Formula::Or(terms) => Formula::Or(
                terms.iter().map(|term| bind(term, domains, used)).collect::<Option<Vec<_>>>()?,
            ),
            Formula::Implies(lhs, rhs) => {
                Formula::Implies(boxed(lhs, used)?, boxed(rhs, used)?)
            }
            Formula::Eq(lhs, rhs) => Formula::Eq(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Lt(lhs, rhs) => Formula::Lt(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Le(lhs, rhs) => Formula::Le(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Gt(lhs, rhs) => Formula::Gt(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Ge(lhs, rhs) => Formula::Ge(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Add(lhs, rhs) => Formula::Add(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Sub(lhs, rhs) => Formula::Sub(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Mul(lhs, rhs) => Formula::Mul(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Div(lhs, rhs) => Formula::Div(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Rem(lhs, rhs) => Formula::Rem(boxed(lhs, used)?, boxed(rhs, used)?),
            Formula::Neg(inner) => Formula::Neg(boxed(inner, used)?),
            _ => return None,
        })
    }

    let rebound = bind(formula, &domains, &mut used)?;
    (used.len() == domains.len()
        && domains.keys().all(|name| used.contains(*name))
        && class(&rebound) == Some(Class::Bool))
        .then_some(rebound)
}

/// Compiler-owned loop clause before its source span is paired with a MIR
/// natural-loop header.  Pairing happens after MIR extraction, where both the
/// source span and the sound dominator-based loop structure are available.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoopContractSpec {
    pub kind: LoopContractKind,
    /// Stable source-loop identity minted by the compiler query. Every clause
    /// on one authored loop carries the same id; consumers must bind the group
    /// once and may not let individual clauses select different MIR headers.
    #[serde(default)]
    pub source_loop_id: u32,
    /// Span of the complete source loop (`while ... { ... }`).
    pub loop_head: SourceSpan,
    /// Exact source header span used only as binding evidence after grouping
    /// by `source_loop_id`; it is not itself a semantic identity key.
    #[serde(default)]
    pub header_span: SourceSpan,
    /// Span of the authored predicate/measure, used for the obligation row.
    pub span: SourceSpan,
    pub body: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LoopContractKind {
    Invariant,
    Decreases,
}

/// Compiler-owned proof items extracted from native Trust proof syntax.
///
/// A native `proof fn` is represented here as data owned by tRustc and passed
/// to verification. It is not modeled as a proc macro, not recovered from
/// source text, and not treated as a runtime Rust function.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompilerProofItemBundle {
    #[serde(default)]
    pub proof_items: Vec<CompilerProofItem>,
    #[serde(default)]
    pub summary: CompilerProofItemSummary,
}

impl CompilerProofItemBundle {
    #[must_use]
    pub fn new(proof_items: Vec<CompilerProofItem>) -> Self {
        let summary = CompilerProofItemSummary::from_items(&proof_items);
        Self { proof_items, summary }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.proof_items.is_empty()
    }
}

/// One compiler-owned proof item in the rustc-independent verification model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerProofItem {
    pub item_id: String,
    pub name: String,
    pub kind: ProofItemKind,
    pub target: ProofItemTarget,
    pub signature: ProofItemSignature,
    pub contracts: CompilerContractBundle,
    pub body: ProofItemBody,
    pub source: ProofItemSource,
    pub span: SourceSpan,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub metadata: Vec<(String, String)>,
}

impl CompilerProofItem {
    #[must_use]
    pub fn is_runtime_erased(&self) -> bool {
        matches!(self.kind, ProofItemKind::ProofFn | ProofItemKind::Lemma)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemKind {
    /// Native `proof fn`: checked as a lemma and erased before codegen.
    ProofFn,
    /// Compiler-synthesized or imported lemma.
    Lemma,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemTarget {
    LocalNamespace,
    Function { def_path: String },
    Contract { function: String, contract_index: usize },
    Crate { name: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ProofItemSignature {
    #[serde(default)]
    pub params: Vec<ProofItemParam>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofItemParam {
    pub name: Option<String>,
    pub ty: String,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemBody {
    CompilerOwned { body_ref: String },
    NativeScript { engine: String, text: String },
    Unsupported { reason: String },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemSource {
    NativeSyntax,
    Synthesized,
    Metadata,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct CompilerProofItemSummary {
    pub total: u32,
    pub proof_fns: u32,
    pub lemmas: u32,
    pub unsupported: u32,
}

impl CompilerProofItemSummary {
    #[must_use]
    pub fn from_items(items: &[CompilerProofItem]) -> Self {
        let mut summary = Self { total: items.len() as u32, ..Self::default() };
        for item in items {
            match item.kind {
                ProofItemKind::ProofFn => summary.proof_fns += 1,
                ProofItemKind::Lemma => summary.lemmas += 1,
            }
            if matches!(item.body, ProofItemBody::Unsupported { .. }) {
                summary.unsupported += 1;
            }
        }
        summary
    }
}

/// Source used for contract metadata during MIR extraction.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractExtractionSource {
    /// A typed compiler contract bundle was supplied by the caller.
    CompilerContractBundle,
    /// Contracts survived as rustc HIR attributes.
    RustcHirAttributes,
    /// No native compiler contract source was available.
    #[default]
    Unavailable,
    /// Legacy source scraping was explicitly enabled for compatibility/debugging.
    CompatDebugSourceScraping,
}

/// Audit record for how contract metadata was obtained.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ContractExtractionReport {
    #[serde(default)]
    pub source: ContractExtractionSource,
    #[serde(default)]
    pub source_scraping_used: bool,
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractKind {
    Requires,
    Ensures,
    Invariant,
    Decreases,
    // trust-wp-style contract extensions for Horn clause lowering.
    /// Loop invariant that must hold at a specific loop header.
    /// Unlike `Invariant` (a general assertion), `LoopInvariant` is lowered
    /// to three CHC obligations: initiation, consecution, and sufficiency.
    LoopInvariant,
    /// Type refinement predicate constraining a variable's domain
    /// (e.g., `x: {v: i32 | v > 0}`). Lowered to Horn clause body constraints.
    TypeRefinement,
    /// Frame condition specifying which variables a function may modify.
    /// Everything not in the modifies set is implicitly preserved.
    Modifies,
}

impl ContractKind {
    /// The attribute name as it appears in source code.
    pub fn attr_name(&self) -> &'static str {
        match self {
            ContractKind::Requires => "requires",
            ContractKind::Ensures => "ensures",
            ContractKind::Invariant => "invariant",
            ContractKind::Decreases => "decreases",
            // trust_wp contract extension attribute names.
            ContractKind::LoopInvariant => "loop_invariant",
            ContractKind::TypeRefinement => "refine",
            ContractKind::Modifies => "modifies",
        }
    }

    /// Format as a source-level attribute string, e.g. `#[requires("x > 0")]`.
    pub fn format_attr(&self, expr: &str) -> String {
        format!("#[{}(\"{}\")]", self.attr_name(), expr)
    }

    /// Parse a contract kind from an attribute name string.
    #[must_use]
    pub fn from_attr_name(name: &str) -> Option<Self> {
        match name {
            "requires" => Some(ContractKind::Requires),
            "ensures" => Some(ContractKind::Ensures),
            "invariant" => Some(ContractKind::Invariant),
            "decreases" => Some(ContractKind::Decreases),
            // trust_wp contract extension attribute names.
            "loop_invariant" => Some(ContractKind::LoopInvariant),
            "refine" => Some(ContractKind::TypeRefinement),
            "modifies" => Some(ContractKind::Modifies),
            _ => None,
        }
    }
}

impl std::fmt::Display for ContractKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.attr_name())
    }
}

// Decreases clause for termination checking.

/// A decreases clause specifying a well-founded measure that must strictly
/// decrease to prove termination.
///
/// The `measure` is a Formula over function locals that maps to a natural
/// number (non-negative integer). Termination is proved by showing:
///   1. The measure is non-negative (bounded below by 0).
///   2. The measure strictly decreases on each iteration/recursive call.
///
/// Trustc extracts first-class function-signature `decreases` clauses for
/// recursion. A loop variant additionally needs authenticated loop-site/header
/// identity and therefore travels through the separate loop-contract schema.
/// The `LoopVariant` representation below is not synthesized from a
/// function-level clause.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecreasesClause {
    /// The expression that must decrease (e.g., `n`, `len - i`).
    pub measure: String,
    /// Where this clause was specified or inferred.
    pub span: SourceSpan,
    /// The kind of termination argument this clause supports.
    pub kind: DecreasesKind,
}

/// Whether the decreases clause applies to a loop or a recursive function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DecreasesKind {
    /// Loop variant: measure decreases on each iteration of the loop at the
    /// given back-edge block. First-class loop clauses use the separate
    /// identity-bound loop-contract lane; this is not produced from a
    /// function-level `decreases` clause.
    LoopVariant { header_block: usize },
    /// Recursive function: measure decreases on each recursive call.
    Recursion,
}

/// Trust metadata extracted from local items.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct TrustMetadata {
    pub contracts: Vec<Contract>,
    #[serde(default)]
    pub proof_items: Vec<TrustProofItem>,
    pub trust_annotations: Vec<TrustAnnotation>,
    // Structured spec from parsed contracts.
    #[serde(default)]
    pub spec: FunctionSpec,
    /// Records whether contracts came from native compiler facts or from the
    /// retired compatibility source scraper.
    #[serde(default)]
    pub contract_extraction: ContractExtractionReport,
}

/// An explicit trust annotation extracted from source attributes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustAnnotation {
    pub kind: TrustAnnotationKind,
    pub span: SourceSpan,
    pub body: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustAnnotationKind {
    Boundary,
    Model,
    Assumption,
    /// Trust (T9 contract-panic): `#[trust(contract_panic(message_contains = "..."))]`
    /// — a declared, INTENTIONAL fail-closed panic contract. The enclosing
    /// `TrustAnnotation::body` carries the `message_contains` payload (exactly as
    /// `Assumption` carries the assume body): a panic-freedom obligation for a
    /// panic call whose const-str message CONTAINS this payload may be
    /// reclassified as a contract panic (never a proof; always counted visibly).
    /// The extraction layer rejects a malformed/empty payload as a hard error —
    /// an annotation that could never match anything must not extract silently.
    ContractPanic,
}

// Trust: #828 — function signatures need structural hashing through nested types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FnSig {
    pub params: Vec<Ty>,
    pub ret: Box<Ty>,
}

/// Trust: PHASE 4 — one constructor of an ENUM `Ty::Adt`.
///
/// At the MIR statement level Trust already carries this data
/// (`StateMachine`/`VariantDef`-shaped via discriminants + `SwitchInt` target
/// tag sets); P4 lifts it to the TYPE level so an enum is no longer
/// indistinguishable from a struct over the union of its fields. A
/// single-constructor "struct" `Ty::Adt` has `variants: []`; an n-constructor
/// enum has `n` `VariantDef`s. `trust-clean` reflects these into a real
/// multi-constructor Clean inductive (recursor / casesOn / noConfusion derived
/// by the kernel), and the `discriminant` grounds the `SwitchInt` tag set so an
/// exhaustive match's `otherwise -> Unreachable` discharges via the inductive's
/// total `casesOn`.
/// Trust (B3-1): the `#[repr(iN)]`/`#[repr(uN)]` tag-representation hint an
/// enum pins, carried verbatim from rustc so the oracle bridge can rebuild a
/// trust-ir `EnumDef` whose `canonical_tag_repr` matches the THIR producer's
/// byte-for-byte. Mirrors `trust_ir::EnumTagRepr` (trust-types stays
/// dependency-free of trust-ir; the bridge maps 1:1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EnumReprHint {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

/// Lossless Serde boundary for the B3-1 faithful-enum marker.
///
/// `Option<Option<EnumReprHint>>` has three meaningful in-memory states, but a
/// human-readable Serde format normally writes both `None` and `Some(None)` as
/// `null`.  That would erase the eligibility bit when JSON is persisted.  Keep
/// the existing Rust type (and therefore every consumer) while assigning the
/// one formerly ambiguous state an explicit human-readable marker:
///
/// * `None` -> `null` (also the fail-closed interpretation of legacy `null`);
/// * `Some(None)` -> `{ "state": "eligible_rust_default" }`;
/// * `Some(Some(I8))` -> `"I8"` (the pre-existing explicit-repr spelling).
///
/// Non-human-readable formats already encode both `Option` discriminants, so
/// delegate to the derived nested-`Option` representation byte-for-byte.  This
/// preserves existing bincode payloads while making JSON lossless.  Missing
/// fields remain outer `None` through the field's `#[serde(default)]`.
mod faithful_enum_repr_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::EnumReprHint;

    #[derive(Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    struct HumanMarker {
        state: HumanMarkerState,
    }

    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    enum HumanMarkerState {
        EligibleRustDefault,
    }

    #[derive(Deserialize)]
    #[serde(untagged)]
    enum HumanInput {
        Marker(HumanMarker),
        Legacy(Option<EnumReprHint>),
    }

    pub(super) fn serialize<S>(
        value: &Option<Option<EnumReprHint>>,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if !serializer.is_human_readable() {
            return value.serialize(serializer);
        }
        match value {
            None => serializer.serialize_none(),
            Some(None) => {
                HumanMarker { state: HumanMarkerState::EligibleRustDefault }.serialize(serializer)
            }
            Some(Some(repr)) => repr.serialize(serializer),
        }
    }

    pub(super) fn deserialize<'de, D>(
        deserializer: D,
    ) -> Result<Option<Option<EnumReprHint>>, D::Error>
    where
        D: Deserializer<'de>,
    {
        if !deserializer.is_human_readable() {
            return Option::<Option<EnumReprHint>>::deserialize(deserializer);
        }
        match HumanInput::deserialize(deserializer)? {
            HumanInput::Marker(HumanMarker { state: HumanMarkerState::EligibleRustDefault }) => {
                Ok(Some(None))
            }
            HumanInput::Legacy(value) => Ok(value.map(Some)),
        }
    }
}

/// Trust (B3-4 T3): rustc's concrete layout for an extracted ADT, carried on
/// the FAITHFUL differential lane so the trust-ir bridge can fill the same
/// StructDef size/align/offsets/repr the THIR producer fills (T2) — the
/// two-producer layout-agreement census keys on it. Offsets are byte offsets
/// in SOURCE-DECLARATION order, parallel to the Adt's `fields` view. `repr`
/// mirrors trust-ir's StructRepr one-hint collapse (transparent > packed >
/// C > Rust); the numeric fields carry the actual bytes regardless.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AdtLayoutInfo {
    pub size: u64,
    pub align: u64,
    /// Per-field byte offset, source-declaration indexed (parallel to `fields`).
    pub field_offsets: Vec<u64>,
    /// One-hint repr class: "rust" | "c" | "transparent" | "packed:<bytes>".
    pub repr: String,
}

/// Trust (B3-3): how a multi-variant enum's discriminant is encoded in
/// memory. Mirrors trust_ir::EnumTagEncoding (trust-types stays
/// dependency-free of trust-ir; the bridge maps 1:1). `Direct` is a plain tag
/// word whose value IS the effective discriminant; `Niche` stores the
/// discriminant inside an otherwise-invalid bit pattern of a payload field —
/// the untagged variant is encoded by the field holding its own valid value,
/// each niche variant by `niche_start + (variant - niche_variants_start)`
/// (wrapping at the lane width) at `niche_offset`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EnumTagEncodingInfo {
    Direct {
        tag_offset: u64,
        /// The rustc tag scalar's width/signedness — a CHECK CARRIER, not part
        /// of the trust-ir descriptor (whose Direct tag lane is normatively
        /// sized at `canonical_tag_repr`): the bridge declines the copy-through
        /// when this disagrees with the canonical repr it computes, so a
        /// rustc-widened tag can never mint a descriptor whose normative tag
        /// claim is wrong.
        tag_ty: EnumReprHint,
    },
    Niche {
        untagged_variant: u32,
        niche_variants_start: u32,
        niche_variants_end: u32,
        niche_start: u128,
        niche_offset: u64,
        /// In-memory width/signedness of the niche scalar (reuses the
        /// EnumReprHint carrier exactly as its doc's "bridge maps 1:1" rule).
        niche_ty: EnumReprHint,
    },
}

/// Trust (B3-3): the CONCRETE memory layout of an enum as rustc computed it —
/// the trust-ir-free twin of trust_ir::EnumLayoutDescriptor (normative when
/// present on the trust-ir side; the bridge copies this through verbatim).
/// `variant_field_offsets` are per-variant, per-field byte offsets in
/// SOURCE-DECLARATION order, parallel to each variant's fields.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnumLayoutInfo {
    pub encoding: EnumTagEncodingInfo,
    pub size: u64,
    pub align: u64,
    pub variant_field_offsets: Vec<Vec<u64>>,
}


#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VariantDef {
    /// Variant name (e.g. `Some`, `None`, `A`, `B`).
    pub name: String,
    /// The discriminant tag this variant carries in `SwitchInt`. Stored as
    /// `i128` so it spans both signed (`#[repr(i8)] enum`) and the common
    /// non-negative tags; the `SwitchInt` tag set is `u128` and converts in.
    pub discriminant: i128,
    /// This variant's own fields, in MIR definition order: `(field_name, ty)`.
    /// A field-less variant (`None`, `B`) has `fields: []` (a nullary
    /// constructor). A tuple variant (`Some(T)`) names fields `0`, `1`, … .
    pub fields: Vec<(String, Ty)>,
}

/// Trust: piece #7a — the identity of a const-generic length parameter, used as
/// the key for [`Ty::SymArray`]'s symbolic length. `index` is the const-param's
/// position within the enclosing item's generics (unique WITHIN one item, so `M`
/// and `N` in the same fn never collide); `name` (e.g. `"N"`) makes the minted
/// SMT symbol readable AND — critically — makes it byte-match the symbol the
/// const-generic VALUE `N` produces when read as a guard operand. Both fields are
/// carried so a rename-only or reorder-only body cannot silently alias two
/// distinct params onto one symbol. Rendered to an SMT symbol by
/// [`const_param_symbol`].
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConstLen {
    pub index: u32,
    pub name: String,
}

/// Trust: piece #7a — sanitize a const-param name fragment so a non-identifier
/// name cannot break the SMT symbol. Mirrors the sanitization used at the
/// operand-lowering sites in trust-vcgen; kept here so ALL three mint sites
/// (array length in `ty_convert`, value operand in `convert`/`lib.rs`, native
/// path in `chc.rs`) render a BYTE-IDENTICAL string via one shared helper.
fn sanitize_const_param_fragment(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push('_');
    }
    out
}

/// Trust: piece #7a — the ONE canonical SMT symbol for a const-generic value /
/// array length, keyed on the param IDENTITY (`index` + `name`), NEVER on
/// `(width, signed)`. Called from every mint site so the guard's `N` and the
/// array's length `N` are the SAME SMT term (and a distinct param `M` stays a
/// distinct term). Deliberately does NOT end with `__slice_len`, so the
/// suffix-gated `conjoin_slice_len_bounds` pass will not attach a spurious
/// `0 <= N <= isize::MAX` where-fact (INV-4). The `__trust_constparam_` prefix is
/// registered in trust-vcgen's freshen deny-list (`is_aliasing_opaque_symbol_name`)
/// so the R1 σ callsite path splits distinct occurrences apart.
pub fn const_param_symbol(index: u32, name: &str) -> String {
    format!("__trust_constparam_{}_{}", index, sanitize_const_param_fragment(name))
}

/// Trust: W19 mutators inc-1 (2026-07-24) — the ADT KIND discriminator carried on
/// [`Ty::Adt`]. The union/struct/enum distinction is ERASED at extraction (a UNION
/// lowers byte-identically to a struct — see `trust-mir-extract::ty_convert`, "treat
/// structs and unions identically"), so a `Ty::Adt` alone cannot tell a struct from a
/// union. That erasure is UNSOUND for the field-setter frame surface: the total
/// `∀k≠fld, other field unchanged` frame is OPERATIONALLY FALSE for a union (union
/// fields overlap at byte offset 0). This kind carries the discriminator so the
/// setter recognizer's G-STRUCT-KIND gate (`clean_ground::sem_field_set_shape_of`) can
/// decline a union (and an enum, and an un-migrated `None`) FAIL-CLOSED. Populated ONLY
/// by `trust-mir-extract` from rustc's `AdtDef` (`is_struct`/`is_union`/`is_enum`);
/// every hand-built / synthetic `Ty::Adt` leaves it `None` (the fail-closed default).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AdtKind {
    /// A `struct` — non-overlapping fields at distinct byte offsets. The ONLY kind the
    /// field-setter frame surface admits (its per-field frame is operationally sound).
    Struct,
    /// A `union` — fields OVERLAP at byte offset 0. The per-field independence frame is
    /// operationally FALSE, so the setter recognizer declines it.
    Union,
    /// An `enum` — a tagged sum. Out of the single-anonymous-constructor setter fragment.
    Enum,
}

/// Simplified type representation.
// Trust: #828 — MIR function-like types require `Ty` to participate in hashing.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Ty {
    Bool,
    Int {
        width: u32,
        signed: bool,
    },
    /// Trust (v25 B1, ADDITIVE like `SymArray`): pointer-width integer — Rust
    /// `isize`/`usize` carried FAITHFULLY instead of the historical
    /// `Int{width: pointer_width}` collapse that destroyed the identity
    /// before the trust-ir bridge could see it. Emitted ONLY by the
    /// faithful-extraction path (`extract_function_faithful`, the trust-ir
    /// differential's lane); the verifier pipeline keeps receiving the
    /// legacy `Int` spelling until its migration wave, so its ~700 direct
    /// `Ty::Int{..}` matches never silently fail-close on this variant.
    /// Width resolves to the pinned 64-bit target (`int_width` → 64).
    PtrSizedInt {
        signed: bool,
    },
    /// Trust (v25 B1, same lane as `PtrSizedInt`): Rust `char` carried
    /// faithfully (legacy path spells it `Int{width:32, signed:false}`).
    /// NOT an integer for arithmetic purposes; `int_width` still reports 32
    /// so width-driven plumbing stays correct.
    Char,
    Float {
        width: u32,
    },
    Ref {
        mutable: bool,
        inner: Box<Ty>,
    },
    // Raw pointer type for provenance-aware pointer modeling.
    // Distinguishes `*const T` (mutable=false) from `*mut T` (mutable=true).
    RawPtr {
        mutable: bool,
        pointee: Box<Ty>,
    },
    Slice {
        elem: Box<Ty>,
    },
    /// Trust (B2-2, RFC TRUST_IR_V2): the `str` DST, DISTINCT from `[u8]`. Emitted by
    /// `trust-mir-extract`'s ty_convert ONLY on the FAITHFUL-extraction lane (the B1
    /// `PtrSizedInt`/`Char` precedent) so the trust-ir bridge can spell `&str` as the
    /// format's first-class `FatPtr(FatPtrKind::Str)` — structurally equal to the
    /// producer's. The legacy verifier lane keeps the historical `Slice { elem: u8 }`
    /// conflation byte-identically.
    Str,
    Array {
        elem: Box<Ty>,
        len: u64,
    },
    // Trust: piece #7a — an un-monomorphized `[T; N]` whose length is a
    // const-generic PARAM (`N`), not a concrete `u64`. ADDITIVE variant: the
    // concrete-length `Ty::Array` (and its ~40 consumers) stays BYTE-IDENTICAL,
    // so no consumer silently mis-reads a symbolic length as a concrete `0`. A
    // `SymArray`'s length is modeled as the SMT symbol
    // `__trust_constparam_{index}_{name}` (see [`const_param_symbol`]), the SAME
    // symbol the const-generic VALUE `N` lowers to, so a guard `if i < N`
    // discharges the bounds VC for `a[i]`. SOUNDNESS: the length symbol is keyed
    // on the const-param IDENTITY (`ParamConst.index` + `name`), NEVER on
    // `(width, signed)` — so two DISTINCT usize const-params `M`, `N` get
    // DISTINCT symbols and never alias (the "M==N collision" false-proof). The
    // length of an array is its immutable type parameter, so no mutation channel
    // (`&mut`, swap, setter, raw store) can change it — the symbol needs no
    // havoc/versioning. Consumers that must fail-closed on an unknown symbolic
    // length simply omit an arm and fall through to their existing `_ =>`.
    SymArray {
        elem: Box<Ty>,
        len_sym: ConstLen,
    },
    Tuple(Vec<Ty>),
    Adt {
        name: String,
        fields: Vec<(String, Ty)>,
        // Trust: PHASE 4 — variant/discriminant structure for ENUMS. ADDITIVE:
        // a STRUCT has `variants: []` (the `fields` are its single anonymous
        // constructor's fields, exactly as before P4); an ENUM has one
        // `VariantDef` per constructor, each carrying its discriminant tag and
        // its own field list. `fields` is RETAINED as the union/struct view so
        // every pre-P4 `Ty::Adt { fields, .. }` consumer keeps working
        // unchanged. The variant structure is what `trust-clean` reflects into a
        // real multi-constructor Clean inductive (with auto-derived recursor /
        // casesOn / noConfusion) instead of an anonymous product. Use
        // [`Ty::adt`] (struct) / [`Ty::adt_enum`] (enum) to construct, so new
        // call sites stay forward-compatible if the shape grows again.
        //
        // `#[serde(default)]`: pre-P4 serialized `Ty::Adt` JSON (existing dump
        // fixtures, caches, proof certificates) has NO `variants` key — it
        // deserializes to an empty `variants` (i.e. a struct), preserving exact
        // backward compatibility. This is essential: without it, every previously
        // serialized struct/enum would fail to deserialize.
        #[serde(default)]
        variants: Vec<VariantDef>,
        // Trust: enum-disc-full-native — niche-safety classification for the
        // discriminant-read range fact in the NATIVE -full bridge. `true` ONLY
        // when this is a fieldless/Direct-tag-encoded enum whose `Discriminant`
        // read yields a tag in `[min_disc, max_disc]` (i.e. layout
        // `Variants::Multiple { tag_encoding: TagEncoding::Direct, .. }`), so the
        // native lowerer may soundly `Assume(min_disc <= disc <= max_disc)` over
        // the extracted tag (which `arr[e as usize]` then consumes). It is `false`
        // for EVERY niche-encoded enum (`Option<&T>`, `Result<bool, ()>`,
        // `Option<NonZeroU8>` — where the discriminant read does NOT recover a
        // dense `0..n` tag), for structs, and for any case where the layout query
        // is unavailable (no `typing_env`) or fails — all FAIL-CLOSED.
        //
        // `#[serde(default)]`: defaults to `false`, so every PRE-EXISTING
        // serialized `Ty::Adt` (caches, proof certs, dump fixtures) deserializes
        // to the conservative `false` — never synthesizing the range fact for a
        // type that was lowered before this classification existed. This is a
        // SEPARATE scalar flag; it does NOT touch `fields` (which keeps `__tag`
        // for `SetDiscriminant`) nor `variants`.
        #[serde(default)]
        disc_index_safe: bool,
        // Trust (B3-1, RFC TRUST_IR_V2): the FAITHFUL-lane first-class-enum marker +
        // tag-repr carrier. `Some` ONLY when (a) the extractor ran under the
        // FaithfulScalarsGuard (the differential's lane — verifier lanes never see
        // it, the B1 PtrSizedInt / B2-2 Ty::Str shielding precedent) AND (b) the
        // enum is ELIGIBLE for the format's first-class EnumDef spelling
        // (mirrors the THIR producer's register_enum: every variant field
        // scalar-mappable, direct tag encoding — disc_index_safe — resolvable
        // 64-bit discriminants). Carries the `#[repr(iN)]`-style tag hint (as
        // `Some(Some(hint))`) or its absence (`Some(None)`) because the producer
        // pins the hint on ITS EnumDef — omitting it here would make two
        // structurally-equal enums disagree on canonical_tag_repr (a false
        // NotRun). Outer `None` = the historical flattened-struct semantics,
        // the fail-safe direction for every flag-ignorant consumer.
        #[serde(default, with = "faithful_enum_repr_serde")]
        faithful_enum_repr: Option<Option<EnumReprHint>>,
        // Trust (B3-4 T3): the CONCRETE layout of this ADT as rustc computed
        // it — size/align in bytes, per-field byte offsets in SOURCE-
        // DECLARATION order (parallel to `fields`), and the repr class. `Some`
        // ONLY when the extractor could run `layout_of` on a fully-concrete
        // type (the producer's T2 gates mirrored); `None` = unknown, the
        // fail-safe every layout-ignorant consumer already assumes. ADDITIVE:
        // `#[serde(default)]` keeps every pre-T3 serialized Ty::Adt (dumps,
        // caches, proof certs) deserializing unchanged; verifier-lane
        // consumers pattern-match `Ty::Adt { .. }` and never read it.
        #[serde(default)]
        layout: Option<Box<AdtLayoutInfo>>,
        // Trust (B3-3): the CONCRETE enum layout (tag/niche encoding + per-
        // variant offsets) as rustc computed it — the trust-ir descriptor
        // twin, filled by the extractor under the T3 gates and copied through
        // by the bridge into trust_ir::EnumDef.layout. `None` = unknown (the
        // pre-B3-3 semantics, every layout-ignorant consumer's fail-safe).
        // ADDITIVE + `#[serde(default)]`, same discipline as `layout` above.
        #[serde(default)]
        enum_layout: Option<Box<EnumLayoutInfo>>,
        // Trust: W19 mutators inc-1 (2026-07-24) — the struct/union/enum
        // discriminator. `Some(Struct)`/`Some(Union)`/`Some(Enum)` ONLY when
        // `trust-mir-extract` lowered this ADT from a rustc `AdtDef` (which knows
        // the kind); `None` for every hand-built / synthetic / pre-migration
        // serialized `Ty::Adt`. Load-bearing SOLELY for the field-setter frame
        // surface's G-STRUCT-KIND gate, which mints ONLY on `Some(Struct)` and
        // declines `Some(Union)` (overlapping fields), `Some(Enum)`, and `None`
        // (un-migrated) FAIL-CLOSED. `#[serde(default)]`: a pre-W19 serialized
        // `Ty::Adt` (dumps, caches, proof certs) has NO `adt_kind` key and
        // deserializes to `None`, so it declines rather than optimistically
        // minting. Like `layout`, a `None` is stripped from the stable content
        // hash (`stable_model_json`) so pre-W19 pins are unperturbed; a `Some`
        // IS hash-visible (it asserts the ADT kind and belongs in identity).
        #[serde(default)]
        adt_kind: Option<AdtKind>,
    },
    /// A recursive algebraic datatype, modeled with the SMT-LIB datatype theory
    /// (Lever A). This is the lowering target for a *recursive* enum/struct
    /// (`clean_kernel::Expr`, `Level`, `Name`, …) that the flat `Ty::Adt`
    /// encoding cannot represent because a field references the type itself.
    ///
    /// `variants` is `[(ctor_name, [(field_name, field_ty)])]`. SMT datatypes are
    /// natively recursive, so a field whose type is this datatype (or another
    /// datatype that transitively references back) is recorded as a BY-NAME
    /// reference: `Ty::Datatype { name: <referent>, variants: vec![] }`. An empty
    /// `variants` vector therefore means "a back-reference to the datatype named
    /// `name`, whose full definition appears at its defining occurrence" — never
    /// "a datatype with zero variants". The defining occurrence (a local's own
    /// declared type) always carries the full, non-empty variant list.
    ///
    /// SOUNDNESS: a datatype value carries NO obligation by itself; it only
    /// introduces a sound SMT-LIB datatype declaration (constructor/selector/
    /// tester axioms, injectivity, acyclicity — all from the standard datatype
    /// theory). A fresh datatype-sorted constant is unconstrained, so it can
    /// never make the solver context vacuously UNSAT (which would false-prove).
    /// Scalar fields read out of a datatype value are still modeled with their
    /// own concrete scalar sort, so genuine overflow/bounds obligations on those
    /// fields remain refutable.
    Datatype {
        /// Datatype (sort) name — the SMT-LIB sort identifier.
        name: String,
        /// One entry per variant/constructor: `(ctor_name, [(field_name, field_ty)])`.
        /// Empty for a by-name recursive reference (see the type-level doc).
        variants: Vec<(String, Vec<(String, Ty)>)>,
    },
    /// Machine bitvector of given width (for binary-lifted code before type recovery).
    // Trust: #575 — return type analysis produces Bv(32) / Bv(64) for machine registers.
    Bv(u32),
    Unit,
    Never,
    // Trust: #828 — preserve closure captures for full MIR type coverage.
    Closure {
        name: String,
        upvars: Vec<Ty>,
        /// Trust (B6, RFC TRUST_IR_V2 — v25 Fn/ByValue slice): the closure's CALL
        /// signature + inferred kind, filled by `trust-mir-extract`'s `ty_convert`
        /// from tcx (`None` when unresolved or constructed away from tcx — e.g. the
        /// bridge's name/arity-driven refinements — which fails the first-class
        /// respell closed). This is what lets the trust-ir bridge spell a by-value
        /// FnOnce env as the format's first-class `Ty::Closure(ClosureTyId)`
        /// STRUCTURALLY EQUAL to the producer's (`ClosureTy { func, captures }`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        call: Option<Box<ClosureCallSig>>,
    },
    // Trust: #828 — model named function items with their signature.
    FnDef {
        name: String,
        sig: Box<FnSig>,
    },
    // Trust: #828 — model first-class function pointer types.
    FnPtr {
        sig: Box<FnSig>,
    },
    // Trust: #828 — represent trait objects as dynamic dispatch types.
    Dynamic {
        trait_name: String,
    },
    // Trust: #828 — preserve coroutine captures for full MIR type coverage.
    Coroutine {
        name: String,
        upvars: Vec<Ty>,
    },
    /// Rust type that is valid MIR but not represented precisely enough by
    /// Trust's proof model yet. VC generation must emit `UnsupportedMir` for
    /// any function whose locals, return type, projections, or aggregate types
    /// contain this marker.
    Unsupported {
        kind: String,
        detail: String,
    },
}

/// Trust (R3, generics): the EXACT `kind` / `detail` pair `trust-mir-extract`'s
/// `normalize_alias` stamps on a PARAM-BEARING projection/opaque/inherent alias
/// (`<S as Serializer>::Ok`, `<B as Flags>::Bits`) — the pre-monomorphization
/// appearance of an associated type whose projection typeck itself could not
/// resolve. Shared as `pub const`s so the producer (extraction), the vcgen
/// declaration relaxation, and the bridge's opaque lowering match EXACTLY this
/// fail-closed class and can never drift apart. SCOPE (load-bearing): ONLY this
/// detail — a MONOMORPHIC alias that merely failed normalization ("did not
/// resolve…", "nest ADTs too deep", "no typing env…") may have a concrete
/// primitive runtime type on which MIR performs primitive ops, so those details
/// stay fail-closed everywhere.
pub const PRE_MONO_ALIAS_KIND: &str = "TyKind::Alias";
pub const PRE_MONO_ALIAS_DETAIL: &str = "alias still has generic parameters (pre-monomorphization)";

impl Ty {
    /// Stable semantic shape hash used by audited type-layout pins.
    ///
    /// Default-valued faithful-enum metadata is canonicalized exactly like
    /// [`VerifiableFunction::content_hash`], while ordinary JSON and binary
    /// serialization retain every field needed for lossless round-trips.
    pub fn try_stable_shape_hash(&self) -> Result<String, serde_json::Error> {
        stable_model_json(self).map(|json| stable_sha256_hex(json.as_bytes()))
    }

    /// Trust (R3, generics): is this the pre-monomorphization param-bearing
    /// alias marker ([`PRE_MONO_ALIAS_KIND`]/[`PRE_MONO_ALIAS_DETAIL`])? A value
    /// of such a type is opaque to rustc's own typeck (had typeck normalized the
    /// projection — e.g. under a `T: Tr<Out = u32>` where-clause — the MIR local
    /// would already be spelled at the concrete type and never reach the
    /// marker), therefore no primitive MIR operation can be typed at it; every
    /// use is a trait call / move / aggregate placement / drop, each of which
    /// fails closed independently.
    #[must_use]
    pub fn is_pre_mono_alias_marker(&self) -> bool {
        matches!(self, Ty::Unsupported { kind, detail }
            if kind == PRE_MONO_ALIAS_KIND && detail == PRE_MONO_ALIAS_DETAIL)
    }

    /// Trust: PHASE 4 — construct a STRUCT `Ty::Adt` (no variants). This is the
    /// forward-compatible constructor for the common pre-P4 shape: it sets
    /// `variants: []`, so call sites do not have to spell the new field.
    #[must_use]
    pub fn adt(name: impl Into<String>, fields: Vec<(String, Ty)>) -> Ty {
        // Trust: enum-disc-full-native — a struct is never discriminant-index-safe.
        Ty::Adt {
            name: name.into(),
            fields,
            variants: Vec::new(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None, enum_layout: None,
            // Trust: W19 — the generic `Ty::adt` constructor is kind-agnostic (a
            // synthetic/hand-built struct). Only `trust-mir-extract` stamps a real
            // `Some(kind)` from rustc's `AdtDef`; leaving it `None` keeps every
            // existing synthetic construction fail-closed (declines G-STRUCT-KIND)
            // and hash-stable (a `None` is stripped from the content hash).
            adt_kind: None,
        }
    }

    /// Trust: PHASE 4 — construct an ENUM `Ty::Adt` from its variant defs. The
    /// `fields` (struct/union view) are derived as the deduplicated union of all
    /// variant fields (first occurrence wins), preserving the pre-P4 invariant
    /// that `fields` is a valid struct-shaped view of the ADT.
    #[must_use]
    pub fn adt_enum(name: impl Into<String>, variants: Vec<VariantDef>) -> Ty {
        let mut fields: Vec<(String, Ty)> = Vec::new();
        for v in &variants {
            for (fname, fty) in &v.fields {
                if !fields.iter().any(|(n, _)| n == fname) {
                    fields.push((fname.clone(), fty.clone()));
                }
            }
        }
        // Trust: enum-disc-full-native — `adt_enum` cannot consult the rustc
        // layout (it has only the abstract variant list), so it conservatively
        // leaves `disc_index_safe = false`. ONLY the rustc-driven extractor
        // (`ty_convert::lower_enum_adt`), which CAN query `tcx.layout_of`, sets
        // the flag true (and only for a `Variants::Multiple { Direct }` layout).
        Ty::Adt {
            name: name.into(),
            fields,
            variants,
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None, enum_layout: None,
            // Trust: W19 — kind-agnostic synthetic constructor (see `Ty::adt`).
            adt_kind: None,
        }
    }

    /// Trust: enum-disc-full-native — like [`Ty::adt_enum`] but carrying the
    /// niche-safety classification computed by the rustc-layout-aware extractor.
    /// `disc_index_safe` must be `true` ONLY for a fieldless/Direct-tag-encoded
    /// enum whose `Discriminant` read yields a dense tag in `[min_disc, max_disc]`.
    #[must_use]
    pub fn adt_enum_with_disc_safety(
        name: impl Into<String>,
        variants: Vec<VariantDef>,
        disc_index_safe: bool,
    ) -> Ty {
        let mut fields: Vec<(String, Ty)> = Vec::new();
        for v in &variants {
            for (fname, fty) in &v.fields {
                if !fields.iter().any(|(n, _)| n == fname) {
                    fields.push((fname.clone(), fty.clone()));
                }
            }
        }
        // Trust: W19 — kind-agnostic synthetic constructor (see `Ty::adt`).
        Ty::Adt { layout: None,  name: name.into(), fields, variants, disc_index_safe, faithful_enum_repr: None, enum_layout: None, adt_kind: None }
    }

    /// Trust: enum-disc-full-native — whether this `Ty::Adt` was classified as
    /// discriminant-index-safe by the layout-aware extractor (Direct tag
    /// encoding, dense `0..n` discriminant). `false` for every other type and
    /// for any ADT lowered/deserialized before this classification existed.
    #[must_use]
    pub fn disc_index_safe(&self) -> bool {
        matches!(self, Ty::Adt { disc_index_safe: true, .. })
    }

    /// Structural `Ty` equality that IGNORES the internal `disc_index_safe` flag on
    /// `Adt`s (recursively, at every nesting level). This flag is a lowering
    /// REPRESENTATION artifact — it can be computed differently for the SAME Rust type
    /// in different contexts (e.g. an `[Op; N]` element vs a `[Op]` element). A plain
    /// `==` then treats two spellings of one type as distinct, which false-rejects
    /// value-preserving coercions (array→slice unsize) as "element type changes" and
    /// blocks lowering/verification. This compares modulo that flag while STILL
    /// distinguishing genuinely different types (name / fields / variants / discriminants).
    #[must_use]
    pub fn eq_ignoring_disc_index_safe(&self, other: &Ty) -> bool {
        fn fields_eq(a: &[(String, Ty)], b: &[(String, Ty)]) -> bool {
            a.len() == b.len()
                && a.iter()
                    .zip(b)
                    .all(|((n1, t1), (n2, t2))| n1 == n2 && t1.eq_ignoring_disc_index_safe(t2))
        }
        match (self, other) {
            (
                Ty::Adt { layout: _,
                    enum_layout: _,
                    name: n1,
                    fields: f1,
                    variants: v1,
                    disc_index_safe: _,
                    faithful_enum_repr: _,
                    // Trust: W19 — a representation-level discriminator (like
                    // disc_index_safe/layout), ignored by this modulo-flag equality.
                    adt_kind: _,
                },
                Ty::Adt { layout: _,
                    enum_layout: _,
                    name: n2,
                    fields: f2,
                    variants: v2,
                    disc_index_safe: _,
                    faithful_enum_repr: _,
                    adt_kind: _,
                },
            ) => {
                n1 == n2
                    && fields_eq(f1, f2)
                    && v1.len() == v2.len()
                    && v1.iter().zip(v2).all(|(x, y)| {
                        x.name == y.name
                            && x.discriminant == y.discriminant
                            && fields_eq(&x.fields, &y.fields)
                    })
            }
            (Ty::Ref { mutable: m1, inner: i1 }, Ty::Ref { mutable: m2, inner: i2 }) => {
                m1 == m2 && i1.eq_ignoring_disc_index_safe(i2)
            }
            (Ty::RawPtr { mutable: m1, pointee: p1 }, Ty::RawPtr { mutable: m2, pointee: p2 }) => {
                m1 == m2 && p1.eq_ignoring_disc_index_safe(p2)
            }
            (Ty::Slice { elem: e1 }, Ty::Slice { elem: e2 }) => e1.eq_ignoring_disc_index_safe(e2),
            (Ty::Array { elem: e1, len: l1 }, Ty::Array { elem: e2, len: l2 }) => {
                l1 == l2 && e1.eq_ignoring_disc_index_safe(e2)
            }
            (Ty::Tuple(t1), Ty::Tuple(t2)) => {
                t1.len() == t2.len()
                    && t1.iter().zip(t2).all(|(x, y)| x.eq_ignoring_disc_index_safe(y))
            }
            // Every other `Ty` variant carries no `disc_index_safe`, so structural
            // equality is exact for them.
            _ => self == other,
        }
    }

    /// Trust: PHASE 4 — whether this `Ty::Adt` is an ENUM (has ≥1 variant). A
    /// struct (or non-Adt) returns `false`.
    #[must_use]
    pub fn is_enum_adt(&self) -> bool {
        matches!(self, Ty::Adt { variants, .. } if !variants.is_empty())
    }

    /// Lever A — whether this is a modeled recursive `Ty::Datatype` (any form,
    /// including a by-name back-reference). A non-datatype returns `false`.
    #[must_use]
    pub fn is_datatype(&self) -> bool {
        matches!(self, Ty::Datatype { .. })
    }

    /// Number of variants of a modeled enum type. `Some(n)` for an enum
    /// (`Ty::Datatype` or `Ty::Adt`) that carries a non-empty variant list,
    /// where `n` is its variant count; `None` for a struct (no variants), a
    /// by-name datatype reference (compacted field, empty variants), or any
    /// non-ADT type. A real enum value's discriminant is ALWAYS one of `0..n`,
    /// so `n` is exactly the sound upper bound for a discriminant range fact.
    #[must_use]
    pub fn num_variants(&self) -> Option<usize> {
        match self {
            Ty::Datatype { variants, .. } if !variants.is_empty() => Some(variants.len()),
            Ty::Adt { variants, .. } if !variants.is_empty() => Some(variants.len()),
            _ => None,
        }
    }

    /// For a `Ty::Datatype`, returns the field types of variant `variant_idx`,
    /// in declaration order. `None` for a non-datatype or an out-of-range
    /// variant index. Used by projection resolution to type an enum-payload
    /// read (`(x as Variant).field`).
    #[must_use]
    pub fn datatype_variant_field_tys(&self, variant_idx: usize) -> Option<Vec<&Ty>> {
        match self {
            Ty::Datatype { variants, .. } => variants
                .get(variant_idx)
                .map(|(_, fields)| fields.iter().map(|(_, ty)| ty).collect()),
            _ => None,
        }
    }

    /// Returns the bit width for integer types.
    pub fn int_width(&self) -> Option<u32> {
        match self {
            Ty::Int { width, .. } => Some(*width),
            // v25 B1 faithful spellings: pointer-width ints at the pinned
            // 64-bit target; char's carrier is 32 bits.
            Ty::PtrSizedInt { .. } => Some(64),
            Ty::Char => Some(32),
            _ => None,
        }
    }

    /// Returns true if this is a signed integer type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Ty::Int { signed: true, .. } | Ty::PtrSizedInt { signed: true })
    }

    /// Returns true if this is any integer type.
    pub fn is_integer(&self) -> bool {
        matches!(self, Ty::Int { .. })
    }

    /// Returns true if this is any floating-point type.
    pub fn is_float(&self) -> bool {
        matches!(self, Ty::Float { .. })
    }

    /// Returns true if this is a raw pointer type.
    pub fn is_raw_ptr(&self) -> bool {
        matches!(self, Ty::RawPtr { .. })
    }

    // Trust: #828 — identify closure types emitted by MIR lowering.
    pub fn is_closure(&self) -> bool {
        matches!(self, Ty::Closure { .. })
    }

    // Trust: #828 — treat function items and function pointers as callable pointer-like types.
    pub fn is_fn_ptr(&self) -> bool {
        matches!(self, Ty::FnPtr { .. } | Ty::FnDef { .. })
    }

    // Trust: #828 — detect trait object types for dynamic dispatch handling.
    pub fn is_dynamic(&self) -> bool {
        matches!(self, Ty::Dynamic { .. })
    }

    // Trust: #828 — identify coroutine types emitted by async/generator lowering.
    pub fn is_coroutine(&self) -> bool {
        matches!(self, Ty::Coroutine { .. })
    }

    pub fn is_unsupported(&self) -> bool {
        matches!(self, Ty::Unsupported { .. })
    }

    /// Returns true if this is any pointer-like type (Ref or RawPtr).
    pub fn is_pointer_like(&self) -> bool {
        matches!(self, Ty::Ref { .. } | Ty::RawPtr { .. })
    }

    /// Returns the pointee type for Ref or RawPtr, None otherwise.
    pub fn pointee_ty(&self) -> Option<&Ty> {
        match self {
            Ty::Ref { inner, .. } => Some(inner),
            Ty::RawPtr { pointee, .. } => Some(pointee),
            _ => None,
        }
    }

    /// Returns the bit width for floating-point types.
    pub fn float_width(&self) -> Option<u32> {
        match self {
            Ty::Float { width } => Some(*width),
            _ => None,
        }
    }

    /// Create a usize type (64-bit on most platforms).
    pub fn usize() -> Self {
        Ty::Int { width: 64, signed: false }
    }

    /// Create an isize type (64-bit on most platforms).
    pub fn isize() -> Self {
        Ty::Int { width: 64, signed: true }
    }

    /// Create a u8 type.
    pub fn u8() -> Self {
        Ty::Int { width: 8, signed: false }
    }

    /// Create an i8 type.
    pub fn i8() -> Self {
        Ty::Int { width: 8, signed: true }
    }

    /// Create a u16 type.
    pub fn u16() -> Self {
        Ty::Int { width: 16, signed: false }
    }

    /// Create an i16 type.
    pub fn i16() -> Self {
        Ty::Int { width: 16, signed: true }
    }

    /// Create a u32 type.
    pub fn u32() -> Self {
        Ty::Int { width: 32, signed: false }
    }

    /// Create an i32 type.
    pub fn i32() -> Self {
        Ty::Int { width: 32, signed: true }
    }

    /// Create a u64 type.
    pub fn u64() -> Self {
        Ty::Int { width: 64, signed: false }
    }

    /// Create an i64 type.
    pub fn i64() -> Self {
        Ty::Int { width: 64, signed: true }
    }

    /// Create a u128 type.
    pub fn u128() -> Self {
        Ty::Int { width: 128, signed: false }
    }

    /// Create an i128 type.
    pub fn i128() -> Self {
        Ty::Int { width: 128, signed: true }
    }

    /// Create an f32 type.
    pub fn f32_ty() -> Self {
        Ty::Float { width: 32 }
    }

    /// Create an f64 type.
    pub fn f64_ty() -> Self {
        Ty::Float { width: 64 }
    }

    /// Create a bool type.
    pub fn bool_ty() -> Self {
        Ty::Bool
    }

    /// Create a unit type.
    pub fn unit_ty() -> Self {
        Ty::Unit
    }
}

// Block identifier — defined in trust-ir-contract (cross-repo shared
// vocabulary) and re-exported so `trust_types::BlockId` and the `model::*` glob
// are unchanged.
pub use trust_ir_contract::BlockId;

/// A basic block.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BasicBlock {
    pub id: BlockId,
    pub stmts: Vec<Statement>,
    pub terminator: Terminator,
}

impl BasicBlock {
    /// Discover guarded clauses encoded by this block's terminator.
    pub fn discovered_clauses(&self) -> Vec<DiscoveredClause> {
        self.terminator.discovered_clauses(self.id)
    }
}

/// A bounded path-map entry for one reachable block.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PathMapEntry {
    pub block: BlockId,
    pub guards: Vec<GuardCondition>,
    pub exits: Vec<ClauseTarget>,
}

/// Statements we care about for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Statement {
    Assign {
        place: Place,
        rvalue: Rvalue,
        span: SourceSpan, // Trust: per-statement source location for diagnostics
    },
    // Trust: #828 — track local storage lifetime boundaries from MIR.
    StorageLive(usize),
    // Trust: #828 — track local storage lifetime boundaries from MIR.
    StorageDead(usize),
    // Trust: #828 — represent discriminant writes on enum places.
    SetDiscriminant {
        place: Place,
        variant_index: usize,
    },
    // Trust: #828 — model deinitialization effects in MIR.
    /// Internal TrustIr compatibility statement. Current local rustc MIR has no
    /// `StatementKind::Deinit`; when this marker appears, downstream must keep
    /// failing closed unless initializedness semantics are modeled explicitly.
    Deinit {
        place: Place,
    },
    // Trust: #828 — preserve Stacked Borrows retag statements.
    Retag {
        place: Place,
    },
    // Trust: #828 — preserve place mentions emitted as no-op statements.
    PlaceMention(Place),
    // Trust: #828 — support non-diverging intrinsic calls as statements.
    Intrinsic {
        name: String,
        args: Vec<Operand>,
    },
    /// Internal TrustIr sentinel for a rustc MIR statement class that is not
    /// represented by a dedicated `Statement` variant. The sentinel itself is
    /// not an upstream MIR variant; downstream must fail closed by emitting
    /// `VcKind::UnsupportedMir` before treating the function as verified.
    Unsupported {
        kind: String,
        detail: String,
        operands: Vec<Operand>,
        span: SourceSpan,
    },
    // Trust: #828 — carry coverage instrumentation without semantic effect.
    Coverage,
    // Trust: #828 — carry const-eval step counters without semantic effect.
    ConstEvalCounter,
    Nop,
}

/// How a MIR statement/terminator affects place values — the write-completeness
/// taxonomy. Used by the verifier's version oracle (staleness-class S2c, item 4):
/// every variant that can change a place value must be CAPTURED by the oracle's
/// write detection so the freshness theorem applies to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteEffect {
    /// Writes a place value the oracle must version (Assign dest, SetDiscriminant,
    /// Call dest / `&mut`-arg). A stale fact about the place must be renamed away.
    Captured,
    /// Changes no place value (storage/coverage/borrow-event markers, control
    /// flow). No version bump; an entry fact stays live (sound).
    NoValueWrite,
    /// Cannot be modeled as a precise value write; the verifier must fail closed
    /// (UnsupportedMir) or rely on a separately-adjudicated backstop (a custom
    /// `Drop`'s `&mut self` escape, inline asm, an intrinsic's pointer arg).
    FailClosedOrBackstopped,
}

impl Statement {
    /// The write-completeness classification of this statement. EXHAUSTIVE (no
    /// wildcard): adding a `Statement` variant fails to compile until classified,
    /// so a new MIR write channel cannot silently bypass the version oracle.
    pub fn write_effect(&self) -> WriteEffect {
        match self {
            Statement::Assign { .. } => WriteEffect::Captured,
            Statement::SetDiscriminant { .. } => WriteEffect::Captured,
            Statement::Intrinsic { .. } => WriteEffect::FailClosedOrBackstopped,
            Statement::Deinit { .. } => WriteEffect::FailClosedOrBackstopped,
            Statement::Unsupported { .. } => WriteEffect::FailClosedOrBackstopped,
            Statement::Retag { .. } => WriteEffect::NoValueWrite,
            Statement::PlaceMention(_) => WriteEffect::NoValueWrite,
            Statement::StorageLive(_) | Statement::StorageDead(_) => WriteEffect::NoValueWrite,
            Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => {
                WriteEffect::NoValueWrite
            }
        }
    }
}

/// A place (lvalue) in MIR — a local variable possibly with projections.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Place {
    pub local: usize,
    pub projections: Vec<Projection>,
}

impl Place {
    pub fn local(index: usize) -> Self {
        Place { local: index, projections: vec![] }
    }

    pub fn field(local: usize, field: usize) -> Self {
        Place { local, projections: vec![Projection::Field(field)] }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Projection {
    Field(usize),
    Index(usize),
    Deref,
    Downcast(usize),
    /// Type-only projection for opaque `impl Trait`/alias casts in rustc MIR.
    OpaqueCast(Ty),
    /// Projection that opens an unsafe binder without changing storage.
    UnwrapUnsafeBinder(Ty),
    /// Constant-offset indexing into a slice/array (e.g., `[2 from end]`).
    ConstantIndex {
        offset: usize,
        #[serde(default)]
        min_length: usize,
        from_end: bool,
    },
    /// Subslice projection (e.g., `[2..5]` or `[2..-3]`).
    Subslice {
        from: usize,
        to: usize,
        from_end: bool,
    },
}

/// An operand — either a local or a constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(ConstValue),
    // Trust: #564 — carry SMT-level Formula values from binary lifting.
    // Lifted machine semantics produce symbolic expressions (Formula) that
    // cannot be represented as ConstValue. Downstream VC generation reads
    // these directly.
    Symbolic(crate::Formula),
    /// Internal TrustIr sentinel for an operand/constant payload that cannot be
    /// represented precisely. This may be used as an unconstrained formula for
    /// CFG continuity, but it must also produce an `UnsupportedMir` VC so
    /// proofs fail closed.
    Unsupported {
        kind: String,
        detail: String,
    },
}

/// Stable classification for a zero-sized callable item carried by
/// [`ConstValue::CallableItem`].
///
/// The serialized spellings are explicit and lowercase so compiler-internal
/// `TyKind` debug formatting can change without perturbing Trust's dump schema.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CallableKind {
    /// A `TyKind::FnDef` function item.
    #[serde(rename = "fn_def")]
    FnDef,
    /// An upvar-free `TyKind::Closure` constant.
    #[serde(rename = "closure")]
    Closure,
}

fn serialize_fixed_hex_u64<S>(value: &u64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&format!("{value:016x}"))
}

fn deserialize_fixed_hex_u64<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let encoded = String::deserialize(deserializer)?;
    if encoded.len() != 16
        || !encoded.bytes().all(|b| b.is_ascii_digit() || matches!(b, b'a'..=b'f'))
    {
        return Err(serde::de::Error::custom(
            "DefPathHash components must be exactly 16 lowercase hexadecimal digits",
        ));
    }
    u64::from_str_radix(&encoded, 16).map_err(serde::de::Error::custom)
}

/// The two collision-checked 64-bit components of rustc's stable
/// `DefPathHash` for a callable definition.
///
/// Both components serialize as exactly 16 lowercase hexadecimal digits.
/// Keeping the stable crate id separate from the crate-local hash preserves
/// identity across crate graphs containing multiple versions or instances of
/// a same-named crate, where a diagnostic `def_path` string alone is
/// ambiguous.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CallableDefPathHash {
    #[serde(
        serialize_with = "serialize_fixed_hex_u64",
        deserialize_with = "deserialize_fixed_hex_u64"
    )]
    stable_crate_id: u64,
    #[serde(
        serialize_with = "serialize_fixed_hex_u64",
        deserialize_with = "deserialize_fixed_hex_u64"
    )]
    local_hash: u64,
}

impl CallableDefPathHash {
    #[must_use]
    pub const fn new(stable_crate_id: u64, local_hash: u64) -> Self {
        Self { stable_crate_id, local_hash }
    }

    #[must_use]
    pub const fn stable_crate_id(self) -> u64 {
        self.stable_crate_id
    }

    #[must_use]
    pub const fn local_hash(self) -> u64 {
        self.local_hash
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConstValue {
    Bool(bool),
    Int(i128),
    Uint(u128, u32),
    Float(f64),
    FloatBits {
        bits: u128,
        width: u32,
    },
    Unit,
    /// a `&str` literal, carried as its UTF-8 bytes (the length is
    /// `bytes.len()`). Modeled downstream as an opaque, *injectively named* SMT
    /// term — see [`ConstValue::str_smt_var_name`]. The verifier never derives a
    /// string-equality fact from the SMT side; it only refuses to assert a wrong
    /// one. Carrying the bytes lets constant-fold (`v2_const_eq_truth`) decide
    /// literal-vs-literal equality exactly, and removes the spurious
    /// `Unsupported` operand that previously blocked `Proved` for every function
    /// touching a panic/format message.
    ///
    /// T7 (fmt-template bytes): extraction also uses this variant for a fully
    /// readable `&[u8; N]` BYTE-ARRAY constant — the `format_args!` template
    /// (e.g. `b"\x07prefix \xc0\x00"`) every formatted `panic!` hands to
    /// `core::fmt::Arguments::new`, whose literal pieces the contract-panic
    /// matcher decodes (`fmt_template_literal_pieces` in trust-vcgen). The bytes
    /// need NOT be valid UTF-8 in that case. Sound under the same argument as
    /// `&str`: the value stays an opaque symbol, injectively named by the exact
    /// byte sequence — a same-bytes `&str` and `&[u8; N]` sharing a name cannot
    /// meet in any typed comparison, and same-bytes constants of one type
    /// genuinely have equal contents.
    Str {
        bytes: Vec<u8>,
    },
    /// An opaque reference-to-aggregate constant (`&[&str]`, `&[T]`, `&[…]`) whose
    /// concrete contents are not modeled. Like [`ConstValue::Str`], it is lowered to
    /// a fresh-symbolic slice fat pointer (sound over-approximation: length/contents
    /// are not asserted, so value-dependent obligations stay `unknown`, never falsely
    /// proved). Clears the dominant "unsupported constant" blocker for the static
    /// `&[&str]` lookup tables ubiquitous in real code (gap-log build #25).
    OpaqueConst,
    /// A bare (non-reference) INTEGER constant whose value cannot be evaluated at
    /// extraction time — a const-generic param `N`, an associated const `T::LIMIT`,
    /// or `size_of::<T>()` read inside a *generic* body where const-eval is
    /// unavailable. Unlike [`ConstValue::OpaqueConst`] (which lowers to a fat-pointer
    /// `Undef`, the wrong SORT for arithmetic/indexing), this carries the integer
    /// `width`/`signedness` so every consumer can mint a *fresh integer-sorted*
    /// symbol of the matching sort. Sound over-approximation: a fresh symbol asserts
    /// NO value, so value/div/index/equality obligations over it stay `unknown` and
    /// are never falsely proved (see the div-zero and const-eq folds in trust-vcgen,
    /// which must treat this as unknown-valued, never as a known-nonzero/known-unequal
    /// constant). Each occurrence lowers to an independent fresh symbol, so distinct
    /// reads are never asserted equal — strictly weaker than the truth, never falsely
    /// proved.
    OpaqueScalar {
        width: u32,
        signed: bool,
    },
    /// Trust: piece #7a — a const-generic PARAM value (`N`) read as an operand,
    /// carrying the param IDENTITY so it lowers to the SAME symbol
    /// `__trust_constparam_{index}_{name}` (see [`const_param_symbol`]) that the
    /// array length `[T; N]` uses. This is a SEPARATE variant from
    /// [`ConstValue::OpaqueScalar`] on purpose: `OpaqueScalar` (assoc-const /
    /// `size_of::<T>()`) has NO param identity and stays exactly as sound as
    /// before; only the genuinely-identifiable const-param case gains the
    /// per-param symbol. SOUNDNESS: the symbol asserts no value (an unconstrained
    /// `Sort::Int`), so value/div/index/equality obligations over it stay
    /// `unknown` and are never falsely proved. Keying on `(index, name)` — never
    /// on `(width, signed)` — is what prevents two distinct usize const-params
    /// from colliding onto one term (the "M==N collision").
    ConstParam {
        index: u32,
        name: String,
        width: u32,
        signed: bool,
    },
    /// A REFERENCE constant `&Option<T>::None`-style: a promoted/const `&E` where the
    /// std enum E's value is a PAYLOAD-LESS variant. Carries the enum def-path and the
    /// variant INDEX. Value-lowering is identical to `OpaqueConst` (fresh symbolic ref);
    /// the variant information is consumed SYNTACTICALLY by the eq-guard channels.
    UnitVariantRef {
        enum_name: String,
        variant: usize,
    },
    /// A zero-sized callable constant whose runtime payload is unit-like but
    /// whose code identity is semantically relevant to syntactic MIR
    /// recognizers. Downstream value models must continue to treat this as an
    /// opaque/unit-sorted value: `def_path` is extraction evidence, never a
    /// proof fact or a basis for solver equality.
    ///
    /// This is appended to the enum so positional Serde formats retain every
    /// historical discriminant. Historical callable constants encoded as
    /// [`ConstValue::Unit`] remain deserializable, while newly extracted dumps
    /// preserve the exact safe def-path and stable callable kind.
    CallableItem {
        def_path: String,
        kind: CallableKind,
        def_path_hash: CallableDefPathHash,
    },
}

impl ConstValue {
    /// Injective SMT identifier for a callable item's extraction identity.
    ///
    /// The callable kind has a distinct fixed prefix, both collision-checked
    /// rustc `DefPathHash` components are encoded at fixed width, and the
    /// human-readable def-path bytes are hex-encoded without hashing. Keying
    /// on all three protects both real extraction (where rustc rejects hash
    /// collisions) and externally supplied JSON (where a forged duplicate
    /// hash must not conflate two textual paths). Repeated occurrences of the
    /// same triple intentionally share an unconstrained symbol; this asserts
    /// identity, not callable behavior or disequality between distinct terms.
    pub fn callable_smt_var_name(
        def_path: &str,
        kind: CallableKind,
        def_path_hash: CallableDefPathHash,
    ) -> String {
        let prefix = match kind {
            CallableKind::FnDef => "__trust_callable_fn_def_",
            CallableKind::Closure => "__trust_callable_closure_",
        };
        let mut s = format!(
            "{prefix}{:016x}_{:016x}_",
            def_path_hash.stable_crate_id, def_path_hash.local_hash
        );
        s.reserve(def_path.len() * 2);
        for b in def_path.as_bytes() {
            s.push(char::from_digit(u32::from(b >> 4), 16).expect("nibble < 16"));
            s.push(char::from_digit(u32::from(b & 0xf), 16).expect("nibble < 16"));
        }
        s
    }

    /// Injective SMT identifier for a `&str` constant's bytes.
    ///
    /// Hex-encodes the bytes (two fixed hex digits per byte) so that *distinct*
    /// strings can never collide onto one SMT variable. This is a soundness
    /// requirement, not a nicety: if two different string literals aliased to the
    /// same SMT term, the solver would treat them as equal and could "prove" a
    /// false disequality. Hashing is therefore forbidden here. The output uses
    /// only `[_0-9a-f]`, which needs no further SMT-symbol sanitization.
    pub fn str_smt_var_name(bytes: &[u8]) -> String {
        let mut s = String::with_capacity("__trust_str_".len() + bytes.len() * 2);
        s.push_str("__trust_str_");
        for b in bytes {
            s.push(char::from_digit(u32::from(b >> 4), 16).expect("nibble < 16"));
            s.push(char::from_digit(u32::from(b & 0xf), 16).expect("nibble < 16"));
        }
        s
    }
}

/// Rvalues — computations that produce a value.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Ref {
        mutable: bool,
        place: Place,
    },
    Cast(Operand, Ty),
    Aggregate(AggregateKind, Vec<Operand>),
    Discriminant(Place),
    Len(Place),
    /// Array repetition: `[operand; count]`.
    Repeat(Operand, usize),
    /// Raw pointer creation (`&raw const`/`&raw mut`). `mutable` = true for `&raw mut`.
    AddressOf(bool, Place),
    /// Copy for deref — semantically equivalent to `Use(Copy(place))` but
    /// preserved so downstream passes can distinguish compiler-inserted copies.
    CopyForDeref(Place),
    /// Pointer arithmetic `ptr.offset(count)` — the MIR `BinOp::Offset` form.
    ///
    /// Trust (W2 inc-0): the SAME semantic operation as the `core::ptr::{add,sub,
    /// offset}` intrinsic family (`ptr + count * size_of::<T>()`), but arriving as
    /// a MIR `BinOp` instead of a `Terminator::Call`. It is the sole blocker on the
    /// slice-iterator leaf family (`Iter::next` post-increments its cursor with a
    /// `BinOp::Offset`; `Iter::fold`/`into_iter`/`Iter::new` reach it likewise).
    /// Modeled as its own DISTINGUISHABLE variant — rather than an opaque
    /// `Unsupported` marker — so downstream can converge it onto the intrinsic
    /// lane's `(base slice, index)` `PtrModel` and reuse the fail-closed
    /// `ptr_offset_bounds_vc` in-bounds obligation.
    ///
    /// SOUNDNESS: `Offset` is UB when out-of-bounds, so this variant carries the
    /// same obligation discipline as the intrinsic — vcgen emits a fail-closed
    /// `UnsupportedMir`-class in-bounds obligation for it, and it is NEVER modeled
    /// as a total/opaque value without that obligation. `ptr` is the base pointer
    /// operand; `count` is the element offset.
    // Trust: W2 inc-0 — model BinOp::Offset instead of erasing it to Unsupported.
    PtrOffset {
        ptr: Operand,
        count: Operand,
    },
    /// Internal TrustIr sentinel for a rustc MIR rvalue payload that is not
    /// represented by a dedicated `Rvalue` variant. The assignment may remain
    /// in the CFG for continuity, but vcgen must emit an `UnsupportedMir`
    /// obligation for it.
    Unsupported {
        kind: String,
        detail: String,
        operands: Vec<Operand>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    /// Three-way comparison (like `Ord::cmp`): returns -1, 0, or 1.
    // Trust: #383 — proper Cmp semantics instead of mapping to Eq.
    Cmp,
}

impl BinOp {
    /// Returns true if this operation can overflow on integer types.
    pub fn can_overflow(&self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr)
    }

    /// Returns true if this is a division-family operation.
    pub fn is_division(&self) -> bool {
        matches!(self, BinOp::Div | BinOp::Rem)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum UnOp {
    Not,
    Neg,
    /// Extracts metadata (e.g., length) from a fat pointer.
    /// Semantically a no-op for verification: produces an unconstrained usize.
    // Trust: #386 — proper variant instead of fallback to Not.
    PtrMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AggregateKind {
    Tuple,
    Array,
    Adt {
        name: String,
        variant: usize,
        #[serde(default)]
        active_field: Option<usize>,
        /// Trust (C1): the path rendered WITH its concrete monomorphized generic arguments.
        ///
        /// `name` stays args-free because it is obligation identity, a cache key and report
        /// text; changing it would move VERIFICATION identity, not just comparison strings.
        /// This is a separate discriminator so a comparison can see a wrong-args
        /// reconstruction that `name` cannot.
        ///
        /// Generic-arg erasure is a known false-proof vector, not a hypothetical: a
        /// `Vec::<[u8; 1<<40]>::with_capacity(n)` capacity overflow was once reported proved —
        /// and kernel-certified — because `T` was erased to the generic param (hunt-11, see
        /// `trust_mir_extract::safe_def_path_str_with_args`).
        ///
        /// `serde(default)` so an existing serialized record still decodes.
        #[serde(default)]
        args: Option<String>,
    },
    // Trust: #828 — closure aggregates materialize captured environment state.
    // Trust: #20 — schema extension: captures (upvar types in declaration order)
    // and call_kind (Fn / FnMut / FnOnce) so downstream VC-gen can model the
    // closure as a (captures: struct, body: fn(captures, args) -> ret) pair
    // with symbolic captures. VC-gen models construction as capture-field data;
    // closure calls still require callable-summary semantics.
    Closure {
        name: String,
        #[serde(default)]
        captures: Vec<Ty>,
        #[serde(default)]
        call_kind: ClosureCallKind,
    },
    // Trust: #828 — coroutine aggregates materialize generator state.
    Coroutine {
        name: String,
    },
    // Trust: #828 — async closure aggregates have distinct MIR shape.
    CoroutineClosure {
        name: String,
    },
    // Trust: #828 — raw pointer aggregates combine data pointer and metadata.
    RawPtr {
        pointee_ty: Ty,
        mutable: bool,
    },
}

/// Closure call convention — which `Fn*` trait the closure implements.
///
/// Trust (B6): a closure TYPE's call signature + inferred kind — the payload of
/// `Ty::Closure { call }`. `params` are the UNTUPLED call arguments; `ret` is `None`
/// for a unit return (matching the trust-ir producer's empty-`returns` convention, so
/// the bridge's respell is structurally equal by construction).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ClosureCallSig {
    pub kind: ClosureCallKind,
    pub params: Vec<Ty>,
    pub ret: Option<Ty>,
}

/// Mirrors rustc's `ty::ClosureKind`. Used by `AggregateKind::Closure` so the
/// VC-gen consumer can decide how to model the closure environment (shared
/// borrow vs. mutable borrow vs. by-value).
// Trust: #20 — captured-environment schema for closure aggregates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ClosureCallKind {
    /// `Fn` — shared borrow of the environment.
    Fn,
    /// `FnMut` — mutable borrow of the environment.
    FnMut,
    /// `FnOnce` — consumes the environment.
    FnOnce,
}

impl Default for ClosureCallKind {
    /// Defaults to `FnOnce`, the weakest (most general) of the three. This is
    /// only used for serde fallback when an older artifact lacks the field;
    /// fresh lowerings always populate the field explicitly.
    fn default() -> Self {
        ClosureCallKind::FnOnce
    }
}

/// Atomic memory ordering, following the C11/Rust memory model.
///
/// The ordering forms a lattice, NOT a total order.
/// Acquire and Release are incomparable; AcqRel and SeqCst are above both.
///
/// ```text
///        SeqCst
///          |
///        AcqRel
///        /    \
///   Acquire  Release
///        \    /
///        Relaxed
/// ```
///
/// This type deliberately does NOT derive `PartialOrd` or `Ord` because
/// derived `Ord` on an enum uses variant declaration order, which would
/// incorrectly imply a total ordering where Acquire < Release.
///
/// A manual `PartialOrd` is provided that correctly models the C11 lattice:
/// `Acquire` and `Release` are incomparable (`partial_cmp` returns `None`).
/// `Ord` is intentionally NOT implemented — this is a partial order.
// Trust: #603 — canonical ordering type replacing buggy send_sync::AtomicOrdering.
// Trust: #612 — added PartialOrd for lattice comparisons.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

impl AtomicOrdering {
    /// Returns true if this ordering provides acquire semantics.
    ///
    /// Acquire semantics means that no reads or writes in the current
    /// thread can be reordered before this load/fence.
    // Trust: #612 -- ported from send_sync::AtomicOrdering for consolidation.
    #[must_use]
    pub fn is_acquire(&self) -> bool {
        matches!(self, Self::Acquire | Self::AcqRel | Self::SeqCst)
    }

    /// Returns true if this ordering provides release semantics.
    ///
    /// Release semantics means that no reads or writes in the current
    /// thread can be reordered after this store/fence.
    // Trust: #612 -- ported from send_sync::AtomicOrdering for consolidation.
    #[must_use]
    pub fn is_release(&self) -> bool {
        matches!(self, Self::Release | Self::AcqRel | Self::SeqCst)
    }

    /// Human-readable name for diagnostics.
    // Trust: #612 -- ported from send_sync::AtomicOrdering for consolidation.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Relaxed => "Relaxed",
            Self::Acquire => "Acquire",
            Self::Release => "Release",
            Self::AcqRel => "AcqRel",
            Self::SeqCst => "SeqCst",
        }
    }

    /// Returns true if `self` is at least as strong as `other` in the
    /// memory ordering lattice.
    ///
    /// This correctly models the C11 partial order where Acquire and Release
    /// are incomparable. Neither `Acquire.is_at_least(&Release)` nor
    /// `Release.is_at_least(&Acquire)` returns true.
    #[must_use]
    pub fn is_at_least(&self, other: &AtomicOrdering) -> bool {
        use AtomicOrdering::*;
        match (self, other) {
            // Everything is at least Relaxed.
            (_, Relaxed) => true,
            // Relaxed is only at least Relaxed (handled above).
            (Relaxed, _) => false,
            // SeqCst is at least everything.
            (SeqCst, _) => true,
            // Nothing except SeqCst is at least SeqCst.
            (_, SeqCst) => false,
            // AcqRel is at least Acquire, Release, and AcqRel.
            (AcqRel, Acquire | Release | AcqRel) => true,
            // Acquire is at least Acquire but NOT Release.
            (Acquire, Acquire) => true,
            (Acquire, Release | AcqRel) => false,
            // Release is at least Release but NOT Acquire.
            (Release, Release) => true,
            (Release, Acquire | AcqRel) => false,
        }
    }

    /// Returns the join (least upper bound) of two orderings in the lattice.
    #[must_use]
    pub fn join(&self, other: &AtomicOrdering) -> AtomicOrdering {
        use AtomicOrdering::*;
        if self == other {
            return *self;
        }
        match (self, other) {
            (SeqCst, _) | (_, SeqCst) => SeqCst,
            (AcqRel, _) | (_, AcqRel) => AcqRel,
            // Acquire join Release = AcqRel (they are incomparable)
            (Acquire, Release) | (Release, Acquire) => AcqRel,
            (Acquire, Relaxed) | (Relaxed, Acquire) => Acquire,
            (Release, Relaxed) | (Relaxed, Release) => Release,
            // Remaining self==other cases handled above
            _ => {
                unreachable!("AtomicOrdering::join covers all unequal pairs in the current lattice")
            }
        }
    }

    /// Returns the meet (greatest lower bound) of two orderings in the lattice.
    #[must_use]
    pub fn meet(&self, other: &AtomicOrdering) -> AtomicOrdering {
        use AtomicOrdering::*;
        if self == other {
            return *self;
        }
        match (self, other) {
            (Relaxed, _) | (_, Relaxed) => Relaxed,
            (SeqCst, x) | (x, SeqCst) => *x,
            (AcqRel, x) | (x, AcqRel) => *x,
            // Acquire meet Release = Relaxed (they are incomparable)
            (Acquire, Release) | (Release, Acquire) => Relaxed,
            // Remaining self==other cases handled above
            _ => {
                unreachable!("AtomicOrdering::meet covers all unequal pairs in the current lattice")
            }
        }
    }
}

impl std::fmt::Display for AtomicOrdering {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicOrdering::Relaxed => f.write_str("Relaxed"),
            AtomicOrdering::Acquire => f.write_str("Acquire"),
            AtomicOrdering::Release => f.write_str("Release"),
            AtomicOrdering::AcqRel => f.write_str("AcqRel"),
            AtomicOrdering::SeqCst => f.write_str("SeqCst"),
        }
    }
}

// Trust: #612 -- Manual PartialOrd for the C11 memory ordering lattice.
// Acquire and Release are incomparable, so this is a strict partial order
// (no Ord impl). Use `is_at_least()` for a bool check, or `partial_cmp()`
// for Option<Ordering> when you need the full three-way result.
impl PartialOrd for AtomicOrdering {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            return Some(std::cmp::Ordering::Equal);
        }
        let self_ge = self.is_at_least(other);
        let other_ge = other.is_at_least(self);
        match (self_ge, other_ge) {
            (true, false) => Some(std::cmp::Ordering::Greater),
            (false, true) => Some(std::cmp::Ordering::Less),
            // Both true would mean equal, handled above.
            // Both false means incomparable.
            _ => None,
        }
    }
}

/// Atomic operation detected from MIR intrinsic calls.
// Trust: #603 — carries atomic metadata on Terminator::Call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomicOperation {
    /// The place being atomically accessed (first arg = raw pointer target).
    pub place: Place,
    /// Destination place for the return value (for Load, Exchange, CAS, Fetch*).
    /// None for Store and Fence.
    pub dest: Option<Place>,
    /// What kind of atomic operation this is.
    pub op_kind: AtomicOpKind,
    /// The memory ordering used (success ordering for CAS).
    pub ordering: AtomicOrdering,
    /// For CAS: the failure ordering. Must satisfy:
    /// - failure_ordering is not Release or AcqRel
    /// - failure_ordering is no stronger than success ordering
    #[serde(default)]
    pub failure_ordering: Option<AtomicOrdering>,
    /// Source span for diagnostics.
    pub span: SourceSpan,
}

/// The kind of atomic operation.
// Trust: #603 — covers all rustc atomic intrinsics including CompilerFence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicOpKind {
    Load,
    Store,
    Exchange,
    CompareExchange,
    CompareExchangeWeak,
    FetchAdd,
    FetchSub,
    FetchAnd,
    FetchOr,
    FetchXor,
    FetchNand,
    FetchMin,
    FetchMax,
    Fence,
    /// compiler_fence (singlethreadfence): prevents compiler reordering
    /// but does NOT emit a hardware fence. Relevant for signal handlers
    /// and memory-mapped I/O.
    CompilerFence,
}

impl AtomicOpKind {
    /// Returns true if this operation is a read-modify-write operation.
    ///
    /// RMW ops have combined acquire+release semantics when AcqRel is used,
    /// and they extend release sequences (relevant for Phase 2 HB analysis).
    #[must_use]
    pub fn is_rmw(&self) -> bool {
        matches!(
            self,
            AtomicOpKind::Exchange
                | AtomicOpKind::CompareExchange
                | AtomicOpKind::CompareExchangeWeak
                | AtomicOpKind::FetchAdd
                | AtomicOpKind::FetchSub
                | AtomicOpKind::FetchAnd
                | AtomicOpKind::FetchOr
                | AtomicOpKind::FetchXor
                | AtomicOpKind::FetchNand
                | AtomicOpKind::FetchMin
                | AtomicOpKind::FetchMax
        )
    }

    /// Returns true if this is a load-type operation (reads without writing).
    #[must_use]
    pub fn is_load(&self) -> bool {
        matches!(self, AtomicOpKind::Load)
    }

    /// Returns true if this is a store-type operation (writes without reading).
    #[must_use]
    pub fn is_store(&self) -> bool {
        matches!(self, AtomicOpKind::Store)
    }

    /// Returns true if this is a fence operation (no memory location accessed).
    #[must_use]
    pub fn is_fence(&self) -> bool {
        matches!(self, AtomicOpKind::Fence | AtomicOpKind::CompilerFence)
    }
}

impl std::fmt::Display for AtomicOpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicOpKind::Load => f.write_str("load"),
            AtomicOpKind::Store => f.write_str("store"),
            AtomicOpKind::Exchange => f.write_str("exchange"),
            AtomicOpKind::CompareExchange => f.write_str("compare_exchange"),
            AtomicOpKind::CompareExchangeWeak => f.write_str("compare_exchange_weak"),
            AtomicOpKind::FetchAdd => f.write_str("fetch_add"),
            AtomicOpKind::FetchSub => f.write_str("fetch_sub"),
            AtomicOpKind::FetchAnd => f.write_str("fetch_and"),
            AtomicOpKind::FetchOr => f.write_str("fetch_or"),
            AtomicOpKind::FetchXor => f.write_str("fetch_xor"),
            AtomicOpKind::FetchNand => f.write_str("fetch_nand"),
            AtomicOpKind::FetchMin => f.write_str("fetch_min"),
            AtomicOpKind::FetchMax => f.write_str("fetch_max"),
            AtomicOpKind::Fence => f.write_str("fence"),
            AtomicOpKind::CompilerFence => f.write_str("compiler_fence"),
        }
    }
}

/// The sub-operation for a read-modify-write (RMW) atomic.
///
/// RMW operations atomically read a value, apply an operation, and write back.
/// They have combined acquire+release semantics when `AcqRel` is used and
/// extend release sequences (relevant for happens-before analysis).
// Trust: #612 -- factored out of AtomicOpKind for use in data_race::AccessKind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicRmwOp {
    /// Exchange (swap).
    Xchg,
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Bitwise AND.
    And,
    /// Bitwise OR.
    Or,
    /// Bitwise XOR.
    Xor,
    /// Bitwise NAND.
    Nand,
    /// Signed/unsigned minimum.
    Min,
    /// Signed/unsigned maximum.
    Max,
    /// Unsigned minimum (for unsigned comparisons specifically).
    UMin,
    /// Unsigned maximum (for unsigned comparisons specifically).
    UMax,
}

impl std::fmt::Display for AtomicRmwOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicRmwOp::Xchg => f.write_str("xchg"),
            AtomicRmwOp::Add => f.write_str("add"),
            AtomicRmwOp::Sub => f.write_str("sub"),
            AtomicRmwOp::And => f.write_str("and"),
            AtomicRmwOp::Or => f.write_str("or"),
            AtomicRmwOp::Xor => f.write_str("xor"),
            AtomicRmwOp::Nand => f.write_str("nand"),
            AtomicRmwOp::Min => f.write_str("min"),
            AtomicRmwOp::Max => f.write_str("max"),
            AtomicRmwOp::UMin => f.write_str("umin"),
            AtomicRmwOp::UMax => f.write_str("umax"),
        }
    }
}

impl AtomicRmwOp {
    /// Convert from an `AtomicOpKind` fetch variant.
    ///
    /// Returns `None` if the kind is not an RMW operation.
    #[must_use]
    pub fn from_op_kind(kind: AtomicOpKind) -> Option<Self> {
        match kind {
            AtomicOpKind::Exchange => Some(AtomicRmwOp::Xchg),
            AtomicOpKind::FetchAdd => Some(AtomicRmwOp::Add),
            AtomicOpKind::FetchSub => Some(AtomicRmwOp::Sub),
            AtomicOpKind::FetchAnd => Some(AtomicRmwOp::And),
            AtomicOpKind::FetchOr => Some(AtomicRmwOp::Or),
            AtomicOpKind::FetchXor => Some(AtomicRmwOp::Xor),
            AtomicOpKind::FetchNand => Some(AtomicRmwOp::Nand),
            AtomicOpKind::FetchMin => Some(AtomicRmwOp::Min),
            AtomicOpKind::FetchMax => Some(AtomicRmwOp::Max),
            _ => None,
        }
    }
}

/// High-level classification of atomic operations.
///
/// Unifies the various `AtomicOpKind` variants into four categories that
/// matter for memory ordering analysis:
/// - **Load**: read-only, may use Relaxed/Acquire/SeqCst.
/// - **Store**: write-only, may use Relaxed/Release/SeqCst.
/// - **Fence**: no memory location, establishes ordering.
/// - **CmpXchg**: compare-and-exchange with success/failure orderings.
/// - **Rmw**: read-modify-write with a sub-operation.
// Trust: #612 -- higher-level atomic op classification for data race analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicOpClass {
    /// Atomic load (read-only).
    Load,
    /// Atomic store (write-only).
    Store,
    /// Memory fence (no location accessed).
    Fence,
    /// Compare-and-exchange (with weak flag).
    CmpXchg { weak: bool },
    /// Read-modify-write operation.
    Rmw(AtomicRmwOp),
}

impl AtomicOpClass {
    /// Classify an `AtomicOpKind` into its high-level class.
    #[must_use]
    pub fn from_op_kind(kind: AtomicOpKind) -> Self {
        match kind {
            AtomicOpKind::Load => AtomicOpClass::Load,
            AtomicOpKind::Store => AtomicOpClass::Store,
            AtomicOpKind::Fence | AtomicOpKind::CompilerFence => AtomicOpClass::Fence,
            AtomicOpKind::CompareExchange => AtomicOpClass::CmpXchg { weak: false },
            AtomicOpKind::CompareExchangeWeak => AtomicOpClass::CmpXchg { weak: true },
            AtomicOpKind::Exchange => AtomicOpClass::Rmw(AtomicRmwOp::Xchg),
            AtomicOpKind::FetchAdd => AtomicOpClass::Rmw(AtomicRmwOp::Add),
            AtomicOpKind::FetchSub => AtomicOpClass::Rmw(AtomicRmwOp::Sub),
            AtomicOpKind::FetchAnd => AtomicOpClass::Rmw(AtomicRmwOp::And),
            AtomicOpKind::FetchOr => AtomicOpClass::Rmw(AtomicRmwOp::Or),
            AtomicOpKind::FetchXor => AtomicOpClass::Rmw(AtomicRmwOp::Xor),
            AtomicOpKind::FetchNand => AtomicOpClass::Rmw(AtomicRmwOp::Nand),
            AtomicOpKind::FetchMin => AtomicOpClass::Rmw(AtomicRmwOp::Min),
            AtomicOpKind::FetchMax => AtomicOpClass::Rmw(AtomicRmwOp::Max),
        }
    }

    /// Returns true if this class involves a read (Load, CmpXchg, or Rmw).
    #[must_use]
    pub fn is_read(&self) -> bool {
        matches!(self, AtomicOpClass::Load | AtomicOpClass::CmpXchg { .. } | AtomicOpClass::Rmw(_))
    }

    /// Returns true if this class involves a write (Store, CmpXchg, or Rmw).
    #[must_use]
    pub fn is_write(&self) -> bool {
        matches!(self, AtomicOpClass::Store | AtomicOpClass::CmpXchg { .. } | AtomicOpClass::Rmw(_))
    }
}

impl std::fmt::Display for AtomicOpClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicOpClass::Load => f.write_str("load"),
            AtomicOpClass::Store => f.write_str("store"),
            AtomicOpClass::Fence => f.write_str("fence"),
            AtomicOpClass::CmpXchg { weak: false } => f.write_str("cmpxchg"),
            AtomicOpClass::CmpXchg { weak: true } => f.write_str("cmpxchg_weak"),
            AtomicOpClass::Rmw(op) => write!(f, "rmw_{op}"),
        }
    }
}

/// The unwind (cleanup) successor of a panicking terminator — the control-flow
/// edge taken when the terminator's operation panics / unwinds. Mirrors rustc
/// `mir::UnwindAction`. Recording it explicitly is what lets the verifier
/// TRAVERSE the cleanup blocks (which drop the live locals via their own `Drop`
/// terminators and end in `Resume`) and prove each cleanup drop panic-free —
/// instead of silently dropping the edge (which hides a cleanup-path panic) or
/// fail-closing the whole terminator to `Opaque` (which needlessly blocks
/// `Proved` for every cleanup-carrying function). See `Terminator::Resume`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum UnwindEdge {
    /// The operation is provably nounwind: it cannot unwind, so there is no
    /// cleanup successor. Also the back-compat default when an older serialized
    /// bundle omits the field (matching the pre-unwind-modeling behavior where
    /// the edge was simply absent; the terminator's own panic-freedom obligation
    /// still fires independently).
    #[default]
    Unreachable,
    /// On unwind, control propagates directly to the caller with no in-function
    /// cleanup (no live local needs dropping at this point). A `Resume`-like exit
    /// out of the function; contributes no in-CFG block edge.
    Continue,
    /// On unwind, an abort is triggered (rustc `UnwindTerminate`) because a
    /// nounwind boundary was crossed (e.g. a panic during cleanup). A controlled
    /// program abort; contributes no in-CFG block edge and no user-panic exit.
    Terminate,
    /// On unwind, control transfers to this cleanup block, which drops the live
    /// locals (via `Drop` terminators) and ends in `Resume` (or another cleanup /
    /// `Terminate`). A real in-CFG successor the verifier must reach and check.
    Cleanup(BlockId),
}

impl UnwindEdge {
    /// The cleanup block this edge transfers to on unwind, if any. Only
    /// `Cleanup` contributes a real in-CFG successor; `Continue`/`Terminate`/
    /// `Unreachable` are function exits with no in-block successor.
    pub fn cleanup_target(&self) -> Option<BlockId> {
        match self {
            UnwindEdge::Cleanup(block) => Some(*block),
            UnwindEdge::Unreachable | UnwindEdge::Continue | UnwindEdge::Terminate => None,
        }
    }

    // Trust (skip-serializing-if root fix, precedent fae9701cdaab): serde
    // skip-predicate for the three `Terminator::{Call,Assert,Drop}::unwind`
    // fields. `Unreachable` is the back-compat default — the pre-unwind wire
    // had no field at all — so omitting it on serialization byte-restores the
    // pre-unwind serialized form and keeps every audited content-hash pin
    // (e.g. `INSTANTIATOR_ORD_LEAF_CONTENT_HASH`) valid, exactly as
    // `Ty::Adt::faithful_enum_repr`'s skip does for the fold-lane goldens.
    // Real edges (`Continue`/`Terminate`/`Cleanup`) always serialize: they are
    // hash-visible semantic content, and `serde(default)` still round-trips
    // old bundles that omit the field.
    /// Whether this is the `Unreachable` (nounwind / back-compat default)
    /// edge — the serde `skip_serializing_if` predicate for `unwind` fields.
    #[must_use]
    pub fn is_unreachable(&self) -> bool {
        matches!(self, UnwindEdge::Unreachable)
    }
}

/// How a block ends.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Terminator {
    Goto(BlockId),
    SwitchInt {
        discr: Operand,
        targets: Vec<(u128, BlockId)>,
        otherwise: BlockId,
        /// Trust: TyCtxt-vetted exhaustiveness flag, set TRUE only by
        /// `mark_exhaustive_enum_unreachable_switches` when `discr` is a genuine
        /// single-assignment enum-discriminant temp, the case values
        /// (`targets.0`) are EXACTLY the enum's full discriminant tag set, and
        /// `otherwise` targets an `Unreachable` block. Downstream the native CHC
        /// translator conjoins `discr ∈ {case values}` into the default arm,
        /// proving the otherwise-`Unreachable` obligation. Defaults false so
        /// plain-integer / partial matches keep genuine UB, and old serialized
        /// MIR / synthetic test bodies deserialize unchanged.
        #[serde(default)]
        exhaustive_enum_unreachable: bool,
        span: SourceSpan, // Trust: source location for diagnostics
    },
    Return,
    Call {
        func: String,
        args: Vec<Operand>,
        dest: Place,
        target: Option<BlockId>,
        span: SourceSpan, // Trust: source location for diagnostics
        /// Present when the call is a recognized atomic intrinsic.
        /// Downstream passes that don't care about atomics ignore this field.
        #[serde(default)]
        atomic: Option<AtomicOperation>,
        /// Trust: round-19 #3 — the callee is a foreign item (`extern` import)
        /// per rustc's `tcx.is_foreign_item` / a non-Rust ABI, recorded at
        /// extraction. This is the AUTHORITATIVE FFI signal: name-substring
        /// detection (`ffi_vcgen::is_extern_call`) under-approximates and misses
        /// `extern "C"`/`#[no_mangle]` imports whose path lacks libc/extern/ffi.
        /// Defaults false so synthetic/test calls and old serialized MIR are
        /// treated as non-foreign (the FFI path still fires by name for those).
        #[serde(default)]
        is_foreign: bool,
        /// Trust: T5A — true iff the callee's fn SIGNATURE is unsafe per rustc
        /// (`tcx.fn_sig(..).safety() == Unsafe` AND NOT `safe_target_features`,
        /// mirroring rustc's call-unsafety rule; recorded at extraction). This
        /// is the AUTHORITATIVE unsafe-call signal: name heuristics
        /// (`is_unsafe_fn_call`) over-approximate — the `::ffi::` NAMESPACE
        /// entry flagged SAFE `std::ffi` paths (`OsStr::to_str`, …) — and
        /// under-approximate (a local `unsafe fn` with an arbitrary name is
        /// missed). Name matching remains only a fallback for synthetic MIR.
        /// Defaults false so synthetic/test calls and old serialized MIR
        /// deserialize unchanged (the name fallback still fires for those).
        #[serde(default)]
        is_unsafe_sig: bool,
        /// The cleanup successor taken if the callee panics. Defaults to
        /// `Unreachable` for pre-unwind-modeling bundles; the callee's
        /// panic-freedom obligation is tracked independently of this edge.
        /// Skipped when `Unreachable` so pre-unwind bundles re-serialize
        /// byte-identically (audited content-hash pins; see
        /// [`UnwindEdge::is_unreachable`]).
        #[serde(default, skip_serializing_if = "UnwindEdge::is_unreachable")]
        unwind: UnwindEdge,
    },
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: BlockId,
        span: SourceSpan, // Trust: source location for diagnostics
        /// The cleanup successor taken if the assertion fails (the panic path).
        /// Defaults to `Unreachable` for pre-unwind-modeling bundles; the
        /// assertion's own safety obligation (`cond == expected`) is tracked
        /// independently of this edge. Skipped when `Unreachable` so
        /// pre-unwind bundles re-serialize byte-identically (audited
        /// content-hash pins; see [`UnwindEdge::is_unreachable`]).
        #[serde(default, skip_serializing_if = "UnwindEdge::is_unreachable")]
        unwind: UnwindEdge,
    },
    Drop {
        place: Place,
        target: BlockId,
        span: SourceSpan, // Trust: source location for diagnostics
        /// The cleanup successor taken if the drop glue panics. Defaults to
        /// `Unreachable` (nounwind) for bundles serialized before unwind
        /// modeling; the drop-glue panic-freedom obligation is tracked
        /// independently of this edge. Skipped when `Unreachable` so
        /// pre-unwind bundles re-serialize byte-identically (audited
        /// content-hash pins; see [`UnwindEdge::is_unreachable`]).
        #[serde(default, skip_serializing_if = "UnwindEdge::is_unreachable")]
        unwind: UnwindEdge,
    },
    /// Internal TrustIr sentinel for rustc MIR control flow that TrustIr does not yet
    /// model precisely.
    ///
    /// This is deliberately not lowered to `Unreachable`: preserving real
    /// successors prevents false proofs that arise from pruning reachable CFG
    /// paths while still making the unsupported MIR feature explicit.
    Opaque {
        kind: String,
        targets: Vec<BlockId>,
        span: SourceSpan,
    },
    Unreachable,
    /// rustc `UnwindResume` — re-raise an in-flight unwind (panic) to
    /// the caller. A control-flow sink with no successor and NO safety
    /// obligation: the re-raise itself asserts nothing, and the drops executed on
    /// the unwind path are modeled by their own `Drop` terminators. Deliberately
    /// kept distinct from both `Unreachable` (which under pipeline-v2 is a real
    /// assert-unreachable obligation that a *reachable* cleanup block would
    /// spuriously fail) and `Opaque` (which degrades to an Unknown that needlessly
    /// blocks `Proved` for every cleanup-carrying function).
    Resume,
}

impl Terminator {
    /// The write-completeness classification of this terminator. EXHAUSTIVE (no
    /// wildcard): a new `Terminator` variant fails to compile until classified, so
    /// a new MIR write channel cannot silently bypass the version oracle.
    pub fn write_effect(&self) -> WriteEffect {
        match self {
            Terminator::Call { .. } => WriteEffect::Captured, // dest + &mut-arg havoc
            Terminator::Drop { .. } => WriteEffect::FailClosedOrBackstopped, // needs a &mut escape
            Terminator::Opaque { .. } => WriteEffect::FailClosedOrBackstopped, // asm → UnsupportedMir
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Assert { .. }
            | Terminator::Unreachable
            | Terminator::Resume => WriteEffect::NoValueWrite,
        }
    }

    /// Discover guarded clauses for conditional control-flow terminators.
    ///
    /// This is a bounded first slice for MIR guard extraction: only `SwitchInt`
    /// and `Assert` contribute clauses today.
    pub fn discovered_clauses(&self, source: BlockId) -> Vec<DiscoveredClause> {
        match self {
            Terminator::SwitchInt { discr, targets, otherwise, span, .. } => {
                let mut clauses = Vec::with_capacity(targets.len() + 1);

                clauses.extend(targets.iter().map(|(value, target)| DiscoveredClause {
                    source,
                    target: ClauseTarget::Block(*target),
                    guard: GuardCondition::SwitchIntMatch { discr: discr.clone(), value: *value },
                    span: span.clone(),
                }));

                clauses.push(DiscoveredClause {
                    source,
                    target: ClauseTarget::Block(*otherwise),
                    guard: GuardCondition::SwitchIntOtherwise {
                        discr: discr.clone(),
                        excluded_values: targets.iter().map(|(value, _)| *value).collect(),
                    },
                    span: span.clone(),
                });

                clauses
            }
            // `unwind`: the cleanup successor is deliberately NOT emitted as a
            // guarded clause here. It is an UNGUARDED (always-explored) successor
            // via `unguarded_successors`/`exit_targets`, which is the sound over-
            // approximation: the verifier reaches the cleanup block on ALL paths
            // (more than reality — the edge is really taken only when the assert
            // fails) so its drops are checked, never fewer; and it is never gated on
            // `AssertFails`, so it cannot be pruned as unreachable.
            Terminator::Assert { cond, expected, msg, target, span, unwind: _ } => vec![
                DiscoveredClause {
                    source,
                    target: ClauseTarget::Block(*target),
                    guard: GuardCondition::AssertHolds { cond: cond.clone(), expected: *expected },
                    span: span.clone(),
                },
                DiscoveredClause {
                    source,
                    target: ClauseTarget::Panic,
                    guard: GuardCondition::AssertFails {
                        cond: cond.clone(),
                        expected: *expected,
                        msg: msg.clone(),
                    },
                    span: span.clone(),
                },
            ],
            _ => vec![],
        }
    }

    /// The cleanup block this terminator unwinds to on panic, if it carries a
    /// `Cleanup` unwind edge. A real in-CFG successor the verifier must reach so
    /// the cleanup drops are checked; `Continue`/`Terminate`/`Unreachable` unwind
    /// edges are function exits with no in-block successor.
    pub fn unwind_cleanup_target(&self) -> Option<BlockId> {
        match self {
            Terminator::Call { unwind, .. }
            | Terminator::Assert { unwind, .. }
            | Terminator::Drop { unwind, .. } => unwind.cleanup_target(),
            _ => None,
        }
    }

    /// Plain successor blocks that do not add a new guard condition.
    pub fn unguarded_successors(&self) -> Vec<BlockId> {
        let mut succ = match self {
            Terminator::Goto(target) => vec![*target],
            Terminator::Call { target, .. } => target.iter().copied().collect(),
            Terminator::Drop { target, .. } => vec![*target],
            Terminator::Opaque { targets, .. } => targets.clone(),
            Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Assert { .. }
            | Terminator::Unreachable
            | Terminator::Resume => vec![],
        };
        // The unwind/cleanup successor (if any) is a real CFG block that drops
        // the live locals on the panic path and must stay reachable so its own
        // `Drop` obligations are verified (rather than pruned as dead).
        if let Some(cleanup) = self.unwind_cleanup_target() {
            succ.push(cleanup);
        }
        succ
    }

    /// Exit categories directly reachable from this terminator.
    pub fn exit_targets(&self) -> Vec<ClauseTarget> {
        let mut exits = match self {
            Terminator::Return => vec![ClauseTarget::Return],
            Terminator::Unreachable => vec![ClauseTarget::Unreachable],
            // a `Resume` sink propagates an in-flight unwind out of the
            // function. It contributes no in-CFG exit edge and no obligation —
            // exactly the empty-exit behavior the prior `Opaque{targets:[]}`
            // lowering of `UnwindResume` had, so no `exit_targets` consumer changes.
            Terminator::Resume => vec![],
            // (P1-16): Assert has both a normal target (condition holds)
            // and a panic target (condition violated).
            Terminator::Assert { target, .. } => {
                vec![ClauseTarget::Block(*target), ClauseTarget::Panic]
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                let mut exits = targets
                    .iter()
                    .map(|(_, block)| ClauseTarget::Block(*block))
                    .collect::<Vec<_>>();
                exits.push(ClauseTarget::Block(*otherwise));
                exits
            }
            Terminator::Goto(target) | Terminator::Drop { target, .. } => {
                vec![ClauseTarget::Block(*target)]
            }
            Terminator::Call { target, .. } => {
                target.iter().map(|block| ClauseTarget::Block(*block)).collect()
            }
            Terminator::Opaque { targets, .. } => {
                targets.iter().map(|block| ClauseTarget::Block(*block)).collect()
            }
        };
        // The unwind/cleanup block (if any) is a real reachable exit edge: on the
        // panic path control transfers there to drop live locals. Include it so
        // the cleanup block is not pruned and its drops are verified.
        if let Some(cleanup) = self.unwind_cleanup_target() {
            exits.push(ClauseTarget::Block(cleanup));
        }
        exits
    }
}

/// A discovered guarded clause from MIR control flow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiscoveredClause {
    pub source: BlockId,
    pub target: ClauseTarget,
    pub guard: GuardCondition,
    pub span: SourceSpan,
}

/// Successor category for a discovered clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ClauseTarget {
    Block(BlockId),
    Panic,
    Return,
    Unreachable,
}

/// Guard condition recovered from a conditional MIR terminator.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum GuardCondition {
    SwitchIntMatch { discr: Operand, value: u128 },
    SwitchIntOtherwise { discr: Operand, excluded_values: Vec<u128> },
    AssertHolds { cond: Operand, expected: bool },
    AssertFails { cond: Operand, expected: bool, msg: AssertMessage },
}

// Trust: State machine extraction types for TY temporal verification

/// A state machine extracted from enum + match patterns in MIR.
///
/// Represents the transition system: states (enum variants), transitions
/// (match arms that assign new enum values), and initial state. This is
/// the bridge between Rust code and temporal model checking (TY).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateMachine {
    /// Name of the enum type used as state variable.
    pub enum_name: String,
    /// Local variable index holding the state enum.
    pub state_local: usize,
    /// All discovered states (enum variants).
    pub states: Vec<StateInfo>,
    /// Transitions between states discovered from match arms.
    pub transitions: Vec<Transition>,
    /// Discriminant value of the initial state (first assigned variant), if known.
    pub initial_state: Option<u128>,
}

impl StateMachine {
    /// Number of unique states.
    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    pub fn transition_count(&self) -> usize {
        self.transitions.len()
    }

    /// Look up a state name by its discriminant value.
    pub fn state_name(&self, discriminant: u128) -> Option<&str> {
        self.states.iter().find(|s| s.discriminant == discriminant).map(|s| s.name.as_str())
    }
}

/// A single state (enum variant) in a state machine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateInfo {
    /// Variant name (e.g., "Idle", "Connected").
    pub name: String,
    /// Discriminant value used in SwitchInt.
    pub discriminant: u128,
}

/// A transition between two states, discovered from a match arm.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transition {
    /// Discriminant of the source state (matched variant).
    pub from: u128,
    /// Discriminant of the target state (assigned variant).
    pub to: u128,
    /// Block where the match arm lives.
    pub source_block: BlockId,
    /// Block where the state assignment happens.
    pub target_block: BlockId,
}

/// Assert failure messages (mirrors rustc's AssertKind).
// Trust: #413 — added NullPointerDereference, InvalidEnumConstruction,
// ResumedAfterDrop to match rustc's AssertKind variants.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AssertMessage {
    BoundsCheck,
    Overflow(BinOp),
    OverflowNeg,
    DivisionByZero,
    RemainderByZero,
    ResumedAfterReturn,
    ResumedAfterPanic,
    ResumedAfterDrop,
    MisalignedPointerDereference,
    NullPointerDereference,
    InvalidEnumConstruction,
    Custom(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contract_source_ids_are_canonical_bounded_and_collision_resistant() {
        let contract = Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "true".to_string(),
        };

        assert_eq!(
            contract.stable_source_id("demo::f", 0),
            "trust-contract:demo::f:requires:0"
        );
        assert_eq!(
            contract.stable_source_id("<demo::Button as demo::Widget>::rank", 7),
            "trust-contract:<demo::Button%20as%20demo::Widget>::rank:requires:7"
        );
        assert_eq!(
            contract.stable_source_id("demo::A%B?#", 0),
            "trust-contract:demo::A%25B%3F%23:requires:0"
        );
        assert_eq!(
            contract.stable_source_id("demo::café", 0),
            "trust-contract:demo::caf%C3%A9:requires:0"
        );
        assert_ne!(
            contract.stable_source_id("demo::A B", 0),
            contract.stable_source_id("demo::A%20B", 0)
        );

        let long_a = format!("demo::{}", "a".repeat(2_000));
        let long_b = format!("demo::{}b", "a".repeat(1_999));
        let long_id = contract.stable_source_id(&long_a, usize::MAX);
        assert!(long_id.contains("%~sha256~"));
        assert_ne!(long_id, contract.stable_source_id(&long_b, usize::MAX));
        for id in [
            long_id,
            contract.stable_source_id("demo::A B", 0),
            contract.stable_assertion_id(&long_a, usize::MAX),
        ] {
            assert!(id.len() <= 1024, "canonical id exceeded artifact bound: {id}");
            assert!(
                id.bytes().all(|byte| byte.is_ascii_graphic() && !matches!(byte, b'?' | b'#')),
                "canonical id contains an artifact-unsafe byte: {id}"
            );
        }

        assert_eq!(canonical_contract_source_index("trust-contract:demo::f:requires:0"), Some(0));
        for malformed in [
            "garbage:0",
            "trust-contract:demo::f:requires:00",
            "trust-contract:demo::f:unknown:0",
            "trust-contract:demo::A B:requires:0",
            "trust-contract:demo::A%2fB:requires:0",
            "trust-contract:demo%3A%3Af:requires:0",
            "trust-contract:demo::%FF:requires:0",
            "trust-contract:%~sha256~abc:requires:0",
        ] {
            assert_eq!(
                canonical_contract_source_index(malformed),
                None,
                "malformed contract id must decline: {malformed}"
            );
        }
    }

    #[test]
    fn artifact_id_components_preserve_common_paths_without_collisions() {
        assert_eq!(canonical_artifact_id_component("demo::f"), "demo__f");
        assert_eq!(
            canonical_artifact_id_component("demo::checked_transfer"),
            "demo__checked_transfer"
        );
        assert_eq!(canonical_artifact_id_component(""), "_e");
        assert_eq!(canonical_artifact_id_component("a::b"), "a__b");
        assert_eq!(canonical_artifact_id_component("a__b"), "h0_a_u_ub");
        assert_ne!(
            canonical_artifact_id_component("a::b"),
            canonical_artifact_id_component("a__b")
        );
        assert_eq!(canonical_artifact_id_component("café"), "h0_caf_xc3_xa9");

        let long = canonical_artifact_id_component(&"nested::".repeat(200));
        assert!(long.starts_with("h1_"));
        assert!(long.len() <= MAX_INLINE_ARTIFACT_ID_COMPONENT_BYTES);
        assert!(long.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'));
    }

    #[test]
    fn canonical_identity_encodings_are_unique_at_reserved_and_boundary_spellings() {
        let mut corpus = vec![
            "".to_string(),
            "_e".to_string(),
            "h0_".to_string(),
            "h1_".to_string(),
            "a::b".to_string(),
            "a__b".to_string(),
            "a_b".to_string(),
            "a:b".to_string(),
            "a%b".to_string(),
            "café".to_string(),
        ];
        let alphabet = ["a", "_", ":", "%", "é"];
        for left in alphabet {
            for middle in alphabet {
                for right in alphabet {
                    corpus.push(format!("{left}{middle}{right}"));
                }
            }
        }
        let mut encoded = std::collections::BTreeMap::new();
        for raw in corpus {
            let component = canonical_artifact_id_component(&raw);
            assert_eq!(
                encoded.insert(component.clone(), raw.clone()),
                None,
                "distinct raw identity collided at `{component}`",
            );
        }

        assert_eq!(canonical_artifact_id_component(&"a".repeat(384)).len(), 384);
        assert!(canonical_artifact_id_component(&"a".repeat(385)).starts_with("h1_"));
        assert_eq!(canonical_artifact_id_component(&"_".repeat(190)).len(), 383);
        assert!(canonical_artifact_id_component(&"_".repeat(191)).starts_with("h1_"));

        assert_eq!(canonical_contract_function_component(&"a".repeat(900)).len(), 900);
        assert!(canonical_contract_function_component(&"a".repeat(901)).starts_with("%~sha256~"));
        assert_eq!(canonical_contract_function_component(&" ".repeat(300)).len(), 900);
        assert!(canonical_contract_function_component(&" ".repeat(301)).starts_with("%~sha256~"));
    }

    #[test]
    fn canonical_contract_source_parser_roundtrips_every_supported_kind() {
        for (index, kind) in [
            "requires",
            "ensures",
            "invariant",
            "loop_invariant",
            "decreases",
            "assumes",
            "asserts",
            "refine",
            "temporal",
            "modifies",
        ]
        .into_iter()
        .enumerate()
        {
            let id = canonical_contract_source_id("demo::f", kind, index);
            assert_eq!(canonical_contract_source_index(&id), Some(index), "kind `{kind}`");
        }

        assert_eq!(
            canonical_contract_source_id("demo::f", "requires", 7),
            "trust-contract:demo::f:requires:7",
        );
        let kind_delimiter = canonical_contract_source_id("a", "b:c", 0);
        let path_delimiter = canonical_contract_source_id("a:b", "c", 0);
        assert_ne!(kind_delimiter, path_delimiter);
        assert_ne!(
            kind_delimiter,
            canonical_contract_source_id("a", "b%3Ac", 0),
        );
        assert_eq!(canonical_contract_source_index(&kind_delimiter), None);

        let direct_kind = "a".repeat(MAX_DIRECT_CONTRACT_KIND_COMPONENT_BYTES);
        let hashed_kind = "a".repeat(MAX_DIRECT_CONTRACT_KIND_COMPONENT_BYTES + 1);
        assert!(canonical_contract_source_id("demo::f", &direct_kind, 0).contains(&direct_kind));
        assert!(
            canonical_contract_source_id("demo::f", &hashed_kind, 0)
                .contains(":%~sha256~"),
        );
        let long_kind = "x".repeat(10_000);
        let mut distinct_long_kind = long_kind.clone();
        distinct_long_kind.push('y');
        let long_id = canonical_contract_source_id(&"p".repeat(900), &long_kind, usize::MAX);
        assert!(long_id.len() <= 1024, "contract source ID exceeded verifier cap");
        assert_ne!(
            long_id,
            canonical_contract_source_id(
                &"p".repeat(900),
                &distinct_long_kind,
                usize::MAX,
            ),
        );

        for malformed in [
            "trust-contract:demo::A%2FB:requires:0",
            "trust-contract:demo::A%2fB:requires:0",
            "trust-contract:demo::f:requires:184467440737095516160",
        ] {
            assert_eq!(canonical_contract_source_index(malformed), None, "{malformed}");
        }
    }

    // Trust: piece #7a — the const-param symbol keying (INV-1 at the unit level).
    #[test]
    fn const_param_symbol_keys_on_identity_not_width() {
        // Two DISTINCT usize const-params must render to DISTINCT symbols — this
        // is the M==N collision defense at its source.
        assert_eq!(const_param_symbol(0, "M"), "__trust_constparam_0_M");
        assert_eq!(const_param_symbol(1, "N"), "__trust_constparam_1_N");
        assert_ne!(const_param_symbol(0, "M"), const_param_symbol(1, "N"));
        // Same identity => same symbol (the guard/length tie).
        assert_eq!(const_param_symbol(1, "N"), const_param_symbol(1, "N"));
        // A non-identifier name is sanitized so it cannot break the SMT symbol.
        assert_eq!(const_param_symbol(2, "T::LIMIT"), "__trust_constparam_2_T__LIMIT");
        // Deliberately NOT a `__slice_len` (INV-4: no spurious where-fact).
        assert!(!const_param_symbol(1, "N").ends_with("__slice_len"));
    }

    #[test]
    fn test_decompilation_defaults_are_conservative() {
        let artifact = DecompilationArtifact::default();
        assert_eq!(artifact.schema_version, DECOMPILATION_ARTIFACT_SCHEMA_VERSION);
        assert_eq!(artifact.target, DecompileTarget::TrustIr);
        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.verification.status, BinaryVerificationStatus::NotRun);
        assert_eq!(artifact.source_provenance.status, "unavailable");
        assert_eq!(artifact.source_provenance.exact_mapping_count, 0);
        assert_eq!(artifact.source_provenance.ambiguous_mapping_count, 0);
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert_eq!(artifact.verification.proof_certificate, ProofCertificateStatus::NotRequested);
        assert_eq!(
            artifact.reconstruction.validation,
            ReconstructionValidationStatus::NotAttempted
        );
        assert_eq!(artifact.reconstruction.trust_level, TrustLevel::Exploratory);
        assert!(artifact.options.strict);
        assert!(artifact.options.validate_reconstruction);
        assert!(!artifact.options.allow_partial);

        let function = DecompiledFunction::default();
        assert_eq!(function.trust_level, TrustLevel::Exploratory);
        assert_ne!(function.trust_level, TrustLevel::ProofGrade);

        let output = DecompiledOutput::default();
        assert_eq!(output.trust_level, TrustLevel::Exploratory);
        assert_eq!(output.validation, ReconstructionValidationStatus::NotAttempted);
        assert!(output.validated_rust.is_none());
        assert!(artifact.reconstruction.validated_rust.is_none());
        assert!(ReconstructionValidationRecord::default().evidence.is_empty());
    }

    #[test]
    fn preserved_symbolic_formula_evidence_binds_schema_sort_digest_and_origin() {
        let formula = PreservedSymbolicFormula {
            target: DecompileTarget::TrustCg,
            function: Some("main".to_string()),
            block: Some(0),
            statement_index: Some(1),
            location: "bb0[1].rvalue".to_string(),
            formula: Formula::BvAdd(
                Box::new(Formula::Var("x0".to_string(), crate::Sort::BitVec(64))),
                Box::new(Formula::BitVec { value: 1, width: 64 }),
                64,
            ),
        };

        let evidence = formula.evidence();

        assert_eq!(evidence.schema, TRUST_SYMBOLIC_FORMULA_SCHEMA);
        assert_eq!(evidence.sort, "(_ BitVec 64)");
        assert_eq!(evidence.digest.len(), 64);
        assert!(evidence.digest.bytes().all(|byte| byte.is_ascii_hexdigit()));
        assert_eq!(
            evidence.origin,
            "target=trust-cg;function=main;block=bb0;statement=stmt1;location=bb0[1].rvalue"
        );
        assert!(
            formula.matches_schema_aware_consumer_diagnostic(
                &formula.schema_aware_consumer_diagnostic()
            )
        );
        assert!(
            !formula.matches_schema_aware_consumer_diagnostic("trust_symbolic.formula=consumed")
        );
    }

    #[test]
    fn test_binary_artifact_digest_identity_fails_closed() {
        let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "aarch64".to_string(),
            byte_len: Some(64),
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest)),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: 64,
                sha256: digest.to_string(),
            }),
            ..Default::default()
        };
        assert!(metadata.digest_identity_allows_proof_grade());

        let mut missing_root = metadata.clone();
        missing_root.root_artifact_digest = None;
        assert!(!missing_root.digest_identity_allows_proof_grade());
        assert!(
            missing_root
                .digest_identity_blockers()
                .iter()
                .any(|blocker| blocker == "missing root artifact SHA-256 digest")
        );

        let mut missing_selected = metadata.clone();
        missing_selected.selected_image = None;
        assert!(!missing_selected.digest_identity_allows_proof_grade());
        assert!(
            missing_selected
                .digest_identity_blockers()
                .iter()
                .any(|blocker| blocker == "missing selected image digest/range")
        );

        let mut forged_root = metadata.clone();
        forged_root.root_artifact_digest = Some(BinaryArtifactDigest::sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ));
        assert!(!forged_root.digest_identity_allows_proof_grade());
        assert!(forged_root.digest_identity_blockers().iter().any(|blocker| {
            blocker == "root artifact digest does not match whole-file selected image digest"
        }));

        let mut forged_range = metadata;
        forged_range.selected_image = Some(BinarySelectedImageIdentity {
            file_offset: 32,
            file_size: 64,
            sha256: digest.to_string(),
        });
        assert!(!forged_range.digest_identity_allows_proof_grade());
        assert!(
            forged_range
                .digest_identity_blockers()
                .iter()
                .any(|blocker| blocker == "selected image range exceeds root artifact byte length")
        );
    }

    #[test]
    fn test_contract_extraction_defaults_fail_closed_without_source_scraping() {
        let report = ContractExtractionReport::default();
        assert_eq!(report.source, ContractExtractionSource::Unavailable);
        assert!(!report.source_scraping_used);
        assert!(report.diagnostics.is_empty());

        let metadata = TrustMetadata::default();
        assert_eq!(metadata.contract_extraction.source, ContractExtractionSource::Unavailable);
        assert!(!metadata.contract_extraction.source_scraping_used);
        assert!(metadata.contracts.is_empty());
    }

    #[test]
    fn test_compat_source_scraping_report_is_explicit() {
        let report = ContractExtractionReport {
            source: ContractExtractionSource::CompatDebugSourceScraping,
            source_scraping_used: true,
            diagnostics: vec!["compat/debug source scraping enabled".to_string()],
        };

        assert_eq!(report.source, ContractExtractionSource::CompatDebugSourceScraping);
        assert!(report.source_scraping_used);
        assert_ne!(report.source, ContractExtractionSource::Unavailable);
    }

    #[test]
    fn native_proof_fn_metadata_is_required_full_verify() {
        let proof = TrustProofItem::native_proof_fn(
            "sorted_insert_preserves_sorted",
            TrustProofItemKind::Lemma,
            SourceSpan::default(),
        );

        assert!(proof.is_native_syntax());
        assert!(!proof.is_compatibility_import());
        assert!(proof.must_execute_in_full_verify());
        assert_eq!(proof.engine, TrustProofEngineHint::Auto);
        assert_eq!(proof.proof_grade_blocker(), None);
    }

    #[test]
    fn compatibility_proof_import_stays_marked_as_compatibility() {
        let proof = TrustProofItem::compatibility_import(
            "policy_no_untrusted_osc52",
            TrustProofItemSource::TrustVcProofAttribute,
            TrustProofItemKind::Harness,
            TrustProofEngineHint::TrustVc,
            SourceSpan::default(),
        );

        assert!(!proof.is_native_syntax());
        assert!(proof.is_compatibility_import());
        assert!(proof.must_execute_in_full_verify());
        assert_eq!(proof.engine, TrustProofEngineHint::TrustVc);
    }

    #[test]
    fn bounded_proof_items_execute_but_do_not_discharge_full_obligations() {
        let mut proof = TrustProofItem::compatibility_import(
            "legacy_bounded_harness",
            TrustProofItemSource::TrustVcProofAttribute,
            TrustProofItemKind::Harness,
            TrustProofEngineHint::TrustVc,
            SourceSpan::default(),
        );
        proof.mode = TrustProofExecutionMode::BoundedRegression { depth: Some(32) };

        assert!(proof.must_execute_in_full_verify());
        assert_eq!(
            proof.proof_grade_blocker(),
            Some(
                "bounded proof item must execute but cannot discharge unbounded proof obligations"
            )
        );
    }

    #[test]
    fn compiler_contract_bundle_carries_native_proof_items() {
        let contract = Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "n > 0".to_string(),
        };
        let proof = TrustProofItem::native_proof_fn(
            "lemma_positive_step",
            TrustProofItemKind::Lemma,
            SourceSpan::default(),
        );

        let bundle = CompilerContractBundle::new(vec![contract]).with_proof_items(vec![proof]);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.proof_items.len(), 1);
        assert_eq!(bundle.proof_items[0].source, TrustProofItemSource::NativeProofFn);
    }

    #[test]
    fn compiler_contract_typed_proposition_requires_unique_exact_provenance() {
        let contract = Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "__trust_lowered_compiler_contract__:result == x".to_string(),
        };
        let proposition = CompilerContractProposition {
            source_contract_index: 0,
            kind: contract.kind,
            body: contract.body.clone(),
            formula: Formula::Eq(
                Box::new(Formula::Var("_0".to_string(), crate::Sort::Int)),
                Box::new(Formula::Var("x".to_string(), crate::Sort::Int)),
            ),
            variable_domains: vec![
                CompilerContractVariableDomain {
                    name: "_0".to_string(),
                    domain: CompilerContractValueDomain::MachineInt {
                        width: 8,
                        signed: false,
                    },
                },
                CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: CompilerContractValueDomain::MachineInt {
                        width: 8,
                        signed: false,
                    },
                },
            ],
        };
        let exact = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![proposition.clone()]);
        assert_eq!(exact.typed_proposition(0, &contract), Some(&proposition));

        let duplicate = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![proposition.clone(), proposition.clone()]);
        assert!(duplicate.typed_proposition(0, &contract).is_none());

        let mut stale = proposition.clone();
        stale.body.push_str(" && true");
        let exact_plus_stale = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![proposition.clone(), stale]);
        assert!(exact_plus_stale.typed_proposition(0, &contract).is_none());

        let mut formula_drift = proposition;
        formula_drift.formula = Formula::Le(
            Box::new(Formula::Var("_0".to_string(), crate::Sort::Int)),
            Box::new(Formula::Var("x".to_string(), crate::Sort::Int)),
        );
        let structurally_stale = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![formula_drift]);
        assert!(structurally_stale.typed_proposition(0, &contract).is_none());

        let unprefixed_contract = Contract {
            body: "result == x".to_string(),
            ..contract.clone()
        };
        let unprefixed = CompilerContractProposition {
            source_contract_index: 0,
            kind: unprefixed_contract.kind,
            body: unprefixed_contract.body.clone(),
            formula: Formula::Eq(
                Box::new(Formula::Var("_0".to_string(), crate::Sort::Int)),
                Box::new(Formula::Var("x".to_string(), crate::Sort::Int)),
            ),
            variable_domains: vec![
                CompilerContractVariableDomain {
                    name: "_0".to_string(),
                    domain: CompilerContractValueDomain::MachineInt {
                        width: 8,
                        signed: false,
                    },
                },
                CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: CompilerContractValueDomain::MachineInt {
                        width: 8,
                        signed: false,
                    },
                },
            ],
        };
        let missing_prefix = CompilerContractBundle::new(vec![unprefixed_contract.clone()])
            .with_typed_propositions(vec![unprefixed]);
        assert!(missing_prefix.typed_proposition(0, &unprefixed_contract).is_none());
    }

    #[test]
    #[allow(deprecated)]
    fn legacy_typed_contract_formula_digest_is_formula_only_and_non_authoritative() {
        let eq = Formula::Eq(Box::new(Formula::Int(0)), Box::new(Formula::Int(0)));
        let le = Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Int(0)));
        let digest = typed_contract_formula_digest(&eq);

        assert!(digest.starts_with("sha256:"));
        assert_eq!(digest.len(), "sha256:".len() + 64);
        assert_eq!(digest, typed_contract_formula_digest(&eq));
        assert_ne!(digest, typed_contract_formula_digest(&le));
        assert_ne!(
            digest,
            format!("sha256:{}", stable_sha256_hex(&serde_json::to_vec(&eq).unwrap()))
        );
    }

    #[test]
    fn typed_contract_proposition_digest_distinguishes_source_domains() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), crate::Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let domain = |width, signed| {
            vec![CompilerContractVariableDomain {
                name: "x".to_string(),
                domain: CompilerContractValueDomain::MachineInt { width, signed },
            }]
        };
        let u8_digest = typed_contract_proposition_digest(&formula, &domain(8, false));
        assert_ne!(u8_digest, typed_contract_proposition_digest(&formula, &domain(16, false)));
        assert_ne!(u8_digest, typed_contract_proposition_digest(&formula, &domain(8, true)));
        let u64_digest = typed_contract_proposition_digest(&formula, &domain(64, false));
        let usize_domains = vec![CompilerContractVariableDomain {
            name: "x".to_string(),
            domain: CompilerContractValueDomain::PointerSizedInt {
                width: 64,
                signed: false,
            },
        }];
        assert_ne!(u64_digest, typed_contract_proposition_digest(&formula, &usize_domains));
        #[allow(deprecated)]
        {
            // The compatibility digest cannot see either signature; this is
            // exactly why it is deprecated and excluded from authority paths.
            assert_eq!(
                typed_contract_formula_digest(&formula),
                typed_contract_formula_digest(&formula)
            );
        }

        let bool_formula = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), crate::Sort::Bool)),
            Box::new(Formula::Bool(true)),
        );
        let bool_domains = vec![CompilerContractVariableDomain {
            name: "x".to_string(),
            domain: CompilerContractValueDomain::Bool,
        }];
        assert_ne!(u8_digest, typed_contract_proposition_digest(&bool_formula, &bool_domains));
        assert_eq!(
            compiler_contract_formula_with_domains(&
                Formula::Eq(
                    Box::new(Formula::Var("x".to_string(), crate::Sort::Int)),
                    Box::new(Formula::Bool(true)),
                ),
                &bool_domains,
            ),
            Some(bool_formula)
        );
        assert!(compiler_contract_formula_with_domains(&formula, &[]).is_none());
    }

    #[test]
    fn binary_source_provenance_binary_address_only_fails_closed_for_source_backpropagation() {
        let provenance = BinarySourceProvenanceSummary {
            status: "unavailable".to_string(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![
                "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                    .to_string(),
            ],
            source_backpropagation_allowed: true,
        };

        assert!(!provenance.has_exact_debug_source_provenance());
        assert!(!provenance.effective_source_backpropagation_allowed());
        assert!(provenance.binary_address_diagnostics_allowed());

        let diagnostics = provenance.typed_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].kind, BinarySourceProvenanceDiagnosticKind::BinaryAddressOnly);
        assert!(!diagnostics[0].source_backpropagation_allowed);
        assert!(diagnostics[0].binary_address_diagnostics_allowed);
        assert!(diagnostics[0].message.contains("binary-address-only"));
    }

    #[test]
    fn binary_source_provenance_ambiguous_status_rejects_overclaimed_gate() {
        let provenance = BinarySourceProvenanceSummary {
            status: "ambiguous".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 1,
            diagnostics: vec!["ambiguous debug/source rows were withheld".to_string()],
            source_backpropagation_allowed: true,
        };

        assert!(!provenance.has_exact_debug_source_provenance());
        assert!(!provenance.effective_source_backpropagation_allowed());

        let diagnostics = provenance.typed_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].kind, BinarySourceProvenanceDiagnosticKind::BinaryAddressOnly);
        assert!(!diagnostics[0].source_backpropagation_allowed);
        assert!(diagnostics[0].message.contains("ambiguous"));
    }

    #[test]
    fn binary_source_provenance_exact_mapping_allows_source_backpropagation() {
        let provenance = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        };

        assert!(provenance.has_exact_debug_source_provenance());
        assert!(provenance.effective_source_backpropagation_allowed());
        assert!(provenance.binary_address_diagnostics_allowed());
        assert!(provenance.typed_diagnostics().is_empty());
    }

    #[test]
    fn binary_source_provenance_exact_status_without_mappings_rejects_source_backpropagation() {
        let provenance = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        };

        assert!(!provenance.has_exact_debug_source_provenance());
        assert!(!provenance.effective_source_backpropagation_allowed());

        let diagnostics = provenance.typed_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].kind,
            BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected
        );
        assert!(!diagnostics[0].source_backpropagation_allowed);
        assert!(diagnostics[0].binary_address_diagnostics_allowed);
    }

    #[test]
    fn binary_source_provenance_ambiguous_mapping_rejects_source_backpropagation() {
        let provenance = BinarySourceProvenanceSummary {
            status: "ambiguous".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 1,
            diagnostics: vec!["ambiguous binary address-to-source mapping".to_string()],
            source_backpropagation_allowed: true,
        };

        assert!(!provenance.has_exact_debug_source_provenance());
        assert!(!provenance.effective_source_backpropagation_allowed());
        let diagnostics = provenance.typed_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].kind, BinarySourceProvenanceDiagnosticKind::BinaryAddressOnly);
        assert!(!diagnostics[0].source_backpropagation_allowed);
    }

    #[test]
    fn binary_source_provenance_exact_mappings_with_closed_gate_report_gate_rejection() {
        let provenance = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 3,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: false,
        };

        assert!(provenance.has_exact_debug_source_provenance());
        assert!(!provenance.effective_source_backpropagation_allowed());

        let diagnostics = provenance.typed_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].kind,
            BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected
        );
        assert!(diagnostics[0].message.contains("disabled by the provenance gate"));
    }

    #[test]
    fn binary_type_fact_source_ownership_gates_source_backpropagation() {
        let exact_source = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        };
        let exact_source_closed = BinarySourceProvenanceSummary {
            source_backpropagation_allowed: false,
            ..exact_source.clone()
        };
        let ambiguous_source = BinarySourceProvenanceSummary {
            status: "ambiguous".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 1,
            diagnostics: vec!["ambiguous debug/source rows were withheld".to_string()],
            source_backpropagation_allowed: true,
        };

        let source_span = SourceSpan {
            file: "src/debug_types.rs".to_string(),
            line_start: 7,
            col_start: 3,
            line_end: 7,
            col_end: 12,
        };
        let source_origin = BinaryOrigin {
            binary_path: Some("fixtures/type-fact.bin".to_string()),
            function_entry: Some(0x401000),
            instruction_address: 0x401000,
            instruction_size: Some(1),
            encoding: Some(0x90),
            instruction_bytes: vec![0x90],
            source: Some(source_span),
        };
        let exact_fact = BinaryTypeFact {
            subject: BinaryFactSubject::Parameter { function: "debug_types".to_string(), index: 0 },
            recovered_ty: Some(Ty::u64()),
            origin: Some(source_origin.clone()),
            evidence: BinaryFactEvidence::DebugInfo,
            confidence: BinaryFactConfidence::Validated,
            ..Default::default()
        };

        assert_eq!(
            exact_fact.source_ownership(&exact_source),
            BinaryTypeFactSourceOwnership::ExactDebugSource
        );
        assert!(exact_fact.has_exact_debug_source_ownership(&exact_source));
        assert!(exact_fact.source_backpropagation_blockers(&exact_source).is_empty());

        let gate_closed_blockers = exact_fact.source_backpropagation_blockers(&exact_source_closed);
        assert!(
            gate_closed_blockers
                .iter()
                .any(|blocker| { blocker.contains("disabled by the provenance gate") })
        );

        let mut binary_address_fact = exact_fact.clone();
        binary_address_fact.origin = Some(BinaryOrigin {
            source: Some(SourceSpan::binary_address(0x401000)),
            ..source_origin.clone()
        });
        assert_eq!(
            binary_address_fact.source_ownership(&exact_source),
            BinaryTypeFactSourceOwnership::BinaryAddressOnly
        );
        assert!(
            binary_address_fact
                .source_backpropagation_blockers(&exact_source)
                .iter()
                .any(|blocker| blocker.contains("binary-address-only"))
        );

        let missing_origin_fact =
            BinaryTypeFact { origin: None, recovered_ty: Some(Ty::u64()), ..exact_fact.clone() };
        assert_eq!(
            missing_origin_fact.source_ownership(&exact_source),
            BinaryTypeFactSourceOwnership::Missing
        );
        assert!(
            missing_origin_fact
                .source_backpropagation_blockers(&exact_source)
                .iter()
                .any(|blocker| blocker.contains("no exact source ownership origin"))
        );

        assert_eq!(
            exact_fact.source_ownership(&ambiguous_source),
            BinaryTypeFactSourceOwnership::Ambiguous
        );
        assert!(
            exact_fact
                .source_backpropagation_blockers(&ambiguous_source)
                .iter()
                .any(|blocker| blocker.contains("ambiguous"))
        );

        let empty_fact = BinaryTypeFact::default();
        assert_eq!(
            empty_fact.schema_blockers(),
            vec!["type fact has no recovered type or constraints".to_string()]
        );
    }

    #[test]
    fn decompilation_artifact_reports_type_fact_source_backpropagation_blockers() {
        let provenance = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        };
        let binary_only_type_fact = BinaryTypeFact {
            recovered_ty: Some(Ty::u64()),
            origin: Some(BinaryOrigin {
                instruction_address: 0x401000,
                source: Some(SourceSpan::binary_address(0x401000)),
                ..Default::default()
            }),
            evidence: BinaryFactEvidence::DebugInfo,
            confidence: BinaryFactConfidence::Validated,
            ..Default::default()
        };
        let artifact = DecompilationArtifact {
            source_provenance: provenance,
            type_facts: vec![binary_only_type_fact],
            ..Default::default()
        };

        let blockers = artifact.type_fact_source_backpropagation_blockers();
        assert!(blockers.iter().any(|blocker| {
            blocker == "type_fact[0]: type fact source ownership is binary-address-only; source backpropagation rejected"
        }));
    }

    #[test]
    fn binary_origin_canonical_provenance_rejects_default_and_malformed_identity() {
        let default_origin = BinaryOrigin::default();
        let default_blockers = default_origin.canonical_provenance_blockers();
        assert!(default_blockers.iter().any(|blocker| blocker == "missing binary path"));
        assert!(default_blockers.iter().any(|blocker| blocker == "missing function entry address"));
        assert!(default_blockers.iter().any(|blocker| blocker == "missing instruction size"));

        let malformed_origin = BinaryOrigin {
            binary_path: Some("fixtures/tiny".to_string()),
            function_entry: Some(0x401000),
            instruction_address: 0x401010,
            instruction_size: Some(4),
            encoding: None,
            instruction_bytes: vec![0x90, 0x90],
            source: Some(SourceSpan::binary_address(0x401011)),
        };
        let malformed_blockers = malformed_origin.canonical_provenance_blockers();
        assert!(malformed_blockers.iter().any(|blocker| {
            blocker == "instruction size 4 does not match 2 instruction byte(s)"
        }));
        assert!(
            malformed_blockers.iter().any(|blocker| {
                blocker == "binary source span does not match instruction address"
            })
        );

        let canonical_origin = BinaryOrigin {
            instruction_size: Some(2),
            source: Some(SourceSpan::binary_address(0x401010)),
            ..malformed_origin
        };
        assert!(canonical_origin.canonical_provenance_allows_proof_grade());
    }

    #[test]
    fn binary_source_provenance_schema_and_backprop_blockers_are_stable() {
        let malformed_status = BinarySourceProvenanceSummary {
            status: "Exact".to_string(),
            source_backpropagation_allowed: true,
            ..Default::default()
        };
        assert_eq!(
            malformed_status.schema_blockers(),
            vec!["source provenance status `Exact` is not recognized".to_string()]
        );
        assert!(malformed_status.source_backpropagation_blockers().iter().any(|blocker| {
            blocker == "source backpropagation is enabled without exact debug/source provenance"
        }));

        let overclaimed_exact = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        };
        assert_eq!(
            overclaimed_exact.schema_blockers(),
            vec!["exact source provenance has no accepted mappings".to_string()]
        );
        assert!(!overclaimed_exact.source_backpropagation_allows_proof_grade());

        let closed_gate = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: false,
        };
        assert_eq!(
            closed_gate.source_backpropagation_blockers(),
            vec!["source backpropagation is disabled by the provenance gate".to_string()]
        );

        let exact_allowed =
            BinarySourceProvenanceSummary { source_backpropagation_allowed: true, ..closed_gate };
        assert!(exact_allowed.source_backpropagation_allows_proof_grade());
        assert!(
            BinarySourceProvenanceSummary::default()
                .source_backpropagation_blockers()
                .iter()
                .any(|blocker| blocker
                    == "source backpropagation lacks exact debug/source provenance")
        );
    }

    #[test]
    fn solver_dispatch_canonical_replay_rejects_defaulted_origin_replay_and_identity() {
        let legacy_json = r#"{"id":"legacy-dispatch","solver":"ay"}"#;
        let legacy_dispatch: SolverDispatchRecord =
            serde_json::from_str(legacy_json).expect("deserialize legacy solver dispatch");
        let legacy_blockers = legacy_dispatch.canonical_replay_blockers();
        assert!(
            legacy_blockers
                .iter()
                .any(|blocker| blocker == "solver dispatch replay was not completed")
        );
        assert!(
            legacy_blockers
                .iter()
                .any(|blocker| blocker == "solver dispatch is missing binary origin")
        );
        assert!(legacy_blockers.iter().any(|blocker| {
            blocker == "solver dispatch replay identity: missing dispatch binary artifact digest identity"
        }));

        let digest = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let dispatch = SolverDispatchRecord {
            id: "canonical-dispatch".to_string(),
            function: Some("entry".to_string()),
            origin: Some(BinaryOrigin {
                binary_path: Some("fixtures/tiny".to_string()),
                function_entry: Some(0x401000),
                instruction_address: 0x401010,
                instruction_size: Some(1),
                encoding: Some(0x90),
                instruction_bytes: vec![0x90],
                source: Some(SourceSpan::binary_address(0x401010)),
            }),
            solver: "ay".to_string(),
            status: SolverDispatchStatus::Unsat,
            binary_artifact_digest_identity: Some(BinaryArtifactDigestIdentity {
                root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest)),
                selected_image: Some(BinarySelectedImageIdentity {
                    file_offset: 0,
                    file_size: 1,
                    sha256: digest.to_string(),
                }),
            }),
            replay: ReplayStatus::Replayed,
            ..Default::default()
        };
        assert!(dispatch.canonical_replay_allows_proof_grade());
    }

    #[test]
    fn decompilation_artifact_canonical_binary_to_trust_ir_reports_stable_blockers() {
        let artifact = DecompilationArtifact {
            schema_version: DECOMPILATION_ARTIFACT_SCHEMA_VERSION - 1,
            target: DecompileTarget::Rust,
            source_provenance: BinarySourceProvenanceSummary {
                status: "EXACT".to_string(),
                ..Default::default()
            },
            functions: vec![DecompiledFunction {
                name: "entry".to_string(),
                entry: 0x401000,
                verification: BinaryVerificationSummary {
                    solver_dispatch: vec![SolverDispatchRecord {
                        id: "entry:vc0".to_string(),
                        solver: "ay".to_string(),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                ..Default::default()
            }],
            ..Default::default()
        };

        let blockers = artifact.canonical_binary_to_trust_ir_blockers();
        assert!(blockers.iter().any(|blocker| {
            blocker
                == &format!(
                    "decompilation artifact schema version {} is not supported; expected {}",
                    DECOMPILATION_ARTIFACT_SCHEMA_VERSION - 1,
                    DECOMPILATION_ARTIFACT_SCHEMA_VERSION
                )
        }));
        assert!(
            blockers
                .iter()
                .any(|blocker| blocker == "decompilation artifact target is not TrustIr")
        );
        assert!(
            blockers
                .iter()
                .any(|blocker| blocker == "binary metadata: missing root artifact byte length")
        );
        assert!(blockers.iter().any(|blocker| {
            blocker == "source provenance: source provenance status `EXACT` is not recognized"
        }));
        assert!(
            blockers
                .iter()
                .any(|blocker| blocker == "function[0] `entry` is missing binary origin")
        );
        assert!(
            blockers
                .iter()
                .any(|blocker| blocker == "function[0] `entry` has no instruction provenance")
        );
        assert!(
            blockers
                .iter()
                .any(|blocker| blocker == "function[0] `entry` is missing lifted TrustIr body")
        );
        assert!(blockers.iter().any(|blocker| {
            blocker == "function[0] `entry` dispatch[0]: solver dispatch replay was not completed"
        }));
    }

    #[test]
    fn test_binary_origin_deserializes_legacy_json_without_instruction_bytes() {
        let json = r#"{
            "binary_path": "fixtures/tiny",
            "function_entry": 4198400,
            "instruction_address": 4198416,
            "instruction_size": 7,
            "encoding": 5,
            "source": null
        }"#;

        let origin: BinaryOrigin =
            serde_json::from_str(json).expect("legacy BinaryOrigin should deserialize");

        assert_eq!(origin.binary_path.as_deref(), Some("fixtures/tiny"));
        assert_eq!(origin.function_entry, Some(0x401000));
        assert_eq!(origin.instruction_address, 0x401010);
        assert_eq!(origin.instruction_size, Some(7));
        assert_eq!(origin.encoding, Some(5));
        assert!(origin.instruction_bytes.is_empty());
    }

    #[test]
    fn reconstruction_validation_record_roundtrips_structured_evidence() {
        let record = ReconstructionValidationRecord {
            candidate: ReconstructionCandidateKind::StructuredTrustIr,
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::Partial,
            evidence: vec![
                ReconstructionValidationEvidence::BidirectionalTrustIrRefinement,
                ReconstructionValidationEvidence::NoCheckedProofCertificate,
                ReconstructionValidationEvidence::NoBinaryProofObligation,
            ],
            ..Default::default()
        };

        let encoded = serde_json::to_string(&record).expect("serialize record");
        assert!(encoded.contains("BidirectionalTrustIrRefinement"));

        let decoded: ReconstructionValidationRecord =
            serde_json::from_str(&encoded).expect("deserialize record");
        assert_eq!(decoded.evidence, record.evidence);
    }

    #[test]
    fn validated_rust_reconstruction_roundtrips_strict_subset_evidence() {
        let validated_rust = ValidatedRustReconstruction {
            status: ReconstructionValidationStatus::Failed,
            trust_level: TrustLevel::Rejected,
            eligibility: vec![RustReconstructionEligibility {
                function: Some("binary_fn".into()),
                eligible: false,
                rejections: vec![
                    RustReconstructionRejectionKind::NonStraightLine,
                    RustReconstructionRejectionKind::MemoryAccess,
                    RustReconstructionRejectionKind::Call,
                    RustReconstructionRejectionKind::Unsupported,
                ],
                evidence: vec![
                    ReconstructionValidationEvidence::RejectedNonStraightLine,
                    ReconstructionValidationEvidence::RejectedMemoryAccess,
                    ReconstructionValidationEvidence::RejectedCall,
                    ReconstructionValidationEvidence::RejectedUnsupported,
                ],
                diagnostics: vec!["strict subset rejected".into()],
                ..Default::default()
            }],
            validation_records: vec![ReconstructionValidationRecord {
                target: DecompileTarget::Rust,
                candidate: ReconstructionCandidateKind::ValidatedRustStrictSubset,
                status: ReconstructionValidationStatus::Failed,
                trust_level: TrustLevel::Rejected,
                evidence: vec![ReconstructionValidationEvidence::RejectedNonStraightLine],
                ..Default::default()
            }],
            diagnostics: vec!["compile-back validation not implemented".into()],
        };

        let output = DecompiledOutput {
            target: DecompileTarget::Rust,
            validated_rust: Some(validated_rust.clone()),
            ..Default::default()
        };
        let encoded = serde_json::to_string(&output).expect("serialize output");
        assert!(encoded.contains("validated_rust"));
        assert!(encoded.contains("ValidatedRustStrictSubset"));
        assert!(encoded.contains("RejectedMemoryAccess"));

        let decoded: DecompiledOutput = serde_json::from_str(&encoded).expect("deserialize output");
        assert_eq!(decoded.validated_rust, Some(validated_rust));
    }

    #[test]
    fn test_binary_verification_summary_aggregates_status_counts_and_replay() {
        let proved = BinaryVerificationSummary::from_solver_dispatch(vec![SolverDispatchRecord {
            id: "vc0".into(),
            solver: "ay".into(),
            status: SolverDispatchStatus::Unsat,
            replay: ReplayStatus::Replayed,
            ..Default::default()
        }]);
        assert_eq!(proved.status, BinaryVerificationStatus::Proved);
        assert_eq!(proved.proved, 1);
        assert_eq!(proved.failed, 0);
        assert_eq!(proved.replay, ReplayStatus::Replayed);
        assert_eq!(proved.trust_level, TrustLevel::Partial);

        let unsupported =
            BinaryVerificationSummary::from_solver_dispatch(vec![SolverDispatchRecord {
                id: "vc0".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Unsupported,
                ..Default::default()
            }]);
        assert_eq!(unsupported.status, BinaryVerificationStatus::Unsupported);
        assert_eq!(unsupported.unsupported, 1);
        assert_eq!(unsupported.trust_level, TrustLevel::Partial);

        let rejected =
            BinaryVerificationSummary::from_solver_dispatch(vec![SolverDispatchRecord {
                id: "vc0".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Rejected,
                ..Default::default()
            }]);
        assert_eq!(rejected.status, BinaryVerificationStatus::Rejected);
        assert_eq!(rejected.rejected, 1);
        assert_eq!(rejected.trust_level, TrustLevel::Rejected);

        let mixed = BinaryVerificationSummary::from_solver_dispatch(vec![
            SolverDispatchRecord {
                id: "vc0".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Unsat,
                replay: ReplayStatus::Replayed,
                ..Default::default()
            },
            SolverDispatchRecord {
                id: "vc1".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Sat,
                replay: ReplayStatus::Failed,
                ..Default::default()
            },
            SolverDispatchRecord {
                id: "vc2".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Timeout,
                replay: ReplayStatus::NotAttempted,
                ..Default::default()
            },
        ]);
        assert_eq!(mixed.status, BinaryVerificationStatus::Mixed);
        assert_eq!(mixed.total_vcs, 3);
        assert_eq!(mixed.proved, 1);
        assert_eq!(mixed.failed, 1);
        assert_eq!(mixed.timeout, 1);
        assert_eq!(mixed.replay, ReplayStatus::Failed);
        assert_eq!(mixed.trust_level, TrustLevel::Partial);
    }

    #[test]
    fn test_binary_verification_summary_treats_non_bad_state_semantics_as_unknown() {
        let summary = BinaryVerificationSummary::from_solver_dispatch(vec![
            SolverDispatchRecord {
                id: "vc0".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Unsat,
                query_semantics: SolverQuerySemantics::SatIsFeasiblePath,
                ..Default::default()
            },
            SolverDispatchRecord {
                id: "vc1".into(),
                solver: "ay".into(),
                status: SolverDispatchStatus::Sat,
                query_semantics: SolverQuerySemantics::SatIsSatisfiableOnly,
                ..Default::default()
            },
        ]);

        assert_eq!(summary.status, BinaryVerificationStatus::Unknown);
        assert_eq!(summary.proved, 0);
        assert_eq!(summary.failed, 0);
        assert_eq!(summary.unknown, 2);
    }

    #[test]
    fn test_unsupported_ledger_and_exploit_witness_shell_roundtrip() {
        let origin = BinaryOrigin {
            binary_path: Some("fixtures/tiny".into()),
            function_entry: Some(0x401000),
            instruction_address: 0x401010,
            instruction_size: Some(2),
            encoding: Some(0x0b0f),
            instruction_bytes: vec![0x0f, 0x0b],
            source: None,
        };
        let ledger = UnsupportedLedger {
            records: vec![UnsupportedRecord {
                stage: "lift".into(),
                architecture: Some("x86_64".into()),
                origin: Some(origin.clone()),
                opcode: Some("ud2".into()),
                operand: None,
                feature: "trap instruction semantics".into(),
            }],
        };
        assert!(!ledger.is_empty());
        assert_eq!(origin.span().binary_address_value(), Some(0x401010));

        let claim = CompilerClaim {
            component: "lifter".into(),
            claim: "instruction has modeled semantics".into(),
            location: Some(origin.span()),
            assumptions: vec![ModelAssumption {
                stage: "decode".into(),
                description: "instruction bytes decoded by fixture".into(),
            }],
        };
        let witness = ExploitWitness {
            claim,
            refutation: RefutationKind::TranslationMismatch,
            function: "main".into(),
            location: Some(SourceSpan::binary_address(0x401010)),
            model: None,
            replay: ReplayStatus::Spurious,
            attribution: Some("semantic lifter".into()),
        };

        let json =
            serde_json::to_string(&(ledger, witness)).expect("serialize witness shell tuple");
        let (round_ledger, round_witness): (UnsupportedLedger, ExploitWitness) =
            serde_json::from_str(&json).expect("deserialize witness shell tuple");

        assert_eq!(round_ledger.records.len(), 1);
        assert_eq!(round_ledger.records[0].stage, "lift");
        assert_eq!(
            round_ledger.records[0].origin.as_ref().map(|origin| origin.instruction_address),
            Some(0x401010)
        );
        assert_eq!(
            round_ledger.records[0].origin.as_ref().map(|origin| origin.instruction_bytes.clone()),
            Some(vec![0x0f, 0x0b])
        );
        assert_eq!(round_witness.function, "main");
        assert_eq!(round_witness.replay, ReplayStatus::Spurious);
        assert!(round_witness.location.as_ref().is_some_and(SourceSpan::is_binary));
    }

    #[test]
    fn test_aarch64_atomic_semantic_facts_are_typed_but_fail_closed() {
        let origin = BinaryOrigin {
            binary_path: Some("fixtures/aarch64/atomics".into()),
            function_entry: Some(0x401000),
            instruction_address: 0x401008,
            instruction_size: Some(4),
            encoding: Some(0xC85F_FC20),
            instruction_bytes: 0xC85F_FC20_u32.to_le_bytes().to_vec(),
            source: None,
        };
        let ledger = UnsupportedLedger {
            records: vec![UnsupportedRecord {
                stage: "trust-lift::semantic-lift".into(),
                architecture: Some("aarch64".into()),
                origin: Some(origin.clone()),
                opcode: Some("Ldaxr".into()),
                operand: Some("X0, [X1]".into()),
                feature:
                    "AArch64 atomic/exclusive memory-order semantics are unsupported fail-closed: LDAXR combines acquire ordering with an exclusive-monitor reservation"
                        .into(),
            }],
        };

        assert_eq!(ledger.family_count(UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY), 1);
        let facts = ledger.aarch64_atomic_semantic_facts();
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.origin.as_ref().map(|origin| origin.instruction_address), Some(0x401008));
        assert_eq!(fact.opcode, "Ldaxr");
        assert_eq!(fact.access, MemoryAccessKind::Read);
        assert_eq!(fact.ordering, MemoryOrderingSemantics::Acquire);
        assert_eq!(fact.exclusive_monitor, Aarch64ExclusiveMonitorSemantics::LoadReserve);
        assert!(!fact.reports_status);
        assert!(fact.missing_witnesses.iter().any(|witness| witness == "acquire ordering event"));
        assert!(
            fact.missing_witnesses
                .iter()
                .any(|witness| witness == "exclusive-monitor reservation state")
        );
        assert!(!fact.proof_grade_gate_accepted());
        assert!(
            fact.proof_grade_rejection_reason()
                .is_some_and(|reason| reason.contains("not proof-consumed"))
        );
    }

    #[test]
    fn test_aarch64_store_exclusive_fact_reports_status_result() {
        let record = UnsupportedRecord {
            stage: "trust-lift::semantic-lift".into(),
            architecture: Some("aarch64".into()),
            origin: None,
            opcode: Some("Stlxr".into()),
            operand: Some("W2, X0, [X1]".into()),
            feature:
                "AArch64 atomic/exclusive memory-order semantics are unsupported fail-closed: STLXR combines release ordering with monitor-conditional store success"
                    .into(),
        };

        let fact = record
            .aarch64_atomic_semantic_fact()
            .expect("STLXR unsupported record should recover a typed semantic fact");
        assert_eq!(fact.access, MemoryAccessKind::Write);
        assert_eq!(fact.ordering, MemoryOrderingSemantics::Release);
        assert_eq!(fact.exclusive_monitor, Aarch64ExclusiveMonitorSemantics::StoreConditional);
        assert!(fact.reports_status);
        assert!(
            fact.missing_witnesses
                .iter()
                .any(|witness| witness == "store-conditional status result")
        );
        assert!(!fact.proof_grade_gate_accepted());
    }

    #[test]
    fn test_aarch64_sync_boundary_facts_are_typed_but_fail_closed() {
        let origin = BinaryOrigin {
            binary_path: Some("fixtures/aarch64/barrier".into()),
            function_entry: Some(0x401000),
            instruction_address: 0x40100c,
            instruction_size: Some(4),
            encoding: Some(0xD503_3B9F),
            instruction_bytes: 0xD503_3B9F_u32.to_le_bytes().to_vec(),
            source: None,
        };
        let ledger = UnsupportedLedger {
            records: vec![UnsupportedRecord {
                stage: "trust-lift::semantic-lift".into(),
                architecture: Some("aarch64".into()),
                origin: Some(origin.clone()),
                opcode: Some("Dmb".into()),
                operand: Some("ISH full".into()),
                feature:
                    "AArch64 synchronization boundary modeled as explicit partial unsupported-ledger boundary; kind=DataMemoryBarrier; scope=InnerShareable; ordering=LoadsAndStores; clears_exclusive_monitor=false; raw_option=0xb; not proof-grade until ordering/monitor witnesses are proof-consumed"
                        .into(),
            }],
        };

        assert_eq!(ledger.family_count(UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY), 1);
        let facts = ledger.aarch64_sync_boundary_semantic_facts();
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.origin.as_ref().map(|origin| origin.instruction_address), Some(0x40100c));
        assert_eq!(fact.opcode, "Dmb");
        assert_eq!(fact.kind, Aarch64SyncBoundaryKind::DataMemoryBarrier);
        assert_eq!(fact.scope, Aarch64SyncScope::InnerShareable);
        assert_eq!(fact.ordering, Aarch64SyncOrdering::LoadsAndStores);
        assert_eq!(fact.raw_option, Some(0xb));
        assert!(!fact.clears_exclusive_monitor);
        assert!(fact.missing_witnesses.iter().any(|witness| witness == "barrier ordering event"));
        assert!(fact.missing_witnesses.iter().any(|witness| witness == "happens-before witness"));
        assert!(!fact.proof_grade_gate_accepted());
        assert!(
            fact.proof_grade_rejection_reason()
                .is_some_and(|reason| reason.contains("sync boundary fact"))
        );
    }

    #[test]
    fn test_aarch64_sync_boundary_fact_scope_is_exact_and_does_not_match_atomic() {
        let ldar_record = UnsupportedRecord {
            stage: "trust-lift::semantic-lift".into(),
            architecture: Some("aarch64".into()),
            origin: None,
            opcode: Some("Ldar".into()),
            operand: Some("X0, [X1]".into()),
            feature:
                "AArch64 atomic memory-order access modeled as explicit partial unsupported-ledger boundary"
                    .into(),
        };
        assert!(ldar_record.aarch64_atomic_semantic_fact().is_some());
        assert!(ldar_record.aarch64_sync_boundary_semantic_fact().is_none());

        let clrex_record = UnsupportedRecord {
            stage: "trust-lift::semantic-lift".into(),
            architecture: Some("aarch64".into()),
            origin: None,
            opcode: Some("Clrex".into()),
            operand: None,
            feature:
                "AArch64 synchronization boundary modeled as explicit partial unsupported-ledger boundary; kind=ClearExclusiveMonitor; scope=Local; ordering=None; clears_exclusive_monitor=true; raw_option=0x0; not proof-grade until ordering/monitor witnesses are proof-consumed"
                    .into(),
        };
        let clrex = clrex_record
            .aarch64_sync_boundary_semantic_fact()
            .expect("CLREX should recover a sync-boundary fact");
        assert_eq!(clrex.kind, Aarch64SyncBoundaryKind::ClearExclusiveMonitor);
        assert_eq!(clrex.scope, Aarch64SyncScope::Local);
        assert_eq!(clrex.ordering, Aarch64SyncOrdering::None);
        assert!(clrex.clears_exclusive_monitor);
        assert_eq!(clrex.raw_option, Some(0));
        assert!(clrex.missing_witnesses.iter().any(|witness| witness == "monitor clear witness"));
    }

    #[test]
    fn test_decompilation_artifact_serde_roundtrip() {
        let origin = BinaryOrigin {
            binary_path: Some("fixtures/tiny".to_string()),
            function_entry: Some(0x1000),
            instruction_address: 0x1010,
            instruction_size: Some(4),
            encoding: Some(0x8948_247c),
            instruction_bytes: vec![0x48, 0x89, 0x7c, 0x24],
            source: None,
        };

        let address = Formula::Var("rsp_minus_8".to_string(), crate::Sort::BitVec(64));
        let memory_access = MemoryAccessFact {
            origin: origin.clone(),
            kind: MemoryAccessKind::Write,
            address: address.clone(),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(-8)),
            extent: Some(8),
            provenance: Some("rsp-relative".to_string()),
            taint: vec!["arg0".to_string()],
        };

        let param_storage =
            BinaryStorageLocation::Register { name: "rdi".to_string(), bit_width: Some(64) };
        let ret_storage =
            BinaryStorageLocation::Register { name: "rax".to_string(), bit_width: Some(64) };
        let signature = BinaryFunctionSignature {
            name: "main".to_string(),
            entry: 0x1000,
            calling_convention: BinaryCallingConvention::SystemV,
            parameters: vec![BinaryParameter {
                index: 0,
                name: Some("arg0".to_string()),
                ty: Some(Ty::u64()),
                storage: param_storage.clone(),
                evidence: BinaryFactEvidence::AbiDefault,
                trust_level: TrustLevel::Partial,
            }],
            returns: vec![BinaryReturn {
                index: 0,
                ty: Some(Ty::u64()),
                storage: ret_storage.clone(),
                evidence: BinaryFactEvidence::AbiDefault,
                trust_level: TrustLevel::Partial,
            }],
            stack_delta: Some(0),
            origin: Some(origin.clone()),
            ..Default::default()
        };

        let type_fact = BinaryTypeFact {
            subject: BinaryFactSubject::Parameter { function: "main".to_string(), index: 0 },
            recovered_ty: Some(Ty::u64()),
            constraints: vec![Formula::Bool(true)],
            origin: Some(origin.clone()),
            evidence: BinaryFactEvidence::RegisterUse,
            confidence: BinaryFactConfidence::Inferred,
            trust_level: TrustLevel::Partial,
            assumptions: vec![],
        };

        let output = DecompiledOutput {
            target: DecompileTarget::Rust,
            text: Some("pub unsafe fn main(arg0: u64) -> u64 { arg0 }".to_string()),
            validation: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            diagnostics: vec!["rust output requires validation".to_string()],
            ..Default::default()
        };

        let function = DecompiledFunction {
            name: "main".to_string(),
            entry: 0x1000,
            address_range: Some(BinaryAddressRange { start: 0x1000, end: 0x1020 }),
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin.clone()],
            signature,
            output: Some(output.clone()),
            type_facts: vec![type_fact.clone()],
            memory_accesses: vec![memory_access.clone()],
            trust_level: TrustLevel::Partial,
            ..Default::default()
        };

        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                format: BinaryArtifactFormat::Elf,
                image_kind: BinaryImageKind::Executable,
                architecture: "x86_64".to_string(),
                entry_point: Some(0x1000),
                byte_len: Some(4096),
                segments: vec![BinarySegment {
                    name: Some(".text".to_string()),
                    virtual_range: BinaryAddressRange { start: 0x1000, end: 0x1100 },
                    permissions: BinarySegmentPermissions {
                        read: true,
                        write: false,
                        execute: true,
                    },
                    ..Default::default()
                }],
                symbols: vec![BinarySymbol {
                    name: "main".to_string(),
                    address: 0x1000,
                    size: Some(0x20),
                    kind: BinarySymbolKind::Function,
                }],
                ..Default::default()
            },
            options: DecompileOptions {
                target: DecompileTarget::Rust,
                allow_partial: true,
                emit_unsafe_rust: true,
                entry_points: vec![0x1000],
                ..Default::default()
            },
            target: DecompileTarget::Rust,
            functions: vec![function],
            type_facts: vec![type_fact],
            memory_model: BinaryMemoryModel {
                pointer_width_bits: Some(64),
                endianness: Endianness::Little,
                regions: vec![BinaryMemoryRegion {
                    name: Some("stack".to_string()),
                    kind: MemoryRegionKind::Stack,
                    evidence: BinaryFactEvidence::StackUse,
                    ..Default::default()
                }],
                accesses: vec![memory_access],
                trust_level: TrustLevel::Partial,
                ..Default::default()
            },
            source_provenance: BinarySourceProvenanceSummary {
                status: "exact".to_string(),
                exact_mapping_count: 1,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "exact source provenance recovered for 1 address(es)".to_string(),
                ],
                source_backpropagation_allowed: true,
            },
            verification: BinaryVerificationSummary {
                status: BinaryVerificationStatus::Unknown,
                total_vcs: 1,
                unknown: 1,
                solver_dispatch: vec![SolverDispatchRecord {
                    id: "main:oob:0".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin),
                    solver: "ay".to_string(),
                    backend: Some("smtlib2".to_string()),
                    status: SolverDispatchStatus::Unknown,
                    elapsed_ms: Some(3),
                    diagnostics: vec!["solver returned unknown".to_string()],
                    ..Default::default()
                }],
                ..Default::default()
            },
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::Rust,
                outputs: vec![output],
                validation: ReconstructionValidationStatus::NotAttempted,
                trust_level: TrustLevel::Exploratory,
                ..Default::default()
            },
            trust_level: TrustLevel::Partial,
            ..Default::default()
        };

        let json = serde_json::to_string(&artifact).expect("serialize decompilation artifact");
        let round: DecompilationArtifact =
            serde_json::from_str(&json).expect("deserialize decompilation artifact");

        assert_eq!(round.schema_version, DECOMPILATION_ARTIFACT_SCHEMA_VERSION);
        assert_eq!(round.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(round.binary.architecture, "x86_64");
        assert_eq!(round.target, DecompileTarget::Rust);
        assert_eq!(round.source_provenance.status, "exact");
        assert_eq!(round.source_provenance.exact_mapping_count, 1);
        assert!(round.source_provenance.source_backpropagation_allowed);
        assert_eq!(round.functions.len(), 1);
        assert_eq!(round.functions[0].instruction_provenance[0].instruction_address, 0x1010);
        assert_eq!(
            round.functions[0].instruction_provenance[0].instruction_bytes,
            vec![0x48, 0x89, 0x7c, 0x24]
        );
        assert_eq!(
            round.functions[0].signature.calling_convention,
            BinaryCallingConvention::SystemV
        );
        assert_eq!(round.functions[0].signature.parameters[0].storage, param_storage);
        assert_eq!(round.functions[0].signature.returns[0].storage, ret_storage);
        assert_eq!(round.functions[0].memory_accesses[0].kind, MemoryAccessKind::Write);
        assert_eq!(
            round.functions[0].memory_accesses[0].origin.instruction_bytes,
            vec![0x48, 0x89, 0x7c, 0x24]
        );
        assert_eq!(round.memory_model.endianness, Endianness::Little);
        assert_eq!(round.verification.status, BinaryVerificationStatus::Unknown);
        assert_eq!(
            round.verification.solver_dispatch[0].query_semantics,
            SolverQuerySemantics::SatIsCounterexample
        );
        assert_eq!(round.reconstruction.trust_level, TrustLevel::Exploratory);
        assert_ne!(round.trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn test_build_midpoint_function() {
        // Hand-build the MIR for: fn get_midpoint(a: usize, b: usize) -> usize { (a + b) / 2 }
        //
        // MIR (simplified):
        //   _0: usize (return)
        //   _1: usize (a)
        //   _2: usize (b)
        //   _3: (usize, bool) (checked add result)
        //   _4: usize (add result)
        //   _5: usize (final result)
        //
        //   bb0:
        //     _3 = CheckedAdd(_1, _2)
        //     assert(!(_3.1), "overflow") -> bb1
        //   bb1:
        //     _4 = (_3.0)
        //     _5 = Div(_4, const 2)
        //     _0 = _5
        //     return

        let func = VerifiableFunction {
            name: "get_midpoint".to_string(),
            def_path: "midpoint::get_midpoint".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0 return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) }, // _1
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) }, // _2
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None }, // _3 checked result
                    LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4
                    LocalDecl { index: 5, ty: Ty::usize(), name: None }, // _5
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Div,
                                    Operand::Copy(Place::local(4)),
                                    Operand::Constant(ConstValue::Uint(2, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        assert_eq!(func.name, "get_midpoint");
        assert_eq!(func.body.locals.len(), 6);
        assert_eq!(func.body.blocks.len(), 2);
        assert_eq!(func.body.arg_count, 2);

        // Verify we can find the overflow assert
        let has_overflow_assert = func.body.blocks.iter().any(|bb| {
            matches!(
                &bb.terminator,
                Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Add), .. }
            )
        });
        assert!(has_overflow_assert, "must have overflow assert for checked add");

        // Verify we can find the division
        let has_div = func.body.blocks.iter().any(|bb| {
            bb.stmts.iter().any(|stmt| {
                matches!(stmt, Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Div, ..), .. })
            })
        });
        assert!(has_div, "must have division operation");

        let clauses = func.body.discovered_clauses();
        assert_eq!(clauses.len(), 2);
        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Block(BlockId(1)))
                && matches!(&clause.guard, GuardCondition::AssertHolds { expected: false, .. })
        }));
        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Panic)
                && matches!(
                    &clause.guard,
                    GuardCondition::AssertFails {
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        ..
                    }
                )
        }));
    }

    #[test]
    fn test_switch_int_clause_discovery() {
        let block = BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(1)),
                targets: vec![(0, BlockId(4)), (7, BlockId(5))],
                otherwise: BlockId(6),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };

        let clauses = block.discovered_clauses();
        assert_eq!(clauses.len(), 3);

        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Block(BlockId(4)))
                && matches!(
                    &clause.guard,
                    GuardCondition::SwitchIntMatch { discr, value: 0 }
                        if matches!(discr, Operand::Copy(place) if *place == Place::local(1))
                )
        }));

        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Block(BlockId(5)))
                && matches!(
                    &clause.guard,
                    GuardCondition::SwitchIntMatch { discr, value: 7 }
                        if matches!(discr, Operand::Copy(place) if *place == Place::local(1))
                )
        }));

        let otherwise = clauses
            .iter()
            .find(|clause| matches!(clause.target, ClauseTarget::Block(BlockId(6))))
            .expect("otherwise clause");

        match &otherwise.guard {
            GuardCondition::SwitchIntOtherwise { discr, excluded_values } => {
                assert!(matches!(discr, Operand::Copy(place) if *place == Place::local(1)));
                assert_eq!(excluded_values.as_slice(), &[0, 7]);
            }
            other => panic!("unexpected guard: {other:?}"),
        }
    }

    #[test]
    fn test_path_map_accumulates_guards() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: Some("flag".into()) }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(0)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(0)),
                        expected: true,
                        msg: AssertMessage::Custom("must hold".into()),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let path_map = body.path_map();
        assert_eq!(path_map.len(), 4);

        let bb3 = path_map.iter().find(|entry| entry.block == BlockId(3)).expect("bb3");
        assert_eq!(bb3.guards.len(), 2);
        assert!(matches!(bb3.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));
        assert!(matches!(bb3.guards[1], GuardCondition::AssertHolds { expected: true, .. }));
        assert_eq!(bb3.exits, vec![ClauseTarget::Return]);
    }

    #[test]
    fn test_path_map_tracks_otherwise_branch() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: Some("state".into()) }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(0)),
                        targets: vec![(0, BlockId(1)), (7, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let path_map = body.path_map();
        let bb3 = path_map.iter().find(|entry| entry.block == BlockId(3)).expect("bb3");
        assert_eq!(bb3.guards.len(), 1);
        assert!(matches!(
            &bb3.guards[0],
            GuardCondition::SwitchIntOtherwise { excluded_values, .. } if excluded_values == &vec![0, 7]
        ));
        assert_eq!(bb3.exits, vec![ClauseTarget::Unreachable]);
    }

    #[test]
    fn test_content_hash_deterministic() {
        let func = VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let h1 = func.content_hash();
        let h2 = func.content_hash();
        assert_eq!(h1, h2, "content hash must be deterministic");
        assert_eq!(h1.len(), 64, "hash is SHA-256 (64 hex chars)");
    }

    #[test]
    fn test_content_hash_changes_with_body() {
        let func1 = VerifiableFunction {
            name: "f".to_string(),
            def_path: "m::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let func2 = VerifiableFunction {
            name: "f".to_string(),
            def_path: "m::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        assert_ne!(
            func1.content_hash(),
            func2.content_hash(),
            "different bodies must have different hashes"
        );
    }

    #[test]
    fn test_content_hash_ignores_name_and_span() {
        let func1 = VerifiableFunction {
            name: "foo".to_string(),
            def_path: "m::foo".to_string(),
            span: SourceSpan {
                file: "a.rs".into(),
                line_start: 1,
                col_start: 0,
                line_end: 1,
                col_end: 10,
            },
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let func2 = VerifiableFunction {
            name: "bar".to_string(),
            def_path: "m::bar".to_string(),
            span: SourceSpan {
                file: "b.rs".into(),
                line_start: 99,
                col_start: 0,
                line_end: 99,
                col_end: 10,
            },
            body: func1.body.clone(),
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        assert_eq!(
            func1.content_hash(),
            func2.content_hash(),
            "hash depends only on body+contracts, not name/span"
        );
    }

    #[test]
    fn test_serialization_roundtrip() {
        let func = VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let json = serde_json::to_string(&func).expect("serialize");
        let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.name, "test");
    }

    #[test]
    fn test_ty_helpers() {
        assert_eq!(Ty::u8(), Ty::Int { width: 8, signed: false });
        assert_eq!(Ty::i8(), Ty::Int { width: 8, signed: true });
        assert_eq!(Ty::u16(), Ty::Int { width: 16, signed: false });
        assert_eq!(Ty::i16(), Ty::Int { width: 16, signed: true });
        assert_eq!(Ty::u32(), Ty::Int { width: 32, signed: false });
        assert_eq!(Ty::i32(), Ty::Int { width: 32, signed: true });
        assert_eq!(Ty::u64(), Ty::Int { width: 64, signed: false });
        assert_eq!(Ty::i64(), Ty::Int { width: 64, signed: true });
        assert_eq!(Ty::u128(), Ty::Int { width: 128, signed: false });
        assert_eq!(Ty::i128(), Ty::Int { width: 128, signed: true });
        assert!(Ty::usize().is_integer());
        assert!(!Ty::usize().is_signed());
        assert_eq!(Ty::usize(), Ty::Int { width: 64, signed: false });
        assert!(Ty::isize().is_signed());
        assert_eq!(Ty::isize(), Ty::Int { width: 64, signed: true });
        assert_eq!(Ty::u32().int_width(), Some(32));
        assert_eq!(Ty::f32_ty(), Ty::Float { width: 32 });
        assert_eq!(Ty::f64_ty(), Ty::Float { width: 64 });
        assert!(Ty::f32_ty().is_float());
        assert!(Ty::f64_ty().is_float());
        assert!(!Ty::u32().is_float());
        assert!(!Ty::Bool.is_float());
        assert_eq!(Ty::f32_ty().float_width(), Some(32));
        assert_eq!(Ty::f64_ty().float_width(), Some(64));
        assert_eq!(Ty::u32().float_width(), None);
        assert_eq!(Ty::bool_ty(), Ty::Bool);
        assert_eq!(Ty::unit_ty(), Ty::Unit);
        assert_eq!(Ty::Bool.int_width(), None);
    }

    // -------------------------------------------------------------------
    // AtomicOrdering lattice tests
    // -------------------------------------------------------------------

    #[test]
    fn test_ordering_is_at_least_reflexive() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert!(o.is_at_least(&o), "{o} should be at least itself");
        }
    }

    #[test]
    fn test_ordering_relaxed_weakest() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert!(o.is_at_least(&Relaxed), "{o} should be at least Relaxed");
        }
    }

    #[test]
    fn test_ordering_seqcst_strongest() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert!(SeqCst.is_at_least(&o), "SeqCst should be at least {o}");
        }
        // Only SeqCst is at least SeqCst.
        assert!(!AcqRel.is_at_least(&SeqCst));
        assert!(!Acquire.is_at_least(&SeqCst));
        assert!(!Release.is_at_least(&SeqCst));
        assert!(!Relaxed.is_at_least(&SeqCst));
    }

    #[test]
    fn test_ordering_acquire_release_incomparable() {
        use AtomicOrdering::*;
        assert!(!Acquire.is_at_least(&Release), "Acquire does NOT provide Release semantics");
        assert!(!Release.is_at_least(&Acquire), "Release does NOT provide Acquire semantics");
    }

    #[test]
    fn test_ordering_acqrel_subsumes_both() {
        use AtomicOrdering::*;
        assert!(AcqRel.is_at_least(&Acquire));
        assert!(AcqRel.is_at_least(&Release));
        assert!(AcqRel.is_at_least(&Relaxed));
        assert!(AcqRel.is_at_least(&AcqRel));
        assert!(!Acquire.is_at_least(&AcqRel));
        assert!(!Release.is_at_least(&AcqRel));
    }

    #[test]
    fn test_ordering_partial_cmp_equal() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert_eq!(o.partial_cmp(&o), Some(std::cmp::Ordering::Equal));
        }
    }

    #[test]
    fn test_ordering_partial_cmp_incomparable() {
        use AtomicOrdering::*;
        assert_eq!(Acquire.partial_cmp(&Release), None, "Acquire and Release are incomparable");
        assert_eq!(Release.partial_cmp(&Acquire), None);
    }

    #[test]
    fn test_ordering_partial_cmp_comparable() {
        use AtomicOrdering::*;
        assert_eq!(Relaxed.partial_cmp(&SeqCst), Some(std::cmp::Ordering::Less));
        assert_eq!(SeqCst.partial_cmp(&Relaxed), Some(std::cmp::Ordering::Greater));
        assert_eq!(Acquire.partial_cmp(&AcqRel), Some(std::cmp::Ordering::Less));
        assert_eq!(AcqRel.partial_cmp(&Acquire), Some(std::cmp::Ordering::Greater));
        assert_eq!(Release.partial_cmp(&AcqRel), Some(std::cmp::Ordering::Less));
        assert_eq!(AcqRel.partial_cmp(&Release), Some(std::cmp::Ordering::Greater));
        assert_eq!(Relaxed.partial_cmp(&Acquire), Some(std::cmp::Ordering::Less));
        assert_eq!(Relaxed.partial_cmp(&Release), Some(std::cmp::Ordering::Less));
    }

    #[test]
    fn test_ordering_join_lattice() {
        use AtomicOrdering::*;
        // Join is the least upper bound.
        assert_eq!(Relaxed.join(&Relaxed), Relaxed);
        assert_eq!(Relaxed.join(&Acquire), Acquire);
        assert_eq!(Relaxed.join(&Release), Release);
        assert_eq!(Acquire.join(&Release), AcqRel, "join of incomparable elements");
        assert_eq!(Release.join(&Acquire), AcqRel);
        assert_eq!(Acquire.join(&AcqRel), AcqRel);
        assert_eq!(AcqRel.join(&SeqCst), SeqCst);
        assert_eq!(SeqCst.join(&Relaxed), SeqCst);
    }

    #[test]
    fn test_ordering_meet_lattice() {
        use AtomicOrdering::*;
        // Meet is the greatest lower bound.
        assert_eq!(SeqCst.meet(&SeqCst), SeqCst);
        assert_eq!(SeqCst.meet(&AcqRel), AcqRel);
        assert_eq!(AcqRel.meet(&Acquire), Acquire);
        assert_eq!(AcqRel.meet(&Release), Release);
        assert_eq!(Acquire.meet(&Release), Relaxed, "meet of incomparable elements");
        assert_eq!(Release.meet(&Acquire), Relaxed);
        assert_eq!(Acquire.meet(&Relaxed), Relaxed);
        assert_eq!(Relaxed.meet(&Relaxed), Relaxed);
    }

    #[test]
    fn test_ordering_join_commutative() {
        use AtomicOrdering::*;
        let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
        for &a in &all {
            for &b in &all {
                assert_eq!(a.join(&b), b.join(&a), "join({a}, {b}) should be commutative");
            }
        }
    }

    #[test]
    fn test_ordering_meet_commutative() {
        use AtomicOrdering::*;
        let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
        for &a in &all {
            for &b in &all {
                assert_eq!(a.meet(&b), b.meet(&a), "meet({a}, {b}) should be commutative");
            }
        }
    }

    #[test]
    fn test_ordering_display() {
        assert_eq!(AtomicOrdering::Relaxed.to_string(), "Relaxed");
        assert_eq!(AtomicOrdering::Acquire.to_string(), "Acquire");
        assert_eq!(AtomicOrdering::Release.to_string(), "Release");
        assert_eq!(AtomicOrdering::AcqRel.to_string(), "AcqRel");
        assert_eq!(AtomicOrdering::SeqCst.to_string(), "SeqCst");
    }

    // -------------------------------------------------------------------
    // AtomicOpKind classification tests
    // -------------------------------------------------------------------

    #[test]
    fn test_atomic_op_kind_classification() {
        assert!(AtomicOpKind::Load.is_load());
        assert!(!AtomicOpKind::Load.is_store());
        assert!(!AtomicOpKind::Load.is_rmw());
        assert!(!AtomicOpKind::Load.is_fence());

        assert!(AtomicOpKind::Store.is_store());
        assert!(!AtomicOpKind::Store.is_load());
        assert!(!AtomicOpKind::Store.is_rmw());

        assert!(AtomicOpKind::FetchAdd.is_rmw());
        assert!(!AtomicOpKind::FetchAdd.is_load());
        assert!(!AtomicOpKind::FetchAdd.is_store());

        assert!(AtomicOpKind::Fence.is_fence());
        assert!(AtomicOpKind::CompilerFence.is_fence());
        assert!(!AtomicOpKind::Fence.is_rmw());
    }

    #[test]
    fn test_atomic_rmw_op_from_op_kind() {
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Exchange), Some(AtomicRmwOp::Xchg));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchAdd), Some(AtomicRmwOp::Add));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchSub), Some(AtomicRmwOp::Sub));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchAnd), Some(AtomicRmwOp::And));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchOr), Some(AtomicRmwOp::Or));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchXor), Some(AtomicRmwOp::Xor));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchNand), Some(AtomicRmwOp::Nand));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchMin), Some(AtomicRmwOp::Min));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchMax), Some(AtomicRmwOp::Max));
        // Non-RMW kinds return None.
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Load), None);
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Store), None);
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Fence), None);
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::CompareExchange), None);
    }

    #[test]
    fn test_atomic_op_class_from_op_kind() {
        assert_eq!(AtomicOpClass::from_op_kind(AtomicOpKind::Load), AtomicOpClass::Load);
        assert_eq!(AtomicOpClass::from_op_kind(AtomicOpKind::Store), AtomicOpClass::Store);
        assert_eq!(AtomicOpClass::from_op_kind(AtomicOpKind::Fence), AtomicOpClass::Fence);
        assert_eq!(
            AtomicOpClass::from_op_kind(AtomicOpKind::CompareExchange),
            AtomicOpClass::CmpXchg { weak: false }
        );
        assert_eq!(
            AtomicOpClass::from_op_kind(AtomicOpKind::CompareExchangeWeak),
            AtomicOpClass::CmpXchg { weak: true }
        );
        assert_eq!(
            AtomicOpClass::from_op_kind(AtomicOpKind::FetchAdd),
            AtomicOpClass::Rmw(AtomicRmwOp::Add)
        );
    }

    #[test]
    fn test_atomic_op_class_read_write() {
        assert!(AtomicOpClass::Load.is_read());
        assert!(!AtomicOpClass::Load.is_write());
        assert!(!AtomicOpClass::Store.is_read());
        assert!(AtomicOpClass::Store.is_write());
        // RMW is both.
        let rmw = AtomicOpClass::Rmw(AtomicRmwOp::Add);
        assert!(rmw.is_read());
        assert!(rmw.is_write());
        // CmpXchg is both.
        let cas = AtomicOpClass::CmpXchg { weak: false };
        assert!(cas.is_read());
        assert!(cas.is_write());
        // Fence is neither.
        assert!(!AtomicOpClass::Fence.is_read());
        assert!(!AtomicOpClass::Fence.is_write());
    }

    #[test]
    fn test_atomic_rmw_op_display() {
        assert_eq!(AtomicRmwOp::Xchg.to_string(), "xchg");
        assert_eq!(AtomicRmwOp::Add.to_string(), "add");
        assert_eq!(AtomicRmwOp::Sub.to_string(), "sub");
        assert_eq!(AtomicRmwOp::UMin.to_string(), "umin");
        assert_eq!(AtomicRmwOp::UMax.to_string(), "umax");
    }

    #[test]
    fn test_atomic_op_class_display() {
        assert_eq!(AtomicOpClass::Load.to_string(), "load");
        assert_eq!(AtomicOpClass::Store.to_string(), "store");
        assert_eq!(AtomicOpClass::Fence.to_string(), "fence");
        assert_eq!(AtomicOpClass::CmpXchg { weak: false }.to_string(), "cmpxchg");
        assert_eq!(AtomicOpClass::CmpXchg { weak: true }.to_string(), "cmpxchg_weak");
        assert_eq!(AtomicOpClass::Rmw(AtomicRmwOp::Add).to_string(), "rmw_add");
    }

    #[test]
    fn test_atomic_rmw_op_serialization_roundtrip() {
        let ops = vec![
            AtomicRmwOp::Xchg,
            AtomicRmwOp::Add,
            AtomicRmwOp::Sub,
            AtomicRmwOp::And,
            AtomicRmwOp::Or,
            AtomicRmwOp::Xor,
            AtomicRmwOp::Nand,
            AtomicRmwOp::Min,
            AtomicRmwOp::Max,
            AtomicRmwOp::UMin,
            AtomicRmwOp::UMax,
        ];
        let json = serde_json::to_string(&ops).expect("serialize");
        let round: Vec<AtomicRmwOp> = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, ops);
    }

    // Trust: enum-disc-full-native — `disc_index_safe` classification.

    #[test]
    fn struct_adt_is_never_disc_index_safe() {
        let s = Ty::adt("S", vec![("x".into(), Ty::u32())]);
        assert!(!s.disc_index_safe());
    }

    #[test]
    fn adt_enum_defaults_disc_index_safe_false() {
        // `adt_enum` cannot consult the rustc layout, so it stays false.
        let e = Ty::adt_enum(
            "E",
            vec![
                VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
            ],
        );
        assert!(!e.disc_index_safe());
        assert_eq!(e.num_variants(), Some(2));
    }

    #[test]
    fn adt_enum_with_disc_safety_threads_flag_and_keeps_tag_view() {
        let e = Ty::adt_enum_with_disc_safety(
            "E",
            vec![
                VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "B".into(), discriminant: 3, fields: vec![] },
            ],
            true,
        );
        assert!(e.disc_index_safe());
        // A false classification must NOT report safe.
        let e_unsafe = Ty::adt_enum_with_disc_safety(
            "E",
            vec![VariantDef { name: "A".into(), discriminant: 0, fields: vec![] }],
            false,
        );
        assert!(!e_unsafe.disc_index_safe());
    }

    #[test]
    fn disc_index_safe_defaults_false_on_deserialize() {
        // A serialized `Ty::Adt` with NO `disc_index_safe` key (pre-feature)
        // must deserialize to the conservative `false`.
        let json = r#"{"Adt":{"name":"E","fields":[],"variants":[{"name":"A","discriminant":0,"fields":[]}]}}"#;
        let ty: Ty = serde_json::from_str(json).expect("deserialize legacy Adt");
        assert!(!ty.disc_index_safe(), "legacy ADT must default to fail-closed false");
        let encoded = serde_json::to_value(&ty).expect("serialize legacy-shaped Adt");
        assert_eq!(
            encoded["Adt"].get("disc_index_safe"),
            Some(&serde_json::Value::Bool(false)),
            "ordinary wire serialization must retain the fixed schema field"
        );
    }

    #[test]
    fn disc_index_safe_roundtrips_when_true() {
        let e = Ty::adt_enum_with_disc_safety(
            "E",
            vec![VariantDef { name: "A".into(), discriminant: 0, fields: vec![] }],
            true,
        );
        let json = serde_json::to_string(&e).expect("serialize");
        let back: Ty = serde_json::from_str(&json).expect("deserialize");
        assert!(back.disc_index_safe());
        assert_eq!(back, e);
    }

    fn faithful_enum_adt(repr: Option<Option<EnumReprHint>>) -> Ty {
        Ty::Adt { adt_kind: None, layout: None,
            name: "E".into(),
            fields: vec![("__tag".into(), Ty::i64())],
            variants: vec![
                VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
            ],
            disc_index_safe: true,
            faithful_enum_repr: repr, enum_layout: None, }
    }

    fn faithful_enum_repr(ty: &Ty) -> Option<Option<EnumReprHint>> {
        match ty {
            Ty::Adt { faithful_enum_repr, .. } => *faithful_enum_repr,
            _ => panic!("expected Ty::Adt"),
        }
    }

    fn faithful_enum_repr_states() -> Vec<Option<Option<EnumReprHint>>> {
        let hints = [
            EnumReprHint::U8,
            EnumReprHint::U16,
            EnumReprHint::U32,
            EnumReprHint::U64,
            EnumReprHint::I8,
            EnumReprHint::I16,
            EnumReprHint::I32,
            EnumReprHint::I64,
        ];
        let mut states = vec![None, Some(None)];
        states.extend(hints.into_iter().map(|hint| Some(Some(hint))));
        states
    }

    #[test]
    fn faithful_enum_repr_json_roundtrips_every_state_without_legacy_drift() {
        for state in faithful_enum_repr_states() {
            let ty = faithful_enum_adt(state);
            let encoded = serde_json::to_value(&ty).expect("serialize faithful enum Ty");
            let wire = &encoded["Adt"]["faithful_enum_repr"];
            match state {
                None => assert!(wire.is_null(), "outer None must retain legacy null spelling"),
                Some(None) => assert_eq!(
                    wire,
                    &serde_json::json!({"state": "eligible_rust_default"}),
                    "eligible enum without #[repr] needs an explicit marker"
                ),
                Some(Some(hint)) => assert_eq!(
                    wire,
                    &serde_json::to_value(hint).expect("serialize repr hint"),
                    "explicit repr hints must retain their legacy JSON spelling"
                ),
            }
            let decoded: Ty =
                serde_json::from_value(encoded).expect("deserialize faithful enum Ty");
            assert_eq!(decoded, ty, "JSON must retain the exact nested-option state");
        }
    }

    #[test]
    fn faithful_enum_repr_legacy_json_is_backward_compatible_and_fail_closed() {
        let missing = r#"{"Adt":{"name":"E","fields":[],"variants":[],"disc_index_safe":true}}"#;
        let missing: Ty = serde_json::from_str(missing).expect("deserialize pre-B3 ADT");
        assert_eq!(faithful_enum_repr(&missing), None);

        // B3-1's original derived spelling collapsed both outer None and
        // Some(None) to null.  The only sound legacy interpretation is outer
        // None: old bytes cannot be allowed to mint faithful-enum eligibility.
        let legacy_null = r#"{"Adt":{"name":"E","fields":[],"variants":[],"disc_index_safe":true,"faithful_enum_repr":null}}"#;
        let legacy_null: Ty =
            serde_json::from_str(legacy_null).expect("deserialize legacy null marker");
        assert_eq!(faithful_enum_repr(&legacy_null), None);

        for hint in [
            EnumReprHint::U8,
            EnumReprHint::U16,
            EnumReprHint::U32,
            EnumReprHint::U64,
            EnumReprHint::I8,
            EnumReprHint::I16,
            EnumReprHint::I32,
            EnumReprHint::I64,
        ] {
            let mut legacy = serde_json::to_value(faithful_enum_adt(None))
                .expect("serialize legacy explicit carrier shell");
            legacy["Adt"]["faithful_enum_repr"] =
                serde_json::to_value(hint).expect("serialize legacy repr hint");
            let decoded: Ty =
                serde_json::from_value(legacy).expect("deserialize legacy explicit repr");
            assert_eq!(faithful_enum_repr(&decoded), Some(Some(hint)));
        }
    }

    #[test]
    fn faithful_enum_repr_json_rejects_every_noncanonical_marker_shape() {
        let malformed = [
            serde_json::json!(true),
            serde_json::json!(0),
            serde_json::json!([]),
            serde_json::json!("eligible_rust_default"),
            serde_json::json!("U128"),
            serde_json::json!({}),
            serde_json::json!({"state": "unknown"}),
            serde_json::json!({"state": "EligibleRustDefault"}),
            serde_json::json!({"state": "eligible_rust_default", "repr": null}),
            serde_json::json!({"state": "eligible_rust_default", "extra": true}),
            serde_json::json!({"state": "explicit", "repr": "I8"}),
        ];
        for marker in malformed {
            let mut encoded = serde_json::to_value(faithful_enum_adt(None))
                .expect("serialize malformed-input shell");
            encoded["Adt"]["faithful_enum_repr"] = marker.clone();
            assert!(
                serde_json::from_value::<Ty>(encoded).is_err(),
                "malformed faithful-enum marker must be rejected: {marker}"
            );
        }

        let duplicate_state = r#"{"Adt":{"name":"E","fields":[],"variants":[],"disc_index_safe":true,"faithful_enum_repr":{"state":"eligible_rust_default","state":"eligible_rust_default"}}}"#;
        assert!(
            serde_json::from_str::<Ty>(duplicate_state).is_err(),
            "duplicate state keys must be rejected"
        );
    }

    #[test]
    fn faithful_enum_repr_bincode_keeps_nested_option_wire_and_roundtrips() {
        struct FieldWire<'a>(&'a Option<Option<EnumReprHint>>);

        impl Serialize for FieldWire<'_> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                faithful_enum_repr_serde::serialize(self.0, serializer)
            }
        }

        let mut whole_ty_encodings = Vec::new();
        for state in faithful_enum_repr_states() {
            assert_eq!(
                bincode::serialize(&FieldWire(&state)).expect("serialize field wire"),
                bincode::serialize(&state).expect("serialize derived nested option"),
                "non-human-readable field bytes must stay backward-compatible"
            );

            let ty = faithful_enum_adt(state);
            let encoded = bincode::serialize(&ty).expect("serialize faithful enum Ty");
            let decoded: Ty = bincode::deserialize(&encoded).expect("deserialize faithful enum Ty");
            assert_eq!(decoded, ty, "bincode must retain the exact nested-option state");
            whole_ty_encodings.push(encoded);
        }
        for left in 0..whole_ty_encodings.len() {
            for right in (left + 1)..whole_ty_encodings.len() {
                assert_ne!(
                    whole_ty_encodings[left], whole_ty_encodings[right],
                    "every faithful-enum state needs distinct binary bytes"
                );
            }
        }
    }

    #[test]
    fn faithful_enum_default_keeps_binary_field_but_not_semantic_hash_material() {
        let ty = Ty::adt("Legacy", Vec::new());
        let encoded = bincode::serialize(&ty).expect("serialize default-metadata ADT");
        let decoded: Ty = bincode::deserialize(&encoded).expect("deserialize default-metadata ADT");
        assert_eq!(decoded, ty, "binary wire must retain false + outer-None fields");

        let legacy_json = r#"{"Adt":{"name":"Legacy","fields":[],"variants":[],"disc_index_safe":false}}"#;
        assert_eq!(
            ty.try_stable_shape_hash().expect("hash default-metadata ADT"),
            stable_sha256_hex(legacy_json.as_bytes()),
            "outer-None faithful metadata must preserve the pre-B3 semantic shape hash"
        );

        let marked = Ty::Adt { adt_kind: None, layout: None,
            name: "Legacy".into(),
            fields: Vec::new(),
            variants: Vec::new(),
            disc_index_safe: false,
            faithful_enum_repr: Some(None), enum_layout: None, };
        let marked_bytes = bincode::serialize(&marked).expect("serialize marked ADT");
        let marked_back: Ty =
            bincode::deserialize(&marked_bytes).expect("deserialize marked ADT");
        assert_eq!(marked_back, marked, "false + Some(None) must not shift binary fields");
        assert_ne!(
            marked.try_stable_shape_hash().expect("hash marked ADT"),
            ty.try_stable_shape_hash().expect("hash unmarked ADT"),
            "non-default faithful-enum authority must remain hash-visible"
        );

        // Trust (B3-3): `enum_layout` follows the same discipline — a None
        // default is hash-invisible (the legacy_json above carries no key and
        // still matched), while a Some(concrete layout) IS hash-visible and
        // round-trips the binary wire.
        let laid = Ty::Adt { adt_kind: None,
            layout: None,
            name: "Legacy".into(),
            fields: Vec::new(),
            variants: Vec::new(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: Some(Box::new(EnumLayoutInfo {
                encoding: EnumTagEncodingInfo::Niche {
                    untagged_variant: 0,
                    niche_variants_start: 1,
                    niche_variants_end: 1,
                    niche_start: u128::from(u64::MAX),
                    niche_offset: 0,
                    niche_ty: EnumReprHint::U64,
                },
                size: 8,
                align: 8,
                variant_field_offsets: vec![vec![0], vec![]],
            })),
        };
        let laid_bytes = bincode::serialize(&laid).expect("serialize laid ADT");
        let laid_back: Ty = bincode::deserialize(&laid_bytes).expect("deserialize laid ADT");
        assert_eq!(laid_back, laid, "enum_layout must round-trip the binary wire");
        assert_ne!(
            laid.try_stable_shape_hash().expect("hash laid ADT"),
            ty.try_stable_shape_hash().expect("hash unlaid ADT"),
            "a concrete enum_layout asserts bytes and must be hash-visible"
        );
    }

    #[test]
    fn non_adt_types_are_not_disc_index_safe() {
        assert!(!Ty::Bool.disc_index_safe());
        assert!(!Ty::u32().disc_index_safe());
        assert!(!Ty::Array { elem: Box::new(Ty::u8()), len: 4 }.disc_index_safe());
    }
}
