// trust-proof-cert/proof_bundle.rs: ProofBundle format with assumptions,
// environment capture, and reported assurance metadata.
//
// A ProofBundle packages all verification artifacts for a crate or function
// into a single, internally checksummed structure. It extends (not replaces) the
// existing ProofCertificate/CertificateChain infrastructure.
//
// Part of #830: Phase 1 of the Universal Proof Certificate Format.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{CertError, CertificateChain, ProofCertificate};

// ---------------------------------------------------------------------------
// Reported assurance classification
// ---------------------------------------------------------------------------

/// Non-authoritative classification reported by public certificate metadata.
///
/// Values are claims/inventory labels only. This type cannot represent local
/// kernel replay success and must not be used as an acceptance verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReportedAssurance {
    /// A `Certified` record carries a cryptographically consistent
    /// Certifier/Root signature. This is still only a signed claim: no kernel
    /// term was replayed here and the embedded key is not inherently trusted.
    SignedCertificationClaim,
    /// The record reports an unbounded/sound-strength result.
    ReportedSoundnessClaim,
    /// The record reports a bounded result.
    BoundedResultClaim,
    /// No stronger result category can be honestly inferred from the record.
    Unclassified,
}

impl ReportedAssurance {
    /// Human-readable, explicitly non-authoritative label.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::SignedCertificationClaim => "signed certification claim (not replayed)",
            Self::ReportedSoundnessClaim => "reported soundness claim (not replayed)",
            Self::BoundedResultClaim => "bounded result claim (not replayed)",
            Self::Unclassified => "unclassified public record",
        }
    }

    /// Classify claims in a public certificate record.
    ///
    /// Even a signed certification record remains a claim because this path
    /// neither supplies verifier-owned anchor policy nor replays a kernel term.
    #[must_use]
    pub fn from_certificate_record(cert: &ProofCertificate) -> Self {
        use crate::CertificationStatus;
        #[allow(unreachable_patterns)] // CertificationStatus is #[non_exhaustive]
        match cert.status {
            CertificationStatus::Certified
                if crate::check_certificate_signature_integrity(cert).is_ok()
                    && matches!(
                        cert.signature.as_ref().map(|signature| signature.trust_level),
                        Some(crate::TrustLevel::Certifier | crate::TrustLevel::Root)
                    ) =>
            {
                Self::SignedCertificationClaim
            }
            CertificationStatus::Certified | CertificationStatus::Trusted => {
                if cert.solver.strength.is_bounded() {
                    Self::BoundedResultClaim
                } else if cert.solver.strength.is_sound() {
                    Self::ReportedSoundnessClaim
                } else {
                    Self::Unclassified
                }
            }
            _ => Self::Unclassified,
        }
    }
}

impl fmt::Display for ReportedAssurance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ---------------------------------------------------------------------------
// AssumptionSet
// ---------------------------------------------------------------------------

/// Captures all assumptions under which a proof bundle was generated.
///
/// A proof is only valid when its assumptions hold. This struct makes those
/// assumptions explicit and machine-readable.
///
/// Trust (dep-TCB ledger, Stage 0): `trust_levels` is populated by a real
/// producer — [`AssumptionSet::from_scoped_out_deps`] — which classifies every
/// dependency that verification was *scoped out of* into an explicit
/// [`TrustAssumption`] row. Crucially, the `core`/`alloc`/`std` hard-skip is the
/// largest silent TCB surface, so it always appears as explicit `Trusted`/
/// `Conditional` rows rather than being assumed away invisibly. Before this
/// producer existed the set was only ever `::default()`-constructed, which
/// rendered the crate's trust base as empty — an honesty bug, not a soundness
/// one (it under-reported the TCB).
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct AssumptionSet {
    /// Trust levels assumed for external dependencies (e.g., "std::vec::Vec: Trusted").
    pub trust_levels: Vec<TrustAssumption>,
    /// Axioms assumed by the solver (e.g., integer overflow semantics).
    pub axioms: Vec<String>,
    /// Code paths that were NOT verified (e.g., unsafe blocks, FFI calls).
    pub unverified_paths: Vec<String>,
    /// Panic strategy assumed during verification (abort vs unwind).
    pub panic_strategy: PanicStrategy,
    /// Codegen options that affect verification soundness.
    pub codegen_options: Vec<CodegenOption>,
    /// Solver versions used (solver_name -> version string).
    pub solver_versions: Vec<SolverVersion>,
}

/// The `core`/`alloc`/`std` crates the verifier hard-skips. Verification never
/// produces obligations for these (the compiler self-gates on the crate under
/// check), so every property a verified crate proves is *conditional* on the
/// standard library behaving as its types/contracts claim. This is the largest
/// single chunk of the trust base, and the dep-TCB ledger surfaces it
/// explicitly rather than letting it sit silent.
const STD_HARD_SKIP_CRATES: &[&str] = &["core", "alloc", "std"];

impl AssumptionSet {
    /// Trust (dep-TCB ledger, Stage 0): build the trust-level assumption rows
    /// from the set of dependencies that verification was *scoped out of*.
    ///
    /// `verify_target` is the crate (or comma-joined crates) actually verified;
    /// `scoped_out_deps` is every other crate that participated in the build but
    /// produced no obligations (transitive registry/path dependencies). Each
    /// becomes an explicit [`TrustAssumption`] so the proof report can state the
    /// crate's full trust base instead of silently assuming its dependencies.
    ///
    /// The `core`/`alloc`/`std` hard-skip is emitted unconditionally as
    /// `Trusted`/`Conditional` rows — it is never present in `scoped_out_deps`
    /// (the compiler skips it before the dep graph is even consulted), yet it is
    /// the dominant TCB surface, so it must appear in the ledger regardless.
    ///
    /// Classification is deliberately conservative: a scoped-out dependency is
    /// `Conditional` (its correctness is an unverified premise of the proof),
    /// never `Verified` — we do not have its ProofBundle here, so claiming
    /// `Verified` would over-state assurance. The std crates are split: `core`
    /// (type-system / intrinsic surface) is `Trusted`; `alloc`/`std` (allocator,
    /// OS, FFI surface) are `Conditional`.
    #[must_use]
    pub fn from_scoped_out_deps<I, S>(verify_target: Option<&str>, scoped_out_deps: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut trust_levels = Vec::new();

        // The std hard-skip is always part of the TCB, even when the dep graph
        // is empty. core = type-system/intrinsics (Trusted); alloc/std =
        // allocator/OS/FFI surface (Conditional — a heavier, more reviewable
        // assumption).
        for &name in STD_HARD_SKIP_CRATES {
            let level = if name == "core" {
                TrustAssumptionLevel::Trusted
            } else {
                TrustAssumptionLevel::Conditional
            };
            trust_levels.push(TrustAssumption {
                path: name.to_string(),
                level,
                reason: format!(
                    "standard-library crate `{name}` is hard-skipped by the verifier; \
                     all proofs are conditional on its correctness"
                ),
            });
        }

        // Every scoped-out dependency is an unverified premise. We have no
        // ProofBundle for it here, so the honest (conservative) classification
        // is Conditional — never Verified.
        let target = verify_target.unwrap_or("");
        for dep in scoped_out_deps {
            let dep = dep.as_ref();
            // A dep that names the verify target itself is not scoped out.
            if dep.is_empty()
                || dep == target
                || target.split(',').any(|t| t == dep)
                || STD_HARD_SKIP_CRATES.contains(&dep)
            {
                continue;
            }
            trust_levels.push(TrustAssumption {
                path: dep.to_string(),
                level: TrustAssumptionLevel::Conditional,
                reason: "dependency was scoped out of verification (no obligations produced); \
                         proof is conditional on its correctness"
                    .to_string(),
            });
        }

        Self { trust_levels, ..Self::default() }
    }

    /// Trust (dep-TCB ledger, Stage 0): render the trust-level assumption rows
    /// as human-readable ledger lines, sorted for stable output (deterministic
    /// across runs). Returns an empty vec when there are no trust-level
    /// assumptions. The lines are plain strings so a renderer (e.g.
    /// `trust-report`) can append them without taking a dependency on this
    /// crate's types.
    #[must_use]
    pub fn render_tcb_ledger(&self) -> Vec<String> {
        let mut rows: Vec<String> = self
            .trust_levels
            .iter()
            .map(|a| format!("{:<12} {}  ({})", a.level.label(), a.path, a.reason))
            .collect();
        rows.sort();
        rows
    }
}

/// A trust assumption about an external dependency or function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustAssumption {
    /// Path of the trusted item (e.g., "std::vec::Vec::push").
    pub path: String,
    /// What level of trust is assumed.
    pub level: TrustAssumptionLevel,
    /// Why this assumption is made.
    pub reason: String,
}

/// Level of trust assumed for an external item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustAssumptionLevel {
    /// Fully verified by Trust (has its own ProofBundle).
    Verified,
    /// Assumed correct based on Rust's type system guarantees.
    TypeSafe,
    /// Assumed correct without verification (e.g., FFI, unsafe).
    Trusted,
    /// Known to be unverified; proof is conditional on this item's correctness.
    Conditional,
}

impl TrustAssumptionLevel {
    /// Stable, human-readable label for the dep-TCB ledger.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            Self::Verified => "Verified",
            Self::TypeSafe => "TypeSafe",
            Self::Trusted => "Trusted",
            Self::Conditional => "Conditional",
        }
    }
}

/// Panic strategy affects verification semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PanicStrategy {
    /// panic = "abort" — unwinding is not modeled.
    #[default]
    Abort,
    /// panic = "unwind" — unwinding paths must be verified.
    Unwind,
}

impl fmt::Display for PanicStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Abort => write!(f, "abort"),
            Self::Unwind => write!(f, "unwind"),
        }
    }
}

/// A codegen option that may affect soundness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodegenOption {
    /// Option name (e.g., "opt-level", "overflow-checks").
    pub name: String,
    /// Option value.
    pub value: String,
}

/// Version of a solver used in verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverVersion {
    /// Solver name (e.g., "ay", "trust-wp", "clean").
    pub name: String,
    /// Version string.
    pub version: String,
}

// ---------------------------------------------------------------------------
// EnvironmentFingerprint
// ---------------------------------------------------------------------------

/// Captures the build/verification environment at proof time.
///
/// Two proofs generated in different environments may not be equivalent even
/// if the source is identical, because codegen, optimization, and platform
/// differences can affect semantics.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct EnvironmentFingerprint {
    /// Trust compiler version.
    pub trust_version: String,
    /// Rust toolchain version (e.g., "nightly-2026-04-15").
    pub rust_toolchain: String,
    /// Target triple (e.g., "aarch64-apple-darwin").
    pub target_triple: String,
    /// Platform description (e.g., "Darwin 25.4.0").
    pub platform: String,
    /// Solver timeout in milliseconds (0 = no timeout).
    pub solver_timeout_ms: u64,
    /// Whether path remapping was applied (affects debug info, not semantics).
    pub path_remap: bool,
    /// Deterministic seed for reproducible verification.
    pub deterministic_seed: Option<u64>,
    /// Linker identifier (affects binary layout).
    pub linker_id: String,
    /// Optimization level.
    pub opt_level: String,
}

// ---------------------------------------------------------------------------
// ProvenArtifact
// ---------------------------------------------------------------------------

/// A content-addressed artifact with optional inline bytes.
///
/// Artifacts are identified by their SHA-256 hash. The actual bytes may be
/// stored inline (for small artifacts) or referenced externally.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenArtifact {
    /// SHA-256 hash of the artifact content.
    pub artifact_hash: [u8; 32],
    /// Human-readable description of the artifact.
    pub description: String,
    /// MIME type or format identifier (e.g., "application/x-elf", "text/x-rust").
    pub format: String,
    /// Inline artifact bytes (None if stored externally).
    #[serde(default, skip_serializing_if = "Option::is_none", with = "optional_bytes_as_base64")]
    pub inline_bytes: Option<Vec<u8>>,
    /// Size of the artifact in bytes.
    pub size_bytes: u64,
}

impl ProvenArtifact {
    /// Create a new artifact from raw bytes.
    #[must_use]
    pub fn from_bytes(bytes: &[u8], description: &str, format: &str) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        let hash: [u8; 32] = hasher.finalize().into();
        Self {
            artifact_hash: hash,
            description: description.to_string(),
            format: format.to_string(),
            inline_bytes: Some(bytes.to_vec()),
            size_bytes: bytes.len() as u64,
        }
    }

    /// Create an artifact reference without inline bytes.
    #[must_use]
    pub fn reference_only(hash: [u8; 32], size: u64, description: &str, format: &str) -> Self {
        Self {
            artifact_hash: hash,
            description: description.to_string(),
            format: format.to_string(),
            inline_bytes: None,
            size_bytes: size,
        }
    }

    /// Check inline bytes against the recorded hash and size.
    ///
    /// `Ok(None)` means bytes are not carried, so integrity is unavailable; it
    /// must not be treated as success.
    pub fn check_inline_integrity(&self) -> Result<Option<bool>, CertError> {
        match &self.inline_bytes {
            Some(bytes) => {
                let mut hasher = Sha256::new();
                hasher.update(bytes);
                let computed: [u8; 32] = hasher.finalize().into();
                Ok(Some(computed == self.artifact_hash && bytes.len() as u64 == self.size_bytes))
            }
            None => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// DependencyRef
// ---------------------------------------------------------------------------

/// Reference to another proof bundle (cross-crate composition).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DependencyRef {
    /// Crate name of the dependency.
    pub crate_name: String,
    /// Crate version.
    pub crate_version: String,
    /// SHA-256 hash of the dependency's proof bundle.
    pub bundle_hash: [u8; 32],
    /// Assurance category reported by the dependency record. Not locally replayed.
    pub reported_assurance: ReportedAssurance,
    /// Functions from the dependency that this bundle relies on.
    pub relied_functions: Vec<String>,
}

// ---------------------------------------------------------------------------
// Certificate wrappers
// ---------------------------------------------------------------------------

/// A carried, re-checkable kernel proof term — the de Bruijn "Certified"
/// payload on the cold packaging path. Mirrors
/// `trust_ir::ProofEvidence::CleanCic` but is `Eq` (so `FunctionCertificate`
/// keeps its derive) and is *always* a kernel term, never some other evidence
/// kind. `term`/`context` are meant to be RE-CHECKED by a CIC kernel (via
/// `trust_certify::recheck_cleancic`), not trusted; `lineage` binds the payload
/// to the obligation it certifies.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CarriedCleanCic {
    /// Serialized CIC proof term (re-checked by the consumer, not trusted).
    pub term: Vec<u8>,
    /// Serialized kernel context the term type-checks against.
    pub context: Vec<u8>,
    /// Lineage digest binding term+context to the certified obligation, so the
    /// cert cannot be replayed onto a different obligation.
    pub lineage: trust_ir::ProofDigest,
}

/// Wraps an existing ProofCertificate for MIR-level verification.
///
/// This provides backward compatibility with the existing certificate format
/// while fitting into the new ProofBundle structure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionCertificate {
    /// The existing MIR-level proof certificate.
    pub mir_cert: ProofCertificate,
    /// The certificate chain for this function.
    pub chain: CertificateChain,
    /// Non-authoritative assurance category derived from record metadata.
    pub reported_assurance: ReportedAssurance,
    /// Function def_path.
    pub function_path: String,
    /// Kernel-checkable CleanCic proof terms carried for offline re-check
    /// (M-Pkg). Empty unless the obligation reached the `Certified` tier and
    /// `certify_vc` produced a term. Carrying the term is the difference between
    /// a `Certified` LABEL and a `Certified` label backed by a re-checkable
    /// proof — so the label never out-runs the proof.
    #[serde(default)]
    pub clean_cic: Vec<CarriedCleanCic>,
}

impl FunctionCertificate {
    /// Create from an existing ProofCertificate and chain.
    #[must_use]
    pub fn from_existing(cert: ProofCertificate, chain: CertificateChain) -> Self {
        let reported_assurance = ReportedAssurance::from_certificate_record(&cert);
        let function_path = cert.function.clone();
        Self { mir_cert: cert, chain, reported_assurance, function_path, clean_cic: Vec::new() }
    }

    /// Check internal consistency of the public function record.
    ///
    /// This validates identity, VC hash, chain structure, proof-step shape, and
    /// signature/status consistency. It does not replay proof semantics.
    #[must_use]
    pub fn record_integrity_valid(&self) -> bool {
        let signature_consistent = match self.mir_cert.status {
            crate::CertificationStatus::Certified => {
                self.mir_cert.signature.as_ref().is_some_and(|signature| {
                    matches!(
                        signature.trust_level,
                        crate::TrustLevel::Certifier | crate::TrustLevel::Root
                    ) && crate::check_certificate_signature_integrity(&self.mir_cert).is_ok()
                })
            }
            crate::CertificationStatus::Trusted => {
                self.mir_cert.signature.as_ref().is_none_or(|_| {
                    crate::check_certificate_signature_integrity(&self.mir_cert).is_ok()
                })
            }
        };

        self.function_path == self.mir_cert.function
            && self.mir_cert.version == crate::CERT_FORMAT_VERSION
            && self.mir_cert.id
                == crate::CertificateId::generate(&self.mir_cert.function, &self.mir_cert.timestamp)
            && self.mir_cert.verify_vc_hash()
            && self.mir_cert.check_proof_step_shape().is_ok()
            && crate::ChainValidator::validate(&self.chain).valid
            && signature_consistent
    }

    /// Attach kernel-checkable CleanCic proof terms to this certificate. Only
    /// `ProofEvidence::CleanCic` variants are carried (the only re-checkable
    /// kind); any other evidence is dropped, since the cold packaging path
    /// carries kernel terms, not labels. Does NOT change the assurance tier —
    /// carrying a term is available evidence, not an automatic upgrade. Only a
    /// separate API that actually rechecks the exact term/context/lineage may
    /// produce an authoritative result.
    #[must_use]
    pub fn with_clean_cic(mut self, evidence: Vec<trust_ir::ProofEvidence>) -> Self {
        self.clean_cic = evidence
            .into_iter()
            .filter_map(|ev| match ev {
                // kernel_recheck: trust-ir's CleanCic re-check evidence (added with the CleanCic
                // re-checker); bound-and-ignored here — carrying it into CarriedCleanCic is a follow-up.
                trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck: _ } => {
                    Some(CarriedCleanCic { term, context, lineage })
                }
                _ => None,
            })
            .collect();
        self
    }
}

/// Public translation-validation result record (MIR -> LLVM IR).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransvalCertificate {
    /// Hash of the MIR input.
    pub mir_hash: [u8; 32],
    /// Hash of the LLVM IR output.
    pub llvm_hash: [u8; 32],
    /// Solver reported by the producer.
    pub solver: String,
    /// Time spent verifying in milliseconds.
    pub time_ms: u64,
    /// Timestamp of verification.
    pub timestamp: String,
}

/// Public codegen-check result record (LLVM IR -> machine code).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodegenCertificate {
    /// Hash of the LLVM IR input.
    pub llvm_hash: [u8; 32],
    /// Hash of the machine code output.
    pub machine_hash: [u8; 32],
    /// Check method reported by the producer.
    pub method: String,
    /// Time spent verifying in milliseconds.
    pub time_ms: u64,
    /// Timestamp of verification.
    pub timestamp: String,
}

/// Public self-check claim about the Trust compiler itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SelfCertLevel {
    /// Producer claims an external tool checked the compiler.
    ExternalCheckClaim,
    /// Producer claims a bootstrapped self-check.
    BootstrapCheckClaim,
    /// No self-check claim is carried.
    None,
}

/// Public self-check record for the compiler.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SelfCertificate {
    /// Reported self-check category.
    pub level: SelfCertLevel,
    /// Hash of the compiler binary named by the record.
    pub compiler_hash: [u8; 32],
    /// Producer description of the self-check process.
    pub description: String,
    /// Timestamp.
    pub timestamp: String,
}

// ---------------------------------------------------------------------------
// RecordInventory
// ---------------------------------------------------------------------------

/// Inventory of public function records and their internal consistency.
///
/// Counts are derived from `function_certs` by bundle constructors; callers
/// cannot use a builder setter to manufacture them. They do not report semantic
/// semantic proof coverage.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct RecordInventory {
    /// Number of function certificate records carried by the bundle.
    pub function_records: usize,
    /// Number of records that passed internal consistency checks.
    pub integrity_valid_function_records: usize,
    /// Paths of internally consistent records.
    pub integrity_valid_functions: Vec<String>,
    /// Paths of records that failed one or more consistency checks.
    pub integrity_invalid_functions: Vec<String>,
}

impl RecordInventory {
    /// Internally consistent record percentage (0.0 to 100.0).
    #[must_use]
    pub fn integrity_valid_percent(&self) -> f64 {
        if self.function_records == 0 {
            0.0
        } else {
            (self.integrity_valid_function_records as f64 / self.function_records as f64) * 100.0
        }
    }
}

// ---------------------------------------------------------------------------
// ProofBundle
// ---------------------------------------------------------------------------

/// Current proof bundle format version.
pub const PROOF_BUNDLE_VERSION: u32 = 2;

/// A complete proof bundle packaging all verification artifacts.
///
/// This is the top-level structure for Trust's Universal Proof Certificate Format.
/// It contains function certificates, environment fingerprint, assumptions,
/// record inventory and internal-consistency metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofBundle {
    /// Format version.
    pub version: u32,
    /// Crate name.
    pub crate_name: String,
    /// Crate version.
    pub crate_version: String,
    /// When this bundle was created (ISO 8601).
    pub created_at: String,
    /// Weakest assurance category reported by the carried records.
    /// This is never a replay verdict.
    reported_assurance: ReportedAssurance,
    /// Function-level certificates.
    function_certs: Vec<FunctionCertificate>,
    /// Public translation-check records (MIR -> LLVM).
    pub transval_records: Vec<TransvalCertificate>,
    /// Public codegen-check records (LLVM -> machine code).
    pub codegen_records: Vec<CodegenCertificate>,
    /// Public compiler self-check record, if carried.
    pub self_check_record: Option<SelfCertificate>,
    /// Assumptions under which verification was performed.
    pub assumptions: AssumptionSet,
    /// Environment fingerprint at verification time.
    pub environment: EnvironmentFingerprint,
    /// Dependency records with producer-reported assurance metadata.
    pub dependencies: Vec<DependencyRef>,
    /// Derived public-record inventory.
    record_inventory: RecordInventory,
    /// Content-addressed artifact records (e.g., a compiled binary claim).
    pub artifacts: Vec<ProvenArtifact>,
    /// SHA-256 digest of canonical bundle content (internal consistency only).
    bundle_digest: [u8; 32],
}

impl ProofBundle {
    /// Create a new proof bundle builder.
    #[must_use = "builder must be consumed via .build() to produce a ProofBundle"]
    pub fn builder(crate_name: &str, crate_version: &str) -> ProofBundleBuilder {
        ProofBundleBuilder {
            crate_name: crate_name.to_string(),
            crate_version: crate_version.to_string(),
            function_certs: Vec::new(),
            transval_records: Vec::new(),
            codegen_records: Vec::new(),
            self_check_record: None,
            assumptions: AssumptionSet::default(),
            environment: EnvironmentFingerprint::default(),
            dependencies: Vec::new(),
            artifacts: Vec::new(),
            timestamp: current_timestamp(),
        }
    }

    /// Create a bundle from existing ProofCertificates (backward compatibility).
    ///
    /// Wraps each `(ProofCertificate, CertificateChain)` pair in a
    /// `FunctionCertificate` and computes the overall assurance tier.
    #[must_use]
    pub fn from_existing_certs(
        crate_name: &str,
        crate_version: &str,
        certs: Vec<(ProofCertificate, CertificateChain)>,
    ) -> Result<Self, CertError> {
        let mut function_certs: Vec<FunctionCertificate> = certs
            .into_iter()
            .map(|(cert, chain)| FunctionCertificate::from_existing(cert, chain))
            .collect();
        canonicalize_function_records(&mut function_certs);
        ensure_function_record_integrity(&function_certs)?;
        let reported_assurance = compute_weakest_reported_assurance(&function_certs);
        let record_inventory = compute_record_inventory(&function_certs);

        let timestamp = current_timestamp();

        let mut bundle = Self {
            version: PROOF_BUNDLE_VERSION,
            crate_name: crate_name.to_string(),
            crate_version: crate_version.to_string(),
            created_at: timestamp,
            reported_assurance,
            function_certs,
            transval_records: Vec::new(),
            codegen_records: Vec::new(),
            self_check_record: None,
            assumptions: AssumptionSet::default(),
            environment: EnvironmentFingerprint::default(),
            dependencies: Vec::new(),
            record_inventory,
            artifacts: Vec::new(),
            bundle_digest: [0u8; 32], // computed below
        };

        // Safe to use expect here: only fails on serialization of the bundle's own fields,
        // which are all known-good constructed above.
        bundle.bundle_digest =
            bundle.compute_hash().expect("invariant: bundle fields are serializable");
        Ok(bundle)
    }

    /// Check bundle internal consistency by recomputing its self-digest.
    ///
    /// This is not authenticity: a constructor can recompute a digest over
    /// arbitrary claims.
    pub fn check_internal_consistency(&self) -> Result<bool, CertError> {
        let computed = self.compute_hash()?;
        Ok(computed == self.bundle_digest
            && self.version == PROOF_BUNDLE_VERSION
            && self.reported_assurance == compute_weakest_reported_assurance(&self.function_certs)
            && self.record_inventory == compute_record_inventory(&self.function_certs)
            && self.function_certs.iter().all(FunctionCertificate::record_integrity_valid))
    }

    /// Carried function certificate records.
    #[must_use]
    pub fn function_records(&self) -> &[FunctionCertificate] {
        &self.function_certs
    }

    /// Weakest reported assurance category. Never a proof verdict.
    #[must_use]
    pub fn reported_assurance(&self) -> ReportedAssurance {
        self.reported_assurance
    }

    /// Derived record inventory.
    #[must_use]
    pub fn record_inventory(&self) -> &RecordInventory {
        &self.record_inventory
    }

    /// Bundle self-digest (not a signature).
    #[must_use]
    pub fn bundle_digest(&self) -> [u8; 32] {
        self.bundle_digest
    }

    /// Check carried artifact bytes. `None` entries are unresolved references.
    pub fn check_artifact_records(&self) -> Result<Vec<Option<bool>>, CertError> {
        self.artifacts.iter().map(ProvenArtifact::check_inline_integrity).collect()
    }

    /// Compute the SHA-256 self-digest of canonical bundle content.
    ///
    /// The digest covers everything except the `bundle_digest` field itself.
    fn compute_hash(&self) -> Result<[u8; 32], CertError> {
        let mut hasher = Sha256::new();

        // Version and identity
        hasher.update(self.version.to_le_bytes());
        hasher.update(self.crate_name.as_bytes());
        hasher.update(b"|");
        hasher.update(self.crate_version.as_bytes());
        hasher.update(b"|");
        hasher.update(self.created_at.as_bytes());
        hasher.update(b"|");
        hasher.update(format!("{:?}", self.reported_assurance).as_bytes());
        hasher.update(b"|");

        // Function certificates (serialized)
        let fc_json = serde_json::to_string(&self.function_certs)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(fc_json.as_bytes());
        hasher.update(b"|");

        // Transval certificates
        let tv_json = serde_json::to_string(&self.transval_records)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(tv_json.as_bytes());
        hasher.update(b"|");

        // Codegen certificates
        let cg_json = serde_json::to_string(&self.codegen_records)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(cg_json.as_bytes());
        hasher.update(b"|");

        // Self cert
        let sc_json = serde_json::to_string(&self.self_check_record)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(sc_json.as_bytes());
        hasher.update(b"|");

        // Assumptions
        let as_json = serde_json::to_string(&self.assumptions)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(as_json.as_bytes());
        hasher.update(b"|");

        // Environment
        let env_json = serde_json::to_string(&self.environment)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(env_json.as_bytes());
        hasher.update(b"|");

        // Dependencies
        let dep_json = serde_json::to_string(&self.dependencies)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(dep_json.as_bytes());
        hasher.update(b"|");

        // Coverage
        let cov_json = serde_json::to_string(&self.record_inventory)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(cov_json.as_bytes());
        hasher.update(b"|");

        // Artifact records, including descriptive metadata and inline bytes.
        let artifact_json = serde_json::to_string(&self.artifacts)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(artifact_json.as_bytes());

        Ok(hasher.finalize().into())
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        let bundle: Self = serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        if !bundle.check_internal_consistency()? {
            return Err(CertError::InvalidCertificate {
                reason: "bundle record failed version, digest, derived-field, or record-integrity checks"
                    .to_string(),
            });
        }
        if bundle
            .artifacts
            .iter()
            .any(|artifact| matches!(artifact.check_inline_integrity(), Ok(Some(false)) | Err(_)))
        {
            return Err(CertError::InvalidCertificate {
                reason: "bundle contains an inline artifact with invalid record integrity"
                    .to_string(),
            });
        }
        Ok(bundle)
    }
}

impl fmt::Display for ProofBundle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ProofBundle: {} v{}", self.crate_name, self.crate_version)?;
        writeln!(f, "  Created: {}", self.created_at)?;
        writeln!(f, "  Reported assurance: {}", self.reported_assurance)?;
        writeln!(f, "  Proof authority: unavailable (records not replayed)")?;
        writeln!(
            f,
            "  Function records: {}/{} internally consistent ({:.1}%)",
            self.record_inventory.integrity_valid_function_records,
            self.record_inventory.function_records,
            self.record_inventory.integrity_valid_percent()
        )?;
        writeln!(f, "  Dependencies: {}", self.dependencies.len())?;
        writeln!(f, "  Artifacts: {}", self.artifacts.len())?;

        if !self.assumptions.axioms.is_empty() {
            writeln!(f, "  Axioms: {}", self.assumptions.axioms.len())?;
        }
        if !self.assumptions.unverified_paths.is_empty() {
            writeln!(f, "  Unverified paths: {}", self.assumptions.unverified_paths.len())?;
        }

        writeln!(f, "  Environment:")?;
        if !self.environment.trust_version.is_empty() {
            writeln!(f, "    Trust: {}", self.environment.trust_version)?;
        }
        if !self.environment.rust_toolchain.is_empty() {
            writeln!(f, "    Toolchain: {}", self.environment.rust_toolchain)?;
        }
        if !self.environment.target_triple.is_empty() {
            writeln!(f, "    Target: {}", self.environment.target_triple)?;
        }

        let digest_hex: String = self.bundle_digest.iter().map(|b| format!("{b:02x}")).collect();
        writeln!(f, "  Internal digest: {}", &digest_hex[..16])?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Builder for constructing a ProofBundle incrementally.
#[must_use]
pub struct ProofBundleBuilder {
    crate_name: String,
    crate_version: String,
    function_certs: Vec<FunctionCertificate>,
    transval_records: Vec<TransvalCertificate>,
    codegen_records: Vec<CodegenCertificate>,
    self_check_record: Option<SelfCertificate>,
    assumptions: AssumptionSet,
    environment: EnvironmentFingerprint,
    dependencies: Vec<DependencyRef>,
    artifacts: Vec<ProvenArtifact>,
    timestamp: String,
}

impl ProofBundleBuilder {
    /// Add a function certificate.
    pub fn add_function_cert(&mut self, cert: FunctionCertificate) -> &mut Self {
        self.function_certs.push(cert);
        self
    }

    /// Add an existing ProofCertificate with its chain.
    pub fn add_existing_cert(
        &mut self,
        cert: ProofCertificate,
        chain: CertificateChain,
    ) -> &mut Self {
        self.function_certs.push(FunctionCertificate::from_existing(cert, chain));
        self
    }

    /// Add a public translation-check record.
    pub fn add_transval_record(&mut self, record: TransvalCertificate) -> &mut Self {
        self.transval_records.push(record);
        self
    }

    /// Add a public codegen-check record.
    pub fn add_codegen_record(&mut self, record: CodegenCertificate) -> &mut Self {
        self.codegen_records.push(record);
        self
    }

    /// Set a public compiler self-check record.
    pub fn set_self_check_record(&mut self, record: SelfCertificate) -> &mut Self {
        self.self_check_record = Some(record);
        self
    }

    /// Set the assumptions.
    pub fn set_assumptions(&mut self, assumptions: AssumptionSet) -> &mut Self {
        self.assumptions = assumptions;
        self
    }

    /// Set the environment fingerprint.
    pub fn set_environment(&mut self, env: EnvironmentFingerprint) -> &mut Self {
        self.environment = env;
        self
    }

    /// Add a dependency reference.
    pub fn add_dependency(&mut self, dep: DependencyRef) -> &mut Self {
        self.dependencies.push(dep);
        self
    }

    /// Add a content-addressed artifact record.
    pub fn add_artifact(&mut self, artifact: ProvenArtifact) -> &mut Self {
        self.artifacts.push(artifact);
        self
    }

    /// Set the timestamp.
    pub fn set_timestamp(&mut self, timestamp: &str) -> &mut Self {
        self.timestamp = timestamp.to_string();
        self
    }

    /// Build the ProofBundle, computing the integrity hash.
    pub fn build(mut self) -> Result<ProofBundle, CertError> {
        canonicalize_function_records(&mut self.function_certs);
        ensure_function_record_integrity(&self.function_certs)?;
        ensure_inline_artifact_integrity(&self.artifacts)?;
        let reported_assurance = compute_weakest_reported_assurance(&self.function_certs);
        let record_inventory = compute_record_inventory(&self.function_certs);

        let mut bundle = ProofBundle {
            version: PROOF_BUNDLE_VERSION,
            crate_name: self.crate_name,
            crate_version: self.crate_version,
            created_at: self.timestamp,
            reported_assurance,
            function_certs: self.function_certs,
            transval_records: self.transval_records,
            codegen_records: self.codegen_records,
            self_check_record: self.self_check_record,
            assumptions: self.assumptions,
            environment: self.environment,
            dependencies: self.dependencies,
            record_inventory,
            artifacts: self.artifacts,
            bundle_digest: [0u8; 32],
        };

        bundle.bundle_digest = bundle.compute_hash()?;
        Ok(bundle)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn canonicalize_function_records(records: &mut [FunctionCertificate]) {
    for record in records {
        record.reported_assurance = ReportedAssurance::from_certificate_record(&record.mir_cert);
    }
}

fn ensure_function_record_integrity(records: &[FunctionCertificate]) -> Result<(), CertError> {
    let mut paths = BTreeSet::new();
    for record in records {
        if !paths.insert(record.function_path.as_str()) {
            return Err(CertError::InvalidCertificate {
                reason: format!("duplicate function certificate record: {}", record.function_path),
            });
        }
        if !record.record_integrity_valid() {
            return Err(CertError::InvalidCertificate {
                reason: format!(
                    "function certificate record failed internal integrity checks: {}",
                    record.function_path
                ),
            });
        }
    }
    Ok(())
}

fn ensure_inline_artifact_integrity(artifacts: &[ProvenArtifact]) -> Result<(), CertError> {
    for artifact in artifacts {
        if matches!(artifact.check_inline_integrity()?, Some(false)) {
            return Err(CertError::InvalidCertificate {
                reason: format!(
                    "inline artifact record failed hash/size integrity: {}",
                    artifact.description
                ),
            });
        }
    }
    Ok(())
}

fn compute_record_inventory(records: &[FunctionCertificate]) -> RecordInventory {
    let mut integrity_valid_functions = Vec::new();
    let mut integrity_invalid_functions = Vec::new();
    for record in records {
        if record.record_integrity_valid() {
            integrity_valid_functions.push(record.function_path.clone());
        } else {
            integrity_invalid_functions.push(record.function_path.clone());
        }
    }
    RecordInventory {
        function_records: records.len(),
        integrity_valid_function_records: integrity_valid_functions.len(),
        integrity_valid_functions,
        integrity_invalid_functions,
    }
}

/// Compute the weakest category reported across all function records.
/// Returns `Unclassified` if there are no records.
fn compute_weakest_reported_assurance(certs: &[FunctionCertificate]) -> ReportedAssurance {
    certs
        .iter()
        .map(|record| record.reported_assurance)
        // Strongest-to-weakest declaration order means max() is weakest.
        .max()
        .unwrap_or(ReportedAssurance::Unclassified)
}

/// Get the current UTC timestamp.
fn current_timestamp() -> String {
    let dur =
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    format!("{}Z", dur.as_secs())
}

// ---------------------------------------------------------------------------
// Serde helper for Option<Vec<u8>> as base64
// ---------------------------------------------------------------------------

mod optional_bytes_as_base64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub(crate) fn serialize<S>(data: &Option<Vec<u8>>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match data {
            Some(bytes) => {
                // Encode bytes as hex string for JSON compatibility without
                // adding a base64 dependency.
                let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
                hex.serialize(serializer)
            }
            None => serializer.serialize_none(),
        }
    }

    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<Option<Vec<u8>>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let opt: Option<String> = Option::deserialize(deserializer)?;
        match opt {
            Some(hex) => {
                let bytes: Result<Vec<u8>, _> = (0..hex.len())
                    .step_by(2)
                    .map(|i| {
                        u8::from_str_radix(&hex[i..i + 2], 16).map_err(serde::de::Error::custom)
                    })
                    .collect();
                Ok(Some(bytes?))
            }
            None => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofCertificate, SolverInfo,
        VcSnapshot,
    };

    fn make_cert(function: &str, certified: bool) -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: format!("{function}-vc"),
            location: None,
        };
        let solver = SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let mut cert = ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            vc_snapshot,
            solver,
            vec![1, 2, 3],
            "2026-04-15T00:00:00Z".to_string(),
        );
        if certified {
            // This creates a cryptographically consistent signed certification
            // CLAIM. It is not kernel replay authority.
            let key = crate::CertSigningKey::generate(crate::TrustLevel::Certifier);
            cert.upgrade_to_certified(&key).expect("test cert certifier upgrade");
        }
        cert
    }

    #[test]
    fn forged_unsigned_certified_is_not_a_signed_certification_claim() {
        let mut forged = make_cert("forged", false);
        forged.status = crate::CertificationStatus::Certified; // no signature
        assert_ne!(
            ReportedAssurance::from_certificate_record(&forged),
            ReportedAssurance::SignedCertificationClaim,
            "unsigned/forged Certified must not yield a signed claim"
        );
        let signed = make_cert("signed", true);
        assert_eq!(
            ReportedAssurance::from_certificate_record(&signed),
            ReportedAssurance::SignedCertificationClaim
        );
    }

    #[test]
    fn self_signed_certified_is_only_a_reported_claim() {
        let vc = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "rogue-vc".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let mut cert = ProofCertificate::new_trusted(
            "attacker".to_string(),
            FunctionHash::from_bytes(b"attacker-body"),
            vc,
            solver,
            vec![1, 2, 3],
            "2026-04-15T00:00:00Z".to_string(),
        );
        let rogue = crate::CertSigningKey::generate(crate::TrustLevel::Certifier);
        cert.upgrade_to_certified(&rogue).expect("self-sign");
        // Deliberately do NOT register `rogue` as a trust anchor.
        assert!(
            crate::check_certificate_signature_integrity(&cert).is_ok(),
            "the self-signature verifies against the embedded key"
        );
        assert_eq!(
            ReportedAssurance::from_certificate_record(&cert),
            ReportedAssurance::SignedCertificationClaim,
            "classification records the signed claim but grants no authority"
        );
    }

    fn make_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir".to_string(),
            output_hash: "vc".to_string(),
            time_ms: 1,
            timestamp: "2026-04-15T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc".to_string(),
            output_hash: "proof".to_string(),
            time_ms: 10,
            timestamp: "2026-04-15T00:00:01Z".to_string(),
        });
        chain
    }

    fn make_environment() -> EnvironmentFingerprint {
        EnvironmentFingerprint {
            trust_version: "0.1.0".to_string(),
            rust_toolchain: "nightly-2026-04-15".to_string(),
            target_triple: "aarch64-apple-darwin".to_string(),
            platform: "Darwin 25.4.0".to_string(),
            solver_timeout_ms: 30000,
            path_remap: false,
            deterministic_seed: Some(42),
            linker_id: "ld-prime".to_string(),
            opt_level: "2".to_string(),
        }
    }

    fn make_assumptions() -> AssumptionSet {
        AssumptionSet {
            trust_levels: vec![TrustAssumption {
                path: "std::vec::Vec::push".to_string(),
                level: TrustAssumptionLevel::TypeSafe,
                reason: "stdlib type safety".to_string(),
            }],
            axioms: vec!["integer overflow wraps".to_string()],
            unverified_paths: vec!["crate::ffi::extern_call".to_string()],
            panic_strategy: PanicStrategy::Abort,
            codegen_options: vec![CodegenOption {
                name: "overflow-checks".to_string(),
                value: "true".to_string(),
            }],
            solver_versions: vec![SolverVersion {
                name: "ay".to_string(),
                version: "1.0.0".to_string(),
            }],
        }
    }

    // -----------------------------------------------------------------------
    // ReportedAssurance
    // -----------------------------------------------------------------------

    #[test]
    fn test_reported_assurance_ordering() {
        assert!(
            ReportedAssurance::SignedCertificationClaim < ReportedAssurance::ReportedSoundnessClaim
        );
        assert!(ReportedAssurance::ReportedSoundnessClaim < ReportedAssurance::BoundedResultClaim);
        assert!(ReportedAssurance::BoundedResultClaim < ReportedAssurance::Unclassified);
    }

    #[test]
    fn test_reported_assurance_from_signed_certification_record() {
        let cert = make_cert("crate::foo", true);
        assert_eq!(
            ReportedAssurance::from_certificate_record(&cert),
            ReportedAssurance::SignedCertificationClaim
        );
    }

    #[test]
    fn test_assurance_tier_from_smt_cert() {
        let cert = make_cert("crate::foo", false);
        assert_eq!(
            ReportedAssurance::from_certificate_record(&cert),
            ReportedAssurance::ReportedSoundnessClaim
        );
    }

    #[test]
    fn test_assurance_tier_from_bounded_cert() {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "vc-data".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "trust-mc".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 100,
            strength: ProofStrength::bounded(10),
            evidence: None,
        };
        let cert = ProofCertificate::new_trusted(
            "crate::bounded".to_string(),
            FunctionHash::from_bytes(b"bounded-body"),
            vc_snapshot,
            solver,
            vec![],
            "2026-04-15T00:00:00Z".to_string(),
        );
        assert_eq!(
            ReportedAssurance::from_certificate_record(&cert),
            ReportedAssurance::BoundedResultClaim
        );
    }

    #[test]
    fn test_reported_assurance_display_is_non_authoritative() {
        assert!(
            format!("{}", ReportedAssurance::SignedCertificationClaim).contains("not replayed")
        );
        assert!(format!("{}", ReportedAssurance::ReportedSoundnessClaim).contains("claim"));
    }

    // -----------------------------------------------------------------------
    // ProvenArtifact
    // -----------------------------------------------------------------------

    #[test]
    fn test_artifact_from_bytes_and_verify() {
        let data = b"fn main() { println!(\"hello\"); }";
        let artifact = ProvenArtifact::from_bytes(data, "main.rs source", "text/x-rust");

        assert_eq!(artifact.size_bytes, data.len() as u64);
        assert!(artifact.inline_bytes.is_some());
        assert_eq!(artifact.check_inline_integrity().unwrap(), Some(true));
    }

    #[test]
    fn test_artifact_reference_only() {
        let hash = [0xABu8; 32];
        let artifact = ProvenArtifact::reference_only(hash, 1024, "binary", "application/x-elf");

        assert!(artifact.inline_bytes.is_none());
        assert_eq!(artifact.size_bytes, 1024);
        assert_eq!(
            artifact.check_inline_integrity().unwrap(),
            None,
            "external bytes are unresolved, never implicitly valid"
        );
    }

    #[test]
    fn test_artifact_tampered_fails_integrity() {
        let data = b"original content";
        let mut artifact = ProvenArtifact::from_bytes(data, "test", "text/plain");

        // Tamper with the inline bytes
        if let Some(ref mut bytes) = artifact.inline_bytes {
            bytes[0] = 0xFF;
        }

        assert_eq!(artifact.check_inline_integrity().unwrap(), Some(false));
    }

    // -----------------------------------------------------------------------
    // ProofBundle construction and integrity
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bundle_from_existing_certs() {
        let certs = vec![
            (make_cert("crate::foo", false), make_chain()),
            (make_cert("crate::bar", true), make_chain()),
        ];

        let bundle = ProofBundle::from_existing_certs("test-crate", "0.1.0", certs).unwrap();

        assert_eq!(bundle.crate_name, "test-crate");
        assert_eq!(bundle.crate_version, "0.1.0");
        assert_eq!(bundle.function_records().len(), 2);
        assert_eq!(bundle.version, PROOF_BUNDLE_VERSION);
        assert_eq!(bundle.reported_assurance(), ReportedAssurance::ReportedSoundnessClaim);
        assert_eq!(bundle.record_inventory().integrity_valid_function_records, 2);
    }

    #[test]
    fn test_proof_bundle_integrity_valid() {
        let certs = vec![(make_cert("crate::foo", false), make_chain())];
        let bundle = ProofBundle::from_existing_certs("test", "0.1.0", certs).unwrap();

        assert!(bundle.check_internal_consistency().unwrap());
    }

    #[test]
    fn test_proof_bundle_integrity_tampered() {
        let certs = vec![(make_cert("crate::foo", false), make_chain())];
        let mut bundle = ProofBundle::from_existing_certs("test", "0.1.0", certs).unwrap();

        // Tamper with the crate name
        bundle.crate_name = "evil-crate".to_string();

        assert!(!bundle.check_internal_consistency().unwrap());
    }

    // -----------------------------------------------------------------------
    // JSON roundtrip
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bundle_json_roundtrip() {
        let certs = vec![
            (make_cert("crate::foo", false), make_chain()),
            (make_cert("crate::bar", true), make_chain()),
        ];
        let bundle = ProofBundle::from_existing_certs("test-crate", "0.1.0", certs).unwrap();

        let json = bundle.to_json().expect("should serialize");
        let restored = ProofBundle::from_json(&json).expect("should deserialize");

        assert_eq!(restored.crate_name, bundle.crate_name);
        assert_eq!(restored.function_records().len(), bundle.function_records().len());
        assert_eq!(restored.bundle_digest(), bundle.bundle_digest());
        assert!(restored.check_internal_consistency().unwrap());
    }

    #[test]
    fn test_proof_bundle_full_roundtrip_with_all_fields() {
        let mut builder = ProofBundle::builder("full-crate", "1.2.3");
        builder
            .add_existing_cert(make_cert("crate::alpha", true), make_chain())
            .add_existing_cert(make_cert("crate::beta", false), make_chain())
            .set_assumptions(make_assumptions())
            .set_environment(make_environment())
            .add_dependency(DependencyRef {
                crate_name: "dep-crate".to_string(),
                crate_version: "0.5.0".to_string(),
                bundle_hash: [0x42; 32],
                reported_assurance: ReportedAssurance::ReportedSoundnessClaim,
                relied_functions: vec!["dep::util::helper".to_string()],
            })
            .add_artifact(ProvenArtifact::from_bytes(
                b"test binary",
                "test artifact",
                "application/octet-stream",
            ))
            .set_timestamp("2026-04-15T12:00:00Z");

        let bundle = builder.build().expect("should build");

        let json = bundle.to_json().expect("should serialize");
        let restored = ProofBundle::from_json(&json).expect("should deserialize");

        // Verify all fields survive roundtrip
        assert_eq!(restored.crate_name, "full-crate");
        assert_eq!(restored.crate_version, "1.2.3");
        assert_eq!(restored.created_at, "2026-04-15T12:00:00Z");
        assert_eq!(restored.function_records().len(), 2);
        assert_eq!(restored.dependencies.len(), 1);
        assert_eq!(restored.dependencies[0].crate_name, "dep-crate");
        assert_eq!(restored.assumptions.axioms, vec!["integer overflow wraps"]);
        assert_eq!(restored.assumptions.panic_strategy, PanicStrategy::Abort);
        assert_eq!(restored.environment.trust_version, "0.1.0");
        assert_eq!(restored.environment.solver_timeout_ms, 30000);
        assert_eq!(restored.environment.deterministic_seed, Some(42));
        assert_eq!(restored.record_inventory().function_records, 2);
        assert_eq!(restored.record_inventory().integrity_valid_function_records, 2);
        assert_eq!(restored.artifacts.len(), 1);
        assert!(restored.check_internal_consistency().unwrap());
        assert_eq!(restored.bundle_digest(), bundle.bundle_digest());
    }

    // -----------------------------------------------------------------------
    // Builder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_builder_empty() {
        let mut builder = ProofBundle::builder("empty", "0.0.0");
        builder.set_timestamp("2026-04-15T00:00:00Z");
        let bundle = builder.build().expect("should build");

        assert!(bundle.function_records().is_empty());
        assert_eq!(bundle.reported_assurance(), ReportedAssurance::Unclassified);
        assert!(bundle.check_internal_consistency().unwrap());
    }

    #[test]
    fn test_builder_incremental() {
        let mut builder = ProofBundle::builder("inc", "0.1.0");
        builder.add_existing_cert(make_cert("crate::a", false), make_chain());
        builder.add_existing_cert(make_cert("crate::b", false), make_chain());
        builder.set_timestamp("2026-04-15T00:00:00Z");

        let bundle = builder.build().expect("should build");

        assert_eq!(bundle.function_records().len(), 2);
        assert_eq!(bundle.reported_assurance(), ReportedAssurance::ReportedSoundnessClaim);
    }

    #[test]
    fn builder_recomputes_caller_forged_reported_assurance() {
        let mut record =
            FunctionCertificate::from_existing(make_cert("crate::a", false), make_chain());
        record.reported_assurance = ReportedAssurance::SignedCertificationClaim;
        let mut builder = ProofBundle::builder("claims", "1");
        builder.add_function_cert(record);

        let bundle = builder.build().unwrap();
        assert_eq!(bundle.reported_assurance(), ReportedAssurance::ReportedSoundnessClaim);
        assert_eq!(
            bundle.function_records()[0].reported_assurance,
            ReportedAssurance::ReportedSoundnessClaim
        );
    }

    #[test]
    fn builder_rejects_invalid_and_duplicate_function_records() {
        let mut invalid =
            FunctionCertificate::from_existing(make_cert("crate::bad", false), make_chain());
        invalid.mir_cert.vc_hash[0] ^= 1;
        let mut invalid_builder = ProofBundle::builder("invalid", "1");
        invalid_builder.add_function_cert(invalid);
        assert!(invalid_builder.build().is_err());

        let mut duplicate_builder = ProofBundle::builder("duplicate", "1");
        duplicate_builder
            .add_existing_cert(make_cert("crate::same", false), make_chain())
            .add_existing_cert(make_cert("crate::same", false), make_chain());
        assert!(duplicate_builder.build().is_err());
    }

    #[test]
    fn deserialization_rejects_forged_derived_fields_even_with_recomputed_digest() {
        let mut bundle = ProofBundle::from_existing_certs(
            "forged",
            "1",
            vec![(make_cert("crate::a", false), make_chain())],
        )
        .unwrap();
        bundle.reported_assurance = ReportedAssurance::SignedCertificationClaim;
        bundle.record_inventory.integrity_valid_function_records = 99;
        bundle.bundle_digest = bundle.compute_hash().unwrap();

        let json = serde_json::to_string(&bundle).unwrap();
        assert!(ProofBundle::from_json(&json).is_err());
    }

    #[test]
    fn builder_rejects_invalid_inline_artifact_size() {
        let mut artifact = ProvenArtifact::from_bytes(b"bytes", "artifact", "application/test");
        artifact.size_bytes += 1;
        let mut builder = ProofBundle::builder("artifact", "1");
        builder.add_artifact(artifact);
        assert!(builder.build().is_err());
    }

    #[test]
    fn caller_supplied_auxiliary_records_do_not_create_assurance() {
        let mut builder = ProofBundle::builder("aux", "1");
        builder
            .add_transval_record(TransvalCertificate {
                mir_hash: [1; 32],
                llvm_hash: [2; 32],
                solver: "caller".to_string(),
                time_ms: 1,
                timestamp: "now".to_string(),
            })
            .add_codegen_record(CodegenCertificate {
                llvm_hash: [2; 32],
                machine_hash: [3; 32],
                method: "caller".to_string(),
                time_ms: 1,
                timestamp: "now".to_string(),
            })
            .set_self_check_record(SelfCertificate {
                level: SelfCertLevel::ExternalCheckClaim,
                compiler_hash: [4; 32],
                description: "caller claim".to_string(),
                timestamp: "now".to_string(),
            });

        let bundle = builder.build().unwrap();
        assert_eq!(bundle.reported_assurance(), ReportedAssurance::Unclassified);
        assert_eq!(bundle.record_inventory().function_records, 0);
        assert!(format!("{bundle}").contains("Proof authority: unavailable"));
    }

    // -----------------------------------------------------------------------
    // RecordInventory
    // -----------------------------------------------------------------------

    #[test]
    fn test_record_inventory_percent_full() {
        let inventory = RecordInventory {
            function_records: 2,
            integrity_valid_function_records: 2,
            integrity_valid_functions: vec!["a".to_string(), "b".to_string()],
            integrity_invalid_functions: Vec::new(),
        };
        assert!((inventory.integrity_valid_percent() - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_record_inventory_percent_partial() {
        let inventory = RecordInventory {
            function_records: 4,
            integrity_valid_function_records: 3,
            integrity_valid_functions: vec!["a".to_string(), "b".to_string(), "c".to_string()],
            integrity_invalid_functions: vec!["d".to_string()],
        };
        assert!((inventory.integrity_valid_percent() - 75.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_record_inventory_percent_empty() {
        let inventory = RecordInventory::default();
        assert!((inventory.integrity_valid_percent() - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Display
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bundle_display() {
        let certs = vec![(make_cert("crate::foo", false), make_chain())];
        let bundle = ProofBundle::from_existing_certs("display-test", "0.1.0", certs).unwrap();

        let output = format!("{bundle}");
        assert!(output.contains("display-test"));
        assert!(output.contains("v0.1.0"));
        assert!(output.contains("reported soundness claim (not replayed)"));
        assert!(output.contains("Proof authority: unavailable"));
        assert!(output.contains("1/1 internally consistent"));
        assert!(!output.contains(" verified"));
        assert!(!output.contains(" proved"));
    }

    // -----------------------------------------------------------------------
    // FunctionCertificate backward compat
    // -----------------------------------------------------------------------

    #[test]
    fn test_function_cert_from_existing() {
        let cert = make_cert("crate::compat", false);
        let chain = make_chain();

        let fc = FunctionCertificate::from_existing(cert.clone(), chain.clone());

        assert_eq!(fc.function_path, "crate::compat");
        assert_eq!(fc.reported_assurance, ReportedAssurance::ReportedSoundnessClaim);
        assert_eq!(fc.mir_cert, cert);
        assert_eq!(fc.chain, chain);
    }

    // -----------------------------------------------------------------------
    // AssumptionSet serde
    // -----------------------------------------------------------------------

    #[test]
    fn test_assumption_set_json_roundtrip() {
        let assumptions = make_assumptions();
        let json = serde_json::to_string_pretty(&assumptions).expect("should serialize");
        let restored: AssumptionSet = serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored, assumptions);
    }

    // -----------------------------------------------------------------------
    // dep-TCB ledger producer (Stage 0)
    // -----------------------------------------------------------------------

    #[test]
    fn test_from_scoped_out_deps_always_emits_std_hard_skip() {
        // Even with no dependency graph, the core/alloc/std hard-skip must
        // appear as explicit rows — it is the dominant silent TCB surface.
        let set = AssumptionSet::from_scoped_out_deps(Some("mycrate"), Vec::<String>::new());
        let paths: Vec<&str> = set.trust_levels.iter().map(|a| a.path.as_str()).collect();
        assert!(paths.contains(&"core"), "core must be an explicit TCB row");
        assert!(paths.contains(&"alloc"), "alloc must be an explicit TCB row");
        assert!(paths.contains(&"std"), "std must be an explicit TCB row");
        // core is Trusted; alloc/std are the heavier Conditional surface.
        let core = set.trust_levels.iter().find(|a| a.path == "core").unwrap();
        assert_eq!(core.level, TrustAssumptionLevel::Trusted);
        let std_row = set.trust_levels.iter().find(|a| a.path == "std").unwrap();
        assert_eq!(std_row.level, TrustAssumptionLevel::Conditional);
    }

    #[test]
    fn test_from_scoped_out_deps_classifies_deps_conservatively() {
        let set = AssumptionSet::from_scoped_out_deps(
            Some("mycrate"),
            ["serde", "mycrate", "core", "rand"],
        );
        // The verify target and std crates are filtered from the dep rows.
        let serde = set.trust_levels.iter().find(|a| a.path == "serde").unwrap();
        // A scoped-out dep is Conditional (unverified premise), never Verified.
        assert_eq!(serde.level, TrustAssumptionLevel::Conditional);
        assert!(
            !set.trust_levels.iter().any(|a| a.path == "mycrate"),
            "the verify target is not a scoped-out dependency"
        );
        // `core` appears exactly once (from the std hard-skip), not duplicated
        // by the dep list.
        assert_eq!(set.trust_levels.iter().filter(|a| a.path == "core").count(), 1);
    }

    #[test]
    fn test_render_tcb_ledger_lines() {
        let set = AssumptionSet::from_scoped_out_deps(None, ["serde"]);
        let lines = set.render_tcb_ledger();
        assert!(lines.iter().any(|l| l.contains("serde") && l.contains("Conditional")));
        assert!(lines.iter().any(|l| l.contains("core") && l.contains("Trusted")));
    }

    // -----------------------------------------------------------------------
    // EnvironmentFingerprint serde
    // -----------------------------------------------------------------------

    #[test]
    fn test_environment_json_roundtrip() {
        let env = make_environment();
        let json = serde_json::to_string_pretty(&env).expect("should serialize");
        let restored: EnvironmentFingerprint =
            serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored, env);
    }

    // -----------------------------------------------------------------------
    // Artifact serde
    // -----------------------------------------------------------------------

    #[test]
    fn test_artifact_json_roundtrip_with_bytes() {
        let artifact = ProvenArtifact::from_bytes(b"hello world", "test", "text/plain");
        let json = serde_json::to_string_pretty(&artifact).expect("should serialize");
        let restored: ProvenArtifact = serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored.artifact_hash, artifact.artifact_hash);
        assert_eq!(restored.inline_bytes, artifact.inline_bytes);
        assert_eq!(restored.check_inline_integrity().unwrap(), Some(true));
    }

    #[test]
    fn test_artifact_json_roundtrip_without_bytes() {
        let artifact =
            ProvenArtifact::reference_only([0xAB; 32], 512, "binary", "application/x-elf");
        let json = serde_json::to_string_pretty(&artifact).expect("should serialize");
        let restored: ProvenArtifact = serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored.artifact_hash, artifact.artifact_hash);
        assert!(restored.inline_bytes.is_none());
    }

    // -----------------------------------------------------------------------
    // Verify all artifacts
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_artifacts_all_valid() {
        let mut builder = ProofBundle::builder("art-test", "0.1.0");
        builder
            .add_artifact(ProvenArtifact::from_bytes(b"a", "a", "text/plain"))
            .add_artifact(ProvenArtifact::from_bytes(b"b", "b", "text/plain"))
            .set_timestamp("2026-04-15T00:00:00Z");

        let bundle = builder.build().expect("should build");
        let results = bundle.check_artifact_records().expect("should inspect");

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|result| *result == Some(true)));
    }

    // -----------------------------------------------------------------------
    // Weakest reported-assurance computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_weakest_reported_assurance_mixed() {
        let certs = vec![
            FunctionCertificate::from_existing(make_cert("a", true), make_chain()),
            FunctionCertificate::from_existing(make_cert("b", false), make_chain()),
        ];
        assert_eq!(
            compute_weakest_reported_assurance(&certs),
            ReportedAssurance::ReportedSoundnessClaim
        );
    }

    #[test]
    fn test_weakest_reported_assurance_all_signed_claims() {
        let certs = vec![
            FunctionCertificate::from_existing(make_cert("a", true), make_chain()),
            FunctionCertificate::from_existing(make_cert("b", true), make_chain()),
        ];
        assert_eq!(
            compute_weakest_reported_assurance(&certs),
            ReportedAssurance::SignedCertificationClaim
        );
    }

    #[test]
    fn test_weakest_reported_assurance_empty() {
        let certs: Vec<FunctionCertificate> = Vec::new();
        assert_eq!(compute_weakest_reported_assurance(&certs), ReportedAssurance::Unclassified);
    }
}
