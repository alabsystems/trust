//! Trust (step 2 increment 6, step 6.1): THE PER-DEFINITION RMETA ENTRY BUILDER.
//!
//! Design: `docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md` §2.2 (a level-R entry),
//! §2.4 (the evidence), §2.5 (identity), §3 (when it is produced) and §4 (what the encoder
//! refuses). The complete codec is now frozen; the schema-5 protocol extension requires
//! separate exact-blob review. The consumer (step 6.3) re-checks its unlicensed data.
//!
//! # What an entry is
//!
//! One SELF-CONTAINED `trust_ir::Module` per non-generic definition, in trust-ir's own binary
//! format, built from the per-body module the effect-conservation gate (D28) JUDGED at
//! `mir_built` — never re-lowered:
//!
//! * `functions[0]` is the body, named by the PRODUCING session's link symbol (`tcx.symbol_name`);
//! * one bodyless, signed declaration per callee, named by the producing session's symbol of the
//!   instance its RAW call site resolves to (re-derived as the frozen
//!   `instance_admission::decide_edge` re-derives an edge: the site's `(def, args)` resolved at
//!   `TypingEnv::fully_monomorphized()` must be the plain item the producer's ledger keyed);
//! * every table row the body references (the per-body module already carries exactly its own);
//! * every body-local global WITH its initializer; a `static` the body reads becomes an
//!   `External` declaration named by the static's symbol, never a copy (a static has one
//!   address);
//! * its source-file table spelled as rustc's own metadata spells those files (after
//!   `--remap-path-prefix`), never the build machine's local paths;
//! * the module's target, so the bytes validate standalone.
//!
//! # What a name in an entry is
//!
//! A name is the PRODUCING session's `tcx.symbol_name`. It is the name a consumer links only for
//! an instance whose symbol carries no instantiating crate: a non-generic item that is not
//! cross-crate-inlinable (`rustc_symbol_mangling::compute_symbol_name` adds the instantiating
//! crate for a generic instance, and for an `#[inline]` one rustc instantiates as
//! `GloballyShared { may_conflict: true }`, i.e. at `-Copt-level=0`). The body itself and an
//! `#[inline]` or generic callee are exactly such instances: a consumer that instantiates them
//! names its own copy by its own session's symbol, so the step-6.3 consumer must re-derive each
//! such name from the evidence ledger's identity (`DefPathHash` and site key) rather than link
//! the producer's spelling, which no object exports. Linking the producer's spelling fails
//! closed (an undefined or internal symbol), never as a different function.
//!
//! Beside the module travels the EVIDENCE a consumer needs to re-derive effect conservation
//! (D39 (ii), D4): every input `effect_conservation::judge` and `ir_census` read for this body —
//! the built MIR's effect census, the producer's drop claim, the callee ledger, the enum types
//! the producing session collapsed that this body holds, the producer's degraded struct rows and
//! its placeholder lanes — with every `DefId` spelled as its `DefPathHash` and every `Span` as a
//! body-local ordinal. (`ir_census`'s callee result types are the declarations' signed types in
//! the module itself.) No verdict bit is written.
//!
//! # What it refuses
//!
//! An entry is the claim "this is the body". The encoder writes none, and records why, for a body
//! that is not a function body, Clean-origin, not fully lowered, not CONSERVED (D28), carrying a
//! check with no panic site (D19: trust-ir's pin carries amendment P's sited `Assert`, but the
//! producer still emits every check with `site: None`), `#[track_caller]` or calling a
//! `#[track_caller]` callee (the symbol's ABI takes a hidden `&'static Location` the trust-ir
//! call does not pass), naming a callee or a global it cannot name by symbol, naming a source
//! file the session's source map does not, changed in effect shape by the extraction, or invalid
//! standalone. See [`EntryRefusal`].
//! Generic definitions use the separate level-S writer after their own complete template
//! gates. Its authenticated bytes are not R entries or runtime admission capabilities.
//!
//! # When
//!
//! Candidates are captured at `mir_built` by the mainline lowering ([`record_candidate`]); the
//! evidence is retained by the effect-conservation finalizer ([`retain_evidence`]); the entries
//! are built once, after analysis, when metadata is encoded ([`local_entries`], the
//! `trust_ir_local_entries` query) — `tcx.symbol_name` is legal there and not inside `mir_built`.
//! A session that writes no entries ([`crate_refusal`]: incremental, metadata-only, proc-macro, no
//! metadata) captures nothing.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::middle::trust_ir_entry::{TrustIrEntryBlob, TrustIrLocalEntries};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_span::def_id::{DefId, LocalDefId};
use trust_ir::value::GlobalId;
use trust_ir::{BlockId, FuncId, Function, Inst, Linkage, Module};

use crate::effect_conservation::{AssertClass, MirCensus, MirEffectKind, StoreValue};
use crate::template_lowering::LaneFacts;
use crate::{BodyKind, CalleeRef, GlobalOrigin, Lowered};

/// The entry's own magic: a level-R entry blob (not a bare trust-ir module, whose magic is
/// `TRUST_IR`, and not a level-S template).
pub const ENTRY_MAGIC: &[u8; 8] = b"TRIRENTR";
/// The entry schema. Bump on ANY change to the framing below or to the evidence section.
/// 2: the evidence carries every input of the D28 judgement (schema 2), and the source-file
/// table is spelled as rustc's metadata spells it.
/// 3: the evidence vocabulary includes the audited core Boolean-to-integer conversion.
/// 4: evidence retains exact location-derived store argument correspondences.
/// 5: the complete envelope binds the actual producing overflow-check mode,
/// owner, module and evidence; the module digest remains a separate identity.
pub const ENTRY_SCHEMA: u32 = 5;
/// The evidence section's own magic and schema (a versioned section of the entry, §2.4).
pub const EVIDENCE_MAGIC: &[u8; 8] = b"TRIREVID";
/// 2: adds the collapsed enum types, the degraded struct rows and the placeholder lanes.
/// 3: adds the Boolean-to-integer equivalence, without renumbering existing codes.
/// 4: adds exact store-effect/argument bindings, preserving the coarse store census.
pub const EVIDENCE_SCHEMA: u32 = 4;

// =============================================================================================
// The refusals (§4)
// =============================================================================================

/// Why the encoder wrote no entry for a definition. Rendered ([`EntryRefusal::reason`]) into the
/// crate header's unencoded rows, so a consumer's refusal names why a body is absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryRefusal {
    /// The producer never recorded a body for this definition in this session.
    NoProducerRecord,
    /// The producer recorded the body twice; neither record is trusted.
    DuplicateRecord,
    /// A generic definition (a level-S template) whose row writes no byte yet: why (step 6.5.1;
    /// see the `TEMPLATE_*` reasons). Trust's pin carries amendment S (wire v57); the encoder
    /// writes templates from step 6.5.4.
    TemplatePending(String),
    /// A generic definition whose template uses a construct the level-S lane does not carry yet
    /// (a lane refusal, a closure-kind body, or a `validate_template` refusal classed by variant,
    /// INC6.5-CLASSES): what.
    TemplateUnsupported(String),
    /// A const or static initializer: CTFE stays on MIR (design §2.1).
    NotAFunctionBody,
    /// A Clean-origin definition (below tier `gate`; step 3 owns it).
    CleanOrigin,
    /// The producer did not fully lower the body: its tags.
    NotLowered(Vec<String>),
    /// The effect-conservation check did not run, or has no verdict, or its census was not
    /// retained.
    ConservationUnchecked(String),
    /// The body is not CONSERVED (D28): the verdict's class labels (`not-conserved(call)`,
    /// `abstracted(drop)`, …).
    NotConserved(Vec<String>),
    /// A reachable `Assert` with no D19 panic site: the check classes.
    UnsitedPanic(Vec<&'static str>),
    /// The body, or a callee, is `#[track_caller]`: its symbol's ABI takes a hidden
    /// `&'static Location` argument that the trust-ir signature and call do not carry, so a
    /// consumer linking the entry would pass none (and lose the D19 panic site it names).
    CallerLocation(String),
    /// Rustc does not export this internal attribute; an importer cannot
    /// reconstruct its inherited overflow semantics from upstream metadata.
    InheritedOverflowChecks,
    /// A callee the consumer could not link by symbol.
    UnnamedCallee(String),
    /// A global the consumer could not bind (an external global not named by a symbol, or a
    /// body-local one with no initializer).
    UnnamedGlobal(String),
    /// The entry's effect shape differs from the judged body's (D28 leg 3's analog).
    ExtractionNotConserved(String),
    /// The entry is not self-contained or does not validate standalone: the first finding.
    Invalid(String),
}

impl EntryRefusal {
    /// The recorded reason, in the design's spelling (§4).
    pub fn reason(&self) -> String {
        match self {
            EntryRefusal::NoProducerRecord => {
                rustc_middle::middle::trust_ir_entry::UNRECORDED_REASON.to_string()
            }
            EntryRefusal::DuplicateRecord => {
                "not-lowered(the producer recorded this body twice)".to_string()
            }
            EntryRefusal::TemplatePending(why) => format!("template-pending({why})"),
            EntryRefusal::TemplateUnsupported(what) => format!("template-unsupported({what})"),
            EntryRefusal::NotAFunctionBody => {
                "not-a-function(a const or static initializer: CTFE stays on MIR)".to_string()
            }
            EntryRefusal::CleanOrigin => "clean-origin".to_string(),
            EntryRefusal::NotLowered(tags) => format!("not-lowered({})", tags.join("; ")),
            EntryRefusal::ConservationUnchecked(why) => format!("conservation-unchecked({why})"),
            EntryRefusal::NotConserved(classes) => classes.join("+"),
            EntryRefusal::UnsitedPanic(kinds) => format!("unsited-panic({})", kinds.join("+")),
            EntryRefusal::CallerLocation(what) => format!("caller-location({what})"),
            EntryRefusal::InheritedOverflowChecks => {
                "inherited-overflow-checks(the compiler-only attribute is not exported)".into()
            }
            EntryRefusal::UnnamedCallee(edge) => format!("unnamed-callee({edge})"),
            EntryRefusal::UnnamedGlobal(global) => format!("unnamed-global({global})"),
            EntryRefusal::ExtractionNotConserved(why) => format!("extraction-not-conserved({why})"),
            EntryRefusal::Invalid(first) => format!("invalid({first})"),
        }
    }

    /// The short class (the reason up to its first `(`), for histograms.
    pub fn class(&self) -> &'static str {
        match self {
            EntryRefusal::NoProducerRecord
            | EntryRefusal::DuplicateRecord
            | EntryRefusal::NotLowered(_) => "not-lowered",
            EntryRefusal::TemplatePending(_) => "template-pending",
            EntryRefusal::TemplateUnsupported(_) => "template-unsupported",
            EntryRefusal::NotAFunctionBody => "not-a-function",
            EntryRefusal::CleanOrigin => "clean-origin",
            EntryRefusal::ConservationUnchecked(_) => "conservation-unchecked",
            EntryRefusal::NotConserved(_) => "not-conserved",
            EntryRefusal::UnsitedPanic(_) => "unsited-panic",
            EntryRefusal::CallerLocation(_) => "caller-location",
            EntryRefusal::InheritedOverflowChecks => "inherited-overflow-checks",
            EntryRefusal::UnnamedCallee(_) => "unnamed-callee",
            EntryRefusal::UnnamedGlobal(_) => "unnamed-global",
            EntryRefusal::ExtractionNotConserved(_) => "extraction-not-conserved",
            EntryRefusal::Invalid(_) => "invalid",
        }
    }
}

/// A local-only metadata refusal, not an admission result. The typed LocalDefId
/// ensures the attribute is read from HIR, where it still exists; Rustc omits it
/// from cross-crate attributes. Both canonical R/S writers use this same check.
pub fn inherited_overflow_refusal(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<EntryRefusal> {
    rustc_attr_ir::find_attr!(
        tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)),
        RustcInheritOverflowChecks
    )
    .then_some(EntryRefusal::InheritedOverflowChecks)
}

// =============================================================================================
// The candidates: captured at `mir_built`, drained when metadata is encoded
// =============================================================================================

/// One body the mainline lowering recorded, as the entry builder needs it. Lifetime-free, so it
/// survives in the session's `'static` state until metadata is encoded.
#[derive(Clone, Debug)]
pub struct Candidate {
    /// The per-body module exactly as the lowering produced it (and as the effect census read
    /// `functions[0]` of it).
    pub module: Module,
    pub callees: Vec<CalleeRef>,
    /// Parallel to `module.globals`.
    pub global_origins: Vec<GlobalOrigin>,
    pub body_kind: BodyKind,
    /// The producer's own reasons the body is not fully lowered (empty: fully lowered).
    pub not_lowered: Vec<String>,
}

/// A [`Candidate`] as the registry keeps it until metadata is encoded: the per-body module in
/// trust-ir's own binary form, which is a fraction of its in-memory size. A candidate lives from
/// its body's `mir_built` to the end of analysis, so every body's copy is resident at once; on
/// `core` the in-memory copies cost the producer's peak RSS ~8% (2.72 -> 2.93-2.98 GB, measured
/// 2026-10-05). `module` is `None` for a body refused before its module is read.
struct StoredCandidate {
    module: Option<Vec<u8>>,
    callees: Vec<CalleeRef>,
    global_origins: Vec<GlobalOrigin>,
    body_kind: BodyKind,
    not_lowered: Vec<String>,
}

impl StoredCandidate {
    /// The candidate the builder reads. The binary form round-trips (trust-ir's codec is
    /// canonical and lossless); a module that does not decode is refused by name.
    fn load(&self) -> Result<Candidate, EntryRefusal> {
        let module = match &self.module {
            None => Module::new(String::new()),
            Some(bytes) => trust_ir::binary::deserialize_module(bytes).map_err(|e| {
                EntryRefusal::Invalid(format!("the per-body module does not decode: {e:?}"))
            })?,
        };
        Ok(Candidate {
            module,
            callees: self.callees.clone(),
            global_origins: self.global_origins.clone(),
            body_kind: self.body_kind,
            not_lowered: self.not_lowered.clone(),
        })
    }
}

/// What [`retain_evidence`] keeps of the effect-conservation finalizer's registry for one body:
/// every input the D28 judgement of that body read besides the per-body module and its ledger.
#[derive(Clone, Debug)]
pub struct RetainedEvidence {
    pub census: MirCensus,
    pub drop_claim: Option<crate::drops::DropClaim>,
    /// `census.enum_types` restricted to the enum types ANY lowering of this session collapsed to
    /// a lone `bool`/`()` placeholder (`judge`'s session-wide `collapsed` set, which it intersects
    /// with exactly this).
    pub collapsed_enum_types: Vec<u128>,
    /// The producer's degraded struct rows of this body (`LowerCx::rmw_degraded_structs`), as
    /// `StructId` indices of its per-body module (and of the entry, which keeps that table).
    pub degraded_structs: Vec<u32>,
    /// `ir_census`'s `lanes` input.
    pub union_lane: bool,
    pub enum_param_lane: bool,
}

/// The session registry: candidates by `DefIndex`, and the evidence the finalizer retained.
#[derive(Default)]
struct EntryRegistry {
    candidates: BTreeMap<u32, StoredCandidate>,
    duplicated: BTreeSet<u32>,
    evidence: BTreeMap<u32, RetainedEvidence>,
    /// Trust (step 6.5.1): the template lane's record per definition ([`record_template`]).
    templates: BTreeMap<u32, StoredTemplate>,
    /// def indices whose template was recorded twice: neither record is trusted.
    templates_duplicated: BTreeSet<u32>,
}

// =============================================================================================
// The level-S template records (step 6.5.1): captured at `mir_built`, built at encode time
// =============================================================================================

/// The `template-pending` reasons (step 6.5.1).
///
/// The template lane did not run in this session (`-Ztrust-ir-lower-templates` is off, the
/// default until step 6.5.4).
pub const TEMPLATE_CAPTURE_OFF: &str = "capture off";
/// The lane ran but recorded nothing for this definition (a generic body that is not a fn body).
pub const TEMPLATE_NOT_RECORDED: &str = "no template lowering was recorded";
/// Every gate passed: the template validates and is conserved; no byte is written until 6.5.4.
pub const TEMPLATE_VALIDATED: &str =
    "validated and conserved; level-S entries are written from step 6.5.4";

/// A non-generic closure-kind body's `template-pending` reason (INC6.5-CLOSURES).
pub fn template_non_generic_reason(kind: &str) -> String {
    format!("non-generic {kind}: level R (design §2.1), not routed in 6.5 (INC6.5-CLOSURES)")
}

/// Why the capture stored no module: the capture-time gates, in the builder's order (the
/// precedent of [`record_candidate`]: a body refused before its module is read stores none).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaptureRefusal {
    /// A closure, coroutine, coroutine-closure, synthetic coroutine body or inline const, by
    /// kind; `generic` when it has a template parameter (INC6.5-CLOSURES).
    ClosureKind { kind: &'static str, generic: bool },
    /// The lane's own refusals (`template-unsupported`), sorted and deduplicated.
    Lane(Vec<String>),
    /// The producer's not-fully-lowered reasons ([`not_lowered_reasons`]).
    NotLowered(Vec<String>),
    /// A reachable unsited check ([`unsited_checks`], INC6.5-SITES).
    UnsitedPanic(Vec<&'static str>),
}

/// A captured template lowering, as the builder reads it.
#[derive(Clone, Debug)]
pub struct TemplateCandidate {
    /// The per-body SENTINEL module exactly as the template lowering produced it (and as the
    /// effect census of the template read `functions[0]` of it).
    pub module: Module,
    pub callees: Vec<CalleeRef>,
    /// Parallel to `module.globals`.
    pub global_origins: Vec<GlobalOrigin>,
    pub facts: LaneFacts,
}

/// One definition's template record, as the builder reads it.
#[derive(Clone, Debug)]
pub struct TemplateRecord {
    pub body_kind: BodyKind,
    pub capture: Result<TemplateCandidate, CaptureRefusal>,
}

/// A [`TemplateRecord`] as the registry keeps it: the sentinel module in trust-ir's binary form,
/// or, for a capture refused at capture time, only the reason.
pub(crate) struct StoredTemplate {
    body_kind: BodyKind,
    capture: Result<StoredTemplateModule, CaptureRefusal>,
}

struct StoredTemplateModule {
    module: Vec<u8>,
    callees: Vec<CalleeRef>,
    global_origins: Vec<GlobalOrigin>,
    facts: LaneFacts,
}

impl StoredTemplate {
    /// A capture refused at capture time: its reason only.
    pub(crate) fn refused(body_kind: BodyKind, refusal: CaptureRefusal) -> StoredTemplate {
        StoredTemplate { body_kind, capture: Err(refusal) }
    }

    /// The record of a template lowering: the capture-time gates in the builder's order (the
    /// lane's refusals, the producer's not-fully-lowered reasons, a reachable unsited check),
    /// else the sentinel module in its wire image (a module the binary writer refuses is a
    /// not-lowered reason and stores nothing), its ledger and global origins, and the lane's
    /// facts.
    pub(crate) fn of_lowering(
        lowered: &Lowered,
        lane: &crate::template_lowering::TemplateLane<'_>,
    ) -> StoredTemplate {
        let body_kind = lowered.body_kind;
        let labels = lane.refusal_labels();
        if !labels.is_empty() {
            return StoredTemplate::refused(body_kind, CaptureRefusal::Lane(labels));
        }
        let not_lowered = not_lowered_reasons(lowered);
        if !not_lowered.is_empty() {
            return StoredTemplate::refused(body_kind, CaptureRefusal::NotLowered(not_lowered));
        }
        let unsited = lowered.module.functions.first().map(unsited_checks).unwrap_or_default();
        if !unsited.is_empty() {
            return StoredTemplate::refused(body_kind, CaptureRefusal::UnsitedPanic(unsited));
        }
        // Trust (trust-ir D1b, INC6.5-LANE): a sentinel module the binary writer refuses stores
        // no copy, and that refusal is a not-lowered reason, as `record_candidate` records it
        // for a level-R candidate.
        let module = match trust_ir::binary::serialize_module(&lowered.module) {
            Ok(bytes) => bytes,
            Err(refusal) => {
                return StoredTemplate::refused(
                    body_kind,
                    CaptureRefusal::NotLowered(vec![format!(
                        "the per-body module has no wire image: {refusal}"
                    )]),
                );
            }
        };
        StoredTemplate {
            body_kind,
            capture: Ok(StoredTemplateModule {
                module,
                callees: lowered.callees.clone(),
                global_origins: lowered.global_origins.clone(),
                facts: lane.facts(),
            }),
        }
    }

    /// A closure-kind body's record (INC6.5-CLOSURES): recorded by kind, never lowered.
    fn is_closure_kind(&self) -> bool {
        matches!(self.capture, Err(CaptureRefusal::ClosureKind { .. }))
    }

    /// The stored module's byte count, when one is stored (the R-8 memory proxy).
    fn module_bytes(&self) -> Option<usize> {
        self.capture.as_ref().ok().map(|m| m.module.len())
    }

    /// The record the builder reads. The binary form round-trips; a module that does not decode
    /// is refused by name.
    fn load(&self) -> Result<TemplateRecord, EntryRefusal> {
        let capture = match &self.capture {
            Err(refusal) => Err(refusal.clone()),
            Ok(stored) => Ok(TemplateCandidate {
                module: trust_ir::binary::deserialize_module(&stored.module).map_err(|e| {
                    EntryRefusal::Invalid(format!("the sentinel module does not decode: {e:?}"))
                })?,
                callees: stored.callees.clone(),
                global_origins: stored.global_origins.clone(),
                facts: stored.facts.clone(),
            }),
        };
        Ok(TemplateRecord { body_kind: self.body_kind, capture })
    }
}

/// Record `def`'s template lane outcome. Called by `template_lowering::capture` only; inert
/// unless this session builds rmeta entries.
pub(crate) fn record_template(tcx: TyCtxt<'_>, def: LocalDefId, stored: StoredTemplate) {
    if !entries_enabled(tcx) {
        return;
    }
    let index = def.local_def_index.as_u32();
    tcx.sess.with_trust_compiler_state::<EntryRegistry, _>(|r| {
        if r.templates.insert(index, stored).is_some() {
            r.templates_duplicated.insert(index);
        }
    });
}

/// Why a session in which the producer RUNS attempts no entry at all: the crate header's
/// crate-wide refusal, a class and its reason. `None`: entries are attempted per definition.
///
/// * `no-metadata`: the crate writes no metadata (an executable, a staticlib or cdylib).
///   Nothing reads an entry, so none is captured.
/// * `proc-macro`: the crate's rmeta carries no bodies (rustc encodes no MIR for a proc-macro
///   crate), so none is captured; its header still records this, as every header does.
/// * `incremental`: the candidates are captured at `mir_built`, and a body whose `mir_built`
///   replays green from the incremental cache records nothing, so an entry set would depend on
///   the cache's state.
/// * `metadata-only`: `should_encode_mir`'s two session-wide conjuncts both fail (no
///   `-Zalways-encode-mir`, and the session does not codegen), so rustc encodes no MIR and no
///   definition is in the encode set.
pub fn crate_refusal(tcx: TyCtxt<'_>) -> Option<&'static str> {
    let sess = tcx.sess;
    if tcx.crate_types().contains(&rustc_structures::CrateType::ProcMacro) {
        return Some("proc-macro(a proc-macro crate's metadata carries no bodies, so no entry)");
    }
    if !tcx.needs_metadata() {
        return Some("no-metadata(the crate writes no metadata that could carry an entry)");
    }
    if sess.opts.incremental.is_some() {
        return Some("incremental(the producer's per-body records do not survive a cache replay)");
    }
    if !(sess.opts.unstable_opts.always_encode_mir || sess.opts.output_types.should_codegen()) {
        return Some(
            "metadata-only(rustc encodes no MIR in a session that does not codegen, so no entry)",
        );
    }
    None
}

/// Does this session build rmeta entries? Exactly when the producer runs (design §3.2: no new
/// flag) and [`crate_refusal`] names no crate-wide reason. Gates the capture
/// ([`record_candidate`], [`retain_evidence`]) as well as the build, so a session that writes no
/// entry pays for none.
pub fn entries_enabled(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.trust_ir_lower_enabled() && crate_refusal(tcx).is_none()
}

/// The producer's own not-fully-lowered reasons for a lowering, read off the producer's ground
/// truth rather than off the crate splice, which on a crate whose module fails final validation
/// publishes nothing at all (design M2, M6).
///
/// A SUPERSET of what the frozen crate splice (`crate_module::splice_refusal`) refuses on. The
/// splice's own flags: the `unsupported` tags, symbolic, union and enum-parameter lanes,
/// fn-pointer adapters, coroutine frame pointers and ZST callable stand-ins (and its generated
/// `SyntheticCoroutineBody` gate, which [`record_candidate`] adds from the def kind). Refused
/// HERE although the splice does not gate on them, because an entry is captured at `mir_built`
/// and no seam differential ever judges it:
/// * a pending-const sentinel: the crate module resolves it at finalize
///   (`crate_module::resolve_pending_consts`), after the candidate was captured, so the
///   candidate's module still holds the placeholder;
/// * opaque collapse: a placeholder standing for a real value; the instance lane, which no seam
///   differential judges either, refuses it the same way (`LaneRefused("opaque collapse")`, D17);
/// * a place-path value carrier: sound only uninterpreted under the CLEAN-ONLY contract (the
///   seam skips such bodies), and a consumer executes the entry;
/// * a withheld layout: the splice refuses one only where the signature reaches it (R2); an
///   entry refuses any.
///
/// Measured cost on `core` (design M14): pending-const sentinels 1,137 bodies, opaque collapse
/// 858.
///
/// `Lowered` is destructured EXHAUSTIVELY, with no `..` (the instance lane's `lowering_facts`
/// discipline): a new field does not compile here until it is classified as a reason or named as
/// not one. Each reason is pinned by the unit test
/// `every_not_lowered_flag_is_its_own_reason_and_nothing_else_is_one`, and the wire from the
/// producer to the refusal by `tests/run-make/trust-ir-rmeta-entry-rederivation` (a pending-const
/// body).
pub fn not_lowered_reasons(lowered: &Lowered) -> Vec<String> {
    let Lowered {
        // A REASON: the one-function precondition.
        module,
        // Not a reason: a static becomes a declaration and a body-local global travels with its
        // initializer, or `rewrite_globals` refuses it (`unnamed-global`).
        global_origins: _,
        // Not a reason here: `build_entry_module`'s `not-a-function` gate reads it.
        body_kind: _,
        // REASONS (below).
        opaque_collapse,
        // Not a reason: a census of `register_enum` declines; its consequence, the opaque lane,
        // sets `opaque_collapse`.
        enum_declines: _,
        union_lane,
        layout_withheld_structs,
        enum_param_lane,
        symbolic,
        unsubstituted_opaque_return,
        unsupported,
        // Not a reason: interpretation eligibility. Its writers that place a stand-in gate through
        // their own flags, and an `Inst::Undef` through the D28 verdict (`abstracted(undef)`).
        contains_call: _,
        place_path_carrier,
        zst_closure_arg,
        coroutine_frame_ptr,
        fnptr_adapter,
        // Not a reason: flip-only gates. A thin or `&mut` reborrow arm emits no instruction and
        // binds the reborrowed value itself (as `instance_admission::lowering_facts` classes them).
        thin_reborrows: _,
        mut_reborrows: _,
        // Not a reason: the edges, which `assemble_entry` names by symbol or refuses.
        callees: _,
        pending_consts,
        // Not a reason: flip reshaping evidence only.
        enum_fold_switch_blocks: _,
    } = lowered;
    let mut out: Vec<String> = Vec::new();
    let mut tags: Vec<&str> = unsupported.iter().map(|(_, what)| *what).collect();
    tags.sort_unstable();
    tags.dedup();
    out.extend(tags.into_iter().map(str::to_string));
    let flags: [(bool, &str); 11] = [
        (*symbolic, "symbolic"),
        (*unsubstituted_opaque_return, "unsubstituted opaque return"),
        (!pending_consts.is_empty(), "pending-const sentinel"),
        (*opaque_collapse, "opaque collapse"),
        (*union_lane, "union lane"),
        (*enum_param_lane, "enum-parameter lane"),
        (*fnptr_adapter, "fn-pointer adapter"),
        (*coroutine_frame_ptr, "coroutine frame pointer"),
        (*zst_closure_arg, "ZST callable stand-in"),
        (*place_path_carrier, "place-path value carrier"),
        (!layout_withheld_structs.is_empty(), "layout withheld"),
    ];
    out.extend(flags.into_iter().filter(|(set, _)| *set).map(|(_, what)| what.to_string()));
    if module.functions.len() != 1 {
        out.push(format!("{} functions in the per-body module", module.functions.len()));
    }
    out
}

/// Capture `def`'s mainline lowering as an entry candidate. Called by the producer's
/// `mir_built`-hook lowering only (the same gate as the effect census's producer side: never the
/// `trust_ir_of` query, the instance lane or the collect-all census).
pub(crate) fn record_candidate(tcx: TyCtxt<'_>, def: LocalDefId, lowered: &Lowered) {
    if !entries_enabled(tcx) {
        return;
    }
    // A generic definition or an initializer is refused before its module is read
    // ([`build_entry_module`]'s first two gates), so its candidate carries no copy of it: the
    // copy is the cost of a candidate, and in `core` most bodies are generic.
    let refused_before_the_module =
        lowered.body_kind != BodyKind::Fn || tcx.generics_of(def).requires_monomorphization(tcx);
    let candidate = if refused_before_the_module {
        StoredCandidate {
            module: None,
            callees: Vec::new(),
            global_origins: Vec::new(),
            body_kind: lowered.body_kind,
            not_lowered: Vec::new(),
        }
    } else {
        let mut reasons = not_lowered_reasons(lowered);
        // The splice's first gate (`BodyRecord::generated_ungated`): no certificate for
        // the coroutine state-transform protocol a generated body implements.
        if tcx.def_kind(def) == rustc_hir::def::DefKind::SyntheticCoroutineBody {
            reasons.push("generated coroutine body (ungated)".to_string());
        }
        // Trust (trust-ir D1b): a module the binary writer refuses has no stored copy, and
        // that refusal is itself a reason the entry is not lowered.
        let module = match trust_ir::binary::serialize_module(&lowered.module) {
            Ok(bytes) => Some(bytes),
            Err(refusal) => {
                reasons.push(format!("the per-body module has no wire image: {refusal}"));
                None
            }
        };
        StoredCandidate {
            module,
            callees: lowered.callees.clone(),
            global_origins: lowered.global_origins.clone(),
            body_kind: lowered.body_kind,
            not_lowered: reasons,
        }
    };
    let index = def.local_def_index.as_u32();
    tcx.sess.with_trust_compiler_state::<EntryRegistry, _>(|r| {
        if r.candidates.insert(index, candidate).is_some() {
            r.duplicated.insert(index);
        }
    });
}

/// Keep, for the entry's evidence, every input the effect-conservation finalizer's judgement of a
/// body read besides its module and ledger: the MIR census, the drop claim, the collapsed enum
/// types it holds (`collapsed` is the session-wide set `judge` intersects), the degraded struct
/// rows and the placeholder lanes. Called by `effect_conservation::finalize` before it drops its
/// registry. A body with a MIR census and no producer record keeps nothing (it has no verdict to
/// re-derive, and its entry is refused).
///
/// Step 6.5.1 (INC6.5-JUDGE): a definition with a TEMPLATE record keeps the template's producer
/// half and the set its template was judged with, `collapsed_t` (the mainline set plus the
/// templates' own collapses); every other definition is retained exactly as before.
pub(crate) fn retain_evidence(
    tcx: TyCtxt<'_>,
    mir: &mut BTreeMap<u32, MirCensus>,
    producer: &mut BTreeMap<u32, crate::effect_conservation::ProducerBody>,
    template: &mut BTreeMap<u32, crate::effect_conservation::ProducerBody>,
    collapsed: &BTreeSet<u128>,
    collapsed_t: &BTreeSet<u128>,
) {
    if !entries_enabled(tcx) {
        return;
    }
    let retained = retained_evidence(mir, producer, template, collapsed, collapsed_t);
    tcx.sess.with_trust_compiler_state::<EntryRegistry, _>(|r| r.evidence = retained);
}

/// [`retain_evidence`]'s rule, TyCtxt-free. Drains `mir`.
pub(crate) fn retained_evidence(
    mir: &mut BTreeMap<u32, MirCensus>,
    producer: &mut BTreeMap<u32, crate::effect_conservation::ProducerBody>,
    template: &mut BTreeMap<u32, crate::effect_conservation::ProducerBody>,
    collapsed: &BTreeSet<u128>,
    collapsed_t: &BTreeSet<u128>,
) -> BTreeMap<u32, RetainedEvidence> {
    std::mem::take(mir)
        .into_iter()
        .filter_map(|(index, census)| {
            let (p, collapsed) = match template.get_mut(&index) {
                Some(t) => (t, collapsed_t),
                None => (producer.get_mut(&index)?, collapsed),
            };
            let collapsed_enum_types = census.enum_types.intersection(collapsed).copied().collect();
            Some((
                index,
                RetainedEvidence {
                    collapsed_enum_types,
                    drop_claim: p.drop_claim.take(),
                    degraded_structs: p.degraded_structs.iter().map(|s| s.index()).collect(),
                    union_lane: p.census.abstractions.union_lane,
                    enum_param_lane: p.census.abstractions.enum_param_lane,
                    census,
                },
            ))
        })
        .collect()
}

// =============================================================================================
// The builder: pure core
// =============================================================================================

/// The effect-conservation verdict, as the builder reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerdictInput {
    /// The check did not run, or has no verdict for the body: why.
    Unchecked(String),
    /// The verdict's class labels; empty means CONSERVED.
    Classes(Vec<String>),
}

/// Everything about one body the builder decides on, TyCtxt-free.
pub struct EntryInputs<'a> {
    pub candidate: &'a Candidate,
    pub generic: bool,
    pub clean_origin: bool,
    pub verdict: VerdictInput,
}

/// Why [`EntryNames::callee_symbol`] gives a callee edge no name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CalleeNameRefusal {
    /// No symbol a consumer could link: why.
    Unnamed(String),
    /// The callee is `#[track_caller]` (`InstanceKind::requires_caller_location`): its symbol's
    /// ABI takes a hidden `&'static Location` argument that the trust-ir call does not pass.
    CallerLocation,
}

/// What `RustcNames::callee_symbol` re-derived for one concretely keyed callee edge: its RAW
/// call site resolved as codegen resolves a callee operand. TyCtxt-free, so the guard's decision
/// ([`judge_rederived_callee`]) is unit-tested branch by branch; the rustc half only computes
/// these facts (pinned end to end by `tests/run-make/trust-ir-rmeta-entry-rederivation`).
pub struct RederivedCallee<'a> {
    /// The resolved instance, for the refusal's recorded reason. Formatted only when the edge is
    /// refused; the production caller passes an [`UntrimmedInstance`], since a trimmed path in a
    /// session that emits no diagnostic is an internal compiler error.
    pub resolved: &'a dyn std::fmt::Display,
    /// The resolved instance is `InstanceKind::Item` of the ledger's `def_id`: not an intrinsic,
    /// a virtual call, a shim, nor any other definition.
    pub is_ledger_item: bool,
    /// The resolved instance's own concrete key; `None` when its args are not encodable (or it is
    /// not the ledger's item, when it is not computed).
    pub key: Option<crate::lineage::ConcreteCalleeKey>,
    /// The resolved instance is the body's own instance (a recursive call).
    pub is_self: bool,
    /// The resolved instance takes a hidden caller location (`#[track_caller]`).
    pub requires_caller_location: bool,
}

/// The re-derivation guard's decision for one concretely keyed callee edge, in order: the site
/// must resolve to exactly the plain item the ledger linked, at exactly the instance the ledger
/// keyed; a self edge has no declaration of its own (the body's name is not a callee's); a
/// `#[track_caller]` callee's symbol takes an argument the trust-ir call does not pass. PURE.
pub fn judge_rederived_callee(
    ledger_key: &crate::lineage::ConcreteCalleeKey,
    r: &RederivedCallee<'_>,
) -> Result<(), CalleeNameRefusal> {
    if !r.is_ledger_item {
        return Err(CalleeNameRefusal::Unnamed(format!(
            "its call site resolves to `{}`, which is not the plain item the ledger linked (an \
             intrinsic, a virtual call or a shim has no symbol of its own here)",
            r.resolved
        )));
    }
    let Some(key) = &r.key else {
        return Err(CalleeNameRefusal::Unnamed(
            "the resolved instance's args are not encodable".to_string(),
        ));
    };
    if key != ledger_key {
        return Err(CalleeNameRefusal::Unnamed(format!(
            "its call site resolves to `{}`, which is not the instance the ledger keyed",
            r.resolved
        )));
    }
    if r.is_self {
        return Err(CalleeNameRefusal::Unnamed(
            "a self edge (a recursive call is linked by the body's own name)".to_string(),
        ));
    }
    // The symbol's ABI is the instance's `FnAbi`, which for a `#[track_caller]` callee ends in
    // the hidden caller-location argument codegen supplies at a MIR call site; the trust-ir call
    // passes none (the producer spells no caller location: D19's Trust half is not built).
    if r.requires_caller_location {
        return Err(CalleeNameRefusal::CallerLocation);
    }
    Ok(())
}

/// The names the builder asks rustc for. Production answers with `tcx.symbol_name` over
/// re-derived instances ([`RustcNames`]); unit tests answer with fixtures.
pub trait EntryNames {
    /// The body's own link symbol.
    fn body_symbol(&self) -> Result<String, String>;
    /// The body's exact source ABI and target convention. Metadata must preserve the judged
    /// body's convention; neither an absent signature nor an unsupported ABI defaults to C.
    fn body_abi(&self) -> crate::calling_convention::FunctionAbi;
    /// Whether the body is `#[track_caller]`: its symbol then takes a hidden `&'static Location`
    /// parameter that the per-body function's signature does not have.
    fn body_requires_caller_location(&self) -> bool;
    /// The link symbol of callee edge `FuncId(k)`, or why it has none.
    fn callee_symbol(&self, k: usize, callee: &CalleeRef) -> Result<String, CalleeNameRefusal>;
    /// Exact physical foreign prototype, when the producing session can read
    /// the original Item/FnAbi. Absence retains the existing signed reader.
    fn foreign_signature(&self, _callee: &CalleeRef) -> Option<trust_ir::FuncTy> { None }
    /// The link symbol of the static `def`, or why it has none.
    fn static_symbol(&self, def: DefId) -> Result<String, String>;
    /// The spelling rustc's metadata gives the source file the per-body module names `local`
    /// (the rendering the producer interns, `prefer_remapped_unconditionally`): its name after
    /// `--remap-path-prefix`, as `RealFileName::update_for_crate_metadata` leaves it. `Err` when
    /// the session's source map does not name it unambiguously; the reason must not repeat the
    /// path (it is recorded in rmeta).
    fn file_name(&self, local: &str) -> Result<String, String>;
    /// The target the entry is stamped with.
    fn target_info(&self) -> trust_ir::TargetInfo;
}

/// The gates that need no module work, in the design's order (§4), then [`assemble_entry`].
pub fn build_entry_module(
    inputs: &EntryInputs<'_>,
    names: &dyn EntryNames,
) -> Result<Module, EntryRefusal> {
    let c = inputs.candidate;
    if inputs.generic {
        // Production routes a generic definition to the template builder before this function
        // (`local_entries`); a generic input reaching it is a level-S row all the same.
        return Err(EntryRefusal::TemplatePending(
            "a generic definition is a level-S template, built by the template builder".to_string(),
        ));
    }
    if c.body_kind != BodyKind::Fn {
        return Err(EntryRefusal::NotAFunctionBody);
    }
    if inputs.clean_origin {
        return Err(EntryRefusal::CleanOrigin);
    }
    if !c.not_lowered.is_empty() {
        return Err(EntryRefusal::NotLowered(c.not_lowered.clone()));
    }
    match &inputs.verdict {
        VerdictInput::Unchecked(why) => {
            return Err(EntryRefusal::ConservationUnchecked(why.clone()));
        }
        VerdictInput::Classes(classes) if !classes.is_empty() => {
            return Err(EntryRefusal::NotConserved(classes.clone()));
        }
        VerdictInput::Classes(_) => {}
    }
    let body = c.module.functions.first().ok_or_else(|| {
        EntryRefusal::Invalid("the per-body module carries no function".to_string())
    })?;
    let unsited = unsited_checks(body);
    if !unsited.is_empty() {
        return Err(EntryRefusal::UnsitedPanic(unsited));
    }
    assemble_entry(c, names)
}

/// The check classes of every REACHABLE `Assert` in `body`, deduplicated, in class order. Under
/// D19 a failed check's outcome is (kind, operands, entry, location). Trust's pin carries
/// amendment P's sited `Assert` (wire v54), but the producer emits every check with
/// `site: None` (D19's Trust half is not built), so every reachable check is unsited; this rule
/// refuses each one, sited or not, until that half lands (INC6.5-SITES).
pub fn unsited_checks(body: &Function) -> Vec<&'static str> {
    let reachable = crate::effect_conservation::ir_reachable(body);
    let mut classes: BTreeSet<AssertClass> = BTreeSet::new();
    for (i, block) in body.blocks.iter().enumerate() {
        if !reachable.get(i).copied().unwrap_or(false) {
            continue;
        }
        for node in &block.body {
            if matches!(node.inst, Inst::Assert { .. }) {
                classes.insert(AssertClass::of_ir(&node.proofs));
            }
        }
    }
    classes.into_iter().map(assert_class_label).collect()
}

fn assert_class_label(class: AssertClass) -> &'static str {
    match class {
        AssertClass::Bounds => "bounds",
        AssertClass::Overflow => "overflow",
        AssertClass::Shift => "shift",
        AssertClass::DivZero => "div-zero",
        AssertClass::Other => "other",
    }
}

/// Does the body (`FuncId(0)`) call `callee` directly? PURE (the instance lane's rule: an edge
/// with no call site at all is a reify-only edge whose result nothing observed).
fn body_calls(module: &Module, callee: FuncId) -> bool {
    module.function_by_id(FuncId::new(0)).is_some_and(|body| {
        body.blocks.iter().flat_map(|b| b.body.iter()).any(|node| {
            matches!(&node.inst, Inst::Call { callee: c, .. } | Inst::Invoke { callee: c, .. } if *c == callee)
        })
    })
}

/// THE EXTRACTION: the judged per-body module, made self-contained. PURE given `names`.
pub fn assemble_entry(c: &Candidate, names: &dyn EntryNames) -> Result<Module, EntryRefusal> {
    let mut module = c.module.clone();
    if module.functions.len() != 1 || module.functions[0].id != FuncId::new(0) {
        return Err(EntryRefusal::Invalid(format!(
            "the per-body module holds {} function(s); exactly the body at FuncId(0) was expected",
            module.functions.len()
        )));
    }
    // 0. The source files, as rustc's metadata spells them: an entry is written into rmeta, so
    //    it carries the names rustc's metadata writes for them (`RealFileName::
    //    update_for_crate_metadata`), looked up by the rendering the producer interned.
    for (index, file) in module.files.iter_mut().enumerate() {
        *file = names.file_name(file).map_err(|why| {
            EntryRefusal::Invalid(format!("source file {index} has no metadata spelling: {why}"))
        })?;
    }
    // 1. The body, by its link symbol (the producing session's; see the module doc). Linkage and
    //    visibility are advisory (design §2.2): the consumer re-stamps them for its own copy.
    //    A `#[track_caller]` body's symbol takes a hidden `&'static Location` its trust-ir
    //    signature does not have: refused, never written with the wrong arity.
    if names.body_requires_caller_location() {
        return Err(EntryRefusal::CallerLocation(
            "the body is #[track_caller]: its symbol takes a hidden &'static Location parameter \
             its trust-ir signature does not have"
                .to_string(),
        ));
    }
    let symbol = names
        .body_symbol()
        .map_err(|why| EntryRefusal::Invalid(format!("the body has no link symbol: {why}")))?;
    module.functions[0].name = symbol;
    let convention = names.body_abi().calling_conv()
        .map_err(|why| EntryRefusal::Invalid(why.to_string()))?;
    if module.functions[0].calling_conv != convention {
        return Err(EntryRefusal::Invalid("judged body and source calling convention disagree".into()));
    }
    module.functions[0].calling_conv = convention;
    // 2. One signed declaration per callee edge, by the symbol of the instance its site resolves
    //    to. The ledger is dense `1..=n` (checked), as the instance lane requires.
    let mut declared: BTreeSet<String> = BTreeSet::new();
    declared.insert(module.functions[0].name.clone());
    for (position, callee) in c.callees.iter().enumerate() {
        let k = position + 1;
        if callee.func_id != FuncId::new(k as u32) {
            return Err(EntryRefusal::Invalid(format!(
                "the callee ledger is not dense: position {k} holds FuncId({})",
                callee.func_id.index()
            )));
        }
        let name = names.callee_symbol(k, callee).map_err(|why| match why {
            CalleeNameRefusal::Unnamed(why) => {
                EntryRefusal::UnnamedCallee(format!("FuncId({k}) `{}`: {why}", callee.def_path))
            }
            CalleeNameRefusal::CallerLocation => EntryRefusal::CallerLocation(format!(
                "callee FuncId({k}) `{}` is #[track_caller]: its symbol takes a hidden \
                 &'static Location argument the trust-ir call does not pass",
                callee.def_path
            )),
        })?;
        if name.starts_with('!') || !declared.insert(name.clone()) {
            return Err(EntryRefusal::UnnamedCallee(format!(
                "FuncId({k}) `{}`: `{name}` is reserved or already declared",
                callee.def_path
            )));
        }
        let func_ty = if let Some(exact) = names.foreign_signature(callee) {
            crate::foreign_signature::check_observation(&exact, callee.abi, &callee.params,
                callee.ret_ty.as_ref(), callee.ret_ty_conflict, body_calls(&module, callee.func_id))
                .map_err(|why| EntryRefusal::UnnamedCallee(format!("FuncId({k}) `{}`: {why}", callee.def_path)))?;
            exact
        } else { crate::instance_admission::declaration_func_ty(
            &callee.params,
            callee.ret_ty.clone(),
            callee.ret_ty_conflict,
            body_calls(&module, callee.func_id),
        )
        .map_err(|why| {
            EntryRefusal::UnnamedCallee(format!(
                "FuncId({k}) `{}`: its declaration cannot be signed: {why}",
                callee.def_path
            ))
        })? };
        // Trust (trust-ir D1b): a refused table door refuses the entry, never panics.
        let foreign_prototype = func_ty.abi.is_some();
        let ty = module.intern_func_type(func_ty).map_err(|refusal| {
            EntryRefusal::Invalid(format!("FuncId({k}) `{}`: {refusal}", callee.def_path))
        })?;
        let mut declaration = Function::new(callee.func_id, name, ty, BlockId::new(0))
            .with_producer(trust_ir::Producer::TRust);
        if foreign_prototype { declaration.producer = None; }
        declaration.linkage = Linkage::External;
        declaration.calling_conv = callee.abi.calling_conv()
            .map_err(|why| EntryRefusal::Invalid(why.to_string()))?;
        module
            .try_add_function(declaration)
            .map_err(|refusal| EntryRefusal::Invalid(refusal.to_string()))?;
    }
    // 3. Globals: a static is a declaration by its symbol; a body-local global travels with its
    //    initializer.
    let static_declarations = rewrite_globals(&mut module, &c.global_origins, names)?;
    // 4. The target, so the bytes validate standalone (a bodyless external declaration demands a
    //    pinned target, `TargetInfoRequired`).
    module.target_info = Some(names.target_info());
    // 5. Extraction may add or remove no effect (D28 leg 3's analog).
    check_extraction(&c.module, &module)?;
    // 6. Self-contained (the instance lane's rule, plus the static declarations) and valid
    //    standalone.
    entry_is_self_contained(&module, c.callees.len(), &static_declarations)
        .map_err(EntryRefusal::Invalid)?;
    if let Some(first) = trust_ir_build::validate_module(&module).first() {
        return Err(EntryRefusal::Invalid(format!("validate_module: {first:?}")));
    }
    Ok(module)
}

/// D28 leg 3's analog: the entry's body must have the effect shape of the judged per-body
/// function (`effect_conservation::ir_shape`: calls, escaping stores, drops, undefs, asm,
/// suspends, checks). Extraction renames and declares; it may add or remove no effect. PURE.
pub fn check_extraction(judged: &Module, entry: &Module) -> Result<(), EntryRefusal> {
    let (Some(judged_body), Some(entry_body)) = (judged.functions.first(), entry.functions.first())
    else {
        return Err(EntryRefusal::ExtractionNotConserved("a module has no body".to_string()));
    };
    let judged_shape = crate::effect_conservation::ir_shape(judged, judged_body);
    let entry_shape = crate::effect_conservation::ir_shape(entry, entry_body);
    if judged_shape != entry_shape {
        return Err(EntryRefusal::ExtractionNotConserved(format!(
            "the entry's effect shape {entry_shape:?} differs from the judged body's {judged_shape:?}"
        )));
    }
    Ok(())
}

/// Is `entry` SELF-CONTAINED with `n` callee declarations? The instance lane's rule
/// (`instance_admission::instance_module_is_self_contained`: exactly `1 + n` functions with dense
/// ids, `FuncId(0)` the only body, unique names, and trust-ir's dependency census from
/// `FuncId(0)` refusing nothing but the `n` bodyless declarations), with the one admission an
/// entry needs and an instance module never has: a global [`rewrite_globals`] declared for a
/// `static`, whose contents are by design not in the module (the consumer binds the producing
/// crate's static by its symbol). PURE. `Err` names the first violation.
pub fn entry_is_self_contained(
    entry: &Module,
    n: usize,
    static_declarations: &BTreeSet<GlobalId>,
) -> Result<(), String> {
    use trust_ir::function_dependencies::{DependencyRefusalKind, inspect_function_dependencies};
    if entry.functions.len() != n + 1 {
        return Err(format!(
            "{} function(s) where the body plus {n} declaration(s) were expected",
            entry.functions.len()
        ));
    }
    for (position, function) in entry.functions.iter().enumerate() {
        if function.id != FuncId::new(position as u32) {
            return Err(format!(
                "position {position} holds FuncId({}); ids must be dense",
                function.id.index()
            ));
        }
        let bodied = !function.blocks.is_empty();
        if position == 0 && !bodied {
            return Err("FuncId(0) carries no body".to_string());
        }
        if position != 0 && bodied {
            return Err(format!(
                "declaration FuncId({position}) `{}` carries a body",
                function.name
            ));
        }
    }
    let mut names = BTreeSet::new();
    for function in &entry.functions {
        if !names.insert(function.name.as_str()) {
            return Err(format!("two functions are named `{}`", function.name));
        }
    }
    let census = inspect_function_dependencies(entry, FuncId::new(0));
    for refusal in census.refusals() {
        match &refusal.kind {
            DependencyRefusalKind::BodylessFunction(id)
                if (1..=n).contains(&(id.index() as usize)) => {}
            DependencyRefusalKind::MissingGlobalInitializer(g)
                if static_declarations.contains(g) => {}
            other => return Err(format!("dependency census refuses {other:?}")),
        }
    }
    Ok(())
}

/// Rewrite the per-body globals for a module that leaves this crate. PURE given `names`.
///
/// * A global the producer minted for a `static` (`GlobalOrigin::Static`) becomes an `External`
///   declaration named by the static's link symbol, with no initializer: a static has ONE
///   address, so a consumer must bind the producing crate's static, never a private copy of its
///   value (reachability makes a static an inlinable body names exported, design §2.2).
/// * A body-local global (a promoted constant, a string literal, a vtable) must be
///   `Internal`/`Private` WITH its initializer; the consumer re-emits it under a fresh local
///   name, as rustc does with an inlined body's allocations.
pub fn rewrite_globals(
    module: &mut Module,
    origins: &[GlobalOrigin],
    names: &dyn EntryNames,
) -> Result<BTreeSet<GlobalId>, EntryRefusal> {
    if origins.len() != module.globals.len() {
        return Err(EntryRefusal::UnnamedGlobal(format!(
            "{} global origin(s) recorded for {} global(s)",
            origins.len(),
            module.globals.len()
        )));
    }
    let mut static_declarations = BTreeSet::new();
    for (index, (global, origin)) in module.globals.iter_mut().zip(origins).enumerate() {
        match origin {
            GlobalOrigin::Static(def) => {
                static_declarations.insert(GlobalId::new(index as u32));
                let symbol = names.static_symbol(*def).map_err(|why| {
                    EntryRefusal::UnnamedGlobal(format!("`{}`: {why}", global.name))
                })?;
                global.name = symbol;
                global.initializer = None;
                global.linkage = Linkage::External;
            }
            GlobalOrigin::BodyLocal => {
                let local = matches!(global.linkage, Linkage::Internal | Linkage::Private);
                if !local || global.initializer.is_none() {
                    return Err(EntryRefusal::UnnamedGlobal(format!(
                        "`{}`: a body-local global must be internal with an initializer \
                         (linkage {:?}, initializer {})",
                        global.name,
                        global.linkage,
                        if global.initializer.is_some() { "present" } else { "absent" }
                    )));
                }
            }
        }
    }
    Ok(static_declarations)
}

// =============================================================================================
// The template builder (step 6.5.1): pure core
// =============================================================================================

/// Everything about one GENERIC definition's row the template builder decides on, TyCtxt-free.
pub struct TemplateInputs<'a> {
    /// The lane's record for the definition; `None` when it recorded none.
    pub record: Option<&'a TemplateRecord>,
    /// The lane recorded the definition twice.
    pub duplicated: bool,
    /// The lane ran in this session (`-Ztrust-ir-lower-templates`).
    pub capture_on: bool,
    pub clean_origin: bool,
    /// The TEMPLATE's own verdict (`ConservationVerdicts::template_verdict`), never the mainline
    /// one (INC6.5-JUDGE).
    pub verdict: VerdictInput,
    /// The template identity (`def_path_str`, untrimmed). Read only by the abstraction.
    pub identity: String,
}

/// THE TEMPLATE BUILDER: the gates, in the plan's order (§1(d)), then the template. PURE given
/// `names`.
///
/// 1. no record: `template-pending` (`capture off`, or `no template lowering was recorded`); a
///    duplicate record: `not-lowered(..twice)`;
/// 2. `not-a-function`; 3. `clean-origin`;
/// 4. a closure-kind body: `template-unsupported(<kind> body (INC6.5-CLOSURES))`, or, with no
///    template parameter, `template-pending(non-generic <kind> ..)`;
/// 5. the lane's refusals: `template-unsupported`; 6. `not-lowered`; 7. `unsited-panic`;
/// 8. `caller-location` for the body;
/// 9. the TEMPLATE verdict: `conservation-unchecked` or `not-conserved`;
/// 10. [`assemble_template`] (ground callees by symbol with every level-R refusal, the globals,
///     self-containment, the abstraction);
/// 11. `validate_template`, classed by `template_lowering::template_refusal`;
/// 12. the extraction check ([`check_template_extraction`]).
///
/// `Ok` is a template every gate passed; [`template_row`] records it `template-pending(..)`.
pub fn build_template(
    inputs: &TemplateInputs<'_>,
    names: &dyn EntryNames,
) -> Result<trust_ir::template::Template, EntryRefusal> {
    let Some(record) = inputs.record else {
        let why = if inputs.capture_on { TEMPLATE_NOT_RECORDED } else { TEMPLATE_CAPTURE_OFF };
        return Err(EntryRefusal::TemplatePending(why.to_string()));
    };
    if inputs.duplicated {
        return Err(EntryRefusal::DuplicateRecord);
    }
    if record.body_kind != BodyKind::Fn {
        return Err(EntryRefusal::NotAFunctionBody);
    }
    if inputs.clean_origin {
        return Err(EntryRefusal::CleanOrigin);
    }
    let c = match &record.capture {
        Ok(c) => c,
        Err(CaptureRefusal::ClosureKind { kind, generic: true }) => {
            return Err(EntryRefusal::TemplateUnsupported(format!(
                "{kind} body (INC6.5-CLOSURES)"
            )));
        }
        Err(CaptureRefusal::ClosureKind { kind, generic: false }) => {
            return Err(EntryRefusal::TemplatePending(template_non_generic_reason(kind)));
        }
        Err(CaptureRefusal::Lane(labels)) => {
            return Err(EntryRefusal::TemplateUnsupported(labels.join("; ")));
        }
        Err(CaptureRefusal::NotLowered(tags)) => {
            return Err(EntryRefusal::NotLowered(tags.clone()));
        }
        Err(CaptureRefusal::UnsitedPanic(kinds)) => {
            return Err(EntryRefusal::UnsitedPanic(kinds.clone()));
        }
    };
    // Gate 7 again, on the stored module itself: a captured module never carries a reachable
    // unsited check (the capture refused it), and this keeps the order a property of the
    // builder rather than of the capture alone.
    let unsited = c.module.functions.first().map(unsited_checks).unwrap_or_default();
    if !unsited.is_empty() {
        return Err(EntryRefusal::UnsitedPanic(unsited));
    }
    if names.body_requires_caller_location() {
        return Err(EntryRefusal::CallerLocation(
            "the body is #[track_caller]: its symbol takes a hidden &'static Location parameter \
             its trust-ir signature does not have"
                .to_string(),
        ));
    }
    match &inputs.verdict {
        VerdictInput::Unchecked(why) => {
            return Err(EntryRefusal::ConservationUnchecked(why.clone()));
        }
        VerdictInput::Classes(classes) if !classes.is_empty() => {
            return Err(EntryRefusal::NotConserved(classes.clone()));
        }
        VerdictInput::Classes(_) => {}
    }
    // Trust (6.5.4): one source builder, shared with pending inspection. Its S validation,
    // skolem self-containment and complete extraction checks remain after every gate above.
    crate::template_lowering::pending::source_template(c, names, inputs.identity.clone())
}

/// The row a generic definition records in step 6.5.1: [`build_template`]'s refusal, or, for a
/// template every gate passed, `template-pending(validated and conserved; ..6.5.4)`. No byte is
/// written in either case.
pub fn template_row(inputs: &TemplateInputs<'_>, names: &dyn EntryNames) -> EntryRefusal {
    match build_template(inputs, names) {
        Ok(_) => EntryRefusal::TemplatePending(TEMPLATE_VALIDATED.to_string()),
        Err(refusal) => refusal,
    }
}

/// THE TEMPLATE EXTRACTION (beside the untouched level-R [`assemble_entry`]): the judged sentinel
/// module made self-contained, then abstracted. PURE given `names`.
///
/// * The source files, as rustc's metadata spells them (a template is written into rmeta from
///   step 6.5.4; it carries the remapped names a level-R entry carries).
/// * One signed declaration per callee edge, named as [`assemble_entry`] names it
///   ([`EntryNames::callee_symbol`], with every level-R refusal: a havoc edge, a non-Item
///   resolution, `#[track_caller]`). The body keeps no symbol: the abstraction names it
///   `!template_body`, and the host names the instance.
/// * [`rewrite_globals`] (returned: the self-containment rule admits their declarations) and the
///   target.
/// * `template_lowering::abstract_template`.
///
/// The self-containment rule runs in [`build_template`], on the template's skolem instance.
pub fn assemble_template(
    c: &TemplateCandidate,
    names: &dyn EntryNames,
    identity: String,
) -> Result<(trust_ir::template::Template, BTreeSet<GlobalId>), EntryRefusal> {
    if !names.body_abi().is_plain_rust() {
        return Err(EntryRefusal::Invalid("template source calling convention requires an adapter".into()));
    }
    let mut module = c.module.clone();
    if module.functions.len() != 1 || module.functions[0].id != FuncId::new(0) {
        return Err(EntryRefusal::Invalid(format!(
            "the sentinel module holds {} function(s); exactly the body at FuncId(0) was expected",
            module.functions.len()
        )));
    }
    for (index, file) in module.files.iter_mut().enumerate() {
        *file = names.file_name(file).map_err(|why| {
            EntryRefusal::Invalid(format!("source file {index} has no metadata spelling: {why}"))
        })?;
    }
    let mut declared: BTreeSet<String> = BTreeSet::new();
    for (position, callee) in c.callees.iter().enumerate() {
        let k = position + 1;
        if callee.func_id != FuncId::new(k as u32) {
            return Err(EntryRefusal::Invalid(format!(
                "the callee ledger is not dense: position {k} holds FuncId({})",
                callee.func_id.index()
            )));
        }
        let name = names.callee_symbol(k, callee).map_err(|why| match why {
            CalleeNameRefusal::Unnamed(why) => {
                EntryRefusal::UnnamedCallee(format!("FuncId({k}) `{}`: {why}", callee.def_path))
            }
            CalleeNameRefusal::CallerLocation => EntryRefusal::CallerLocation(format!(
                "callee FuncId({k}) `{}` is #[track_caller]: its symbol takes a hidden \
                 &'static Location argument the trust-ir call does not pass",
                callee.def_path
            )),
        })?;
        if name.starts_with('!') || !declared.insert(name.clone()) {
            return Err(EntryRefusal::UnnamedCallee(format!(
                "FuncId({k}) `{}`: `{name}` is reserved or already declared",
                callee.def_path
            )));
        }
        let func_ty = crate::instance_admission::declaration_func_ty(
            &callee.params,
            callee.ret_ty.clone(),
            callee.ret_ty_conflict,
            body_calls(&module, callee.func_id),
        )
        .map_err(|why| {
            EntryRefusal::UnnamedCallee(format!(
                "FuncId({k}) `{}`: its declaration cannot be signed: {why}",
                callee.def_path
            ))
        })?;
        // Trust (trust-ir D1b): a refused table door refuses the template, never panics
        // (`assemble_entry`'s rule).
        let ty = module.intern_func_type(func_ty).map_err(|refusal| {
            EntryRefusal::Invalid(format!("FuncId({k}) `{}`: {refusal}", callee.def_path))
        })?;
        let mut declaration = Function::new(callee.func_id, name, ty, BlockId::new(0))
            .with_producer(trust_ir::Producer::TRust);
        declaration.linkage = Linkage::External;
        declaration.calling_conv = callee.abi.calling_conv()
            .map_err(|why| EntryRefusal::Invalid(why.to_string()))?;
        module
            .try_add_function(declaration)
            .map_err(|refusal| EntryRefusal::Invalid(refusal.to_string()))?;
    }
    let static_declarations = rewrite_globals(&mut module, &c.global_origins, names)?;
    module.target_info = Some(names.target_info());
    let template = crate::template_lowering::abstract_template(&module, &c.facts, identity)?;
    Ok((template, static_declarations))
}

/// THE TEMPLATE EXTRACTION CHECK (INC6.5-JUDGE): the effect census and shape of the template's
/// SKOLEM instance (`trust_ir_build::template::skolem_instance`, every parameter a fresh
/// layout-less struct) must equal the census and shape the template was JUDGED with (the
/// census of the captured sentinel module, recomputed from the same inputs by the same pure
/// rule, `effect_conservation::producer_body`'s). The skolem instance names each ground callee
/// row by its symbol, so the ledger is carried over by symbol. Abstraction renames and declares;
/// it may add or remove no effect. PURE.
pub fn check_template_extraction(
    c: &TemplateCandidate,
    t: &trust_ir::template::Template,
) -> Result<(), EntryRefusal> {
    let skolem = trust_ir_build::template::skolem_instance(t).map_err(|e| {
        EntryRefusal::ExtractionNotConserved(format!(
            "template: the template has no skolem instance: {e}"
        ))
    })?;
    check_template_extraction_on(c, t, &skolem)
}

/// [`check_template_extraction`] against an already built skolem instance of `t`.
fn check_template_extraction_on(
    c: &TemplateCandidate,
    t: &trust_ir::template::Template,
    skolem: &Module,
) -> Result<(), EntryRefusal> {
    use crate::effect_conservation::{census_ledger, ir_census, ir_shape};
    let refused = |why: String| EntryRefusal::ExtractionNotConserved(format!("template: {why}"));
    let judged_body = c
        .module
        .functions
        .first()
        .ok_or_else(|| refused("the judged module has no body".into()))?;
    let (ledger, callee_returns) = census_ledger(&c.callees);
    let degraded: BTreeSet<trust_ir::StructId> =
        c.facts.degraded_structs.iter().map(|i| trust_ir::StructId::new(*i)).collect();
    let judged =
        ir_census(&c.module, judged_body, &ledger, &callee_returns, &degraded, c.facts.lanes);
    let skolem_body = skolem
        .functions
        .first()
        .ok_or_else(|| refused("the skolem instance has no body".into()))?;
    // Ground callee rows by symbol: template FuncId -> skolem FuncId.
    let mut by_symbol: BTreeMap<&str, FuncId> = BTreeMap::new();
    for f in skolem.functions.iter().skip(1) {
        by_symbol.insert(f.name.as_str(), f.id);
    }
    let mut remap: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    for f in t.module.functions.iter().skip(1) {
        let Some(id) = by_symbol.get(f.name.as_str()) else {
            return Err(refused(format!(
                "callee row `{}` is not declared in the skolem instance",
                f.name
            )));
        };
        remap.insert(f.id, *id);
    }
    let remapped = |id: &FuncId| remap.get(id).copied().unwrap_or(*id);
    let skolem_ledger =
        ledger.iter().map(|(id, row)| (remapped(id), row.clone())).collect::<BTreeMap<_, _>>();
    let skolem_returns = callee_returns
        .iter()
        .map(|(id, ty)| (remapped(id), ty.clone()))
        .collect::<BTreeMap<_, _>>();
    let instance =
        ir_census(&skolem, skolem_body, &skolem_ledger, &skolem_returns, &degraded, c.facts.lanes);
    if instance != judged {
        return Err(refused(format!(
            "the skolem instance's effect census differs from the judged census (shapes {:?} \
             and {:?})",
            instance.shape, judged.shape
        )));
    }
    let (judged_shape, instance_shape) =
        (ir_shape(&c.module, judged_body), ir_shape(&skolem, skolem_body));
    if judged_shape != instance_shape {
        return Err(refused(format!(
            "the skolem instance's effect shape {instance_shape:?} differs from the judged \
             body's {judged_shape:?}"
        )));
    }
    Ok(())
}

// =============================================================================================
// The blob (§2.5): framing, digest, evidence
// =============================================================================================

/// The identity an entry is bound to: the producing crate's `StableCrateId` and the definition's
/// `DefPathHash` local half.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EntryBinding {
    pub stable_crate_id: u64,
    pub local_hash: u64,
}

/// Frame an entry with an explicit producing overflow-check mode. The whole-envelope digest
/// binds the header, owner, mode, module digest, module bytes and complete evidence bytes.
/// The module's own stable digest is retained separately; neither digest grants proof authority.
/// Deterministic: every part is a pure function of its inputs. A module the binary writer
/// refuses (trust-ir D1b) has no entry: [`EntryRefusal::Invalid`].
pub fn frame_entry(
    module: &Module,
    binding: EntryBinding,
    overflow_checks: bool,
    evidence: &[u8],
) -> Result<Vec<u8>, EntryRefusal> {
    let bytes = trust_ir::binary::serialize_module(module).map_err(|refusal| {
        EntryRefusal::Invalid(format!("the entry module has no wire image: {refusal}"))
    })?;
    let digest = module.stable_digest();
    let mut payload = Vec::new();
    payload.extend_from_slice(&binding.stable_crate_id.to_le_bytes());
    payload.extend_from_slice(&binding.local_hash.to_le_bytes());
    payload.push(u8::from(overflow_checks));
    payload.extend_from_slice(&digest.bytes);
    payload.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    payload.extend_from_slice(&bytes);
    payload.extend_from_slice(&(evidence.len() as u64).to_le_bytes());
    payload.extend_from_slice(evidence);
    let mut out = Vec::new();
    out.extend_from_slice(ENTRY_MAGIC);
    out.extend_from_slice(&ENTRY_SCHEMA.to_le_bytes());
    out.extend_from_slice(&trust_ir::binary::VERSION.to_le_bytes());
    let content_digest = entry_content_digest(&out, &payload)
        .map_err(|e| EntryRefusal::Invalid(format!("entry envelope: {e}")))?;
    out.extend_from_slice(&content_digest);
    out.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    out.extend_from_slice(&payload);
    Ok(out)
}

fn entry_content_digest(header: &[u8], payload: &[u8]) -> Result<[u8; 32], EntryDecodeError> {
    let len = header
        .len()
        .checked_add(payload.len())
        .and_then(|n| u64::try_from(n).ok())
        .ok_or(EntryDecodeError::LengthOverflow("envelope digest"))?;
    let mut digest =
        trust_ir::proof::ProofDigest::sha256_domain_stream("trust.rmeta.entry-envelope.v1", len);
    digest
        .update(header)
        .and_then(|()| digest.update(payload))
        .and_then(|()| digest.finish())
        .map(|d| d.bytes)
        .map_err(|_| EntryDecodeError::LengthOverflow("envelope digest"))
}

/// A decoded entry, checked: the magic and schema, the producing trust-ir version against this
/// compiler's, exact envelope framing and content digest, then canonical overflow mode and the
/// independent module digest. The caller must separately bind the requested Rust identity,
/// rederive effects and enforce admission. [`decode_entry_for_overflow`] also compares the mode.
#[derive(Debug)]
pub struct DecodedEntry {
    pub binding: EntryBinding,
    pub producer_trust_ir_version: u32,
    /// The actual producing session's overflow-check mode, never inferred from its body.
    pub overflow_checks: bool,
    /// Domain-separated digest of header plus complete owner/mode/module/evidence payload.
    pub content_digest: [u8; 32],
    /// The module's stable digest; its meaning is unchanged from entry schema 4.
    pub digest: [u8; 32],
    pub module: Module,
    pub evidence: Vec<u8>,
}

/// Why an entry did not decode (the consumer's `[upstream-entry](<check>)`, design §5.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryDecodeError {
    Truncated(&'static str),
    Magic,
    Schema(u32),
    EvidenceSchema(u32),
    TrustIrVersion { producer: u32, consumer: u32 },
    Module(String),
    EnvelopeDigest,
    Digest,
    OverflowByte(u8),
    OverflowMode { producer: bool, consumer: bool },
    LengthOverflow(&'static str),
    TrailingBytes(usize),
}

impl std::fmt::Display for EntryDecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EntryDecodeError::Truncated(what) => write!(f, "truncated({what})"),
            EntryDecodeError::Magic => write!(f, "magic"),
            EntryDecodeError::Schema(s) => write!(f, "schema({s}, expected {ENTRY_SCHEMA})"),
            EntryDecodeError::EvidenceSchema(s) => {
                write!(f, "evidence-schema({s}, expected {EVIDENCE_SCHEMA})")
            }
            EntryDecodeError::TrustIrVersion { producer, consumer } => {
                write!(f, "trust-ir-version(producer {producer}, consumer {consumer})")
            }
            EntryDecodeError::Module(e) => write!(f, "module({e})"),
            EntryDecodeError::EnvelopeDigest => write!(f, "envelope-digest"),
            EntryDecodeError::Digest => write!(f, "digest"),
            EntryDecodeError::OverflowByte(byte) => write!(f, "overflow-check-byte({byte})"),
            EntryDecodeError::OverflowMode { producer, consumer } => {
                write!(f, "overflow-check-mode(producer {producer}, consumer {consumer})")
            }
            EntryDecodeError::LengthOverflow(what) => write!(f, "length-overflow({what})"),
            EntryDecodeError::TrailingBytes(n) => write!(f, "trailing({n} bytes)"),
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize, what: &'static str) -> Result<&'a [u8], EntryDecodeError> {
        let end = self.at.checked_add(n).ok_or(EntryDecodeError::Truncated(what))?;
        let slice = self.bytes.get(self.at..end).ok_or(EntryDecodeError::Truncated(what))?;
        self.at = end;
        Ok(slice)
    }
    fn u32(&mut self, what: &'static str) -> Result<u32, EntryDecodeError> {
        Ok(u32::from_le_bytes(self.take(4, what)?.try_into().unwrap()))
    }
    fn u64(&mut self, what: &'static str) -> Result<u64, EntryDecodeError> {
        Ok(u64::from_le_bytes(self.take(8, what)?.try_into().unwrap()))
    }
    fn part(&mut self, what: &'static str) -> Result<&'a [u8], EntryDecodeError> {
        let len =
            usize::try_from(self.u64(what)?).map_err(|_| EntryDecodeError::LengthOverflow(what))?;
        self.take(len, what)
    }
}

/// Decode and check an entry ([`DecodedEntry`]).
pub fn decode_entry(bytes: &[u8]) -> Result<DecodedEntry, EntryDecodeError> {
    let mut r = Reader { bytes, at: 0 };
    if r.take(8, "magic")? != ENTRY_MAGIC {
        return Err(EntryDecodeError::Magic);
    }
    let schema = r.u32("schema")?;
    if schema != ENTRY_SCHEMA {
        return Err(EntryDecodeError::Schema(schema));
    }
    let producer = r.u32("trust-ir version")?;
    if producer != trust_ir::binary::VERSION {
        return Err(EntryDecodeError::TrustIrVersion {
            producer,
            consumer: trust_ir::binary::VERSION,
        });
    }
    let content_digest: [u8; 32] = r.take(32, "envelope digest")?.try_into().unwrap();
    let payload = r.part("entry payload")?;
    if r.at != bytes.len() {
        return Err(EntryDecodeError::TrailingBytes(bytes.len() - r.at));
    }
    if entry_content_digest(&bytes[..16], payload)? != content_digest {
        return Err(EntryDecodeError::EnvelopeDigest);
    }
    let mut r = Reader { bytes: payload, at: 0 };
    let binding =
        EntryBinding { stable_crate_id: r.u64("binding")?, local_hash: r.u64("binding")? };
    let overflow_checks = match r.take(1, "overflow-check mode")?[0] {
        0 => false,
        1 => true,
        byte => return Err(EntryDecodeError::OverflowByte(byte)),
    };
    let digest: [u8; 32] = r.take(32, "module digest")?.try_into().unwrap();
    let module_bytes = r.part("module")?;
    let evidence = r.part("evidence")?.to_vec();
    if r.at != payload.len() {
        return Err(EntryDecodeError::TrailingBytes(payload.len() - r.at));
    }
    let module = trust_ir::binary::deserialize_module(module_bytes)
        .map_err(|e| EntryDecodeError::Module(format!("{e:?}")))?;
    if module.stable_digest().bytes != digest {
        return Err(EntryDecodeError::Digest);
    }
    Ok(DecodedEntry {
        binding,
        producer_trust_ir_version: producer,
        overflow_checks,
        content_digest,
        digest,
        module,
        evidence,
    })
}

/// Decode real producer bytes and compare an independently supplied consumer overflow setting.
/// Matching settings grant no admission: identity, target, signatures and effects remain owed.
pub fn decode_entry_for_overflow(
    bytes: &[u8],
    consumer_overflow_checks: bool,
) -> Result<DecodedEntry, EntryDecodeError> {
    let entry = decode_entry(bytes)?;
    if entry.overflow_checks != consumer_overflow_checks {
        return Err(EntryDecodeError::OverflowMode {
            producer: entry.overflow_checks,
            consumer: consumer_overflow_checks,
        });
    }
    Ok(entry)
}

// =============================================================================================
// The evidence section (§2.4)
// =============================================================================================

/// A definition's stable identity in the evidence: its `DefPathHash` halves.
pub type StableDef = (u64, u64);

/// The evidence's call identity: what a MIR call names, made session-independent. `site` is the
/// injective typed token of the site's `(def, args)` (`lineage::ConcreteCalleeKey`, whose
/// definition is a `DefPathHash`), so two sites compare equal exactly when their def and their
/// encodable args do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvidenceCall {
    pub ids: Vec<StableDef>,
    pub site: Option<String>,
    pub equivalence: Option<u8>,
    pub enum_result: bool,
    pub enum_args: Vec<bool>,
}

/// One effect of the built MIR's census, session-independent. `span` is a body-local ordinal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvidenceEffectKind {
    Call(EvidenceCall),
    IndirectCall,
    /// The store root: `Arg(i)` as `0..`, `Static` as `u32::MAX - 1`, `Indirect` as `u32::MAX`.
    Store(u32),
    Drop {
        destructor: bool,
    },
    Assert(u8),
    Asm {
        empty_noreturn: bool,
    },
    Yield,
}

/// One live drop the drop oracle elaborated (`drop_oracle::OracleDrop`), session-independent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvidenceOracleDrop {
    pub block: u32,
    pub identity: (u8, u32),
    pub ty: u128,
    pub span: u32,
    /// `None` dead, else the live style (0 static, 1 conditional, 2 open).
    pub style: Option<u8>,
    pub projected: bool,
    pub destructor: bool,
}

/// One live drop of the producer's claim (`drops::DropKey`), session-independent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvidenceDropKey {
    pub identity: (u8, u32),
    pub ty: u128,
    pub span: u32,
    pub style: u8,
}

/// One callee ledger row (the effect census's `LedgerRow`), session-independent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvidenceLedgerRow {
    pub func_id: u32,
    pub ids: Vec<StableDef>,
    pub site: Option<String>,
}

/// The decoded evidence of one entry: every input of the D28 judgement of the body
/// (`effect_conservation::judge` over `ir_census`) that the entry's module does not itself carry.
///
/// From the built MIR's census: `effects` … `drop_dead_blocks`. From the producer:
/// `drop_claim`, `ledger` (`ir_census`'s `ledger`), `degraded_structs` (its `degraded`) and the
/// two lanes (its `lanes`). From the producing session as a whole: `collapsed_enum_types`, the
/// part of `judge`'s session-wide collapsed set this body's `enum_types` meets. `ir_census`'s
/// remaining input, `callee_returns`, is in the module: each callee declaration is signed with
/// exactly the ledger's result type (`instance_admission::declaration_func_ty`), which
/// `ir_census` reads through its declaration fallback when given no map.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Evidence {
    pub effects: Vec<(EvidenceEffectKind, u32)>,
    pub arg_count: u32,
    pub arg_enum: Vec<bool>,
    pub ret_enum: bool,
    pub store_values: Vec<(u32, u8)>,
    /// Schema 4: (original effect ordinal, exact entry argument). These refine
    /// only coarse Indirect stores and require aligned MIR/IR signatures.
    pub exact_store_args: Vec<(u64, u32)>,
    pub enum_types: Vec<u128>,
    pub drop_oracle: Option<Vec<EvidenceOracleDrop>>,
    pub drop_dead_blocks: Vec<u32>,
    pub drop_claim: Option<(Vec<EvidenceDropKey>, u64, Vec<bool>)>,
    pub ledger: Vec<EvidenceLedgerRow>,
    /// Schema 2: `enum_types` ∩ the producing session's collapsed enum types.
    pub collapsed_enum_types: Vec<u128>,
    /// Schema 2: the degraded struct rows, as `StructId` indices of the entry's module.
    pub degraded_structs: Vec<u32>,
    /// Schema 2: the producer's union and enum-parameter placeholder lanes.
    pub union_lane: bool,
    pub enum_param_lane: bool,
}

/// How the evidence encoder spells session-dependent identities. Production answers from the
/// `TyCtxt` ([`RustcNames`]); unit tests with fixtures.
pub trait EvidenceSpelling {
    fn def(&self, def: DefId) -> StableDef;
    fn site(&self, def: DefId, args: &[crate::SiteArg]) -> String;
}

/// Body-local span ordinals, by first appearance (census effects, then the drop oracle, then
/// the claim). Two keys that name the same `Span` get the same ordinal, which is all the drop
/// leg compares.
#[derive(Default)]
struct SpanOrdinals {
    seen: Vec<Span>,
}

impl SpanOrdinals {
    fn of(&mut self, span: Span) -> u32 {
        if let Some(i) = self.seen.iter().position(|s| *s == span) {
            return i as u32;
        }
        self.seen.push(span);
        (self.seen.len() - 1) as u32
    }
}

fn mem_root_code(root: crate::effect_conservation::MemRoot) -> u32 {
    use crate::effect_conservation::MemRoot;
    match root {
        MemRoot::Arg(i) => i,
        MemRoot::Static => u32::MAX - 1,
        MemRoot::Indirect => u32::MAX,
    }
}

fn identity_code(identity: crate::drops::DropIdentity) -> (u8, u32) {
    use crate::drops::DropIdentity;
    match identity {
        DropIdentity::Param(i) => (0, i),
        DropIdentity::Var(i) => (1, i),
        DropIdentity::Other => (2, 0),
    }
}

fn style_code(style: crate::drops::LiveStyle) -> u8 {
    use crate::drops::LiveStyle;
    match style {
        LiveStyle::Static => 0,
        LiveStyle::Conditional => 1,
        LiveStyle::Open => 2,
    }
}

fn assert_code(class: AssertClass) -> u8 {
    match class {
        AssertClass::Bounds => 0,
        AssertClass::Overflow => 1,
        AssertClass::Shift => 2,
        AssertClass::DivZero => 3,
        AssertClass::Other => 4,
    }
}

fn equivalence_code(e: crate::effect_conservation::Equivalence) -> u8 {
    use crate::effect_conservation::Equivalence;
    match e {
        Equivalence::PureIntrinsic => 0,
        Equivalence::SliceLen => 1,
        Equivalence::RangeIntoIter => 2,
        Equivalence::RangeNext => 3,
        Equivalence::OptionDiscriminant => 4,
        Equivalence::TryBranch => 5,
        Equivalence::TryResidual => 6,
        Equivalence::BuiltinEq => 7,
        Equivalence::FormatArguments => 8,
        Equivalence::BoolFromInteger => 9,
    }
}

fn store_value_code(v: StoreValue) -> u8 {
    match v {
        StoreValue::ValuedEnum => 0,
        StoreValue::BoolOrUnit => 1,
        StoreValue::Other => 2,
    }
}

/// Convert the retained evidence to its session-independent form. PURE given `spell`.
pub fn evidence_of(
    retained: &RetainedEvidence,
    callees: &[CalleeRef],
    spell: &dyn EvidenceSpelling,
) -> Evidence {
    let mut spans = SpanOrdinals::default();
    let census = &retained.census;
    let effects = census
        .effects
        .iter()
        .map(|effect| {
            let kind = match &effect.kind {
                MirEffectKind::Call { ids, site_args, equivalence, enum_result, enum_args } => {
                    EvidenceEffectKind::Call(EvidenceCall {
                        ids: ids.iter().map(|d| spell.def(*d)).collect(),
                        site: match (ids.first(), site_args) {
                            (Some(first), Some(args)) => Some(spell.site(*first, args)),
                            _ => None,
                        },
                        equivalence: equivalence.map(equivalence_code),
                        enum_result: *enum_result,
                        enum_args: enum_args.clone(),
                    })
                }
                MirEffectKind::IndirectCall => EvidenceEffectKind::IndirectCall,
                MirEffectKind::Store(root) => EvidenceEffectKind::Store(mem_root_code(*root)),
                MirEffectKind::Drop { destructor } => {
                    EvidenceEffectKind::Drop { destructor: *destructor }
                }
                MirEffectKind::Assert(class) => EvidenceEffectKind::Assert(assert_code(*class)),
                MirEffectKind::Asm { empty_noreturn } => {
                    EvidenceEffectKind::Asm { empty_noreturn: *empty_noreturn }
                }
                MirEffectKind::Yield => EvidenceEffectKind::Yield,
            };
            (kind, spans.of(effect.span))
        })
        .collect();
    let drop_oracle = census.drop_oracle.as_ref().map(|drops| {
        drops
            .iter()
            .map(|(d, destructor)| EvidenceOracleDrop {
                block: d.block.as_u32(),
                identity: identity_code(d.identity),
                ty: d.ty,
                span: spans.of(d.span),
                style: d.style.map(style_code),
                projected: d.projected,
                destructor: *destructor,
            })
            .collect()
    });
    let drop_claim = retained.drop_claim.as_ref().map(|claim| {
        let live = claim
            .live
            .iter()
            .map(|k| EvidenceDropKey {
                identity: identity_code(k.identity),
                ty: k.ty,
                span: spans.of(k.span),
                style: style_code(k.style),
            })
            .collect();
        (live, claim.emitted as u64, claim.destructor.clone())
    });
    let ledger = callees
        .iter()
        .map(|c| {
            let mut ids: Vec<StableDef> = Vec::new();
            for d in [c.site_def_id, c.def_id] {
                let s = spell.def(d);
                if !ids.contains(&s) {
                    ids.push(s);
                }
            }
            EvidenceLedgerRow {
                func_id: c.func_id.index(),
                ids,
                site: c.site_args.as_ref().map(|args| spell.site(c.site_def_id, args)),
            }
        })
        .collect();
    Evidence {
        effects,
        arg_count: census.arg_count,
        arg_enum: census.arg_enum.clone(),
        ret_enum: census.ret_enum,
        store_values: census
            .store_values
            .iter()
            .map(|(root, value)| (mem_root_code(*root), store_value_code(*value)))
            .collect(),
        exact_store_args: census
            .exact_store_args
            .iter()
            .map(|(effect, arg)| (*effect as u64, *arg))
            .collect(),
        enum_types: census.enum_types.iter().copied().collect(),
        drop_oracle,
        drop_dead_blocks: census.drop_dead_blocks.iter().copied().collect(),
        drop_claim,
        ledger,
        collapsed_enum_types: retained.collapsed_enum_types.clone(),
        degraded_structs: retained.degraded_structs.clone(),
        union_lane: retained.union_lane,
        enum_param_lane: retained.enum_param_lane,
    }
}

/// A little-endian, length-prefixed writer: the evidence wire format.
#[derive(Default)]
struct W(Vec<u8>);

impl W {
    fn u8(&mut self, v: u8) {
        self.0.push(v);
    }
    fn bool(&mut self, v: bool) {
        self.0.push(v as u8);
    }
    fn u32(&mut self, v: u32) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn u128(&mut self, v: u128) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn len(&mut self, n: usize) {
        self.u64(n as u64);
    }
    fn str(&mut self, s: &str) {
        self.len(s.len());
        self.0.extend_from_slice(s.as_bytes());
    }
    fn def(&mut self, d: StableDef) {
        self.u64(d.0);
        self.u64(d.1);
    }
    fn bools(&mut self, v: &[bool]) {
        self.len(v.len());
        for b in v {
            self.bool(*b);
        }
    }
    fn opt_str(&mut self, s: &Option<String>) {
        match s {
            None => self.u8(0),
            Some(s) => {
                self.u8(1);
                self.str(s);
            }
        }
    }
}

/// Encode the evidence section: magic, schema, payload.
pub fn encode_evidence(e: &Evidence) -> Vec<u8> {
    let mut w = W::default();
    w.0.extend_from_slice(EVIDENCE_MAGIC);
    w.u32(EVIDENCE_SCHEMA);
    w.len(e.effects.len());
    for (kind, span) in &e.effects {
        match kind {
            EvidenceEffectKind::Call(c) => {
                w.u8(0);
                w.len(c.ids.len());
                for d in &c.ids {
                    w.def(*d);
                }
                w.opt_str(&c.site);
                match c.equivalence {
                    None => w.u8(0xff),
                    Some(code) => w.u8(code),
                }
                w.bool(c.enum_result);
                w.bools(&c.enum_args);
            }
            EvidenceEffectKind::IndirectCall => w.u8(1),
            EvidenceEffectKind::Store(root) => {
                w.u8(2);
                w.u32(*root);
            }
            EvidenceEffectKind::Drop { destructor } => {
                w.u8(3);
                w.bool(*destructor);
            }
            EvidenceEffectKind::Assert(class) => {
                w.u8(4);
                w.u8(*class);
            }
            EvidenceEffectKind::Asm { empty_noreturn } => {
                w.u8(5);
                w.bool(*empty_noreturn);
            }
            EvidenceEffectKind::Yield => w.u8(6),
        }
        w.u32(*span);
    }
    w.u32(e.arg_count);
    w.bools(&e.arg_enum);
    w.bool(e.ret_enum);
    w.len(e.store_values.len());
    for (root, value) in &e.store_values {
        w.u32(*root);
        w.u8(*value);
    }
    w.len(e.enum_types.len());
    for t in &e.enum_types {
        w.u128(*t);
    }
    match &e.drop_oracle {
        None => w.u8(0),
        Some(drops) => {
            w.u8(1);
            w.len(drops.len());
            for d in drops {
                w.u32(d.block);
                w.u8(d.identity.0);
                w.u32(d.identity.1);
                w.u128(d.ty);
                w.u32(d.span);
                match d.style {
                    None => w.u8(0xff),
                    Some(s) => w.u8(s),
                }
                w.bool(d.projected);
                w.bool(d.destructor);
            }
        }
    }
    w.len(e.drop_dead_blocks.len());
    for b in &e.drop_dead_blocks {
        w.u32(*b);
    }
    match &e.drop_claim {
        None => w.u8(0),
        Some((live, emitted, destructor)) => {
            w.u8(1);
            w.len(live.len());
            for k in live {
                w.u8(k.identity.0);
                w.u32(k.identity.1);
                w.u128(k.ty);
                w.u32(k.span);
                w.u8(k.style);
            }
            w.u64(*emitted);
            w.bools(destructor);
        }
    }
    w.len(e.ledger.len());
    for row in &e.ledger {
        w.u32(row.func_id);
        w.len(row.ids.len());
        for d in &row.ids {
            w.def(*d);
        }
        w.opt_str(&row.site);
    }
    w.len(e.collapsed_enum_types.len());
    for t in &e.collapsed_enum_types {
        w.u128(*t);
    }
    w.len(e.degraded_structs.len());
    for s in &e.degraded_structs {
        w.u32(*s);
    }
    w.bool(e.union_lane);
    w.bool(e.enum_param_lane);
    w.len(e.exact_store_args.len());
    for (effect, argument) in &e.exact_store_args {
        w.u64(*effect);
        w.u32(*argument);
    }
    w.0
}

/// The evidence reader. Every length is bounded by the bytes that remain, so a corrupt length
/// fails as `Truncated`, never as an allocation of its claimed size.
struct E<'a>(Reader<'a>);

impl<'a> E<'a> {
    fn u8(&mut self) -> Result<u8, EntryDecodeError> {
        Ok(self.0.take(1, "evidence")?[0])
    }
    fn bool(&mut self) -> Result<bool, EntryDecodeError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(EntryDecodeError::Module("evidence: a bool is not 0 or 1".to_string())),
        }
    }
    fn u32(&mut self) -> Result<u32, EntryDecodeError> {
        self.0.u32("evidence")
    }
    fn u64(&mut self) -> Result<u64, EntryDecodeError> {
        self.0.u64("evidence")
    }
    fn u128(&mut self) -> Result<u128, EntryDecodeError> {
        Ok(u128::from_le_bytes(self.0.take(16, "evidence")?.try_into().unwrap()))
    }
    fn len(&mut self) -> Result<usize, EntryDecodeError> {
        let n = self.u64()?;
        if n > (self.0.bytes.len() - self.0.at) as u64 {
            return Err(EntryDecodeError::Truncated("evidence length"));
        }
        Ok(n as usize)
    }
    fn str(&mut self) -> Result<String, EntryDecodeError> {
        let n = self.len()?;
        let bytes = self.0.take(n, "evidence string")?;
        String::from_utf8(bytes.to_vec())
            .map_err(|_| EntryDecodeError::Module("evidence: a string is not UTF-8".to_string()))
    }
    fn def(&mut self) -> Result<StableDef, EntryDecodeError> {
        Ok((self.u64()?, self.u64()?))
    }
    fn bools(&mut self) -> Result<Vec<bool>, EntryDecodeError> {
        let n = self.len()?;
        (0..n).map(|_| self.bool()).collect()
    }
    fn opt_str(&mut self) -> Result<Option<String>, EntryDecodeError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.str()?)),
            _ => Err(EntryDecodeError::Module("evidence: an option tag is not 0 or 1".to_string())),
        }
    }
}

/// Decode an evidence section ([`encode_evidence`]'s inverse).
pub fn decode_evidence(bytes: &[u8]) -> Result<Evidence, EntryDecodeError> {
    let mut r = E(Reader { bytes, at: 0 });
    if r.0.take(8, "evidence magic")? != EVIDENCE_MAGIC {
        return Err(EntryDecodeError::Magic);
    }
    let schema = r.u32()?;
    if schema != EVIDENCE_SCHEMA {
        return Err(EntryDecodeError::EvidenceSchema(schema));
    }
    let bad = |what: &str| EntryDecodeError::Module(format!("evidence: {what}"));
    let mut e = Evidence::default();
    let n = r.len()?;
    for _ in 0..n {
        let kind = match r.u8()? {
            0 => {
                let ids = (0..r.len()?).map(|_| r.def()).collect::<Result<Vec<_>, _>>()?;
                let site = r.opt_str()?;
                let equivalence = match r.u8()? {
                    0xff => None,
                    code if code <= 9 => Some(code),
                    _ => return Err(bad("an equivalence code is out of range")),
                };
                let enum_result = r.bool()?;
                let enum_args = r.bools()?;
                EvidenceEffectKind::Call(EvidenceCall {
                    ids,
                    site,
                    equivalence,
                    enum_result,
                    enum_args,
                })
            }
            1 => EvidenceEffectKind::IndirectCall,
            2 => EvidenceEffectKind::Store(r.u32()?),
            3 => EvidenceEffectKind::Drop { destructor: r.bool()? },
            4 => match r.u8()? {
                class if class <= 4 => EvidenceEffectKind::Assert(class),
                _ => return Err(bad("an assert class is out of range")),
            },
            5 => EvidenceEffectKind::Asm { empty_noreturn: r.bool()? },
            6 => EvidenceEffectKind::Yield,
            _ => return Err(bad("an unknown effect tag")),
        };
        let span = r.u32()?;
        e.effects.push((kind, span));
    }
    e.arg_count = r.u32()?;
    e.arg_enum = r.bools()?;
    e.ret_enum = r.bool()?;
    for _ in 0..r.len()? {
        let root = r.u32()?;
        let value = r.u8()?;
        if value > 2 {
            return Err(bad("a store value code is out of range"));
        }
        e.store_values.push((root, value));
    }
    for _ in 0..r.len()? {
        e.enum_types.push(r.u128()?);
    }
    e.drop_oracle = match r.u8()? {
        0 => None,
        1 => {
            let mut drops = Vec::new();
            for _ in 0..r.len()? {
                let block = r.u32()?;
                let identity = (r.u8()?, r.u32()?);
                let ty = r.u128()?;
                let span = r.u32()?;
                let style = match r.u8()? {
                    0xff => None,
                    s if s <= 2 => Some(s),
                    _ => return Err(bad("a drop style is out of range")),
                };
                let projected = r.bool()?;
                let destructor = r.bool()?;
                drops.push(EvidenceOracleDrop {
                    block,
                    identity,
                    ty,
                    span,
                    style,
                    projected,
                    destructor,
                });
            }
            Some(drops)
        }
        _ => return Err(bad("an option tag is not 0 or 1")),
    };
    for _ in 0..r.len()? {
        e.drop_dead_blocks.push(r.u32()?);
    }
    e.drop_claim = match r.u8()? {
        0 => None,
        1 => {
            let mut live = Vec::new();
            for _ in 0..r.len()? {
                let identity = (r.u8()?, r.u32()?);
                let ty = r.u128()?;
                let span = r.u32()?;
                let style = r.u8()?;
                if style > 2 {
                    return Err(bad("a drop style is out of range"));
                }
                live.push(EvidenceDropKey { identity, ty, span, style });
            }
            let emitted = r.u64()?;
            let destructor = r.bools()?;
            Some((live, emitted, destructor))
        }
        _ => return Err(bad("an option tag is not 0 or 1")),
    };
    for _ in 0..r.len()? {
        let func_id = r.u32()?;
        let ids = (0..r.len()?).map(|_| r.def()).collect::<Result<Vec<_>, _>>()?;
        let site = r.opt_str()?;
        e.ledger.push(EvidenceLedgerRow { func_id, ids, site });
    }
    for _ in 0..r.len()? {
        e.collapsed_enum_types.push(r.u128()?);
    }
    for _ in 0..r.len()? {
        e.degraded_structs.push(r.u32()?);
    }
    e.union_lane = r.bool()?;
    e.enum_param_lane = r.bool()?;
    let mut previous = None;
    for _ in 0..r.len()? {
        let effect = r.u64()?;
        let argument = r.u32()?;
        let index = usize::try_from(effect)
            .map_err(|_| bad("an exact store effect index is out of range"))?;
        if previous.is_some_and(|old| effect <= old)
            || argument >= e.arg_count
            || !matches!(e.effects.get(index), Some((EvidenceEffectKind::Store(root), _)) if *root == u32::MAX)
        {
            return Err(bad("an exact store argument is invalid"));
        }
        previous = Some(effect);
        e.exact_store_args.push((effect, argument));
    }
    if !e.exact_store_args.is_empty() {
        let store_roots: Vec<_> = e
            .effects
            .iter()
            .filter_map(|(kind, _)| match kind {
                EvidenceEffectKind::Store(root) => Some(*root),
                _ => None,
            })
            .collect();
        if store_roots.len() != e.store_values.len()
            || !store_roots
                .iter()
                .zip(&e.store_values)
                .all(|(root, (value_root, _))| root == value_root)
        {
            return Err(bad("exact store values are not bound to the original store effects"));
        }
    }
    if r.0.at != bytes.len() {
        return Err(EntryDecodeError::TrailingBytes(bytes.len() - r.0.at));
    }
    Ok(e)
}

// =============================================================================================
// The rustc half: names, spelling, and the query provider
// =============================================================================================

/// [`EntryNames`] and [`EvidenceSpelling`] answered by rustc.
struct RustcNames<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    /// [`metadata_file_names`], built once per session.
    files: &'a BTreeMap<String, Option<String>>,
}

/// Every source file of the session, keyed by the rendering the producer interns
/// (`prefer_remapped_unconditionally`, `LowerCx::to_source_span` since WS5.9; the two
/// renderings are one string without `--remap-path-prefix`), mapped to the rendering a
/// consumer of this crate's metadata sees for it: the file name after
/// `RealFileName::update_for_crate_metadata` (the remapped name alone when `--remap-path-prefix`
/// remapped every scope, the local name too only when it remapped some, exactly what
/// `EncodeContext::encode_source_map` writes), rendered the same way. `None` when two files share
/// the interned rendering but not a metadata one.
fn metadata_file_names(tcx: TyCtxt<'_>) -> BTreeMap<String, Option<String>> {
    use rustc_span::FileName;
    let mut out: BTreeMap<String, Option<String>> = BTreeMap::new();
    for file in tcx.sess.source_map().files().iter() {
        // Keyed as `LowerCx::to_source_span` interns. A local-rendering key found no file under
        // `--remap-path-prefix`, and every entry of a remapped build was refused `invalid`
        // (`tests/run-make/trust-ir-rmeta-entry-roundtrip`, measured on the 1.101 stage 1).
        let interned = file.name.prefer_remapped_unconditionally().to_string();
        let exported = match &file.name {
            FileName::Real(real) => {
                let mut real = real.clone();
                real.update_for_crate_metadata();
                FileName::Real(real).prefer_local_unconditionally().to_string()
            }
            other => other.prefer_local_unconditionally().to_string(),
        };
        match out.get(&interned) {
            None => {
                out.insert(interned, Some(exported));
            }
            Some(Some(previous)) if *previous == exported => {}
            Some(_) => {
                out.insert(interned, None);
            }
        }
    }
    out
}

impl<'tcx, 'a> RustcNames<'tcx, 'a> {
    /// The instance whose code is this definition's body: `Item(def)` at its identity args
    /// (lifetimes erased) — for a closure, the args of its own closure type.
    fn body_instance(&self) -> Result<ty::Instance<'tcx>, String> {
        let tcx = self.tcx;
        let def_id = self.def.to_def_id();
        let args = match tcx.def_kind(def_id) {
            rustc_hir::def::DefKind::Closure => {
                match tcx.type_of(def_id).instantiate_identity().skip_normalization().kind() {
                    ty::Closure(_, args) => *args,
                    other => return Err(format!("a closure definition of type kind {other:?}")),
                }
            }
            _ => ty::GenericArgs::identity_for_item(tcx, def_id),
        };
        let args = tcx.erase_and_anonymize_regions(args);
        if args.has_non_region_param() || args.has_infer() {
            return Err("the body's instance args are not concrete".to_string());
        }
        Ok(ty::Instance::new_raw(def_id, args))
    }
}

/// An instance as a refusal reason spells it: in FULL (`with_no_trimmed_paths`). A reason is
/// recorded in sessions that may emit no diagnostic at all (bootstrap and targo set
/// `TRUST_VANILLA_ANNOUNCED`, which silences the one note an unverified build prints), and a
/// trimmed path computed in such a session is an internal compiler error when the session ends
/// (`trimmed_def_paths` sets `must_produce_diag`). Before the 2026-10-05 review's residual fixes
/// every library whose non-generic body called an intrinsic, built with the producer on and no
/// diagnostic, ended in that ICE (`tests/run-make/trust-ir-rmeta-entry-rederivation`).
struct UntrimmedInstance<'tcx>(ty::Instance<'tcx>);

impl std::fmt::Display for UntrimmedInstance<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        rustc_middle::ty::print::with_no_trimmed_paths!(std::fmt::Display::fmt(&self.0, f))
    }
}

/// Trust (1.101): `tcx.symbol_name` debug-asserts against always-const fns —
/// they are comptime-only and have no link symbol. Refuse with the reason
/// instead of asking (the entry/callee stays unnamed, fail-closed).
fn symbol_of_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<String, String> {
    let def_id = instance.def_id();
    if matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) && matches!(tcx.constness(def_id), rustc_hir::Constness::Const { always: true })
    {
        return Err(
            "the definition is an always-const fn, which is comptime-only and has no link symbol"
                .to_string(),
        );
    }
    Ok(tcx.symbol_name(instance).name.to_string())
}

impl<'tcx, 'a> EntryNames for RustcNames<'tcx, 'a> {
    fn foreign_signature(&self, callee: &CalleeRef) -> Option<trust_ir::FuncTy> {
        crate::foreign_signature::read(self.tcx, callee)
    }
    fn body_symbol(&self) -> Result<String, String> {
        symbol_of_instance(self.tcx, self.body_instance()?)
    }

    /// `InstanceKind::Item(def).requires_caller_location`: the body's `#[track_caller]`
    /// attribute, as codegen reads it to add the hidden parameter.
    fn body_requires_caller_location(&self) -> bool {
        ty::InstanceKind::Item(self.def.to_def_id()).requires_caller_location(self.tcx)
    }

    fn file_name(&self, local: &str) -> Result<String, String> {
        match self.files.get(local) {
            Some(Some(name)) => Ok(name.clone()),
            Some(None) => {
                Err("two source files share its local name and differ in metadata".to_string())
            }
            None => Err("the session's source map names no such file".to_string()),
        }
    }

    /// The shared source query is also used by the body/instance/declaration producer.
    fn body_abi(&self) -> crate::calling_convention::FunctionAbi {
        crate::calling_convention::FunctionAbi::of_definition(self.tcx, self.def.to_def_id())
    }

    /// RE-DERIVED, NOT TRUSTED — `instance_admission::decide_edge`'s rule for a body with no
    /// generic args: the raw call site `FnDef(site_def, site_args)` is resolved as codegen
    /// resolves a callee operand, at `TypingEnv::fully_monomorphized()`, and must be exactly
    /// `Item(def)` at the args the ledger's concrete key names. A havoc edge, an intrinsic, a
    /// virtual call, a shim, a reify edge and a self edge have no symbol to link; a
    /// `#[track_caller]` callee has one whose ABI the trust-ir call does not match.
    fn callee_symbol(&self, _k: usize, callee: &CalleeRef) -> Result<String, CalleeNameRefusal> {
        let tcx = self.tcx;
        let unnamed = |why: String| CalleeNameRefusal::Unnamed(why);
        let Some(key) = &callee.concrete_key else {
            return Err(unnamed("a havoc edge: the producer resolved no concrete instance".into()));
        };
        let Some(site_args) = &callee.site_args else {
            return Err(unnamed("its call site's args are not encodable".into()));
        };
        let Some(args) = crate::to_mir::rebuild_site_args(tcx, site_args) else {
            return Err(unnamed("its call site's args do not rebuild".into()));
        };
        let typing_env = ty::TypingEnv::fully_monomorphized();
        if args.has_non_region_param() || args.has_infer() {
            return Err(unnamed("its call site's args are not concrete".into()));
        }
        let resolved = match ty::Instance::try_resolve(tcx, typing_env, callee.site_def_id, args) {
            Ok(Some(j)) => j,
            Ok(None) | Err(_) => return Err(unnamed("its call site does not resolve".into())),
        };
        // The facts, then the decision (`judge_rederived_callee`, unit-tested). Nothing past the
        // first fact is computed for an instance that is not the ledger's item.
        let is_ledger_item = resolved.def == ty::InstanceKind::Item(callee.def_id);
        let shown = UntrimmedInstance(resolved);
        let rederived = RederivedCallee {
            resolved: &shown,
            is_ledger_item,
            key: is_ledger_item.then(|| crate::encode_site_args(tcx, resolved.args)).flatten().map(
                |resolved_args| {
                    crate::lineage::ConcreteCalleeKey::from_site_args(
                        tcx,
                        resolved.def_id(),
                        crate::lineage::ConcreteInstanceKind::Item,
                        &resolved_args,
                    )
                },
            ),
            is_self: is_ledger_item && self.body_instance().ok() == Some(resolved),
            requires_caller_location: is_ledger_item && resolved.def.requires_caller_location(tcx),
        };
        judge_rederived_callee(key, &rederived)?;
        symbol_of_instance(tcx, resolved)
            .map_err(|why| unnamed(format!("its resolved instance has no link symbol: {why}")))
    }

    fn static_symbol(&self, def: DefId) -> Result<String, String> {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Static { .. }) {
            return Err("not a static".to_string());
        }
        if tcx.is_thread_local_static(def) {
            return Err("a thread-local static has no single address to bind".to_string());
        }
        Ok(tcx.symbol_name(ty::Instance::mono(tcx, def)).name.to_string())
    }

    fn target_info(&self) -> trust_ir::TargetInfo {
        crate::crate_module::source_target_info(self.tcx)
    }
}

impl<'tcx, 'a> EvidenceSpelling for RustcNames<'tcx, 'a> {
    fn def(&self, def: DefId) -> StableDef {
        let hash = self.tcx.def_path_hash(def);
        (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
    }

    fn site(&self, def: DefId, args: &[crate::SiteArg]) -> String {
        crate::lineage::ConcreteCalleeKey::from_site_args(
            self.tcx,
            def,
            crate::lineage::ConcreteInstanceKind::Item,
            args,
        )
        .symbol_suffix()
    }
}

/// The effect-conservation verdict of `index`, as the builder reads it.
fn verdict_of(sess: &rustc_session::Session, index: u32) -> VerdictInput {
    sess.with_trust_compiler_state::<crate::effect_conservation::ConservationVerdicts, _>(|v| {
        if !v.ran() {
            return VerdictInput::Unchecked(
                "the effect-conservation check did not run in this session".to_string(),
            );
        }
        match v.verdict(index) {
            None => VerdictInput::Unchecked(
                "the effect-conservation check has no verdict for this body".to_string(),
            ),
            Some(b) => VerdictInput::Classes(b.classes()),
        }
    })
}

/// The TEMPLATE verdict of `index` (step 6.5.1), as the template builder reads it. Never the
/// mainline verdict: a template is judged by its own (INC6.5-JUDGE).
fn template_verdict_of(sess: &rustc_session::Session, index: u32) -> VerdictInput {
    sess.with_trust_compiler_state::<crate::effect_conservation::ConservationVerdicts, _>(|v| {
        template_verdict_input(v, index)
    })
}

/// [`template_verdict_of`]'s rule, TyCtxt-free: `index`'s TEMPLATE verdict, never its mainline
/// one.
pub(crate) fn template_verdict_input(
    v: &crate::effect_conservation::ConservationVerdicts,
    index: u32,
) -> VerdictInput {
    if !v.ran() {
        return VerdictInput::Unchecked(
            "the effect-conservation check did not run in this session".to_string(),
        );
    }
    match v.template_verdict(index) {
        None => VerdictInput::Unchecked(
            "the effect-conservation check has no verdict for this template".to_string(),
        ),
        Some(b) => VerdictInput::Classes(b.classes()),
    }
}

/// One generic definition's authentic S bytes (step 6.5.4), or the ordered refusal.
fn build_template_row(
    tcx: TyCtxt<'_>,
    index: u32,
    registry: &EntryRegistry,
    capture_on: bool,
    clean_origin: &BTreeSet<u32>,
    files: &BTreeMap<String, Option<String>>,
) -> Result<Vec<u8>, EntryRefusal> {
    let def = LocalDefId { local_def_index: rustc_span::def_id::DefIndex::from_u32(index) };
    let names = RustcNames { tcx, def, files };
    let record = match registry.templates.get(&index).map(StoredTemplate::load).transpose() {
        Ok(record) => record,
        Err(refusal) => return Err(refusal),
    };
    // The identity is read only by the abstraction, so it is computed only for a capture that
    // can reach it.
    let identity = match &record {
        Some(TemplateRecord { capture: Ok(_), .. }) => {
            rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()))
        }
        _ => String::new(),
    };
    let inputs = TemplateInputs {
        record: record.as_ref(),
        duplicated: registry.templates_duplicated.contains(&index),
        capture_on,
        clean_origin: clean_origin.contains(&index),
        verdict: template_verdict_of(tcx.sess, index),
        identity,
    };
    let template = build_template(&inputs, &names)?;
    let candidate = record.as_ref().and_then(|r| r.capture.as_ref().ok()).ok_or_else(|| {
        EntryRefusal::Invalid("validated template has no source capture".to_string())
    })?;
    let bindings =
        crate::template_metadata::rustc::check_capture(tcx, def.to_def_id(), &candidate.facts)
            .map_err(|e| EntryRefusal::Invalid(format!("template owner binding: {e}")))?;
    // `retain_evidence` selects the TEMPLATE producer half and collapsed set for this index.
    // This private writer accepts neither a test-provided verdict nor source-model evidence.
    let retained = registry.evidence.get(&index).ok_or_else(|| {
        EntryRefusal::ConservationUnchecked(
            "the template's MIR census was not retained for its evidence".to_string(),
        )
    })?;
    let evidence = encode_evidence(&evidence_of(retained, &candidate.callees, &names));
    if let Some(refusal) = inherited_overflow_refusal(tcx, def) {
        return Err(refusal);
    }
    crate::template_metadata::frame_recorded(tcx, def, &bindings, &template, tcx.sess.overflow_checks(), &evidence)
        .map_err(|e| EntryRefusal::Invalid(format!("template framing: {e}")))
}

/// Build one candidate's entry bytes, or the refusal.
fn build_one<'tcx>(
    tcx: TyCtxt<'tcx>,
    index: u32,
    stored: &StoredCandidate,
    evidence: Option<&RetainedEvidence>,
    clean_origin: &BTreeSet<u32>,
    files: &BTreeMap<String, Option<String>>,
) -> Result<Vec<u8>, EntryRefusal> {
    let def = LocalDefId { local_def_index: rustc_span::def_id::DefIndex::from_u32(index) };
    let names = RustcNames { tcx, def, files };
    let candidate = &stored.load()?;
    let inputs = EntryInputs {
        candidate,
        generic: tcx.generics_of(def).requires_monomorphization(tcx),
        clean_origin: clean_origin.contains(&index),
        verdict: verdict_of(tcx.sess, index),
    };
    let module = build_entry_module(&inputs, &names)?;
    let Some(retained) = evidence else {
        return Err(EntryRefusal::ConservationUnchecked(
            "the body's MIR census was not retained for its evidence".to_string(),
        ));
    };
    let evidence = encode_evidence(&evidence_of(retained, &candidate.callees, &names));
    let hash = tcx.def_path_hash(def.to_def_id());
    let binding = EntryBinding {
        stable_crate_id: hash.stable_crate_id().as_u64(),
        local_hash: hash.local_hash().as_u64(),
    };
    if let Some(refusal) = inherited_overflow_refusal(tcx, def) {
        return Err(refusal);
    }
    frame_entry(&module, binding, tcx.sess.overflow_checks(), &evidence)
}

/// Provider of the `trust_ir_local_entries` query: every recorded body's entry or refusal, built
/// once, after analysis (metadata encoding asks for it). Drains the session registry.
///
/// `producer_ran` is the producer running at all; a session in which it runs but writes no entry
/// carries the [`crate_refusal`] in the header, so a consumer reads why (an incremental,
/// metadata-only or proc-macro build), and a header-less crate means exactly "built without the
/// producer".
///
/// A panic in the builder is a compiler bug and is NOT caught: rustc's panic hook reports it as an
/// internal compiler error before any unwinding a `catch_unwind` could stop, and a query the
/// builder was inside would stay poisoned for codegen, so catching it could only turn a reported
/// ICE into a compile that seems to succeed (review of 87d2139e0e).
pub fn local_entries(tcx: TyCtxt<'_>, (): ()) -> TrustIrLocalEntries {
    let mut out = TrustIrLocalEntries {
        producer_ran: tcx.sess.trust_ir_lower_enabled(),
        trust_ir_version: trust_ir::binary::VERSION,
        entry_schema: ENTRY_SCHEMA,
        crate_refusal: None,
        entries: BTreeMap::new(),
        templates: BTreeSet::new(),
    };
    if !out.producer_ran {
        return out;
    }
    if let Some(refusal) = crate_refusal(tcx) {
        out.crate_refusal = Some(refusal.to_string());
        return out;
    }
    let registry = tcx.sess.with_trust_compiler_state::<EntryRegistry, _>(std::mem::take);
    let files = metadata_file_names(tcx);
    let clean_origin: BTreeSet<u32> = tcx
        .resolutions(())
        .clean_origin_defs
        .iter()
        .map(|&(def, _, _)| def.local_def_index.as_u32())
        .collect();
    // Trust (step 6.5.1): the R-8 memory proxy — the stored modules and their bytes, level-R
    // candidates beside template captures (the memory gate: template bytes <= level-R bytes).
    let count = |sizes: &mut dyn Iterator<Item = usize>| {
        sizes.fold((0usize, 0usize), |(n, bytes), len| (n + 1, bytes + len))
    };
    let (level_r_modules, level_r_bytes) =
        count(&mut registry.candidates.values().filter_map(|c| c.module.as_ref().map(Vec::len)));
    let (template_modules, template_bytes) =
        count(&mut registry.templates.values().filter_map(StoredTemplate::module_bytes));
    // R-8's G: the records of a template LOWERING (every record but a closure-kind body's, which
    // is recorded by kind and not lowered).
    let template_lowerings = registry.templates.values().filter(|t| !t.is_closure_kind()).count();
    tracing::debug!(
        level_r_modules,
        level_r_bytes,
        template_modules,
        template_bytes,
        template_records = registry.templates.len(),
        template_lowerings,
        "trust-ir-lower: template store"
    );
    let capture_on = tcx.sess.opts.unstable_opts.trust_ir_lower_templates;
    for (index, candidate) in &registry.candidates {
        let def = LocalDefId { local_def_index: rustc_span::def_id::DefIndex::from_u32(*index) };
        let result = if registry.duplicated.contains(index) {
            Err(EntryRefusal::DuplicateRecord)
        } else if tcx.generics_of(def).requires_monomorphization(tcx) {
            // Trust (6.5.4): S bytes remain separate from R decoding and runtime admission.
            out.templates.insert(*index);
            let result =
                build_template_row(tcx, *index, &registry, capture_on, &clean_origin, &files);
            // The row with its definition's path (computed only when the event is enabled), so a
            // fixture reads each template's recorded reason by name. `info!`, not `debug!`: a
            // stage built with `rust.debug-logging = false` (dist, and this event's run-make
            // reader on such a host) compiles DEBUG callsites out, and the fixture read nothing.
            tracing::info!(
                def_index = index,
                def_path = %rustc_middle::ty::print::with_no_trimmed_paths!(
                    tcx.def_path_str(def.to_def_id())
                ),
                class = result.as_ref().err().map_or("template", EntryRefusal::class),
                reason = %result.as_ref().err().map_or_else(
                    || "encoded authenticated level-S metadata".to_string(), EntryRefusal::reason,
                ),
                "trust-ir-lower: template row"
            );
            result
        } else {
            build_one(tcx, *index, candidate, registry.evidence.get(index), &clean_origin, &files)
        };
        if let Err(refusal) = &result {
            tracing::debug!(
                def_index = index,
                class = refusal.class(),
                reason = %refusal.reason(),
                "trust-ir-lower: rmeta entry refused"
            );
        }
        out.entries.insert(*index, result.map(TrustIrEntryBlob).map_err(|r| r.reason()));
    }
    out
}

// =============================================================================================
// The consumer's read, for the step-2 scoreboard (probe channel C's `rmeta=` column)
// =============================================================================================

/// What a consuming compilation finds in rmeta for the upstream definition `def`: the class
/// (`entry`, `entry-refused`, `absent`, `no-header`) and the column text. The entry is decoded and
/// checked exactly as the step-6.3 consumer will check it before anything else (design §5.2,
/// checks 2-5): magic and schema, the producing compiler's trust-ir version, the binding to this
/// crate and definition, and the recomputed digest. Nothing is admitted here; this only READS.
pub fn upstream_entry_column(tcx: TyCtxt<'_>, def: DefId) -> (&'static str, String) {
    let Some(header) = tcx.trust_ir_crate_header(def.krate) else {
        return ("no-header", "no-header(compiled-without-the-producer)".to_string());
    };
    let Some(blob) = tcx.trust_ir_entry(def) else {
        let reason = header.unencoded_reason(def.index.as_u32()).unwrap_or("not-in-the-encode-set");
        let class = reason.split('(').next().unwrap_or(reason).trim();
        return ("absent", format!("absent({})", if class.is_empty() { "?" } else { class }));
    };
    match decode_entry_for_overflow(&blob.0, tcx.sess.overflow_checks()) {
        Err(e) => ("entry-refused", format!("entry-refused({})", e.to_string().replace(' ', "_"))),
        Ok(entry) => {
            let hash = tcx.def_path_hash(def);
            let expected = EntryBinding {
                stable_crate_id: tcx.stable_crate_id(def.krate).as_u64(),
                local_hash: hash.local_hash().as_u64(),
            };
            if entry.binding != expected {
                return ("entry-refused", "entry-refused(binding)".to_string());
            }
            if let Err(e) = decode_evidence(&entry.evidence) {
                return (
                    "entry-refused",
                    format!("entry-refused(evidence:{})", e.to_string().replace(' ', "_")),
                );
            }
            (
                "entry",
                format!(
                    "entry(digest-ok,functions={},bytes={})",
                    entry.module.functions.len(),
                    blob.0.len()
                ),
            )
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "rmeta_entry/envelope_tests.rs"]
mod envelope_tests;
