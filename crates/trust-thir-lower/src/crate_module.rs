//! Trust: crate-level `trust_ir::Module` assembly + on-disk artifact (P1 Phase 0, the
//! `trust_ir_of` wiring) — makes the per-body producer output CONSUMABLE.
//!
//! The per-body hook (`build_mir_inner_impl` in `rustc_mir_build`) is the only seam where THIR is
//! reliably un-stolen, so lowering stays per-body there. Each body's [`crate::Lowered`] is handed
//! to [`record`], a thread-safe Session-owned registry (`mir_built` can run concurrently). Once
//! `run_required_analyses` has forced `mir_borrowck` — and therefore `mir_built`, and therefore
//! the hook — for every body owner, the `rustc_interface` `analysis` seam calls
//! [`finalize_and_dump`], which assembles ONE crate-level `Module` and writes the artifacts.
//!
//! # Assembly (two-pass, deterministic)
//!
//! Records are sorted by `DefIndex` (deterministic for a fixed compiler + source: def indices are
//! assigned during expansion/HIR lowering in a parallelism-independent order), then:
//!
//! 1. **Pass 1** — every *spliceable* body (function present, zero `unsupported` entries, and it
//!    passes the fail-closed structural tripwires below) is assigned a dense `FuncId` in sorted
//!    order (`0..N`, so `module.functions[i].id == i`, the `function_by_id` fast path).
//! 2. **Pass 2** — functions are spliced in: renamed to their full `def_path_str` (unique within
//!    the crate, unlike the bare item name), their `FuncTy` interned into the assembled module,
//!    and every `Inst::Call { callee }` rewritten through the body's callee-identity ledger
//!    ([`crate::Lowered::callees`]): a LOCAL callee whose body was itself spliced resolves to its
//!    pass-1 `FuncId`; everything else (extern callee, local callee that failed to lower, unknown
//!    or index-ambiguous identity) is fail-closed as a **bodyless declaration** — no body, no
//!    summary — which is the IR-level "opaque external symbol" state (callers stay havoced), with
//!    an unknown-signature `FuncTy` (`params: [], returns: [], is_vararg: true`) as the explicit
//!    can't-know marker. Declarations take the `FuncId`s after all defined functions, in
//!    first-encounter order (deterministic given the sorted pass-2 walk).
//!
//! Bodies that failed to lower (or trip a fail-closed guard) are NOT silently dropped: every
//! recorded body appears in the `coverage.json` sidecar with its `unsupported` reasons.
//!
//! # Pending local consts (reentrancy-safe eval)
//!
//! Before assembly, [`finalize_and_dump`] runs `resolve_pending_consts`: every LOCAL const the
//! hook deferred (evaluating it inside `mir_built` re-enters MIR building — see
//! `crate::PendingConst`) is evaluated HERE via `const_eval_resolve_for_typeck` — safe at this
//! seam because `run_required_analyses` has already forced `mir_borrowck` (hence `mir_built`)
//! for every body owner — and its placeholder `Inst::Const` sentinel is patched with the real
//! value. Failures mark the body unsupported (`PendingConst(...)` reasons in coverage), and a
//! final tripwire scans the assembled `Module`: any leftover sentinel aborts artifact emission.
//!
//! # Fail-closed tripwires
//!
//! The producer's `map_ty` emits table-free types (scalars, `Tuple`, `Unit`, `Ptr`, `FatPtr`)
//! plus FOUR table-indexed shapes the splice REMAPS: `Ty::Enum(id)` over the body's positional
//! enum table (first-class GENERAL enums — registered defs carry only table-free scalar
//! variant fields, the producer's `register_enum` seedable-scalar wall), `Ty::Struct(id)` over
//! the body's positional struct table (first-class struct values), `Ty::Array(TyId, 0)` over
//! the body's types table (zero-length arrays), and `Ty::Func` in exactly two positions — the
//! `Inst::Const { Constant::FnDef }` a `ReifyFnPointer` coercion produces and (as a bare id)
//! `Inst::CallIndirect { sig }`. Its `FuncId`-bearing emissions are `Inst::Call` callees and
//! those `FnDef` constants, all ledgered. These are load-bearing invariants for splicing, so
//! they are *checked*, not assumed (`splice_ok`): any `Invoke`; an enum table that is not
//! positional or whose variant fields reference ANYTHING table-indexed (enums intern FIRST,
//! so their defs must be self-contained); a struct table that is not positional/nested-first
//! or whose def fields reference anything table-indexed beyond earlier structs and (any)
//! enums; a types table entry referencing anything beyond enums/structs/earlier entries;
//! any UNREMAPPABLE table-indexed `Ty` in a signature / block param / instruction (the
//! per-instruction scan `inst_embedded_tys` covers every producer-emitted variant and refuses
//! unmodeled ones; `Ty::Func` in a signature/merge stays refused, so fn-pointer
//! params/returns/merges are lowered-but-not-spliced for now); a `CallIndirect`/`FnDef` whose
//! per-body sig id fails `body_sig_ok` (out of table, vararg, or higher-order); a `FnDef`
//! without exactly one ledger identity; or any other `Constant` outside the scalar/aggregate
//! allow-list (`Closure`, `SymbolAddr`, …) makes the body non-spliceable (recorded in
//! coverage), never mis-linked. Admitted bodies are prepared in pass 1
//! (`prepare_body_tables`): enum defs intern via `add_enum_def`, struct defs via
//! `add_struct_def` (both structural dedup), types entries via `intern_ty`, and every embedded
//! `EnumId`/`StructId`/`TyId` is rewritten through the resulting maps (intern order
//! enums → structs → types, matching the allowed cross-references above — acyclic by check).
//! Spliced `CallIndirect { sig }` / `Const { ty: Ty::Func }` ids are re-interned from the
//! body's `func_types` snapshot into the assembled table; `FnDef` target `FuncId`s are
//! rewritten through the ledger exactly like `Call` callees (and counted as call-graph edges
//! in the same coverage buckets).
//!
//! # Artifacts (`-Z trust-dump=ir:<dir>`, requires `-Z trust-ir-lower`)
//!
//! * `<crate>.trust-ir.bin` — the assembled `Module` in the trust-ir binary codec
//!   (`trust_ir::binary::serialize_module`; string pool is `BTreeMap`-backed, so byte-stable).
//! * `<crate>.trust-ir.txt` — the canonical text form (`trust_ir::format::canonical`, the
//!   diff-stable rendering).
//! * `<crate>.coverage.json` — per-body `{def_path, def_index, kind, lowered, spliced,
//!   lineage, func_id, instr_count, unsupported: [[reason, count], …], calls: {resolved,
//!   extern_decls, unresolved}, differentials: {interpreter, derived_mir, deferred_to_seam,
//!   seam}}` + crate
//!   totals. `lineage`/`func_id` are the L1 artifact-lineage pair (both schema-additive):
//!   `lineage` is the digest of the pre-assembly (mini-module, callee ledger) this row was
//!   built from — the SAME value the flip event logs for the body it selected — and `func_id`
//!   is the row's index into the assembled `module.functions`. Together they let an external
//!   consumer state "the body the flip compiled is THIS function of the published artifact";
//!   they do not by themselves PROVE the assembled function still means what the pre-assembly
//!   module meant (that is the canonical-remapping certificate, `crate::lineage` §future work).
//!   Differential verdicts are typed `agreed` / `mismatch` / `unsupported` / `not-run`;
//!   deferred bodies receive an exact resolved seam outcome before JSON is rendered, while
//!   non-deferred rows say `not-applicable`. The ambiguous internal `equal` boolean is never
//!   serialized. (`kind` is `"fn"` / `"const-init"` / `"static-init"`;
//!   initializer bodies also carry a `::{const-init}`/`::{static-init}` name suffix in the
//!   assembled module, and totals gain `initializer_bodies` — both schema-additive). It also
//!   carries `direct_obligation_capability: "structural-parity-only-v1"`,
//!   `proof_authority: false`, and `native_verification_requests: false`: direct THIR lowering
//!   does not yet bind source contracts/obligations to its SSA values, so the artifacts are
//!   structural/parity evidence, never a proof result. Finalization rejects any authority-bearing
//!   obligation, certificate, diagnostic, function claim/summary, spec-proof binding, or
//!   certifying `SpecModule::Linked` state that appears while this capability marker is active.
//!   The `calls` buckets count CALL-GRAPH EDGES resolved through the ledger: direct
//!   `Inst::Call` callees plus reified fn-pointer targets (`Constant::FnDef`); indirect
//!   `CallIndirect` sites themselves carry no static edge and are not counted. Hand-rolled
//!   writer: fixed key order, sorted rows, no timestamps — two identical builds produce
//!   byte-identical files.
//!
//! Mirrors the tracked `-Ztrust-dump=mir:` artifact precedent in
//! `rustc_mir_transform::trust_verify`. Registry assembly also drives the crate-seam
//! differential without a dump; when a dump is requested, its artifacts are an explicit
//! compiler output contract.
//! Publication or tripwire failures are returned to the compiler caller and are fatal.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::hash::Hash;
use std::path::PathBuf;

// Trust: `ty` for the finalizer's reentrancy-safe pending-const evaluation
// (`GenericArgs::identity_for_item`, `AliasConst` (né `UnevaluatedConst`), `TypingEnv`, `Value`).
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::Session;
use rustc_span::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_span::{AttrId, Span};
// Trust (wave-16): `GlobalId` is not re-exported at the trust_ir crate root — canonical path.
use trust_ir::value::GlobalId;
use trust_ir::{
    BlockId,
    Constant,
    InstrNode,
    SourceSpan,
    EnumDef,
    EnumId,
    FuncId,
    FuncTy,
    FuncTyId,
    Function,
    // Trust (wave-16): promoted-borrow module globals.
    Global,
    Inst,
    Linkage,
    Module,
    // Trust (temporal-carry): the §2.1 `#[trust::var]`/`#[trust::action]` attributes
    // ride the existing SpecModule metadata channel (RFC-trust-temporal-extraction §2.2).
    SpecAnchor,
    SpecInvariant,
    SpecModule,
    SpecProjectionTarget,
    SpecVar,
    StructDef,
    StructId,
    TEMPORAL_FIELD_PATH_PROJECTION_V1,
    Ty,
    TyId,
    ValueId,
};

use crate::artifact_publication::{Artifact, PreparedPublication};
use crate::{BodyKind, CalleeRef, Lowered, PendingConst};

/// Machine-readable differential state carried by the direct-TrustIR coverage artifact.
///
/// Keep this independent of the tracing-oriented producer enums: artifact consumers must not
/// infer a verdict from `equal`, sample counts, or human-readable notes. In particular,
/// `Unsupported` and `NotRun` are distinct non-verdict states and neither is agreement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArtifactVerdict {
    Agreed,
    Mismatch,
    Unsupported,
    NotRun,
}

impl ArtifactVerdict {
    fn marker(self) -> &'static str {
        match self {
            Self::Agreed => "agreed",
            Self::Mismatch => "mismatch",
            Self::Unsupported => "unsupported",
            Self::NotRun => "not-run",
        }
    }
}

/// Classify an interpreter report without allowing inconsistent producer fields to collapse into
/// a plausible artifact verdict. This is a finalization invariant, not best-effort telemetry.
fn classify_interpreter_verdict(
    mode: crate::differential::DiffMode,
    equal: bool,
    has_unsupported: bool,
) -> Result<ArtifactVerdict, String> {
    use crate::differential::DiffMode;

    match (mode, equal, has_unsupported) {
        (DiffMode::Agreed, true, false) => Ok(ArtifactVerdict::Agreed),
        (DiffMode::MirOracle, false, false) => Ok(ArtifactVerdict::Mismatch),
        (DiffMode::NotRun, false, true) => Ok(ArtifactVerdict::Unsupported),
        (DiffMode::NotRun, false, false) => Ok(ArtifactVerdict::NotRun),
        _ => Err(format!(
            "inconsistent interpreter differential report: mode {mode:?}, equal {equal}, \
             unsupported {has_unsupported}"
        )),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct InterpreterEvidence {
    verdict: ArtifactVerdict,
    samples: usize,
    detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DerivedMirEvidence {
    verdict: ArtifactVerdict,
    detail: String,
    markers_exact: bool,
    markers_detail: String,
}

/// One recorded body: everything the finalizer needs, snapshotted at the hook (THIR/`tcx` query
/// results are reduced to plain owned data so the registry is `'static`).
struct BodyRecord {
    /// `def.to_def_id().index.as_u32()` — the sort key AND the intra-crate callee-mapping key
    /// (the producer's `admit_callee` derives callee `FuncId`s from exactly this index).
    def_index: u32,
    /// Trust: fn body vs const/static INITIALIZER body (`crate::BodyKind`). Initializer bodies
    /// are zero-param functions returning the initializer value (`lower_const_body`); the
    /// assembled module marks them with a `::{const-init}` / `::{static-init}` name suffix
    /// (rustc def paths never produce those segments, so the marker is collision-free and the
    /// braces alphabet already appears in spliced names via `{closure#N}` / `{constant#N}`),
    /// and every coverage row carries a `kind` field.
    kind: BodyKind,
    /// Trust (totality Batch C): body reads >=1 SYMBOLIC assoc const (value-less
    /// extern-immutable global). Lowered-for-coverage but NEVER spliced into the
    /// executable crate module (`splice_ok` checks this field; a value-less global in
    /// the assembled module would be a lie).
    symbolic: bool,
    /// `tcx.def_path_str` — unique, deterministic display identity within the crate.
    def_path: String,
    /// Trust (B3-2c seam guard): the body used a place-path VALUE carrier in a
    /// call arg (wave-RS/MC/receiver-value lanes) — CLEAN-ONLY by contract; the
    /// seam must not link+interpret it (a carried value hits the callee's real
    /// ptr param as a manufactured signature-mismatch defect verdict).
    place_path_carrier: bool,
    /// The per-body lowered function (`functions[0]` of the throwaway per-body module), if the
    /// body was a fn body at all.
    function: Option<Function>,
    /// Its signature, resolved out of the per-body module's `func_types` table.
    func_ty: Option<FuncTy>,
    /// Trust (C2-spans): the mini-module's file table. The splice re-interns every stamped
    /// `SourceSpan.file` through the ASSEMBLED module's table so no span id dangles.
    files: Vec<String>,
    /// Trust (B6): the per-body module's first-class `ClosureTy` table (positional ids,
    /// `closure_types[i]` = `ClosureTyId(i)` — the producer's `pend_closure_ty` convention).
    /// Splicing re-interns each into the assembled module (func re-interned through
    /// `intern_func_ty`, captures remapped) and remaps every embedded `Ty::Closure` id.
    closure_types: Vec<trust_ir::ClosureTy>,
    /// Struct defs the body registered (`register_struct`). Referenced FIRST-CLASS by
    /// `Ty::Struct(id)` in the body's signature / block params / instruction types, under the
    /// per-body positional id space (`structs[i].id == i`, nested fields strictly before their
    /// parent). Splicing re-interns them into the assembled module via `add_struct_def`
    /// (structural dedup) and REMAPS every embedded `StructId` (see `prepare_body_tables` /
    /// `remap_ty`); the well-formedness invariants are CHECKED in `splice_ok`, never assumed.
    structs: Vec<StructDef>,
    /// Trust: enum defs the body registered (`register_enum` — the GENERAL first-class enum
    /// path). Referenced by `Ty::Enum(id)` in the body's signature / block params / instruction
    /// types under the per-body positional id space (`enums[i].id == i`); variant fields are
    /// TABLE-FREE scalars by the producer's seedable-scalar registration wall — re-CHECKED in
    /// `splice_ok` (never assumed), which is what lets pass 1 intern enums FIRST (struct defs
    /// may reference enums, never vice versa). Splicing re-interns via `add_enum_def`
    /// (structural dedup) and remaps every embedded `EnumId`.
    enums: Vec<EnumDef>,
    /// Trust: the per-body module's `types` table snapshot (zero-length-array element types the
    /// producer pended via `pend_ty`; ids positional). `Ty::Array(TyId, 0)` in the body
    /// references it; splicing re-interns entries (`intern_ty`) and remaps embedded `TyId`s.
    types: Vec<Ty>,
    /// Trust (wave-16): promoted-borrow module globals the body registered (the
    /// `Borrow(non-local place)` → `Inst::GlobalAddr` lowering of a rustc-PROMOTED shared borrow
    /// of a const-expr — `&5`, `&C`, `&123u8`, `&true`, `&1.5f32`; Trust (wave-PA) also `&[13, 14]`,
    /// `&(1u8, true)`, `&S { a: 1, b: 2 }`). Referenced by `Inst::GlobalAddr { global }` under the
    /// per-body positional id space (`globals[i]` ↔ `GlobalId(i)`). Each is CHECKED spliceable —
    /// scalar / bytes-`[u8; N]` / `Tuple`-`Struct`-aggregate `ty` with a matching `initializer`
    /// (`global_const_ok`) — in `splice_ok` (never assumed); splicing appends them into the assembled
    /// module with crate-unique deterministic names (`prepare_body_tables`) and remaps every
    /// embedded `GlobalId`.
    globals: Vec<Global>,
    /// Fail-closed reasons, aggregated `(reason, count)` and sorted by reason.
    unsupported: Vec<(String, u64)>,
    /// Trust (v2 Phase 0a): per-tag DETAIL examples `(tag, up to 3 truncated details)`, sorted by
    /// tag — decomposes the bare-"Ty"/"Other" catch-alls in the coverage JSON.
    unsupported_details: Vec<(String, Vec<String>)>,
    /// Trust (v2 Phase 0b): the COLLECT-ALL pass's aggregated `(tag, count)` rows (empty for a
    /// clean body — the pass runs only when the strict pass failed), split PRIMARY vs CASCADE
    /// (unbound-local echo tags are cascades of an earlier failure, ~1339 events / 0 sole).
    collect_primary: Vec<(String, u64)>,
    collect_cascade: Vec<(String, u64)>,
    /// Total `InstrNode`s across the function's blocks.
    instr_count: u64,
    /// Callee-identity ledger (see `Lowered::callees`).
    callees: Vec<CalleeRef>,
    /// Trust: the per-body module's FULL `func_types` table snapshot. Slot 0 is the body's own
    /// signature; slots 1.. are fn-pointer signatures the producer pended (`pend_func_ty`).
    /// Splicing needs it to re-intern the `FuncTyId`s embedded in `Inst::CallIndirect { sig }`
    /// and `Inst::Const { ty: Ty::Func(_) }` into the assembled module's table (`body_sig_ok`
    /// gates, pass 2 remaps).
    func_types: Vec<FuncTy>,
    /// Trust: LOCAL consts the hook deferred (see `Lowered::pending_consts`). The finalizer —
    /// the reentrancy-safe seam — evaluates each one and patches the placeholder `Inst::Const`
    /// in `function` before assembly; any failure marks the body unsupported (never spliced,
    /// never a guessed value). `PendingConst` is plain owned/`Copy` data (`DefId`/`Span` are
    /// lifetime-free), so the `'static` registry invariant holds.
    pending_consts: Vec<PendingConst>,
    /// Trust (B9-A): this body is DEFERRED to the crate-finalize seam differential — clean (no
    /// unsupported shapes, no pending consts) but call-bearing (`differential::deferred_to_seam`).
    /// Its per-body module carries callees as bodyless declarations, so interpretation-equivalence
    /// can only be asserted after the crate module links their bodies. The hook SUPPRESSES its
    /// own differential event for such bodies (`deferred_to_seam` is the single source of truth);
    /// [`run_seam_differentials`] emits the one real verdict at finalize.
    deferred: bool,
    /// Typed hook-time interpreter result. A deferred body's hook result is `NotRun`; its final
    /// linked result is installed separately into the coverage row at crate finalization.
    interpreter: InterpreterEvidence,
    /// Typed direct-TrustIR -> derived-MIR structural comparison result.
    derived_mir: DerivedMirEvidence,
    /// Producer/report invariant violations discovered at registration. They are retained as
    /// owned data so the query hook stays non-panicking, then abort semantic finalization before
    /// assembly, seam comparison, or artifact publication.
    differential_errors: Vec<String>,
    /// Trust (B9-A): the MIR-side verification snapshot (`trust_mir_extract::extract_function`),
    /// taken at the hook for EVERY clean body (call-bearing or not — call-free clean bodies are
    /// the CALLEES the seam bundles link against). `compare` extracts it once and hands it back so
    /// this is never a duplicate extraction. `VerifiableFunction` is fully owned `Clone` data
    /// (no `Rc`), so the `'static` registry invariant holds.
    mir_snapshot: Option<trust_types::VerifiableFunction>,
    /// Trust (L1, artifact-lineage attestation): the per-body lineage digest
    /// ([`crate::lineage::body_lineage_digest`]), computed over the INTACT hook-time
    /// (mini-module, callee ledger) BEFORE `record` strips `functions[0]` for assembly —
    /// so it equals, value-for-value, the digest `flip_registry::record_green` stores and
    /// the flip event logs. Rides into the coverage row so an external consumer can match
    /// "the body the flip selected" to "the row in the published artifact" by digest
    /// equality. `None` only for records whose mini-module carried no single function
    /// (never green-recorded, so nothing to match).
    lineage: Option<trust_ir::ProofDigest>,
}

/// Crate-wide records belong to one compiler Session. rustc_driver can create
/// multiple Sessions in a process, so a process-global registry would leak
/// bodies and dump configuration across invocations.
#[derive(Default)]
struct CrateModuleRegistry {
    records: BTreeMap<u32, BodyRecord>,
    /// Every callback after the first for a DefIndex. The primary map stays
    /// deterministic and bounded, but duplicates must remain observable: a
    /// query/provider replay is an invariant violation, not harmless dedup.
    duplicate_def_indices: Vec<u32>,
}

fn insert_registry_record<T>(
    records: &mut BTreeMap<u32, T>,
    duplicate_def_indices: &mut Vec<u32>,
    def_index: u32,
    record: T,
) {
    use std::collections::btree_map::Entry;

    match records.entry(def_index) {
        Entry::Vacant(entry) => {
            entry.insert(record);
        }
        Entry::Occupied(_) => duplicate_def_indices.push(def_index),
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ArtifactPublicationTarget {
    directory: PathBuf,
    crate_name: String,
}

/// A pre-input single-writer lease for one direct-TrustIR artifact identity.
/// The concrete filesystem transaction stays private so callers cannot publish
/// without going through crate finalization.
#[derive(Debug)]
pub struct PreparedArtifactPublication {
    target: ArtifactPublicationTarget,
    prepared: PreparedPublication,
}

/// `rustc_interface` prepares the artifact transaction from the validated,
/// explicit command-line identity before any input I/O. Keeping the prepared
/// target on `Session` lets the later `TyCtxt` finalizer consume the exact same
/// transaction without a process-global or a second stale-output window.
#[derive(Default)]
struct ArtifactPublicationState {
    target: Option<ArtifactPublicationTarget>,
    prepared: Option<PreparedPublication>,
    error: Option<String>,
}

fn prepare_artifact_target(
    directory: PathBuf,
    crate_name: &str,
) -> Result<PreparedPublication, String> {
    PreparedPublication::prepare(
        directory,
        vec![format!("{crate_name}.trust-ir.bin"), format!("{crate_name}.trust-ir.txt")],
        format!("{crate_name}.coverage.json"),
    )
    .map_err(|error| error.to_string())
}

/// Acquire and invalidate an explicit artifact identity before selecting or
/// reading compiler input. The returned lease must remain alive until it is
/// installed in the Session or the invocation exits; dropping it releases the
/// cross-process writer lock without making a commit marker current.
pub fn acquire_artifact_publication_target(
    directory: PathBuf,
    crate_name: &str,
) -> Result<PreparedArtifactPublication, String> {
    let target =
        ArtifactPublicationTarget { directory: directory.clone(), crate_name: crate_name.into() };
    let prepared = prepare_artifact_target(directory, crate_name)?;
    Ok(PreparedArtifactPublication { target, prepared })
}

/// Transfer a pre-input writer lease into the exact Session that will consume
/// it at finalization. This transfer never reacquires the filesystem lock.
pub fn install_artifact_publication(
    sess: &Session,
    lease: PreparedArtifactPublication,
) -> Result<(), String> {
    if !sess.trust_ir_lower_enabled() {
        return Err(
            "cannot install a direct-TrustIR artifact lease when lowering is disabled".into()
        );
    }
    let Some(directory) = sess.opts.unstable_opts.trust_dump.ir.clone() else {
        return Err("cannot install a direct-TrustIR artifact lease without a dump target".into());
    };
    let Some(crate_name) = sess.opts.crate_name.as_deref() else {
        return Err("cannot install a direct-TrustIR artifact lease without a crate name".into());
    };
    let expected = ArtifactPublicationTarget { directory, crate_name: crate_name.to_string() };
    if lease.target != expected {
        return Err("pre-input artifact lease does not match the Session artifact identity".into());
    }

    sess.with_trust_compiler_state::<ArtifactPublicationState, _>(|state| {
        if state.target.is_some() || state.prepared.is_some() || state.error.is_some() {
            return Err("direct-TrustIR artifact lease was installed more than once".into());
        }
        state.target = Some(lease.target);
        state.prepared = Some(lease.prepared);
        Ok(())
    })
}

/// Invalidate and prepare the direct-TrustIR artifact target for this compiler
/// invocation. The ordinary driver has already installed its pre-input lease,
/// so this is idempotent at parser entry. Custom drivers may use this as a
/// compatibility fallback, but then cannot invalidate failures that happen
/// before their Session exists.
pub fn prepare_artifact_publication(sess: &Session, crate_name: &str) -> Result<(), String> {
    if !sess.trust_ir_lower_enabled() {
        return Ok(());
    }
    let Some(directory) = sess.opts.unstable_opts.trust_dump.ir.clone() else {
        return Ok(());
    };
    let target = ArtifactPublicationTarget { directory, crate_name: crate_name.to_string() };

    sess.with_trust_compiler_state::<ArtifactPublicationState, _>(|state| {
        if let Some(existing) = &state.target {
            if existing != &target {
                return Err(
                    "prepared artifact target does not match the requested crate identity".into()
                );
            }
            return state.error.as_ref().map_or(Ok(()), |error| Err(error.clone()));
        }

        let result = prepare_artifact_target(target.directory.clone(), crate_name);

        state.target = Some(target);
        match result {
            Ok(prepared) => {
                state.prepared = Some(prepared);
                state.error = None;
                Ok(())
            }
            Err(error) => {
                state.prepared = None;
                state.error = Some(error.clone());
                Err(error)
            }
        }
    })
}

fn take_artifact_publication(
    sess: &Session,
    crate_name: &str,
) -> Result<Option<PreparedPublication>, String> {
    if !sess.trust_ir_lower_enabled() {
        return Ok(None);
    }
    let Some(directory) = sess.opts.unstable_opts.trust_dump.ir.clone() else {
        return Ok(None);
    };
    prepare_artifact_publication(sess, crate_name)?;
    let target = ArtifactPublicationTarget { directory, crate_name: crate_name.to_string() };
    sess.with_trust_compiler_state::<ArtifactPublicationState, _>(|state| {
        if state.target.as_ref() != Some(&target) {
            return Err("prepared artifact target does not match the final crate identity".into());
        }
        if let Some(error) = &state.error {
            return Err(error.clone());
        }
        state
            .prepared
            .take()
            .map(Some)
            .ok_or_else(|| "prepared artifact transaction was already consumed".to_string())
    })
}

/// Trust: `--emit=trust-ir` — the first-class OutputType lane. When requested, the
/// registry records regardless of the `TRUST_IR_DUMP` env var, and
/// [`finalize_and_dump`] writes the `.trust-ir.bin` at the requested output path
/// (canonical `.txt` + `coverage.json` companions alongside).
pub fn emit_requested(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.opts.output_types.contains_key(&rustc_session::config::OutputType::TrustIr)
}

/// The `--emit=trust-ir` target path, when requested and writable (a real file
/// path; `--emit=trust-ir=-`/stdout is not a supported target for a binary
/// artifact and is treated as absent).
fn emit_path(tcx: TyCtxt<'_>) -> Option<PathBuf> {
    if !emit_requested(tcx) {
        return None;
    }
    match tcx.output_filenames(()).path(rustc_session::config::OutputType::TrustIr) {
        rustc_session::config::OutFileName::Real(p) => Some(p),
        rustc_session::config::OutFileName::Stdout => None,
    }
}

#[derive(Debug)]
struct EmitPublicationTarget {
    directory: PathBuf,
    binary_name: String,
    text_name: String,
    coverage_name: String,
}

fn emit_publication_target(path: &std::path::Path) -> Result<EmitPublicationTarget, String> {
    let directory = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| std::path::Path::new("."))
        .to_path_buf();
    let text_path = path.with_extension("txt");
    let coverage_path = path.with_extension("coverage.json");
    let file_name = |candidate: &std::path::Path, kind: &str| {
        candidate
            .file_name()
            .and_then(|name| name.to_str())
            .filter(|name| !name.is_empty())
            .map(str::to_string)
            .ok_or_else(|| {
                format!(
                    "--emit=trust-ir {kind} path has no non-empty UTF-8 file name: {}",
                    candidate.display()
                )
            })
    };
    let binary_name = file_name(path, "binary")?;
    let text_name = file_name(&text_path, "canonical-text companion")?;
    let coverage_name = file_name(&coverage_path, "coverage companion")?;
    if binary_name == text_name || binary_name == coverage_name || text_name == coverage_name {
        return Err(format!(
            "--emit=trust-ir output and companion paths are not distinct: {}",
            path.display()
        ));
    }
    Ok(EmitPublicationTarget { directory, binary_name, text_name, coverage_name })
}

fn prepare_emit_publication(target: &EmitPublicationTarget) -> Result<PreparedPublication, String> {
    PreparedPublication::prepare(
        target.directory.clone(),
        vec![target.binary_name.clone(), target.text_name.clone()],
        target.coverage_name.clone(),
    )
    .map_err(|error| error.to_string())
}

/// Trust: per-body registration, called from the `-Z trust-ir-lower` hook in
/// `rustc_mir_build::builder::build_mir_inner_impl` right after the differential — the only seam
/// where the THIR-side lowering reliably exists. Thread-safe (`mir_built` runs in parallel).
///
/// Trust (B9-A): UNCONDITIONAL under `-Z trust-ir-lower` — the registry now feeds the crate-seam
/// call-linking differential ([`run_seam_differentials`]), not only the `TRUST_IR_DUMP` artifact.
/// `mir_snapshot` is the MIR-side verification extraction (`extract_function`), taken by the
/// caller's `compare` for every clean body so the seam can bundle a call-bearing body against its
/// (call-free clean) callees. Artifact emission alone stays behind `dump_dir()`.
pub fn record(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    lowered: Lowered,
    interpreter_report: &crate::differential::DiffReport,
    derived_report: &crate::mir_differential::DerivedReport,
    mir_snapshot: Option<trust_types::VerifiableFunction>,
    collect_all: &[(String, &'static str)],
    collect_all_overflowed: bool,
) {
    let def_index = def.to_def_id().index.as_u32();
    // Trust: `with_no_trimmed_paths!` — a bare `def_path_str` arms `must_produce_diag`, which
    // ICEs at `DiagCtxt` drop on warning-free compiles (masked whenever RUSTC_LOG is set).
    let def_path =
        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));

    // Trust (L1, artifact-lineage attestation): digest the INTACT (mini-module, callee ledger)
    // BEFORE the destructure below removes `functions[0]` — this must be the same value
    // `flip_registry::record_green` minted for this body (same pure function, same input), or
    // the flip event and the artifact row cannot be matched. A refusal (no single function)
    // records `None`: such a body was never green-recorded, so there is no flip to match.
    let lineage = crate::lineage::body_lineage_digest(&lowered.module, &lowered.callees).ok();

    let Lowered {
        mut module,
        body_kind,
        symbolic,
        unsupported: lowered_unsupported,
        contains_call,
        place_path_carrier,
        callees,
        pending_consts,
        // Trust (#173): MEASUREMENT ONLY — consumed by the `body class` debug event at the
        // mir_built hook, not by the crate assembler. Deliberately does NOT gate the splice the
        // way `symbolic` does: an opaque-collapse body is still offered to the splice and to the
        // differential, each of which declines on its own terms. Bound explicitly rather than
        // via `..` so a future field cannot slip past this destructure unnoticed.
        opaque_collapse: _opaque_collapse,
    } = lowered;
    let deferred = lowered_unsupported.is_empty() && pending_consts.is_empty() && contains_call;
    let function =
        if module.functions.is_empty() { None } else { Some(module.functions.remove(0)) };
    let func_ty = function.as_ref().and_then(|f| module.func_type(f.ty).cloned());
    let instr_count =
        function.as_ref().map(|f| f.blocks.iter().map(|b| b.body.len() as u64).sum()).unwrap_or(0);

    // Aggregate fail-closed reasons into deterministic (reason, count) rows.
    let mut unsupported_by_tag: BTreeMap<String, u64> = BTreeMap::new();
    for (_detail, what) in &lowered_unsupported {
        let count = unsupported_by_tag.entry((*what).to_string()).or_default();
        *count = count.saturating_add(1);
    }
    let unsupported = unsupported_by_tag.into_iter().collect();
    // Trust (v2 Phase 0a, RFC docs/TRUST_IR_V2.md §4): ALSO carry per-tag DETAIL examples into the
    // coverage row. Every push site already formats a detail string (`push((format!(..), TAG))`) —
    // the `.0` element, previously DROPPED here — and the bare-"Ty" (397 sole) / "Other" (83 sole)
    // catch-alls are undecomposable without it. Capped at 3 distinct examples per tag, each
    // truncated to 120 chars (char-boundary safe), deterministic order (first-encounter within a
    // tag; tags sorted). Purely additive diagnostics — no lowering/flip behavior change.
    let mut details_by_tag: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (detail, what) in &lowered_unsupported {
        let ex: String = detail.chars().take(120).collect();
        let examples = details_by_tag.entry((*what).to_string()).or_default();
        if examples.len() < 3 && !examples.contains(&ex) {
            examples.push(ex);
        }
    }
    let unsupported_details = details_by_tag.into_iter().collect();

    // Trust (v2 Phase 0b): the COLLECT-ALL second pass — measurement only. The caller re-lowers a
    // failed body once when either tracing or coverage requests it and shares that bounded tag
    // snapshot with this recorder. Aggregate ONLY its tag vector (the collect-all module itself
    // is discarded by construction, and the five `unsupported.is_empty()` gates keep any
    // tag-bearing body out of splice/flip/differential).
    // Tags are split PRIMARY vs CASCADE: an unbound-local echo (`VarRef(unbound)` / `Borrow(...
    // unbound local)`) is the downstream shadow of an earlier failed binding, not a leaf demand.
    // Capped at 4096 events (worst observed body: 1715) with an explicit overflow marker.
    let mut primary_by_tag: BTreeMap<String, u64> = BTreeMap::new();
    let mut cascade_by_tag: BTreeMap<String, u64> = BTreeMap::new();
    // Coverage consumes the shared snapshot only when an artifact will actually be written;
    // debug-only scorecard runs still share the same computation but do not retain these rows.
    if !lowered_unsupported.is_empty()
        && (tcx.sess.opts.unstable_opts.trust_dump.ir.is_some() || emit_requested(tcx))
    {
        if collect_all_overflowed {
            cascade_by_tag.insert("collect-all event overflow (>4096)".to_string(), 1);
        }
        let is_cascade = |t: &str| {
            t == "VarRef(unbound)"
                || t == "Borrow(unbound local)"
                || t == "Borrow(&mut unbound local)"
        };
        for (_detail, what) in collect_all {
            let dst = if is_cascade(what) { &mut cascade_by_tag } else { &mut primary_by_tag };
            let count = dst.entry((*what).to_string()).or_default();
            *count = count.saturating_add(1);
        }
    }
    let collect_primary = primary_by_tag.into_iter().collect();
    let collect_cascade = cascade_by_tag.into_iter().collect();

    // Snapshot typed verdicts while all producer reports are still in scope. Never reconstruct
    // them from logs or serialize the ambiguous `equal` boolean. Inconsistent producer fields are
    // retained as semantic finalization errors; the fallback value is deliberately `NotRun` and
    // can therefore never manufacture agreement even if a future caller mishandles the errors.
    let mut differential_errors = Vec::new();
    if interpreter_report.unsupported != lowered_unsupported {
        differential_errors.push(format!(
            "direct-THIR differential inventory mismatch for `{def_path}` (def index \
             {def_index}): report carried {} unsupported event(s), lowering carried {}",
            interpreter_report.unsupported.len(),
            lowered_unsupported.len(),
        ));
    }
    let retain_artifact_details =
        tcx.sess.opts.unstable_opts.trust_dump.ir.is_some() || emit_requested(tcx);
    let interpreter_detail = if retain_artifact_details {
        interpreter_report.notes.last().cloned().unwrap_or_default()
    } else {
        String::new()
    };
    let interpreter_verdict = match classify_interpreter_verdict(
        interpreter_report.mode,
        interpreter_report.equal,
        !interpreter_report.unsupported.is_empty(),
    ) {
        Ok(verdict) => verdict,
        Err(error) => {
            differential_errors.push(format!(
                "direct-THIR differential invariant failed for `{def_path}` (def index \
                 {def_index}): {error}"
            ));
            ArtifactVerdict::NotRun
        }
    };
    let interpreter = InterpreterEvidence {
        verdict: interpreter_verdict,
        samples: interpreter_report.samples_checked,
        detail: interpreter_detail,
    };
    if interpreter.verdict == ArtifactVerdict::Agreed && interpreter.samples == 0 {
        differential_errors.push(format!(
            "direct-THIR differential invariant failed for `{def_path}` (def index \
             {def_index}): agreement carried zero sampled executions"
        ));
    }
    let derived_mir = DerivedMirEvidence {
        verdict: match derived_report.verdict {
            crate::mir_differential::DerivedVerdict::DerivedAgreed => ArtifactVerdict::Agreed,
            crate::mir_differential::DerivedVerdict::DerivedMismatch => ArtifactVerdict::Mismatch,
            crate::mir_differential::DerivedVerdict::DerivedUnsupported => {
                ArtifactVerdict::Unsupported
            }
        },
        detail: if retain_artifact_details { derived_report.detail.clone() } else { String::new() },
        markers_exact: derived_report.markers_exact,
        markers_detail: if retain_artifact_details {
            derived_report.markers_detail.clone()
        } else {
            String::new()
        },
    };
    if deferred && interpreter.verdict != ArtifactVerdict::NotRun {
        differential_errors.push(format!(
            "direct-THIR deferred differential invariant failed for `{def_path}` (def index \
             {def_index}): hook-time verdict was `{}` instead of `not-run`",
            interpreter.verdict.marker(),
        ));
    }

    let rec = BodyRecord {
        def_index,
        kind: body_kind,
        symbolic,
        def_path,
        place_path_carrier,
        function,
        func_ty,
        structs: module.structs,
        enums: module.enums,
        types: module.types,
        // Trust (wave-16): promoted-borrow globals snapshot.
        globals: module.globals,
        // Trust (C2-spans): file table rides with the record for splice re-interning.
        files: module.files,
        unsupported,
        unsupported_details,
        collect_primary,
        collect_cascade,
        instr_count,
        callees,
        func_types: module.func_types,
        closure_types: module.closure_types,
        pending_consts,
        deferred,
        interpreter,
        derived_mir,
        differential_errors,
        mir_snapshot,
        lineage,
    };

    tcx.sess.with_trust_compiler_state::<CrateModuleRegistry, _>(|registry| {
        insert_registry_record(
            &mut registry.records,
            &mut registry.duplicate_def_indices,
            def_index,
            rec,
        );
    });
}

/// Direct THIR module verification capability carried by the finalizer and its
/// machine-readable coverage sidecar.
///
/// The structural lowering has no sound source-contract/obligation birth path
/// yet. In particular, it has no exact mapping from compiler contract variables
/// and state epochs to the direct THIR SSA values. Consequently an empty direct
/// obligation table means "not wired", never "verified with zero obligations".
/// Keep this typed marker at the producer boundary so enabling the lowering and
/// parity batteries cannot accidentally grant proof authority.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DirectObligationCapability {
    /// Structural lowering and differential parity only; no proof authority.
    StructuralParityOnly,
}

impl DirectObligationCapability {
    /// Stable spelling written to `coverage.json` and tracing output.
    pub const fn marker(self) -> &'static str {
        match self {
            Self::StructuralParityOnly => "structural-parity-only-v1",
        }
    }

    /// Whether this artifact may be treated as source-proof authority.
    pub const fn grants_proof_authority(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
        }
    }

    /// Whether this producer can build direct native verification requests.
    pub const fn emits_native_verification_requests(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
        }
    }
}

/// Current direct THIR obligation capability. Changing this is a deliberate
/// soundness event: source identity, typed formulas, state binding, and exact
/// function/obligation ownership must all be wired first.
pub const DIRECT_OBLIGATION_CAPABILITY: DirectObligationCapability =
    DirectObligationCapability::StructuralParityOnly;

/// What [`finalize_and_dump`] did. The compiler-side caller treats a non-empty
/// [`DumpSummary::errors`] as fatal because the user explicitly requested these
/// evidence artifacts.
pub struct DumpSummary {
    pub dir: PathBuf,
    /// Bodies recorded (i.e. bodies whose `mir_built` ran under the flag).
    pub bodies: usize,
    /// Bodies that lowered with zero `unsupported` entries.
    pub lowered: usize,
    /// Bodies spliced into the assembled crate `Module` as defined functions.
    pub spliced: usize,
    /// Fail-closed declarations created for extern / unresolvable callees.
    pub declarations: usize,
    /// I/O (or similar) failures, as human-readable strings.
    pub errors: Vec<String>,
}

/// Trust (B9-A): one crate-seam differential verdict for a DEFERRED (clean + call-bearing) body.
/// The compiler-side caller (`rustc_mir_build::trust_ir_crate_finalize`) re-emits each as the
/// standard `trust-ir-lower: differential` tracing event so the scorecard classifies it exactly
/// like a hook-time verdict — the difference is only that the callee bodies were linked at
/// finalize instead of being bodyless per-body declarations.
pub struct SeamVerdict {
    pub def_index: u32,
    pub equal: bool,
    pub samples: usize,
    pub mode: crate::differential::DiffMode,
    pub note: String,
}

/// Trust (B9-A): what [`finalize_and_dump`] produced. `seam` is emitted on every
/// direct-TrustIR compile (the registry is populated unconditionally for the
/// lane); `dump` is `Some` whenever either the dump option or first-class
/// `--emit=trust-ir` requested an artifact set.
pub struct FinalizeSummary {
    pub seam: Vec<SeamVerdict>,
    pub dump: Option<DumpSummary>,
    /// Semantic finalization failures independent of artifact publication.
    /// The compiler caller treats any entry as fatal even without a dump.
    pub errors: Vec<String>,
    /// Explicitly separates structural/parity output from proof authority.
    pub direct_obligations: DirectObligationCapability,
}

/// Trust (B9-A): the crate-seam call-linking differential. For every DEFERRED body (clean +
/// call-bearing, `BodyRecord::deferred`), interpretation-equivalence was NOT asserted at the hook
/// because the per-body module carried its callees as bodyless declarations. Here — after
/// [`assemble`] spliced the whole crate and rewrote every intra-crate callee `FuncId` — we gather
/// the deferred body's reachable-callee CLOSURE, build the MIR-side oracle by bundling each
/// closure member's `mir_snapshot` through the SAME `lower_to_trust_ir_functions` path the hook
/// uses for a single body, and run the sampled-interpretation comparison. Exactly one
/// [`SeamVerdict`] per deferred body; every gate fails CLOSED to a coverage-only `NotRun` skip
/// (never a false equivalence claim).
fn run_seam_differentials(records: &[BodyRecord], assembled: &Assembled) -> Vec<SeamVerdict> {
    use crate::differential::{self, DiffMode};

    let skip = |def_index: u32, note: &str| SeamVerdict {
        def_index,
        equal: false,
        samples: 0,
        mode: DiffMode::NotRun,
        note: note.to_string(),
    };

    // `records` and `assembled.assigned` are both def_index-sorted; `assigned[i] == (def_i, FuncId(i))`
    // (spliced functions are added in ascending def_index == ascending FuncId order, `f.id = new_id`).
    let rec_by_def = |def_index: u32| -> Option<&BodyRecord> {
        records.binary_search_by_key(&def_index, |r| r.def_index).ok().map(|i| &records[i])
    };
    // Spliced (dense) FuncId -> its callee def_index. Declaration FuncIds (>= assigned.len()) return
    // None here — but they are filtered by the step-2 declaration gate before this is reached.
    let def_of_func =
        |fid: FuncId| -> Option<u32> { assembled.assigned.get(fid.as_usize()).map(|(d, _)| *d) };
    let func_of_def = |def_index: u32| -> Option<FuncId> {
        assembled
            .assigned
            .binary_search_by_key(&def_index, |(d, _)| *d)
            .ok()
            .map(|i| assembled.assigned[i].1)
    };

    let mut verdicts = Vec::new();
    for r in records.iter().filter(|r| r.deferred) {
        // Trust (B3-2c seam guard): a place-path VALUE-carrier body is CLEAN-ONLY
        // by the wave-RS/MC contract ("never interpreted") — the carrier arg is a
        // VALUE standing in for the callee's pointer param, so linked
        // interpretation manufactures a signature-mismatch THIR-defect verdict
        // out of a deliberate spelling. Fail closed to coverage. Genuinely
        // ill-typed calls (no carrier) still surface as defects.
        if r.place_path_carrier {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: call args carry a place-path value carrier \
                 (CLEAN-ONLY receiver spelling); linked interpretation not asserted \
                 (coverage-only)",
            ));
            continue;
        }
        // step 0 — entry: the deferred body must be spliced into the crate module.
        let Some(entry) = func_of_def(r.def_index) else {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: entry not spliced into the crate module; coverage-only skip",
            ));
            continue;
        };

        // step 1 — reachable-callee closure: BFS over the assembled module from `entry`. Edges:
        // `Inst::Call{callee}`, `Inst::Const{Constant::FnDef}` (reified fn pointers — the same
        // ledger-rewritten ids assemble produced), and a defensive `Inst::Invoke{callee}` arm (the
        // producer never emits it). `CallIndirect` carries no static target — every reified target
        // is a FnDef const already walked, and a fn-ptr PARAM cannot inject an outside target
        // (`Ty::Func` params fail the scalar sample gate downstream).
        let mut closure: Vec<FuncId> = Vec::new();
        let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack = vec![entry];
        while let Some(fid) = stack.pop() {
            if !seen.insert(fid.index()) {
                continue;
            }
            closure.push(fid);
            let Some(func) = assembled.module.function_by_id(fid) else { continue };
            for block in &func.blocks {
                for node in &block.body {
                    match &node.inst {
                        Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                            stack.push(*callee)
                        }
                        Inst::Const { value: Constant::FnDef(target), .. } => stack.push(*target),
                        _ => {}
                    }
                }
            }
        }

        // step 2 — declaration gate: any bodyless callee in the closure means there is no local
        // body to link (extern / havoc / unresolved). LOAD-BEARING: a reachable vararg-sig
        // declaration would err `SignatureMismatch` in the interpreter, which would surface as a
        // FALSE oracle verdict.
        if closure.iter().any(|&fid| {
            assembled.module.function_by_id(fid).map(|f| f.is_declaration()).unwrap_or(true)
        }) {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: reachable callee closure includes an extern/declaration-only \
                 callee (no local body to link); crate-seam interpretation not asserted \
                 (coverage-only)",
            ));
            continue;
        }

        // step 3 — THIR Undef tripwire, scoped PER-CLOSURE (not whole-module: one unrelated
        // invariant-violating body must not over-skip every deferred body).
        if closure.iter().any(|&fid| {
            assembled
                .module
                .function_by_id(fid)
                .map(differential::function_has_undef)
                .unwrap_or(false)
        }) {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: THIR crate module function unexpectedly carries Inst::Undef \
                 (producer invariant violated); coverage-only skip",
            ));
            continue;
        }

        // step 4 — snapshot gathering. Map each closure FuncId -> callee def_index -> its record's
        // `mir_snapshot`. Any missing snapshot (e.g. a finalizer-patched pending-const callee whose
        // hook-time snapshot was skipped) => callee-set asymmetry => fail-closed skip.
        let asymmetry = |def_index: u32| {
            skip(
                def_index,
                "seam-deferred body: callee-set asymmetry between THIR crate module and MIR oracle \
                 bundle (callee def_path sets differ, or a declaration / absent-callee marker in \
                 the reachable closure); fail-closed skip (coverage-only)",
            )
        };
        let mut members: Vec<(u32, &trust_types::VerifiableFunction)> = Vec::new();
        let mut ok = true;
        for &fid in &closure {
            let Some(di) = def_of_func(fid) else {
                ok = false;
                break;
            };
            let Some(vf) = rec_by_def(di).and_then(|rec| rec.mir_snapshot.as_ref()) else {
                ok = false;
                break;
            };
            members.push((di, vf));
        }
        if !ok {
            verdicts.push(asymmetry(r.def_index));
            continue;
        }
        // Bundle FuncIds are positional in the passed order; sort by def_index for determinism.
        members.sort_by_key(|(di, _)| *di);
        let Some(entry_slot) = members.iter().position(|(di, _)| *di == r.def_index) else {
            verdicts.push(asymmetry(r.def_index));
            continue;
        };
        let funcs: Vec<trust_types::VerifiableFunction> =
            members.iter().map(|(_, vf)| (*vf).clone()).collect();

        // step 5 — bundle: the PLAIN entry (no expected-absent set) so any absent DIRECT callee
        // keeps the fatal ABSENT_CALLEE marker (screened next).
        let bundle = match trust_ir_bridge::lower_mir_compat_functions_to_trust_ir(
            format!("{}::seam", assembled.module.name),
            &funcs,
        ) {
            Ok(m) => m,
            Err(e) => {
                verdicts.push(skip(
                    r.def_index,
                    &format!(
                        "seam-deferred body: MIR oracle bundle construction failed ({e:?}); \
                         coverage-only skip — NOT a THIR divergence"
                    ),
                ));
                continue;
            }
        };

        // step 6 — absent-callee/asymmetry scan. MUST precede the panic-model scan (the absent
        // encoding IS an `Assert(const false)`). A marker means the MIR side demanded a callee
        // outside the THIR closure's body set => the callee def_path sets differ.
        if bundle.proof_obligations.iter().any(|o| {
            o.description.contains(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        }) {
            verdicts.push(asymmetry(r.def_index));
            continue;
        }

        // step 7 — bundle preprocessing (same order/semantics as the hook's single-body path).
        if differential::oracle_has_const_false_assert(&bundle) {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: oracle bundle models a diverging panic call as an \
                 unconditional assert(false) (oracle-panic-model); coverage-only skip",
            ));
            continue;
        }
        let mut bundle = bundle;
        differential::rewrite_bool_not_icmp(&mut bundle);
        let bundle = match differential::classify_undefs(&bundle) {
            differential::UndefClass::Live => {
                verdicts.push(skip(
                    r.def_index,
                    "seam-deferred body: MIR oracle bundle carries a LIVE havoc (`Inst::Undef` \
                     outside the proven-dead-seed shape); coverage-only skip — NOT a THIR \
                     divergence",
                ));
                continue;
            }
            differential::UndefClass::DeadSeeds => differential::substitute_dead_seeds(bundle),
            differential::UndefClass::None => bundle,
        };

        // step 8 — verdict.
        let mut rep = differential::compare_entries(
            &assembled.module,
            entry,
            &bundle,
            FuncId::new(entry_slot as u32),
        );
        // Trust: `compare_entries` is the classification authority. In particular, a typed
        // `MirOracle` result is never reclassified by matching its human-readable note. Structural
        // signature comparison already resolves module-local ids through each module's own tables,
        // and the producer emits canonical zero-result unit calls, so neither case needs a seam-only
        // exception. Any remaining signature/result-arity mismatch is a genuine lowering defect.
        if rep.mode == DiffMode::Agreed {
            rep.notes.push(format!(
                "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (seam differential: \
                 call-bearing body linked at crate finalize)",
                rep.samples_checked
            ));
        }
        verdicts.push(SeamVerdict {
            def_index: r.def_index,
            equal: rep.equal,
            samples: rep.samples_checked,
            mode: rep.mode,
            note: rep.notes.last().cloned().unwrap_or_default(),
        });
    }
    verdicts
}

/// Bind crate-seam results back to their deterministic per-body artifact rows.
///
/// The relationship is exact: every deferred row receives one result, non-deferred rows receive
/// none, and duplicate/unknown results fail semantic finalization. This turns a tracing stream
/// into a typed inventory and prevents an omitted seam callback from leaving a plausible-looking
/// hook-time `NotRun` row in a published artifact.
fn install_seam_outcomes(rows: &mut [CoverageRow], verdicts: &[SeamVerdict]) -> Vec<String> {
    use std::collections::btree_map::Entry;

    let mut errors = Vec::new();
    let mut by_def = BTreeMap::<u32, &SeamVerdict>::new();
    for verdict in verdicts {
        match by_def.entry(verdict.def_index) {
            Entry::Vacant(entry) => {
                entry.insert(verdict);
            }
            Entry::Occupied(_) => errors.push(format!(
                "direct-THIR seam inventory contained duplicate verdicts for def index {}",
                verdict.def_index
            )),
        }
    }

    for row in rows {
        let outcome = by_def.remove(&row.def_index);
        match (row.deferred_to_seam, outcome) {
            (true, Some(outcome)) => {
                match classify_interpreter_verdict(outcome.mode, outcome.equal, false) {
                    Ok(verdict) => {
                        if verdict == ArtifactVerdict::Agreed && outcome.samples == 0 {
                            errors.push(format!(
                                "direct-THIR seam verdict for `{}` (def index {}) claimed \
                                 agreement without a sampled execution",
                                row.def_path, row.def_index
                            ));
                            continue;
                        }
                        row.seam = Some(InterpreterEvidence {
                            verdict,
                            samples: outcome.samples,
                            detail: outcome.note.clone(),
                        });
                    }
                    Err(error) => errors.push(format!(
                        "direct-THIR seam differential invariant failed for `{}` (def index \
                         {}): {error}",
                        row.def_path, row.def_index
                    )),
                }
            }
            (true, None) => errors.push(format!(
                "direct-THIR seam inventory omitted deferred body `{}` (def index {})",
                row.def_path, row.def_index
            )),
            (false, Some(_)) => errors.push(format!(
                "direct-THIR seam inventory produced an outcome for non-deferred body `{}` \
                 (def index {})",
                row.def_path, row.def_index
            )),
            (false, None) => {}
        }
    }

    for (def_index, _) in by_def {
        errors.push(format!(
            "direct-THIR seam inventory produced an outcome for unknown def index {def_index}"
        ));
    }
    errors
}

/// Require an exact one-to-one handoff from rustc's HIR body inventory to the
/// direct-THIR registry. An unsupported body still has a `BodyRecord` carrying
/// explicit reasons; absence is never another spelling of "unsupported".
///
/// Both inputs are reduced to plain ids so this invariant is unit-testable
/// without a `TyCtxt`. The finalizer supplies the complete `hir_body_owners`
/// inventory after forcing `mir_built` and the BTreeMap-backed registry drain.
fn body_inventory_errors(expected: &[u32], recorded: &[u32]) -> Vec<String> {
    let expected_set = expected.iter().copied().collect::<BTreeSet<_>>();
    let recorded_set = recorded.iter().copied().collect::<BTreeSet<_>>();
    let missing = expected_set.difference(&recorded_set).copied().collect::<Vec<_>>();
    let unexpected = recorded_set.difference(&expected_set).copied().collect::<Vec<_>>();
    let duplicate_expected = expected.len().saturating_sub(expected_set.len());
    let duplicate_recorded = recorded.len().saturating_sub(recorded_set.len());

    if missing.is_empty()
        && unexpected.is_empty()
        && duplicate_expected == 0
        && duplicate_recorded == 0
    {
        return Vec::new();
    }

    vec![format!(
        "direct-THIR body inventory mismatch: expected {} unique HIR body owner(s), recorded {} \
         unique lowering(s); missing def indices {missing:?}; unexpected def indices \
         {unexpected:?}; duplicate expected ids {duplicate_expected}; duplicate recorded ids \
         {duplicate_recorded}",
        expected_set.len(),
        recorded_set.len(),
    )]
}

/// Enforce the semantic half of [`DirectObligationCapability::StructuralParityOnly`].
///
/// The sidecar marker alone is descriptive metadata and therefore cannot be
/// the authority boundary. Until the direct frontend has exact contract/SSA
/// bindings and owns obligation birth, every claim-bearing table must remain
/// empty. A `SpecModule::Linked` is also authority-bearing: TrustIR defines it
/// as a certifying source/spec relationship even without proof bindings.
/// Instruction-level `ProofAnnotation`s are intentionally excluded: those
/// annotate structural panic checks for MIR parity and are not discharged
/// function/module claims.
fn direct_authority_inventory_errors(module: &Module) -> Vec<String> {
    let obligations = module.proof_obligations.len();
    let certificates = module.proof_certificates.len();
    let diagnostics = module.obligation_diagnostics.len();
    let function_claims: usize =
        module.functions.iter().map(|function| function.proofs.len()).sum();
    let function_summaries =
        module.functions.iter().filter(|function| function.summary.is_some()).count();
    let spec_proofs: usize = module.spec_modules.iter().map(|spec| spec.proofs.len()).sum();
    let linked_specs = module
        .spec_modules
        .iter()
        .filter(|spec| spec.enforcement == trust_ir::SpecEnforcementMode::Linked)
        .count();

    if obligations == 0
        && certificates == 0
        && diagnostics == 0
        && function_claims == 0
        && function_summaries == 0
        && spec_proofs == 0
        && linked_specs == 0
    {
        return Vec::new();
    }

    vec![format!(
        "direct-THIR structural-parity-only authority tripwire: obligations {obligations}, \
         certificates {certificates}, obligation diagnostics {diagnostics}, function claims \
         {function_claims}, function summaries {function_summaries}, spec proof bindings \
         {spec_proofs}, linked spec modules {linked_specs}; direct artifacts cannot carry \
         proof/contract authority until exact source-contract, SSA-state, and \
         obligation-ownership wiring exists"
    )]
}

fn failed_semantic_finalization(
    mut errors: Vec<String>,
    prepared_publication: Option<PreparedPublication>,
    emit_target: Option<&EmitPublicationTarget>,
) -> FinalizeSummary {
    debug_assert!(!errors.is_empty());
    // Dropping a prepared transaction releases its writer lease without
    // publishing a commit marker; preparation already invalidated the prior
    // generation.
    drop(prepared_publication);
    // The dump transaction may own the same directory-wide in-process lock as
    // the first-class emit target, so invalidate the emit generation only
    // after releasing it. Dropping the newly prepared transaction deliberately
    // leaves no commit marker: a failed compile can never make an older emit
    // generation look current.
    if let Some(target) = emit_target {
        match prepare_emit_publication(target) {
            Ok(prepared) => drop(prepared),
            Err(error) => errors.push(format!(
                "failed to invalidate --emit=trust-ir target after semantic failure: {error}"
            )),
        }
    }
    FinalizeSummary {
        seam: Vec::new(),
        dump: None,
        errors,
        direct_obligations: DIRECT_OBLIGATION_CAPABILITY,
    }
}

/// Carry the experimental deferred-verification provenance as digest-bearing,
/// explicitly non-certifying metadata. A `DesignOnly` spec module is the one
/// existing TrustIR channel whose contract says “descriptive material, no proof
/// authority”; using a pending proof obligation here would falsely suggest that
/// an in-tree verifier had a subject and payload it could discharge.
fn install_deferred_verification_disclosure(
    tcx: TyCtxt<'_>,
    module: &mut Module,
    lowered: usize,
    bodies: usize,
) -> Result<(), String> {
    if !tcx.trust_defer_verification() {
        return Ok(());
    }

    const NAME: &str = "@trust-internal::deferred-verification-disclosure-v1";
    if module.spec_modules.iter().any(|spec| spec.name == NAME) {
        return Err(format!("reserved deferred-verification disclosure name collision: {NAME}"));
    }

    let mut disclosure = SpecModule::new(NAME);
    disclosure.invariants.push(SpecInvariant::new(
        "disclosure",
        format!(
            "NON-CERTIFYING DISCLOSURE: rustc borrow/ownership rejection checks were not run \
             for ordinary function bodies; this module carries no loan sets or region facts, \
             and no in-tree verifier can decide that safety claim from this payload. {}/{} \
             bodies did not lower and therefore have no TrustIR subject. This artifact MUST \
             NOT be treated as borrow-checked.",
            bodies.saturating_sub(lowered),
            bodies,
        ),
    ));
    module.spec_modules.push(disclosure);
    Ok(())
}

/// Trust: the crate-level finalizer. Called (via `rustc_mir_build::trust_ir_crate_finalize`) from
/// the `rustc_interface` `analysis` seam after the crate has been confirmed error-free. It forces
/// `mir_built` for every body owner after taking the interface-prepared, already-invalidated
/// artifact transaction, then drains the resulting direct-THIR registry. The seam differential is inert
/// when the crate has no HIR body owners; an explicitly requested genuinely empty dump still
/// publishes a deterministic empty module and coverage sidecar. A partial/missing registry is a
/// semantic finalization error, never an empty success.
pub fn finalize_and_dump(tcx: TyCtxt<'_>) -> FinalizeSummary {
    // Trust (B9-A): the registry drain, resolve, and assemble now run UNGATED — the crate-seam
    // differential ([`run_seam_differentials`]) needs the assembled crate module on every
    // `-Z trust-ir-lower` compile, not only when `-Z trust-dump=ir:` requested an artifact. Only
    // the artifact write stays behind the dump option. Session-scoped storage prevents records
    // leaking when one rustc process creates multiple compiler Sessions.
    let dump_dir = tcx.sess.opts.unstable_opts.trust_dump.ir.clone();
    let first_class_emit_requested = emit_requested(tcx);
    let emit_output = emit_path(tcx);
    let (emit_target, emit_preflight_errors) = match emit_output.as_deref() {
        Some(path) => match emit_publication_target(path) {
            Ok(target) => (Some(target), Vec::new()),
            Err(error) => (None, vec![error]),
        },
        None if first_class_emit_requested => (
            None,
            vec![
                "--emit=trust-ir requires a real output file; stdout (`-`) is unsupported"
                    .to_string(),
            ],
        ),
        None => (None, Vec::new()),
    };
    let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
    let binary_name = format!("{crate_name}.trust-ir.bin");
    let text_name = format!("{crate_name}.trust-ir.txt");
    // coverage.json is the generation-bound commit marker: data files are
    // durable before it appears, and consumers reject a missing marker.
    let coverage_name = format!("{crate_name}.coverage.json");
    // rustc_interface prepared and invalidated this explicit target before
    // input I/O. `take_artifact_publication` is also the fallback
    // for custom compiler drivers that enter a `TyCtxt` without that hook.
    let (prepared_publication, publication_prepare_errors) =
        match take_artifact_publication(tcx.sess, &crate_name) {
            Ok(prepared) => (prepared, Vec::new()),
            Err(error) => (None, vec![error]),
        };
    // The side-effect registry is not a dependency-tracked query output, so
    // finalization must not infer its completeness from whichever downstream
    // analyses happened to run. Explicitly ensure every HIR body owner's live
    // `mir_built` query before draining the registry. This must happen AFTER publication
    // preparation: a lowering-query failure must not leave a prior successful
    // artifact set looking current.
    let expected_body_indices =
        tcx.hir_body_owners().map(|def| def.to_def_id().index.as_u32()).collect::<Vec<_>>();
    tcx.par_hir_body_owners(|def| tcx.ensure_done().mir_built(def));
    let drained_registry =
        tcx.sess.with_trust_compiler_state::<CrateModuleRegistry, _>(std::mem::take);
    let mut records = drained_registry.records.into_values().collect::<Vec<_>>();
    // Determinism anchor: BTreeMap drainage above yields DefIndex order without
    // an additional sort pass. Duplicate callbacks are retained separately and
    // folded into the registration inventory so they cannot be hidden by the
    // unique-key map.
    let mut recorded_body_indices =
        records.iter().map(|record| record.def_index).collect::<Vec<_>>();
    recorded_body_indices.extend(drained_registry.duplicate_def_indices);
    let mut errors = emit_preflight_errors;
    errors.extend(body_inventory_errors(&expected_body_indices, &recorded_body_indices));
    if !errors.is_empty() {
        // The prepared publication transaction has already invalidated the old
        // generation. Drop it without publishing, and do not run const
        // resolution, crate assembly, or seam differentials over a known-
        // incomplete module: even a NotRun/Agreed event would misrepresent the
        // producer inventory. `std::mem::take` above reset *all* session state.
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }
    errors.extend(records.iter().flat_map(|record| record.differential_errors.iter().cloned()));
    if !errors.is_empty() {
        // Typed verdicts are part of the direct-lane evidence contract. Do not resolve consts,
        // assemble, compare at the seam, or publish if the hook supplied an internally
        // inconsistent report: even a fail-safe row would disguise a producer wiring defect.
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Trust: reentrancy-safe local-const evaluation. THIS seam — after `run_required_analyses`
    // has forced `mir_built` for every body owner (via `mir_borrowck` on ordinary lanes, via
    // the explicit force on the deferred-verification lane) — is where
    // `const_eval_resolve_for_typeck` on a local const can no longer re-enter an in-flight
    // MIR-building query (the E0391 cycles / CTFE ICE the hook defers around). Each pending
    // placeholder is patched with the REAL evaluated value, or the body is marked unsupported
    // (never spliced, never a guessed value).
    resolve_pending_consts(tcx, &mut records);

    let mut assembled = assemble(&crate_name, &records);
    stamp_target_info_if_vacuous(tcx, &mut assembled.module);
    // Trust (#181): THE PRODUCER NOW VALIDATES ITS OWN OUTPUT. Log-only.
    //
    // Nothing in this pipeline ever asked "is the module I just emitted WELL-FORMED?". The
    // coverage ratchet asks only "did this body lower without a fail-closed tag", and those are
    // different questions: a corpus sweep with the trust-ir validator found ~31% of emitted
    // modules REJECTED, across four classes, none of which any gate could see. Two were real
    // defects with a silent blast radius — an equal-width `trunc` the format forbids (#164, now
    // fixed), and an `InstrResultArityMismatch` whose mismatched SSA result gets no `val_ty`
    // entry at all, so every downstream type check on that value is vacuously skipped.
    //
    // This is deliberately a TRIPWIRE, not a gate. It emits one debug event per error CLASS so
    // the scorecard can ratchet the counts; it does not fail the build, does not touch `errors`,
    // and does not change a single verdict. Turning it into a gate is a separate, ratified step
    // that has to wait until the known classes are down — a gate that fires on a third of all
    // modules would be turned off within a day, which is how a load-bearing check dies.
    //
    // Costs nothing on a normal compile: `tracing::enabled!` short-circuits before the walk, so
    // only a run that is already collecting debug output (the scorecard) pays for it.
    if tracing::enabled!(tracing::Level::DEBUG) {
        let verrors = trust_ir_build::validate_module(&assembled.module);
        let mut by_class: BTreeMap<String, u64> = BTreeMap::new();
        for e in &verrors {
            let class = validation_error_class(e);
            *by_class.entry(class).or_default() += 1;
        }
        for (class, n) in by_class {
            tracing::debug!(class = %class, n, "trust-ir-lower: module validation error");
        }
        tracing::debug!(
            total = verrors.len(),
            "trust-ir-lower: module validation summary"
        );
    }
    errors.extend(direct_authority_inventory_errors(&assembled.module));
    if !errors.is_empty() {
        // Never feed an authority-bearing direct module into the structural
        // seam oracle. The capability tripwire is a pre-consumption gate, not
        // merely a publication check.
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Trust (temporal-carry, RFC-trust-temporal-extraction §2.2): CARRY the §2.1
    // `#[trust::var]`/`#[trust::action]` tool attributes into the emitted module via the
    // existing SpecModule metadata channel — the same channel `spec-link` metadata rides —
    // so the temporal-extractor recovers the projection/actions from the MODULE, not by
    // re-parsing the target SOURCE. These modules are explicitly DesignOnly:
    // the direct lane has not earned TrustIR's certifying `Linked` state. The
    // metadata is still structurally validated and is inert when no
    // `#[trust::var]`/`#[trust::action]` annotations are present (empty vector
    // → byte-identical dump for un-annotated crates).
    let temporal = derive_temporal_spec_modules(tcx, &assembled.assigned, &assembled.module);
    errors.extend(install_temporal_modules(&mut assembled.module, temporal));
    if let Err(error) = install_deferred_verification_disclosure(
        tcx,
        &mut assembled.module,
        assembled.lowered,
        records.len(),
    ) {
        errors.push(error);
    }
    errors.extend(direct_authority_inventory_errors(&assembled.module));
    if !errors.is_empty() {
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Trust (B9-A): the crate-seam call-linking differential — exactly one verdict per DEFERRED
    // (clean + call-bearing) body, computed only after the module has passed the complete
    // structural-only authority boundary. Runs on every `-Z trust-ir-lower` compile, independent
    // of `TRUST_IR_DUMP`.
    let seam = run_seam_differentials(&records, &assembled);
    errors.extend(install_seam_outcomes(&mut assembled.coverage_rows, &seam));
    if !errors.is_empty() {
        // A partial, duplicate, unexpected, or internally inconsistent seam stream cannot back a
        // per-body evidence artifact. Abort even when no dump was requested so tracing and
        // publication share the same exact inventory contract.
        return failed_semantic_finalization(errors, prepared_publication, emit_target.as_ref());
    }

    // Trust (B9-A): seam verdicts above are returned regardless of artifact
    // output. Dump and first-class emit targets share the exact same rendered
    // module, but each gets a target-specific, digest-bearing commit marker.
    let artifact_requested = dump_dir.is_some() || first_class_emit_requested;
    let mut publication_errors = publication_prepare_errors;
    let mut rendered = None;
    if artifact_requested {
        // Finalizer tripwire: the assembled module must contain ZERO pending-
        // const sentinels. On a hit, neither target is published.
        let leftover_sentinels = count_const_sentinels(&assembled.module);
        if leftover_sentinels > 0 {
            publication_errors.push(format!(
                "tripwire: {leftover_sentinels} unpatched pending-const sentinel(s) in the \
                 assembled module; artifacts NOT written"
            ));
        }
        if publication_errors.is_empty() {
            match coverage_json(
                &crate_name,
                &assembled.coverage_rows,
                assembled.spliced,
                assembled.declarations,
            ) {
                Ok(coverage) => {
                    rendered = Some((
                        coverage,
                        trust_ir::binary::serialize_module(&assembled.module),
                        trust_ir::format::canonical(&assembled.module).into_bytes(),
                    ));
                }
                Err(error) => publication_errors.push(error),
            }
        }
    }

    let mut prepared_publication = prepared_publication;
    if dump_dir.is_some() && publication_errors.is_empty() {
        match (rendered.as_ref(), prepared_publication.take()) {
            (Some((coverage_json, bin, txt)), Some(prepared)) => {
                match coverage_publication_manifest(
                    coverage_json,
                    &binary_name,
                    bin,
                    &text_name,
                    txt,
                ) {
                    Ok(coverage) => {
                        let artifacts = [
                            Artifact { name: &binary_name, bytes: bin },
                            Artifact { name: &text_name, bytes: txt },
                            Artifact { name: &coverage_name, bytes: &coverage },
                        ];
                        if let Err(error) = prepared.publish(&artifacts) {
                            publication_errors
                                .push(format!("dump artifact publication failed: {error}"));
                        }
                    }
                    Err(error) => publication_errors.push(error),
                }
            }
            (None, _) => publication_errors
                .push("artifact bytes were not rendered after successful finalization".into()),
            (_, None) => publication_errors.push(
                "dump publication target was not prepared after successful finalization".into(),
            ),
        }
    }
    // A prepared dump transaction holds a directory-wide in-process lease.
    // Release it before preparing an emit target, which may live in that same
    // directory. This also leaves a failed dump without a current marker.
    drop(prepared_publication);

    if let Some(target) = emit_target.as_ref() {
        match prepare_emit_publication(target) {
            Ok(prepared) if publication_errors.is_empty() => match rendered.as_ref() {
                Some((coverage_json, bin, txt)) => {
                    match coverage_publication_manifest(
                        coverage_json,
                        &target.binary_name,
                        bin,
                        &target.text_name,
                        txt,
                    ) {
                        Ok(coverage) => {
                            let artifacts = [
                                Artifact { name: &target.binary_name, bytes: bin },
                                Artifact { name: &target.text_name, bytes: txt },
                                Artifact { name: &target.coverage_name, bytes: &coverage },
                            ];
                            if let Err(error) = prepared.publish(&artifacts) {
                                publication_errors.push(format!(
                                    "--emit=trust-ir artifact publication failed: {error}"
                                ));
                            }
                        }
                        Err(error) => publication_errors.push(error),
                    }
                }
                None => publication_errors
                    .push("artifact bytes were not rendered after successful finalization".into()),
            },
            Ok(prepared) => {
                // Another requested target already failed. Preparation still
                // invalidated the old emit marker; do not publish a partial
                // multi-target generation.
                drop(prepared);
            }
            Err(error) => publication_errors.push(format!(
                "--emit=trust-ir target preparation failed for `{}`: {error}",
                target.directory.display()
            )),
        }
    }

    let dump = artifact_requested.then(|| DumpSummary {
        dir: dump_dir
            .clone()
            .or_else(|| emit_target.as_ref().map(|target| target.directory.clone()))
            .unwrap_or_default(),
        bodies: records.len(),
        lowered: assembled.lowered,
        spliced: assembled.spliced,
        declarations: assembled.declarations,
        errors: publication_errors,
    });

    FinalizeSummary { seam, dump, errors, direct_obligations: DIRECT_OBLIGATION_CAPABILITY }
}

// ---------------------------------------------------------------------------
// Temporal annotation carry (RFC-trust-temporal-extraction §2.1/§2.2).
//
// The compiler's job (per §2.2) is *carrying* the human-authored
// `#[trust::var]` / `#[trust::action]` tool attributes into `trust_ir::Module`
// so the temporal-extractor reads the projection/actions from the MODULE rather
// than re-parsing the target SOURCE. The projection rides `SpecModule` metadata;
// each action is bound to its exact assembled function by `SpecAnchor::function`.
//
// Mapping (lossless enough to recover the projection from the module):
//   #[trust::var(name = N, kind = K)]  on a struct field
//       -> spec_module <Struct> { var "N" : "K" }        (SpecVar name/ty)
//   #[trust::action(name = A, guard = G, ghost = H)] on a method
//       -> spec_module <Self DefPath> { action "A"
//                               anchor ... function <FuncId>
//                               invariant "A.guard" : "G"
//                               invariant "A.ghost" : "H" }
// Tool attributes are `Attribute::Unparsed` (`get_all_attrs` preserves them
// verbatim; built-ins are parsed+stripped), so a path match on `[trust, var|action]`
// plus `meta_item_list()` name=value extraction is the correct read idiom
// (mirrors `trust_verify::item_has_trust_attr`).
// Ownership walks stop at the nearest action Self: it is an explicit semantic
// machine boundary, so unrelated wrappers may embed it freely. Ambiguity before
// that boundary and any by-value path connecting two action owners fail closed.
// ---------------------------------------------------------------------------

/// Does this attribute's path equal `trust::<name>`?
fn is_trust_attr(attr: &rustc_hir::Attribute, name: &str) -> bool {
    matches!(
        attr.path().as_slice(),
        [tool, n] if tool.as_str() == "trust" && n.as_str() == name
    )
}

/// Crate-wide placement accounting for the temporal tool attributes.
///
/// `hir_walk_attributes` traverses every local HIR attribute map, including
/// item, field, statement, and expression attributes. Collection marks only
/// supported struct-field `var` and impl-method `action` occurrences consumed;
/// any remainder is therefore an authored attribute that would otherwise be
/// silently ignored by the two semantic collection loops.
#[derive(Default)]
struct TemporalAttributeAudit {
    occurrences: Vec<(AttrId, &'static str, Span)>,
    consumed: FxHashSet<AttrId>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for TemporalAttributeAudit {
    fn visit_attribute(&mut self, attr: &'tcx rustc_hir::Attribute) {
        for name in ["var", "action"] {
            if is_trust_attr(attr, name) {
                self.occurrences.push((attr.id(), name, attr.span()));
            }
        }
    }
}

impl TemporalAttributeAudit {
    fn collect(tcx: TyCtxt<'_>) -> Self {
        let mut audit = Self::default();
        tcx.hir_walk_attributes(&mut audit);
        audit
    }

    fn consume(&mut self, attrs: &[rustc_hir::Attribute], name: &'static str) {
        self.consumed
            .extend(attrs.iter().filter(|attr| is_trust_attr(attr, name)).map(|attr| attr.id()));
    }

    fn reject_unconsumed(self, tcx: TyCtxt<'_>) -> Result<(), TemporalCarryError> {
        let Some((_, attribute, span)) =
            self.occurrences.into_iter().find(|(id, _, _)| !self.consumed.contains(id))
        else {
            return Ok(());
        };
        let detail = match attribute {
            "var" => {
                "unsupported target; #[trust::var] is only supported on fields of local structs"
            }
            "action" => {
                "unsupported target; #[trust::action] is only supported on methods in impl blocks"
            }
            _ => unreachable!("temporal attribute audit records only var/action"),
        };
        Err(TemporalCarryError::MalformedAttribute {
            target: tcx.sess.source_map().span_to_diagnostic_string(span),
            attribute,
            detail: detail.to_string(),
        })
    }
}

fn install_temporal_modules(
    module: &mut Module,
    derived: Result<Vec<SpecModule>, TemporalCarryError>,
) -> Vec<String> {
    match derived {
        Ok(spec_modules) => {
            module.spec_modules.extend(spec_modules);
            Vec::new()
        }
        Err(error) => vec![format!("temporal annotation carry failed closed: {error}")],
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TemporalCarryError {
    MalformedAttribute { target: String, attribute: &'static str, detail: String },
    AmbiguousHolder { held: String, holders: Vec<String> },
    OwnershipCycle { owner: String },
    UnownedVariable { owner: String, name: String },
    DeepOwnership { owner: String, name: String, depth: usize },
    DuplicateVariable { machine: String, name: String },
    DuplicateProjection { machine: String, path: String },
    DuplicateAction { machine: String, name: String },
    NestedActionOwners { inner: String, outer: String },
    ActionWithoutVariables { machine: String },
    ActionWithoutSelf { action: String, symbol: String },
    NonStructActionOwner { action: String, owner: String },
    UnsplicedAction { action: String, symbol: String },
    FunctionIdentityMismatch { action: String, symbol: String, function: FuncId },
    DuplicateInvariant { machine: String, name: String },
}

impl fmt::Display for TemporalCarryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedAttribute { target, attribute, detail } => {
                write!(f, "malformed #[trust::{attribute}] on `{target}`: {detail}")
            }
            Self::AmbiguousHolder { held, holders } => {
                write!(f, "ambiguous temporal owner for `{held}`: held by {}", holders.join(", "))
            }
            Self::OwnershipCycle { owner } => {
                write!(f, "temporal by-value ownership cycle at `{owner}`")
            }
            Self::UnownedVariable { owner, name } => {
                write!(f, "temporal variable `{name}` on `{owner}` has no #[trust::action] owner")
            }
            Self::DeepOwnership { owner, name, depth } => write!(
                f,
                "temporal variable `{name}` on `{owner}` is {depth} ownership edges below its action owner; at most one is supported"
            ),
            Self::DuplicateVariable { machine, name } => {
                write!(f, "duplicate temporal variable `{name}` in machine `{machine}`")
            }
            Self::DuplicateProjection { machine, path } => {
                write!(f, "duplicate temporal projection path `{path}` in machine `{machine}`")
            }
            Self::DuplicateAction { machine, name } => {
                write!(f, "duplicate temporal action `{name}` in machine `{machine}`")
            }
            Self::NestedActionOwners { inner, outer } => write!(
                f,
                "nested temporal action owners are ambiguous: `{inner}` is held beneath `{outer}`"
            ),
            Self::ActionWithoutVariables { machine } => write!(
                f,
                "temporal action owner `{machine}` has no uniquely owned #[trust::var] variables"
            ),
            Self::ActionWithoutSelf { action, symbol } => write!(
                f,
                "temporal action `{action}` (`{symbol}`) is an associated function without a self receiver"
            ),
            Self::NonStructActionOwner { action, owner } => {
                write!(f, "temporal action `{action}` has non-struct impl Self owner `{owner}`")
            }
            Self::UnsplicedAction { action, symbol } => {
                write!(f, "temporal action `{action}` (`{symbol}`) has no exact assembled FuncId")
            }
            Self::FunctionIdentityMismatch { action, symbol, function } => write!(
                f,
                "temporal action `{action}` expected `{symbol}` at FuncId {}, but the assembled function does not match",
                function.index()
            ),
            Self::DuplicateInvariant { machine, name } => {
                write!(f, "duplicate temporal invariant `{name}` in machine `{machine}`")
            }
        }
    }
}

/// One by-value ownership edge. `holder[field]` is exactly `held`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TemporalFieldEdge<K> {
    holder: K,
    held: K,
    field: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TemporalVarDecl<K> {
    owner: K,
    name: String,
    kind: String,
    leaf_field: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TemporalActionDecl<K> {
    owner: K,
    name: String,
    function: FuncId,
    rust_symbol: String,
    span: String,
    guard: Option<String>,
    ghost: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedTemporalVar {
    name: String,
    kind: String,
    path: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedTemporalMachine<K> {
    owner: K,
    vars: Vec<ResolvedTemporalVar>,
    actions: Vec<TemporalActionDecl<K>>,
}

/// Resolve the DefId graph independently of rustc collection. Keeping this pure
/// makes the ambiguity/depth/duplicate policy directly regression-testable.
fn resolve_temporal_machines<K, F>(
    edges: &[TemporalFieldEdge<K>],
    vars: &[TemporalVarDecl<K>],
    actions: &[TemporalActionDecl<K>],
    label: F,
) -> Result<Vec<ResolvedTemporalMachine<K>>, TemporalCarryError>
where
    K: Copy + Eq + Hash,
    F: Fn(K) -> String,
{
    let mut parents: FxHashMap<K, Vec<(K, usize)>> = FxHashMap::default();
    for edge in edges {
        parents.entry(edge.held).or_default().push((edge.holder, edge.field));
    }

    let action_owners: FxHashSet<K> = actions.iter().map(|action| action.owner).collect();

    // An action owner is an explicit semantic boundary, so ordinary enclosing
    // uses do not affect it. Two action owners connected by any by-value path,
    // however, would define competing machine boundaries and are rejected
    // explicitly rather than choosing inner/outer based on traversal order.
    let mut checked_action_owners = FxHashSet::default();
    for action in actions {
        let inner = action.owner;
        if !checked_action_owners.insert(inner) {
            continue;
        }
        let mut pending = vec![inner];
        let mut seen = FxHashSet::default();
        while let Some(current) = pending.pop() {
            if !seen.insert(current) {
                continue;
            }
            for (holder, _) in parents.get(&current).into_iter().flatten() {
                if *holder != inner && action_owners.contains(holder) {
                    return Err(TemporalCarryError::NestedActionOwners {
                        inner: label(inner),
                        outer: label(*holder),
                    });
                }
                pending.push(*holder);
            }
        }
    }

    let mut machines = Vec::<ResolvedTemporalMachine<K>>::new();
    let mut machine_index = FxHashMap::<K, usize>::default();
    let mut action_names = FxHashSet::<(K, String)>::default();
    for action in actions {
        if !action_names.insert((action.owner, action.name.clone())) {
            return Err(TemporalCarryError::DuplicateAction {
                machine: label(action.owner),
                name: action.name.clone(),
            });
        }
        let index = *machine_index.entry(action.owner).or_insert_with(|| {
            let index = machines.len();
            machines.push(ResolvedTemporalMachine {
                owner: action.owner,
                vars: Vec::new(),
                actions: Vec::new(),
            });
            index
        });
        machines[index].actions.push(action.clone());
    }

    let mut variable_names = FxHashSet::<(K, String)>::default();
    let mut projection_paths = FxHashSet::<(K, Vec<usize>)>::default();
    for var in vars {
        let mut current = var.owner;
        let mut seen = FxHashSet::default();
        let mut upward_fields = Vec::new();
        let mut selected_owner = None::<(K, usize)>;

        loop {
            if !seen.insert(current) {
                return Err(TemporalCarryError::OwnershipCycle { owner: label(current) });
            }
            if action_owners.contains(&current) {
                // The nearest action Self is the explicit machine boundary.
                // Enclosing by-value embeddings are ordinary uses, not owners of
                // this machine; nested action-owner relationships were rejected
                // by the graph-wide check above.
                selected_owner = Some((current, upward_fields.len()));
                break;
            }
            let Some(candidates) = parents.get(&current) else {
                break;
            };
            if candidates.len() != 1 {
                let holders = candidates
                    .iter()
                    .map(|(holder, field)| format!("{}[{field}]", label(*holder)))
                    .collect();
                return Err(TemporalCarryError::AmbiguousHolder { held: label(current), holders });
            }
            let (holder, field) = candidates[0];
            upward_fields.push(field);
            current = holder;
        }

        let Some((owner, depth)) = selected_owner else {
            return Err(TemporalCarryError::UnownedVariable {
                owner: label(var.owner),
                name: var.name.clone(),
            });
        };
        if depth > 1 {
            return Err(TemporalCarryError::DeepOwnership {
                owner: label(var.owner),
                name: var.name.clone(),
                depth,
            });
        }

        let mut path = upward_fields[..depth].to_vec();
        path.reverse();
        path.push(var.leaf_field);

        if !variable_names.insert((owner, var.name.clone())) {
            return Err(TemporalCarryError::DuplicateVariable {
                machine: label(owner),
                name: var.name.clone(),
            });
        }
        if !projection_paths.insert((owner, path.clone())) {
            return Err(TemporalCarryError::DuplicateProjection {
                machine: label(owner),
                path: path.iter().map(usize::to_string).collect::<Vec<_>>().join(","),
            });
        }
        let index = machine_index[&owner];
        machines[index].vars.push(ResolvedTemporalVar {
            name: var.name.clone(),
            kind: var.kind.clone(),
            path,
        });
    }

    for machine in &machines {
        if machine.vars.is_empty() {
            return Err(TemporalCarryError::ActionWithoutVariables {
                machine: label(machine.owner),
            });
        }
    }
    Ok(machines)
}

fn parse_temporal_attr(
    attr: &rustc_hir::Attribute,
    attribute: &'static str,
    target: &str,
    allowed: &[&str],
    required: &[&str],
) -> Result<BTreeMap<String, String>, TemporalCarryError> {
    let malformed = |detail: String| TemporalCarryError::MalformedAttribute {
        target: target.to_string(),
        attribute,
        detail,
    };
    let list = attr
        .meta_item_list()
        .ok_or_else(|| malformed("expected a parenthesized name = \"value\" list".to_string()))?;
    let mut values = BTreeMap::new();
    for item in &list {
        let key = item.name().map(|name| name.to_string()).ok_or_else(|| {
            malformed("each argument must have a single-segment name".to_string())
        })?;
        if !allowed.contains(&key.as_str()) {
            return Err(malformed(format!("unknown argument `{key}`")));
        }
        let value = item
            .value_str()
            .map(|value| value.to_string())
            .ok_or_else(|| malformed(format!("argument `{key}` must be a string literal")))?;
        if value.trim().is_empty() {
            return Err(malformed(format!("argument `{key}` must not be empty")));
        }
        if values.insert(key.clone(), value).is_some() {
            return Err(malformed(format!("duplicate argument `{key}`")));
        }
    }
    for key in required {
        if !values.contains_key(*key) {
            return Err(malformed(format!("missing required argument `{key}`")));
        }
    }
    Ok(values)
}

fn unique_temporal_attr(
    attrs: &[rustc_hir::Attribute],
    attribute: &'static str,
    target: &str,
    allowed: &[&str],
    required: &[&str],
) -> Result<Option<BTreeMap<String, String>>, TemporalCarryError> {
    let mut matching = attrs.iter().filter(|attr| is_trust_attr(attr, attribute));
    let Some(attr) = matching.next() else {
        return Ok(None);
    };
    if matching.next().is_some() {
        return Err(TemporalCarryError::MalformedAttribute {
            target: target.to_string(),
            attribute,
            detail: "attribute appears more than once".to_string(),
        });
    }
    parse_temporal_attr(attr, attribute, target, allowed, required).map(Some)
}

fn temporal_def_path(tcx: TyCtxt<'_>, did: DefId) -> String {
    rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(did))
}

fn direct_temporal_spec_module(machine_name: String) -> SpecModule {
    // This frontend currently carries the authored projection/action map for
    // downstream extraction, but does not establish the behavioral contracts
    // needed for TrustIR's certifying `Linked` state. Preserve the metadata as
    // explicitly non-certifying until that authority seam is wired and
    // independently validated.
    SpecModule::design_only(machine_name)
}

/// Derive exact, fail-closed temporal `SpecModule`s. The ownership graph is
/// collected once and keyed by DefId, so same-named types/modules cannot merge.
fn derive_temporal_spec_modules(
    tcx: TyCtxt<'_>,
    assigned: &[(u32, FuncId)],
    assembled: &Module,
) -> Result<Vec<SpecModule>, TemporalCarryError> {
    let items = tcx.hir_crate_items(());
    let mut attribute_audit = TemporalAttributeAudit::collect(tcx);
    let mut edges = Vec::<TemporalFieldEdge<DefId>>::new();
    let mut vars = Vec::<TemporalVarDecl<DefId>>::new();

    for item in items.free_items() {
        let owner = item.owner_id.to_def_id();
        if !matches!(tcx.def_kind(owner), DefKind::Struct) {
            continue;
        }
        let variant = tcx.adt_def(owner).non_enum_variant();
        let args = ty::GenericArgs::identity_for_item(tcx, owner);
        for (field, field_def) in variant.fields.iter().enumerate() {
            if let ty::Adt(adt, _) = field_def.ty(tcx, args).skip_normalization().kind() {
                if adt.did().is_local() && matches!(tcx.def_kind(adt.did()), DefKind::Struct) {
                    edges.push(TemporalFieldEdge { holder: owner, held: adt.did(), field });
                }
            }

            let target = temporal_def_path(tcx, field_def.did);
            #[allow(deprecated)]
            let attrs = tcx.get_all_attrs(field_def.did);
            attribute_audit.consume(attrs, "var");
            let Some(mut values) =
                unique_temporal_attr(attrs, "var", &target, &["name", "kind"], &["name", "kind"])?
            else {
                continue;
            };
            vars.push(TemporalVarDecl {
                owner,
                name: values.remove("name").expect("required temporal var name"),
                kind: values.remove("kind").expect("required temporal var kind"),
                leaf_field: field,
            });
        }
    }

    let mut actions = Vec::<TemporalActionDecl<DefId>>::new();
    for item in items.impl_items() {
        let did = item.owner_id.to_def_id();
        if !matches!(tcx.def_kind(did), DefKind::AssocFn) {
            continue;
        }
        let symbol = temporal_def_path(tcx, did);
        #[allow(deprecated)]
        let attrs = tcx.get_all_attrs(did);
        attribute_audit.consume(attrs, "action");
        let Some(mut values) =
            unique_temporal_attr(attrs, "action", &symbol, &["name", "guard", "ghost"], &["name"])?
        else {
            continue;
        };
        let name = values.remove("name").expect("required temporal action name");
        if !matches!(
            tcx.fn_arg_idents(did.expect_local()),
            [Some(ident), ..] if ident.name.as_str() == "self"
        ) {
            return Err(TemporalCarryError::ActionWithoutSelf { action: name, symbol });
        }
        let impl_did = tcx.parent(did);
        let owner = match tcx.type_of(impl_did).instantiate_identity().skip_normalization().kind() {
            ty::Adt(adt, _) if matches!(tcx.def_kind(adt.did()), DefKind::Struct) => adt.did(),
            _ => {
                return Err(TemporalCarryError::NonStructActionOwner {
                    action: name,
                    owner: temporal_def_path(tcx, impl_did),
                });
            }
        };
        let def_index = did.index.as_u32();
        let function = assigned
            .binary_search_by_key(&def_index, |(index, _)| *index)
            .ok()
            .map(|index| assigned[index].1)
            .ok_or_else(|| TemporalCarryError::UnsplicedAction {
                action: name.clone(),
                symbol: symbol.clone(),
            })?;
        if !assembled
            .function_by_id(function)
            .is_some_and(|linked| !linked.is_declaration() && linked.name == symbol)
        {
            return Err(TemporalCarryError::FunctionIdentityMismatch {
                action: name,
                symbol,
                function,
            });
        }
        actions.push(TemporalActionDecl {
            owner,
            name,
            function,
            rust_symbol: symbol,
            span: tcx.sess.source_map().span_to_diagnostic_string(tcx.def_span(did)),
            guard: values.remove("guard"),
            ghost: values.remove("ghost"),
        });
    }

    attribute_audit.reject_unconsumed(tcx)?;

    if vars.is_empty() && actions.is_empty() {
        return Ok(Vec::new());
    }
    let machines =
        resolve_temporal_machines(&edges, &vars, &actions, |did| temporal_def_path(tcx, did))?;
    let mut modules = Vec::with_capacity(machines.len());
    for machine in machines {
        let machine_name = temporal_def_path(tcx, machine.owner);
        let mut module = direct_temporal_spec_module(machine_name.clone());
        let mut invariant_names = BTreeSet::new();
        let mut push_invariant = |name: String,
                                  formula: String,
                                  module: &mut SpecModule|
         -> Result<(), TemporalCarryError> {
            if !invariant_names.insert(name.clone()) {
                return Err(TemporalCarryError::DuplicateInvariant {
                    machine: machine_name.clone(),
                    name,
                });
            }
            module.invariants.push(SpecInvariant::new(name, formula));
            Ok(())
        };
        for var in machine.vars {
            module.vars.push(SpecVar::new(var.name.clone(), var.kind));
            push_invariant(
                format!("{}.path", var.name),
                var.path.iter().map(usize::to_string).collect::<Vec<_>>().join(","),
                &mut module,
            )?;
        }
        for action in machine.actions {
            module.actions.push(action.name.clone());
            module.anchors.push(SpecAnchor {
                machine: machine_name.clone(),
                action: action.name.clone(),
                function: Some(action.function),
                rust_symbol: action.rust_symbol,
                span: action.span,
                project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
                projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
            });
            if let Some(guard) = action.guard {
                push_invariant(format!("{}.guard", action.name), guard, &mut module)?;
            }
            if let Some(ghost) = action.ghost {
                push_invariant(format!("{}.ghost", action.name), ghost, &mut module)?;
            }
        }
        modules.push(module);
    }
    Ok(modules)
}

// ---------------------------------------------------------------------------
// Reentrancy-safe pending-const evaluation (the finalizer half of the hook's
// local-const deferral — see `crate::PendingConst` / `lower_named_const`).
// ---------------------------------------------------------------------------

/// Trust: is `inst` a pending-const placeholder? Exactly the shape the deferral path emits — a
/// bare `Constant::PhantomData` under a SCALAR (int/bool/float) `Inst::Const` type. That
/// combination is ill-typed and produced nowhere else (the slice fat-pointer seed nests
/// `PhantomData` inside a `Constant::Aggregate` under a `Ty::Tuple`; the float-literal/const
/// paths emit `Constant::Float`, never `PhantomData`), so matching it can neither miss a sentinel
/// nor false-positive on legitimate producer output. (wave-8b: `Ty::F32`/`F64` joined for the
/// deferred local FLOAT const.)
fn is_const_sentinel(inst: &Inst) -> bool {
    match inst {
        Inst::Const { ty, value: Constant::PhantomData } => matches!(
            ty,
            Ty::Bool
                | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128
                | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128
                // Trust (v25 B1): first-class isize/usize (pointer-width, 64 on the pinned
                // target) and char (32-bit unsigned carrier, Int-leaf constants) are scalar
                // const types the deferral path may now emit — the sentinel match must see
                // them or a deferred local const of these types leaks past the finalizer.
                | Ty::Isize | Ty::Usize | Ty::Char
                | Ty::F32 | Ty::F64
                // Trust (B7): composite deferred-const placeholders — the SAME PhantomData
                // sentinel under the mapped composite type (struct/tuple/enum + the [T; 0]
                // ZST array). Widening this predicate widens the leftover-sentinel
                // tripwires with it. NOTE: a legitimate `Constant::PhantomData` under
                // `Ty::Unit` (the wave-UF unit-field value) stays OUTSIDE the sentinel set;
                // the wave-UF seed inside a `Constant::Aggregate` is a nested constant, not
                // an `Inst::Const` node, so it can never false-positive here either.
                | Ty::Struct(_) | Ty::Tuple(_) | Ty::Enum(_) | Ty::Array(_, 0)
        ),
        _ => false,
    }
}

/// Count pending-const sentinels anywhere in the module (the finalizer tripwire).
fn count_const_sentinels(module: &Module) -> usize {
    module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.body.iter())
        .filter(|node| is_const_sentinel(&node.inst))
        .count()
}

/// Aggregate one more occurrence of `reason` into a record's sorted `(reason, count)` rows
/// (the same aggregation `record` performs at the hook).
fn bump_unsupported(rows: &mut Vec<(String, u64)>, reason: &str) {
    match rows.iter_mut().find(|(r, _)| r == reason) {
        Some((_, n)) => *n += 1,
        None => {
            rows.push((reason.to_string(), 1));
            rows.sort();
        }
    }
}

/// Trust: evaluate every deferred local const and patch its placeholder in the record's
/// function. Fail-closed at each gate: an evaluation failure, a shape/width mismatch against
/// the hook-recorded expectation, a missing placeholder, or a leftover sentinel all mark the
/// body unsupported (so `splice_ok` refuses it and coverage.json records why) — the artifact
/// never carries a guessed value or an unpatched sentinel.
fn resolve_pending_consts(tcx: TyCtxt<'_>, records: &mut [BodyRecord]) {
    for r in records {
        if r.pending_consts.is_empty() {
            continue;
        }
        for pc in &r.pending_consts {
            // Trust (B7): a composite pending const decodes against the PLACEHOLDER node's
            // mapped trust-ir type + this body's registered struct/enum tables (the same
            // per-body positional id space the node's Ty::Struct/Enum ids reference). A
            // missing placeholder yields None expected-ty and the eval fails closed; the
            // patch below then also reports the precise placeholder-not-found tag.
            let expected_ty = placeholder_ty(r.function.as_ref(), pc.value);
            match eval_pending_const(tcx, pc, expected_ty.as_ref(), &r.structs, &r.enums) {
                Some(constant) => {
                    if !patch_placeholder(r.function.as_mut(), pc.value, constant) {
                        bump_unsupported(&mut r.unsupported, "PendingConst(placeholder not found)");
                    }
                }
                None => {
                    bump_unsupported(&mut r.unsupported, "PendingConst(eval failed at finalize)");
                }
            }
        }
        // Per-body tripwire: after all patches, the function must be sentinel-free (belt and
        // braces on top of the per-entry patch result — e.g. a side-table/IR desync).
        if let Some(f) = &r.function {
            let leftovers = f
                .blocks
                .iter()
                .flat_map(|b| b.body.iter())
                .filter(|node| is_const_sentinel(&node.inst))
                .count();
            if leftovers > 0 {
                bump_unsupported(&mut r.unsupported, "PendingConst(sentinel leak)");
            }
        }
    }
}

/// Trust: evaluate ONE deferred local const via `const_eval_resolve_for_typeck` — the exact
/// query the hook's eager (non-local) path uses — at the reentrancy-safe finalizer seam.
/// Returns the real `Constant` or `None` (fail-closed) when:
///   * the identity args are not all-region (cannot happen if the hook's deferral gate held —
///     arg kinds mirror the param list — but checked, not assumed);
///   * the re-derived const type disagrees with the hook-recorded shape (kind or width);
///   * resolution/evaluation fails or yields a non-scalar valtree.
///
/// The hook stored no `GenericArgsRef` (tcx-interned); `identity_for_item` + region erasure
/// reconstructs the erased `AliasConst` (né `UnevaluatedConst`) the hook would have built, because the deferral
/// was only taken for ALL-REGION use-site args and `erase_and_anonymize_regions` collapses
/// both sides to the same region-free key (regions never affect a const's value).
fn eval_pending_const(
    tcx: TyCtxt<'_>,
    pc: &PendingConst,
    // Trust (B7): the placeholder node's mapped trust-ir type + the body's registered
    // struct/enum tables — the composite leg's decode context. `None`/unused for scalars.
    expected_ty: Option<&Ty>,
    structs: &[StructDef],
    enums: &[EnumDef],
) -> Option<Constant> {
    // An mgca `type const` must never be CTFE'd here (the observed ICE class); the hook's
    // deferral gate already refuses them — checked again, not assumed.
    if tcx.is_type_const(pc.def_id) {
        return None;
    }
    let args = ty::GenericArgs::identity_for_item(tcx, pc.def_id);
    if !args.iter().all(|a| a.as_region().is_some()) {
        return None;
    }
    // Shape tripwire: the const's declared type must match what the hook recorded off the
    // use-site expression type (same tcx, so a mismatch means a real bug — fail closed).
    // Trust: rust 1.99 — `EarlyBinder::instantiate_identity` returns `Unnormalized<T>`;
    // unwrap with `.skip_normalization()` (compiler-idiomatic; the shape check below is
    // structural and the valtree decode path never normalized here before either).
    let rty = tcx.type_of(pc.def_id).instantiate_identity().skip_normalization();
    let pointer_bits = || tcx.data_layout.pointer_size().bits();
    let shape_ok = match rty.kind() {
        // Trust (B7): a composite pending const — the deep shape check IS the
        // double-keyed finalize decoder below (rustc kind x mapped trust-ir type
        // at every level); here only the kind-class + flag coherence is pinned.
        ty::Tuple(_) | ty::Array(..) | ty::Adt(..) => {
            pc.composite && !pc.is_bool && !pc.is_float && !pc.signed && pc.bits == 0
        }
        _ if pc.composite => false,
        ty::Bool => pc.is_bool,
        ty::Int(it) => {
            !pc.is_bool
                && !pc.is_float
                && pc.signed
                && it.bit_width().unwrap_or_else(pointer_bits) == u64::from(pc.bits)
        }
        ty::Uint(ut) => {
            !pc.is_bool
                && !pc.is_float
                && !pc.signed
                && ut.bit_width().unwrap_or_else(pointer_bits) == u64::from(pc.bits)
        }
        // Trust (wave-CH/B1): a deferred LOCAL `char` const uses first-class `Ty::Char` with an
        // unsigned 32-bit code-point carrier, so the hook records `is_bool=is_float=signed=false,
        // bits=32`. `try_to_bits` accepts a `Char` valtree and the shared integer value tail emits
        // `Constant::Int(cp)` without collapsing the type to `U32`. Without this arm a local char
        // const fails closed at finalize (sentinel leak).
        ty::Char => !pc.is_bool && !pc.is_float && !pc.signed && pc.bits == 32,
        // Trust (wave-8b): a deferred local FLOAT const. `bits` is the IEEE width (32/64), matched
        // exactly against the re-derived float type; `signed`/`is_bool` are false.
        ty::Float(ft) => {
            pc.is_float
                && !pc.is_bool
                && !pc.signed
                && match ft {
                    ty::FloatTy::F32 => pc.bits == 32,
                    ty::FloatTy::F64 => pc.bits == 64,
                    _ => false,
                }
        }
        _ => false,
    };
    if !shape_ok {
        return None;
    }
    // Trust: rust 1.99 removed `ty::UnevaluatedConst` — the ty-level unevaluated const is now
    // `ty::AliasConst` (kind classified from the DefId), which is exactly what
    // `const_eval_resolve_for_typeck` takes. Same def/args payload, same erase-then-eval flow.
    let uv = ty::AliasConst::new(tcx, ty::AliasConstKind::new_from_def_id(tcx, pc.def_id), args);
    let uv = tcx.erase_and_anonymize_regions(uv);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let valtree = match tcx.const_eval_resolve_for_typeck(typing_env, uv, pc.span) {
        Ok(Ok(v)) => v,
        // `Ok(Err(_))` (non-valtree'able) and `Err(_)` (reported error / too generic) both
        // fail closed — never a guessed value.
        _ => return None,
    };
    // Trust (B7): the composite leg — recursive branch-valtree decode against the
    // placeholder's mapped type + the body's registered tables. Fail-closed on any
    // level the decoder cannot prove faithful (the caller records the precise
    // PendingConst tag). Scalars keep the exact pre-B7 tail below.
    if pc.composite {
        return finalize_valtree_to_constant(tcx, rty, valtree, expected_ty?, structs, enums, 0);
    }
    let value = ty::Value { ty: rty, valtree };
    if pc.is_bool {
        return value.try_to_bool().map(Constant::Bool);
    }
    let raw = value.try_to_bits(tcx, typing_env)?;
    // Trust (wave-8b): a float const reinterprets the raw IEEE bits into the f64 carrier the hook's
    // eager path and the float-literal arm use (`f64::from(f32)` for F32; `from_bits` for F64).
    // Same FAITHFULNESS GUARD as the eager path (see lower_named_const): the carrier must round-trip
    // the source bits EXACTLY (a signaling/non-canonical f32 NaN the `f32 as f64` widening quiets is
    // declined here — the body then fails PendingConst at finalize rather than patch wrong bits).
    // `bits` is 32/64 (shape-checked above). Never a `sign_extend`.
    if pc.is_float {
        let v: f64 = match pc.bits {
            32 => {
                let carrier = f64::from(f32::from_bits(raw as u32));
                if (carrier as f32).to_bits() != raw as u32 {
                    return None;
                }
                carrier
            }
            64 => {
                let carrier = f64::from_bits(raw as u64);
                if carrier.to_bits() != raw as u64 {
                    return None;
                }
                carrier
            }
            _ => return None,
        };
        return Some(Constant::Float(v));
    }
    Some(crate::integer_constant_from_bits(raw, pc.signed, pc.bits))
}

/// Trust (B7): the mapped trust-ir type of a pending const's placeholder node — the finalize
/// decoder's expected-shape key. Located exactly like `patch_placeholder` (result `ValueId` +
/// sentinel shape); `None` when the body/node is missing (the patch then reports it).
fn placeholder_ty(func: Option<&Function>, value: ValueId) -> Option<Ty> {
    let f = func?;
    for block in &f.blocks {
        for node in &block.body {
            if node.results.first() == Some(&value) && is_const_sentinel(&node.inst) {
                if let Inst::Const { ty, .. } = &node.inst {
                    return Some(ty.clone());
                }
            }
        }
    }
    None
}

/// Trust (B7): the FINALIZER twin of the hook's eager `valtree_to_constant` decoder — decodes a
/// CTFE branch valtree into the producer's aggregate constant model, DOUBLE-KEYED at every level
/// on (the re-derived rustc type kind) x (the placeholder's mapped trust-ir type, resolved
/// through the body's registered struct/enum tables). Mirrors `map_ty`'s value model exactly:
/// tuples and `[T; N > 0]` arrays are `Constant::Aggregate` under `Ty::Tuple`; `[T; 0]` is the
/// empty `Constant::Array`; structs are field-ordered `Aggregate`s; enums are the
/// `[Int(discriminant), fields...]` tag+payload convention with the discriminant read from the
/// REGISTERED `EnumDef` (the same explicit per-variant table the Switch and seed lanes carry —
/// never re-derived from rustc here). Any disagreement between the two keys, an unregistered
/// id, an implicit/missing discriminant entry, or an unproven leaf fails closed (`None`).
fn finalize_valtree_to_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    rty: ty::Ty<'tcx>,
    valtree: ty::ValTree<'tcx>,
    expected: &Ty,
    structs: &[StructDef],
    enums: &[EnumDef],
    depth: usize,
) -> Option<Constant> {
    if depth > 64 {
        return None;
    }
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let pointer_bits = || tcx.data_layout.pointer_size().bits();
    match (rty.kind(), expected) {
        (ty::Bool, Ty::Bool) => ty::Value { ty: rty, valtree }.try_to_bool().map(Constant::Bool),
        // Char consts are Int code-point leaves (the trust-ir validator checks the
        // Unicode scalar range at the Ty::Char declaration).
        (ty::Char, Ty::Char) => {
            let raw = ty::Value { ty: rty, valtree }.try_to_bits(tcx, typing_env)?;
            Some(Constant::Int(raw as i128))
        }
        (ty::Int(it), _) => {
            let (bits, signed) = crate::int_scalar_bits(expected)?;
            if !signed || u64::from(bits) != it.bit_width().unwrap_or_else(pointer_bits) {
                return None;
            }
            let raw = ty::Value { ty: rty, valtree }.try_to_bits(tcx, typing_env)?;
            Some(crate::integer_constant_from_bits(raw, signed, bits))
        }
        (ty::Uint(ut), _) => {
            let (bits, signed) = crate::int_scalar_bits(expected)?;
            if signed || u64::from(bits) != ut.bit_width().unwrap_or_else(pointer_bits) {
                return None;
            }
            let raw = ty::Value { ty: rty, valtree }.try_to_bits(tcx, typing_env)?;
            Some(crate::integer_constant_from_bits(raw, signed, bits))
        }
        // Floats: the same f64-carrier + f32 round-trip faithfulness guard as every
        // other const leg (a signaling f32 NaN the widening would quiet declines).
        (ty::Float(ty::FloatTy::F32), Ty::F32) => {
            let raw = ty::Value { ty: rty, valtree }.try_to_bits(tcx, typing_env)?;
            let carrier = f64::from(f32::from_bits(raw as u32));
            if (carrier as f32).to_bits() != raw as u32 {
                return None;
            }
            Some(Constant::Float(carrier))
        }
        (ty::Float(ty::FloatTy::F64), Ty::F64) => {
            let raw = ty::Value { ty: rty, valtree }.try_to_bits(tcx, typing_env)?;
            Some(Constant::Float(f64::from_bits(raw as u64)))
        }
        (ty::Tuple(fields), Ty::Tuple(elems)) => {
            let branch = valtree.try_to_branch()?;
            if branch.len() != fields.len() || branch.len() != elems.len() {
                return None;
            }
            let mut out = Vec::with_capacity(branch.len());
            for ((c, frty), fex) in branch.iter().zip(fields.iter()).zip(elems.iter()) {
                out.push(finalize_branch_elem(tcx, c, frty, fex, structs, enums, depth + 1)?);
            }
            Some(Constant::Aggregate(out))
        }
        // map_ty's array model: `[T; N > 0]` is a Ty::Tuple of N copies (Aggregate value);
        // `[T; 0]` is the ZST Ty::Array (empty Array value, wave-FRU L3).
        (ty::Array(elem_rty, _), Ty::Tuple(elems)) => {
            let branch = valtree.try_to_branch()?;
            if branch.len() != elems.len() || branch.is_empty() {
                return None;
            }
            let mut out = Vec::with_capacity(branch.len());
            for (c, fex) in branch.iter().zip(elems.iter()) {
                out.push(finalize_branch_elem(tcx, c, *elem_rty, fex, structs, enums, depth + 1)?);
            }
            Some(Constant::Aggregate(out))
        }
        (ty::Array(..), Ty::Array(_, 0)) => {
            let branch = valtree.try_to_branch()?;
            branch.is_empty().then(|| Constant::Array(Vec::new()))
        }
        (ty::Adt(adt, adt_args), Ty::Struct(sid)) if adt.is_struct() => {
            let sd = structs.get(sid.as_usize())?;
            let branch = valtree.try_to_branch()?;
            let variant = adt.non_enum_variant();
            if branch.len() != variant.fields.len() || branch.len() != sd.fields.len() {
                return None;
            }
            let mut out = Vec::with_capacity(branch.len());
            for ((c, f), fd) in branch.iter().zip(variant.fields.iter()).zip(sd.fields.iter()) {
                let frty = f.ty(tcx, adt_args).skip_normalization();
                out.push(finalize_branch_elem(tcx, c, frty, &fd.ty, structs, enums, depth + 1)?);
            }
            Some(Constant::Aggregate(out))
        }
        (ty::Adt(adt, adt_args), Ty::Enum(eid)) if adt.is_enum() => {
            // Branch = [variant-index-leaf(u32), selected variant's fields...].
            let ed = enums.get(eid.as_usize())?;
            let branch = valtree.try_to_branch()?;
            let (vt_idx, field_consts) = branch.split_first()?;
            let ty::ConstKind::Value(iv) = vt_idx.kind() else { return None };
            let vidx = usize::try_from(iv.try_to_bits(tcx, typing_env)?).ok()?;
            let disc = ed.discriminants.get(vidx).copied().flatten()?;
            let ev = ed.variants.get(vidx)?;
            let variant = adt.variant(rustc_abi::VariantIdx::from_usize(vidx));
            if field_consts.len() != variant.fields.len() || field_consts.len() != ev.fields.len() {
                return None;
            }
            let mut out = Vec::with_capacity(1 + field_consts.len());
            out.push(Constant::Int(disc));
            for ((c, f), fex) in
                field_consts.iter().zip(variant.fields.iter()).zip(ev.fields.iter())
            {
                let frty = f.ty(tcx, adt_args).skip_normalization();
                // Trust (B3-2c E5, the FINALIZER twin of the eager decoder's arm —
                // the paired-gate rule): a Unit-typed def field (the admission
                // invariant: drop-free ZST) finalizes as the canonical PhantomData;
                // recursing would produce Aggregate([]) which has no interpreter
                // pair under Ty::Unit (a trap = manufactured divergence).
                if matches!(fex, Ty::Unit) {
                    out.push(Constant::PhantomData);
                    continue;
                }
                out.push(finalize_branch_elem(tcx, *c, frty, fex, structs, enums, depth + 1)?);
            }
            Some(Constant::Aggregate(out))
        }
        _ => None,
    }
}

/// Trust (B7): decode ONE valtree-Branch element at the finalizer. Branch elements are always
/// `ConstKind::Value` for a CTFE-produced valtree; the recorded type must EQUAL the declared
/// field/element type (a disagreement is a model misunderstanding — fail closed, never coerce).
fn finalize_branch_elem<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: ty::Const<'tcx>,
    expected_rty: ty::Ty<'tcx>,
    expected: &Ty,
    structs: &[StructDef],
    enums: &[EnumDef],
    depth: usize,
) -> Option<Constant> {
    let ty::ConstKind::Value(v) = c.kind() else { return None };
    if v.ty != expected_rty {
        return None;
    }
    finalize_valtree_to_constant(tcx, v.ty, v.valtree, expected, structs, enums, depth)
}

/// Replace the placeholder `Inst::Const`'s sentinel value with the evaluated constant. The
/// patch key is the placeholder's result `ValueId` (unique per body in SSA); the node must
/// ALSO still look like a sentinel (`is_const_sentinel`) — a right-id-wrong-shape node means
/// a desync and fails the patch rather than overwriting real IR. Returns `true` iff patched.
fn patch_placeholder(func: Option<&mut Function>, value: ValueId, constant: Constant) -> bool {
    let Some(f) = func else {
        return false;
    };
    for block in &mut f.blocks {
        for node in &mut block.body {
            if node.results.first() == Some(&value) && is_const_sentinel(&node.inst) {
                if let Inst::Const { value: v, .. } = &mut node.inst {
                    *v = constant;
                    return true;
                }
            }
        }
    }
    false
}

/// How one `Inst::Call { callee }` was resolved during splicing.
enum CalleeResolution {
    /// Rewritten to the spliced local target's new dense `FuncId`.
    Local(FuncId),
    /// Fail-closed bodyless declaration. `key` dedups declarations (class-prefixed so a local
    /// path can never merge with an extern one); `name` is the declaration's display identity;
    /// `is_extern` picks the coverage counter.
    /// Trust (#178): `ret` is the RESULT type the crate's call sites bind from this callee, when
    /// they agree and it is table-free (`CalleeRef::ret_ty`). It types the declaration's
    /// signature; `None` keeps the old empty-`returns` spelling. It also joins `key`, so two
    /// sites that disagree mint DISTINCT declarations rather than one whose signature contradicts
    /// half its callers — pre-monomorphization, one `def_path` at two instantiations genuinely is
    /// two functions, and names are display identity only (resolution is by `FuncId`).
    Decl { key: String, name: String, is_extern: bool, ret: Option<Ty> },
}

struct Assembled {
    module: Module,
    /// Deterministic rows are retained until the crate-seam differential has installed an exact
    /// outcome for every deferred body. JSON rendering before that point would publish stale
    /// hook-time `NotRun` states without the linked comparison that supersedes them.
    coverage_rows: Vec<CoverageRow>,
    lowered: usize,
    spliced: usize,
    declarations: usize,
    /// Trust (B9-A): pass-1 dense `FuncId` assignment `(def_index, FuncId)`, def_index-sorted
    /// (`FuncId(i) == assigned[i].1`, `assigned[i].1.as_u32() == i`). The seam differential maps a
    /// deferred body's `def_index` → its spliced entry `FuncId`, and (inverting) a reachable
    /// closure member `FuncId` → its callee `def_index` to gather MIR snapshots.
    assigned: Vec<(u32, FuncId)>,
}

/// Trust: the coverage/marker spelling of a body's kind (see `BodyRecord::kind`).
fn kind_str(kind: BodyKind) -> &'static str {
    match kind {
        BodyKind::Fn => "fn",
        BodyKind::ConstInit => "const-init",
        BodyKind::StaticInit => "static-init",
    }
}

/// Per-body coverage row (all data plain + pre-sorted so the JSON writer is a dumb loop).
struct CoverageRow {
    def_path: String,
    def_index: u32,
    /// Trust: `kind_str` of the body's `BodyKind` (`"fn"` / `"const-init"` / `"static-init"`).
    kind: &'static str,
    lowered: bool,
    /// Trust (totality Batch C): lowered WITH value-less symbolic assoc-const globals —
    /// coverage counts it lowered; splice excludes it.
    symbolic: bool,
    spliced: bool,
    instr_count: u64,
    unsupported: Vec<(String, u64)>,
    /// Trust (v2 Phase 0a): per-tag detail examples (see `BodyRecord::unsupported_details`).
    unsupported_details: Vec<(String, Vec<String>)>,
    /// Trust (v2 Phase 0b): collect-all pass results (see `BodyRecord`).
    collect_primary: Vec<(String, u64)>,
    collect_cascade: Vec<(String, u64)>,
    calls_resolved: u64,
    calls_extern: u64,
    calls_unresolved: u64,
    /// Hook-time sampled interpreter result. For deferred bodies this remains `NotRun`; `seam`
    /// carries the linked crate-finalization result without overwriting historical evidence.
    interpreter: InterpreterEvidence,
    /// Direct-TrustIR -> derived-MIR structural comparison from the same `mir_built` hook.
    derived_mir: DerivedMirEvidence,
    deferred_to_seam: bool,
    /// Present exactly when `deferred_to_seam` is true, and installed only after assembly and
    /// linked comparison. Coverage rendering rejects either a missing or unexpected value.
    seam: Option<InterpreterEvidence>,
    /// Trust (L1): the per-body lineage digest (see `BodyRecord::lineage`) — rendered into
    /// the coverage row so the artifact-side row is digest-matchable against the flip event.
    lineage: Option<trust_ir::ProofDigest>,
    /// Trust (L1): the `FuncId` this body received in the ASSEMBLED module, i.e. its index
    /// into `module.functions` (the assembler maintains `functions[i].id == i` end to end).
    /// `Some` exactly when `spliced`. Without it, pointing at the assembled row means
    /// re-deriving the assembler's own name mangling (`{const-init}` / `{static-init}`
    /// suffixes) from `def_path`; with it, the (row → assembled function) leg of the
    /// lineage chain is an index, not a string match. This is the ADDRESS of the object the
    /// canonical-remapping certificate will have to talk about — it is not that certificate.
    func_id: Option<u32>,
}

fn assemble(crate_name: &str, records: &[BodyRecord]) -> Assembled {
    // ---- Pass 1: dense FuncId assignment for every spliceable body, in DefIndex order. ----
    // (records are already sorted + deduped by def_index.)
    //
    // Trust: pass 1 ALSO interns each admitted body's enum/struct/type tables into the assembled
    // module and pre-remaps every embedded `EnumId`/`StructId`/`TyId` in the body's function +
    // signature (`prepare_body_tables`) — all fallibility lives HERE, before a `FuncId` is assigned, so
    // pass 2 can never desync the dense id space by refusing late. `splice_ok` validated every
    // remap precondition (resolvability, positional ids, nested-first ordering), so a `None`
    // from `prepare_body_tables` is a defensive tripwire (body simply not admitted, recorded in
    // coverage as un-spliced), never a silent mis-emit.
    let mut module = Module::new(crate_name.to_string());
    let mut assigned: Vec<(u32, FuncId)> = Vec::new();
    let mut prepared: Vec<(u32, Function, FuncTy)> = Vec::new();
    for r in records {
        if splice_ok(r) {
            if let Some((func, func_ty)) = prepare_body_tables(r, &mut module) {
                assigned.push((r.def_index, FuncId::new(assigned.len() as u32)));
                prepared.push((r.def_index, func, func_ty));
            }
        }
    }
    let lookup = |def_index: u32| -> Option<FuncId> {
        assigned.binary_search_by_key(&def_index, |(d, _)| *d).ok().map(|i| assigned[i].1)
    };

    // ---- Pass 2: splice functions, rewriting intra-crate callee FuncIds. ----
    // Fail-closed declarations: (dedup key, id, display name), first-encounter order.
    // Trust (#178): `(dedup key, id, display name, agreed table-free return type)`.
    let mut decls: Vec<(String, FuncId, String, Option<Ty>)> = Vec::new();
    let mut rows: Vec<CoverageRow> = Vec::new();

    for r in records {
        let lowered = r.function.is_some() && r.unsupported.is_empty();
        let mut row = CoverageRow {
            def_path: r.def_path.clone(),
            def_index: r.def_index,
            kind: kind_str(r.kind),
            lowered,
            symbolic: r.symbolic,
            spliced: false,
            instr_count: r.instr_count,
            unsupported: r.unsupported.clone(),
            unsupported_details: r.unsupported_details.clone(),
            collect_primary: r.collect_primary.clone(),
            collect_cascade: r.collect_cascade.clone(),
            calls_resolved: 0,
            calls_extern: 0,
            calls_unresolved: 0,
            interpreter: r.interpreter.clone(),
            derived_mir: r.derived_mir.clone(),
            deferred_to_seam: r.deferred,
            seam: None,
            lineage: r.lineage,
            func_id: None,
        };
        let Some(new_id) = lookup(r.def_index) else {
            rows.push(row);
            continue;
        };
        // Pass 1 admitted this body, so its pre-remapped function + signature are present
        // (assigned and prepared are pushed together, same keys, same order).
        let Ok(pi) = prepared.binary_search_by_key(&r.def_index, |(d, _, _)| *d) else {
            rows.push(row);
            continue;
        };
        let (_, func, func_ty) = &prepared[pi];

        let mut f = func.clone();
        f.id = new_id;
        // Trust: initializer bodies are marked IN THE MODULE by a name suffix (`Function` has no
        // kind field, and `FuncAttrs` carries only claim-style optimization hints — `readnone`
        // etc. would be an unproven semantic claim). Names are display identity only (resolution
        // is by `FuncId`/DefIndex), and rustc def paths never produce a `{const-init}` /
        // `{static-init}` segment, so the marker cannot collide with a real path.
        f.name = match r.kind {
            BodyKind::Fn => r.def_path.clone(),
            BodyKind::ConstInit => format!("{}::{{const-init}}", r.def_path),
            BodyKind::StaticInit => format!("{}::{{static-init}}", r.def_path),
        };
        f.ty = intern_func_ty(&mut module, func_ty.clone());
        // (EnumDefs/StructDefs/types were interned and every embedded `EnumId`/`StructId`/`TyId`
        // remapped in pass 1 — `prepare_body_tables`; `f`/`func_ty` here are the pre-remapped
        // clones.)

        for block in &mut f.blocks {
            for node in &mut block.body {
                match &mut node.inst {
                    Inst::Call { callee, .. } => match resolve_callee(r, *callee, &lookup) {
                        CalleeResolution::Local(id) => {
                            *callee = id;
                            row.calls_resolved += 1;
                        }
                        CalleeResolution::Decl { key, name, is_extern, ret } => {
                            *callee = decl_id(&mut decls, assigned.len(), key, name, ret);
                            if is_extern {
                                row.calls_extern += 1;
                            } else {
                                row.calls_unresolved += 1;
                            }
                        }
                    },
                    // Trust: re-intern the indirect-call signature from the body's snapshot
                    // table into the assembled module. `splice_ok` held in pass 1 on this same
                    // immutable record (`body_sig_ok`), so the lookup succeeds; the guard is
                    // shape-preserving, never a default.
                    Inst::CallIndirect { sig, .. } => {
                        if let Some(ft) = r.func_types.get(sig.as_usize()).cloned() {
                            *sig = intern_func_ty(&mut module, ft);
                        }
                    }
                    // Trust: a reified fn-pointer constant — remap its `Ty::Func` sig id the
                    // same way, and rewrite the target `FuncId` through the ledger EXACTLY
                    // like a Call callee (it is a call-graph edge; counted in the same
                    // coverage buckets). `splice_ok` proved the sig resolvable and the ledger
                    // identity unique.
                    Inst::Const { ty, value } => {
                        if let Constant::FnDef(fid) = value {
                            if let Ty::Func(sig) = ty {
                                if let Some(ft) = r.func_types.get(sig.as_usize()).cloned() {
                                    *sig = intern_func_ty(&mut module, ft);
                                }
                            }
                            match resolve_callee(r, *fid, &lookup) {
                                CalleeResolution::Local(id) => {
                                    *fid = id;
                                    row.calls_resolved += 1;
                                }
                                CalleeResolution::Decl { key, name, is_extern, ret } => {
                                    *fid = decl_id(&mut decls, assigned.len(), key, name, ret);
                                    if is_extern {
                                        row.calls_extern += 1;
                                    } else {
                                        row.calls_unresolved += 1;
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        row.spliced = true;
        // Trust (L1): record WHERE this body landed in the assembled module. Declarations are
        // appended after this loop, so `new_id.index()` is a stable index into
        // `module.functions` for the whole artifact.
        row.func_id = Some(new_id.index());
        module.add_function(f);
        rows.push(row);
    }

    // Declarations LAST so `module.functions[i].id == i` stays true end to end. The unknown
    // signature (`is_vararg: true`, no params/returns) is the explicit fail-closed marker, along
    // with bodylessness itself (`Function::is_declaration` — callers stay havoced).
    if !decls.is_empty() {
        // Trust (#178): a declaration's signature is now per-declaration, not one shared
        // `unknown_sig` for the whole module.
        //
        // `is_vararg: true` with empty `params` is the params-side "unknown" encoding, and it is
        // why arg-count mismatches were already rare. `returns` had no such escape hatch:
        // `returns: []` is a POSITIVE CLAIM of "returns nothing", so EVERY call binding a result
        // from a declared callee was ill-typed. That single default was
        // `InstrResultArityMismatch { op: "call", expected: 0, actual: 1 }` — 1542 occurrences,
        // 66% of all validation errors in the corpus.
        //
        // Where the call sites agreed on a table-free result type, spell it. Where they did not,
        // keep the empty `returns` — honest for a callee no site takes a value from, and still
        // the old behavior for everything this lane cannot type.
        for (_key, id, name, ret) in &decls {
            let sig = intern_func_ty(
                &mut module,
                FuncTy {
                    params: Vec::new(),
                    returns: ret.clone().into_iter().collect(),
                    is_vararg: true,
                },
            );
            let mut d = Function::new(*id, name.clone(), sig, BlockId::new(0))
                .with_producer(trust_ir::Producer::TRust);
            d.linkage = Linkage::External;
            module.add_function(d);
        }
    }

    let lowered = rows.iter().filter(|r| r.lowered).count();
    let spliced = rows.iter().filter(|r| r.spliced).count();

    Assembled { module, coverage_rows: rows, lowered, spliced, declarations: decls.len(), assigned }
}

/// Resolve one emitted callee `FuncId` through the body's identity ledger. Fail-closed: only a
/// single unambiguous LOCAL identity whose own body was spliced resolves; everything else becomes
/// a declaration.
fn resolve_callee(
    r: &BodyRecord,
    callee: FuncId,
    lookup: &dyn Fn(u32) -> Option<FuncId>,
) -> CalleeResolution {
    let idents: Vec<&CalleeRef> = r.callees.iter().filter(|c| c.func_id == callee).collect();
    match idents.as_slice() {
        // Trust (wave-20): a FORCED-HAVOC edge (a generic call site) declares — NEVER links — even
        // when its `DefIndex` has a clean local body. Linking a polymorphic call to the callee's
        // identity-lowered body is an identity lie AND re-opens the wave-19 fat/thin DST hole at a
        // generic site. The distinct `havoc:` key prefix keeps it from coalescing with any real
        // `local:`/`extern:` edge to the same symbol; it counts in the honest can't-resolve bucket.
        [c] if c.force_havoc => CalleeResolution::Decl {
            key: format!("havoc:{}{}", c.def_path, ret_key(c)),
            name: c.def_path.clone(),
            is_extern: false,
            ret: decl_ret(c),
        },
        [c] if c.is_local => match lookup(c.def_index) {
            Some(id) => CalleeResolution::Local(id),
            // A real local fn, but its own body did not lower cleanly — declare, don't link.
            None => CalleeResolution::Decl {
                key: format!("local-unlowered:{}{}", c.def_path, ret_key(c)),
                name: c.def_path.clone(),
                is_extern: false,
                ret: decl_ret(c),
            },
        },
        [c] => CalleeResolution::Decl {
            key: format!("extern:{}{}", c.def_path, ret_key(c)),
            name: c.def_path.clone(),
            is_extern: true,
            ret: decl_ret(c),
        },
        // No ledger entry at all — there is no site evidence to type a return with.
        [] => CalleeResolution::Decl {
            key: format!("unknown:{}", callee.index()),
            name: format!("!unknown_callee_{}", callee.index()),
            is_extern: false,
            ret: None,
        },
        // Two identities behind one DefIndex-derived FuncId (local/extern index collision):
        // linking either would be a guess. Declare.
        // Two identities behind one FuncId: their return types are not jointly attributable.
        _ => CalleeResolution::Decl {
            key: format!("ambiguous:{}", callee.index()),
            name: format!("!ambiguous_callee_{}", callee.index()),
            is_extern: false,
            ret: None,
        },
    }
}

/// Trust (#180): pin the module's target — but ONLY when doing so asserts nothing that is not
/// already a fact about the compilation target.
///
/// `validate_module` demands a pinned target from any module carrying an FFI boundary (a bodyless
/// external declaration): byte-level ABI agreement is part of such a module's meaning, and that
/// agreement is only well-defined against a target. 615 occurrences of `TargetInfoRequired` —
/// after #178, the LARGEST remaining class.
///
/// WHY THIS WAS BLOCKED, AND WHY THIS SLICE IS NOT. `TargetInfo::struct_passing` is a real ABI
/// CLAIM with exactly two values, and NEITHER is honest for what this producer emits:
///   * `NativeC` — "a producer marks the memory-classed parameters/returns `byval`/`sret`
///     ([`ParamAttrs`]) per those rules". This producer emits no `ParamAttrs` at all.
///   * `AlwaysMemory` — every by-value aggregate crosses through memory, `byval`/`sret`. Same
///     missing marks.
/// It is also digest-bearing (it flows into `Module::stable_digest`), so a wrong pick silently
/// changes module identity too. Picking one is an owner ruling and this function does not make it.
///
/// BUT the claim quantifies over BY-VALUE AGGREGATES CROSSING CALL EDGES. In a module where no
/// such crossing exists, both policy values describe exactly the same empty set: the field has no
/// observable content, so stamping cannot be a false claim. `triple`, `pointer_size` and
/// `endianness` were never in question — they are facts about the target being compiled for.
///
/// THE SCAN IS DELIBERATELY A SUPERSET AND FAILS CLOSED. Every call edge's types live in some
/// `FuncTy` in `module.func_types` (a `Function` names one via `ty`, a `CallIndirect` via `sig`),
/// so scanning the WHOLE table over-approximates the set of crossings — it can only refuse to
/// stamp a module that would have been fine, never stamp one that is not. The per-type test
/// allow-lists the non-aggregates and treats everything else — including any variant added to
/// `Ty` later — as an aggregate. An over-permissive scan here would stamp exactly the false ABI
/// claim the ruling exists to prevent, so unknown must mean "aggregate".
fn stamp_target_info_if_vacuous(tcx: TyCtxt<'_>, module: &mut Module) {
    if module.target_info.is_some() {
        return;
    }
    fn crosses_by_value_aggregate(ty: &Ty) -> bool {
        !matches!(
            ty,
            Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Ptr
                | Ty::Unit
                | Ty::Never
        )
    }
    let aggregate_at_a_boundary = module.func_types.iter().any(|ft| {
        ft.params.iter().chain(ft.returns.iter()).any(crosses_by_value_aggregate)
    });
    if aggregate_at_a_boundary {
        return;
    }
    let target = &tcx.sess.target;
    module.target_info = Some(trust_ir::TargetInfo {
        triple: target.llvm_target.to_string(),
        pointer_size: u32::from(target.pointer_width / 8),
        endianness: match target.endian {
            rustc_abi::Endian::Little => trust_ir::Endianness::Little,
            rustc_abi::Endian::Big => trust_ir::Endianness::Big,
        },
        // `None` = "derived from the triple" (the documented legacy state), NOT a claim of a
        // specific calling-convention ruleset. The producer has no independent ABI identity to
        // assert here.
        abi: None,
        // Vacuous by the scan above: no by-value aggregate crosses any call edge in this module,
        // so this field ranges over nothing. It is the serde default and carries no content here.
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
}

/// Trust (#178): the return type to give this callee's DECLARATION — the type its call sites
/// agreed on, or `None` if the ledger entry was poisoned by disagreement. Reading the poison flag
/// here (rather than only `ret_ty.is_some()`) is what keeps a contradicted type from being
/// resurrected: `ret_ty` is cleared on conflict, and `ret_ty_conflict` records WHY it is empty.
fn decl_ret(c: &crate::CalleeRef) -> Option<Ty> {
    if c.ret_ty_conflict { None } else { c.ret_ty.clone() }
}

/// Trust (#178): the declaration dedup-key suffix for a callee's agreed return type. Two call
/// sites that bind different types from one `def_path` must NOT collapse into one declaration —
/// its signature would contradict half of them. Empty for the unknown case, so a callee with no
/// agreed type keeps byte-identical keys to the pre-#178 producer.
fn ret_key(c: &crate::CalleeRef) -> String {
    match decl_ret(c) {
        Some(t) => format!("|ret:{t:?}"),
        None => String::new(),
    }
}

/// Trust: mint-or-reuse a fail-closed declaration `FuncId` (`defined` = count of pass-1
/// defined functions; declarations take the ids after them, first-encounter order). Shared by
/// the `Inst::Call` callee rewrite and the `Constant::FnDef` rewrite.
fn decl_id(
    decls: &mut Vec<(String, FuncId, String, Option<Ty>)>,
    defined: usize,
    key: String,
    name: String,
    ret: Option<Ty>,
) -> FuncId {
    match decls.iter().find(|(k, _, _, _)| *k == key) {
        Some((_, id, _, _)) => *id,
        None => {
            let id = FuncId::new((defined + decls.len()) as u32);
            // Trust (#178): `ret` rides the entry so the declaration can be given a signature that
            // actually returns something. It is part of `key`, so a reused entry's stored `ret`
            // always equals this one — no last-writer-wins ambiguity.
            decls.push((key, id, name, ret));
            id
        }
    }
}

/// Equality-interning into `Module::func_types` (`add_func_type` itself never dedups).
fn intern_func_ty(module: &mut Module, ft: FuncTy) -> FuncTyId {
    match module.func_types.iter().position(|existing| *existing == ft) {
        Some(i) => FuncTyId::new(i as u32),
        None => module.add_func_type(ft),
    }
}

/// Can this body be spliced into the crate module as a defined function? Fail-closed structural
/// tripwires on top of "lowered clean" — see the module docs.
///
/// Trust: on top of the original tripwires, this now VALIDATES every precondition of the
/// enum/struct/type-table remap `prepare_body_tables` performs (so pass-1 admission and the
/// remap can never disagree):
///   * the body's enum table is positional (`enums[i].id == i`) and SELF-CONTAINED: every
///     variant field is table-free (the producer's `register_enum` seedable-scalar wall —
///     re-checked, never assumed). Self-containment is what makes the enums-FIRST intern
///     order acyclic;
///   * the body's struct table is positional (`structs[i].id == i`) and NESTED-FIRST: a def's
///     field may reference `Ty::Struct(j)` only for `j < i` (the producer registers fields
///     depth-first — checked, not assumed) or a resolvable `Ty::Enum` (any index — enums are
///     interned first), and nothing else table-indexed (`Ty::Array` inside a struct DEF stays
///     refused: the def→types cross-reference would make the two tables' intern order
///     circular);
///   * the body's types table entries may reference enums/structs (any — both tables are
///     interned first) and strictly-EARLIER types entries (`Ty::Array(j', _)` with `j' < j`,
///     the producer's pend-order invariant), nothing else table-indexed;
///   * every signature / block-param / instruction-embedded type is `ty_spliceable`: table-free
///     OR a resolvable `Ty::Enum`/`Ty::Struct`/`Ty::Array` (which pass 1 remaps).
///     Instruction-embedded types are enumerated by `inst_embedded_tys` — an instruction
///     variant it does not model refuses the body (fail-closed) rather than moving an
///     unscanned type between modules.
fn splice_ok(r: &BodyRecord) -> bool {
    if !r.unsupported.is_empty() {
        return false;
    }
    // Trust (totality Batch C): a symbolic body's module carries value-less
    // extern-immutable globals — lowered-for-coverage, never spliced.
    if r.symbolic {
        return false;
    }
    let (Some(f), Some(ft)) = (&r.function, &r.func_ty) else {
        return false;
    };
    // Enum table: positional ids, and every variant field RESOLVABLE (`enum_def_field_ok`).
    // Trust (#174): this used to demand table-free-or-strictly-earlier-enum, because pass 1
    // interned enums before structs so an enum could not name a struct id. Pass 1 is now a
    // TOPOLOGICAL intern of the enum+struct DAG, so ordering is the intern's job (and a cycle
    // fails the body closed there); splice_ok's job here is resolvability alone.
    for (i, ed) in r.enums.iter().enumerate() {
        if ed.id.as_usize() != i {
            return false;
        }
        // Trust (B3-3): a variant field may be a NESTED first-class enum with
        // a strictly smaller id (registration is inner-before-outer) — the
        // struct-table nested-first discipline, mirrored. Everything else
        // must be table-free.
        if !ed.variants.iter().all(|v| v.fields.iter().all(|f| enum_def_field_ok(r, f))) {
            return false;
        }
    }
    // Struct table: positional ids + nested-first, def fields spliceable (no Array/Func/…).
    for (i, sd) in r.structs.iter().enumerate() {
        if sd.id.as_usize() != i {
            return false;
        }
        if !sd.fields.iter().all(|field| def_field_ok(r, &field.ty, i)) {
            return false;
        }
    }
    // Types table: entries may reference structs + strictly-earlier types entries.
    for (j, t) in r.types.iter().enumerate() {
        if !type_entry_ok(r, t, j) {
            return false;
        }
    }
    // Trust (B6): closure-type table — the `func` id must index the body's own
    // func_types snapshot (with table-free params/returns, re-interned at splice),
    // and every capture must be table-free (the producer's thin-capture gate,
    // CHECKED here, never assumed).
    for ct in &r.closure_types {
        let func_ok = r.func_types.get(ct.func.as_usize()).is_some_and(|ft| {
            !ft.is_vararg && ft.params.iter().chain(ft.returns.iter()).all(ty_table_free)
        });
        if !func_ok || !ct.captures.iter().all(ty_table_free) {
            return false;
        }
    }
    // Trust (wave-16/17/PA): globals table — a global is spliceable ONLY in a strict allow-list of
    // shapes (`global_spliceable`/`global_const_ok`): a TABLE-FREE SCALAR (wave-16 promoted borrow),
    // a BYTES `Ty::Array(TyId, N)` of `Int`s (wave-17 string literal), or a `Ty::Tuple`/`Ty::Struct`
    // aggregate with a `Constant::Aggregate` whose every element/field recursively matches (wave-PA
    // promoted borrow of a const array/tuple/struct of scalars). Any other `ty`/initializer shape
    // makes the whole body non-spliceable — CHECKED here (never assumed), recorded in coverage,
    // never spliced unsoundly.
    if !r.globals.iter().all(|g| global_spliceable(r, g)) {
        return false;
    }
    // Signature and block-param types must be spliceable (remappable ⇒ nothing dangles).
    if !ft.params.iter().chain(ft.returns.iter()).all(|t| ty_spliceable(r, t)) {
        return false;
    }
    for block in &f.blocks {
        if !block.params.iter().all(|(_, ty)| ty_spliceable(r, ty)) {
            return false;
        }
        for node in &block.body {
            // Trust: every instruction-embedded type must be spliceable. The one exception is
            // a reified fn-pointer constant's `Ty::Func` (its own arm below re-interns the sig
            // id through `body_sig_ok`); `inst_embedded_tys` skips exactly that position.
            match inst_embedded_tys(&node.inst) {
                Some(tys) => {
                    if !tys.into_iter().all(|t| ty_spliceable(r, t)) {
                        return false;
                    }
                }
                // An instruction variant the ty-scan does not model (never producer-emitted
                // today) — refuse rather than move an unscanned type between modules.
                None => return false,
            }
            match &node.inst {
                // The FuncId-bearing instruction pass 2 rewrites through the ledger.
                Inst::Call { .. } => {}
                // Trust: an indirect call is spliceable iff its embedded per-body sig id
                // resolves to a non-vararg, table-free signature (pass 2 re-interns it into
                // the assembled module).
                Inst::CallIndirect { sig, .. } => {
                    if !body_sig_ok(r, *sig) {
                        return false;
                    }
                }
                // FuncId-bearing but not rewritten here — never emitted by the producer today;
                // fail closed if that ever changes.
                Inst::Invoke { .. } => return false,
                Inst::Const { ty, value } => match value {
                    // Trust: a reified fn-pointer constant — spliceable iff typed `Ty::Func`
                    // over a resolvable per-body sig AND its `FuncId` has exactly ONE ledger
                    // identity (pass 2 rewrites it exactly like a Call callee; zero identities
                    // means an unledgered emission, two a local/extern DefIndex collision —
                    // both refuse, never guess).
                    Constant::FnDef(fid) => {
                        let Ty::Func(sig) = ty else { return false };
                        if !body_sig_ok(r, *sig) {
                            return false;
                        }
                        if r.callees.iter().filter(|c| c.func_id == *fid).count() != 1 {
                            return false;
                        }
                    }
                    _ => {
                        if !constant_funcid_free(value) {
                            return false;
                        }
                    }
                },
                Inst::Switch { cases, .. } => {
                    if !cases.iter().all(|c| constant_funcid_free(&c.value)) {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

/// Trust: is `ty` movable into the assembled module for body `r` — either verbatim
/// (`ty_table_free`) or via the pass-1 remap (a `Ty::Enum` resolvable in `r.enums` / a
/// `Ty::Struct` resolvable in `r.structs` under the positional-id invariant, or a `Ty::Array`
/// whose `TyId` resolves in `r.types`)? Allow-list recursion, so any unhandled variant fails
/// closed.
fn ty_spliceable(r: &BodyRecord, ty: &Ty) -> bool {
    match ty {
        Ty::Vector(elem, _) => ty_spliceable(r, elem),
        Ty::Tuple(elems) => elems.iter().all(|e| ty_spliceable(r, e)),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => ty_spliceable(r, inner),
        Ty::Struct(sid) => r.structs.get(sid.as_usize()).is_some_and(|sd| sd.id == *sid),
        Ty::Enum(eid) => r.enums.get(eid.as_usize()).is_some_and(|ed| ed.id == *eid),
        Ty::Array(tid, _) => tid.as_usize() < r.types.len(),
        // Trust (B6): a first-class closure type is spliceable iff its id indexes the
        // body's closure_types snapshot (the table's own invariants — func in range,
        // table-free captures — are checked once in `splice_ok`).
        Ty::Closure(cid) => cid.as_usize() < r.closure_types.len(),
        // Trust (B2): a slice fat pointer is spliceable iff its element id indexes
        // the body's types snapshot (remapped in pass 1); id-less fat kinds fall to
        // the table-free catch below.
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(tid)) => tid.as_usize() < r.types.len(),
        // Func/Record/Sequence/Set and anything new: not remapped here.
        _ => ty_table_free(ty),
    }
}

/// Trust: may `ty` appear as a FIELD of struct def index `i` in the body's struct table?
/// Table-free types and Tuple/Vector/Ref-like nesting are fine; a nested `Ty::Struct(j)`
/// must be strictly EARLIER (`j < i` — the nested-first registration order the remap relies
/// on); a `Ty::Enum` must resolve in the body's enum table (ANY index — enums intern before
/// structs, and their defs are checked self-contained, so no cycle is possible); anything
/// else table-indexed (incl. `Ty::Array`, whose types-table entry may itself reference
/// structs — a cross-table cycle) fails closed.
/// Trust (#174): may `ty` appear as a VARIANT FIELD of enum def `i` in a spliceable body?
///
/// The sibling of [`def_field_ok`] for the enum table, and deliberately NOT the same rule.
/// `def_field_ok` keeps a nested-first bound on struct-to-struct references (`sid < i`) because
/// that is the producer's own registration discipline for the struct table; enum variant fields
/// have no such bound to inherit now that pass 1 interns topologically. Both a struct and an
/// enum reference need only RESOLVE against the body's tables — the topological intern places
/// them in dependency order, and a cycle refuses the body there rather than here.
///
/// Everything else must still be table-free: a `Ty::Array`/`Ty::Closure`/`Ty::FatPtr(Slice)`
/// names the TYPES or closure table, which intern strictly after both def tables, so a def
/// field naming one could not be remapped.
fn enum_def_field_ok(r: &BodyRecord, ty: &Ty) -> bool {
    match ty {
        Ty::Vector(elem, _) => enum_def_field_ok(r, elem),
        Ty::Tuple(elems) => elems.iter().all(|e| enum_def_field_ok(r, e)),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => enum_def_field_ok(r, inner),
        Ty::Struct(sid) => r.structs.get(sid.as_usize()).is_some_and(|sd| sd.id == *sid),
        Ty::Enum(eid) => r.enums.get(eid.as_usize()).is_some_and(|ed| ed.id == *eid),
        _ => ty_table_free(ty),
    }
}

fn def_field_ok(r: &BodyRecord, ty: &Ty, i: usize) -> bool {
    match ty {
        Ty::Vector(elem, _) => def_field_ok(r, elem, i),
        Ty::Tuple(elems) => elems.iter().all(|e| def_field_ok(r, e, i)),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => def_field_ok(r, inner, i),
        Ty::Struct(sid) => sid.as_usize() < i,
        Ty::Enum(eid) => r.enums.get(eid.as_usize()).is_some_and(|ed| ed.id == *eid),
        _ => ty_table_free(ty),
    }
}

/// Trust: may `ty` appear as ENTRY `j` of the body's types table? Enums and structs resolve
/// against their (fully-validated, interned-first) tables; a nested `Ty::Array(j', _)` must
/// reference a strictly-earlier entry (`j' < j` — `pend_ty` pends inner-before-outer);
/// anything else table-indexed fails closed.
fn type_entry_ok(r: &BodyRecord, ty: &Ty, j: usize) -> bool {
    match ty {
        Ty::Vector(elem, _) => type_entry_ok(r, elem, j),
        Ty::Tuple(elems) => elems.iter().all(|e| type_entry_ok(r, e, j)),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => type_entry_ok(r, inner, j),
        Ty::Struct(sid) => r.structs.get(sid.as_usize()).is_some_and(|sd| sd.id == *sid),
        Ty::Enum(eid) => r.enums.get(eid.as_usize()).is_some_and(|ed| ed.id == *eid),
        Ty::Array(tid, _) => tid.as_usize() < j,
        _ => ty_table_free(ty),
    }
}

/// Trust: the `Ty` positions embedded in a producer-emitted instruction, for the splice's
/// fail-closed type scan (`splice_ok`) — `None` for any variant this walk does not model
/// (refused there). MUST stay in lockstep with `inst_embedded_tys_mut` (pass-1 remap); the
/// two differ only in mutability. A reified fn-pointer constant's `Ty::Func` is deliberately
/// NOT yielded — its sig id is re-interned by the existing `body_sig_ok`/pass-2 machinery.
fn inst_embedded_tys(inst: &Inst) -> Option<Vec<&Ty>> {
    Some(match inst {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. } => vec![ty],
        Inst::Cast { src_ty, dst_ty, .. } => vec![src_ty, dst_ty],
        Inst::GEP { pointee_ty, .. } => vec![pointee_ty],
        // Trust (B2-1): the fat-pointer trio embeds two types each — the fat pointer
        // type and its metadata type (both may carry a `FatPtr(Slice(TyId))` /
        // table-indexed component, remapped in pass 1 like every other position).
        Inst::PtrData { ptr_ty, .. } => vec![ptr_ty],
        Inst::PtrMetadata { ptr_ty, metadata_ty, .. } => vec![ptr_ty, metadata_ty],
        Inst::PtrFromParts { ptr_ty, metadata_ty, .. } => vec![ptr_ty, metadata_ty],
        Inst::Const { ty, value } => match value {
            Constant::FnDef(_) => vec![],
            _ => vec![ty],
        },
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        // Trust (wave-16): a promoted-borrow global address embeds a `GlobalId`, no `Ty` — the
        // `GlobalId` is remapped separately in `prepare_body_tables`.
        | Inst::GlobalAddr { .. }
        | Inst::NullPtr => vec![],
        _ => return None,
    })
}

/// Mutable twin of [`inst_embedded_tys`] — the pass-1 remap writes through these. Keep in
/// lockstep (same variants, same positions).
fn inst_embedded_tys_mut(inst: &mut Inst) -> Option<Vec<&mut Ty>> {
    Some(match inst {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. } => vec![ty],
        Inst::Cast { src_ty, dst_ty, .. } => vec![src_ty, dst_ty],
        Inst::GEP { pointee_ty, .. } => vec![pointee_ty],
        // Trust (B2-1): lockstep with the immutable walker — the fat-pointer trio.
        Inst::PtrData { ptr_ty, .. } => vec![ptr_ty],
        Inst::PtrMetadata { ptr_ty, metadata_ty, .. } => vec![ptr_ty, metadata_ty],
        Inst::PtrFromParts { ptr_ty, metadata_ty, .. } => vec![ptr_ty, metadata_ty],
        Inst::Const { ty, value } => match value {
            Constant::FnDef(_) => vec![],
            _ => vec![ty],
        },
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        // Trust (wave-16): GlobalAddr embeds a `GlobalId`, no `Ty` (remapped separately).
        | Inst::GlobalAddr { .. }
        | Inst::NullPtr => vec![],
        _ => return None,
    })
}

/// Trust: pass-1 table interning + full type remap for one ADMITTED body (all preconditions
/// validated by `splice_ok` on the same record). Interns the body's struct defs (nested-first,
/// fields remapped, `add_struct_def` structural dedup) and types entries (`intern_ty` equality
/// dedup) into the assembled module, then rewrites every embedded `EnumId`/`StructId`/`TyId`
/// in a CLONE of the body's function + signature. Returns `None` (body not admitted — a
/// defensive tripwire, structurally unreachable) rather than ever emitting a dangling or
/// half-remapped id.
/// Trust (C2-spans): re-intern one instruction's span file id from the body's mini-module
/// table into the assembled module's. A dangling producer id is a bug, but spans are METADATA:
/// drop the span rather than refuse the body — a splice rate must never depend on debug info.
fn remap_node_span(node: &mut InstrNode, files: &[String], module: &mut Module) {
    let Some(sp) = node.span else { return };
    node.span = files
        .get(sp.file as usize)
        .map(|path| SourceSpan { file: module.intern_file(path.as_str()), ..sp });
}

/// Trust (C2-scopes): the scope table's spans carry file ids from the SAME per-body table
/// as instruction spans, so they need the same re-interning — a scope left pointing at the
/// mini-module's index would name a different file (or none) once assembled. The topology
/// (`parent`) is index-into-this-function and needs no remap. Dangling ids drop the span
/// and KEEP the scope: losing a location costs a debugger one line number, losing the entry
/// would renumber every later scope and invalidate every node index pointing past it.
fn remap_func_scopes(func: &mut Function, files: &[String], module: &mut Module) {
    let Some(scopes) = func.scopes.as_mut() else { return };
    for sc in scopes.iter_mut() {
        let Some(sp) = sc.span else { continue };
        sc.span = files
            .get(sp.file as usize)
            .map(|path| SourceSpan { file: module.intern_file(path.as_str()), ..sp });
    }
}

/// Trust (#174): a node in a body's enum+struct definition DAG, for the topological intern in
/// [`prepare_body_tables`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DefNode {
    Enum(usize),
    Struct(usize),
}

/// Collect the enum/struct definitions that `ty` names, appending to `out`.
///
/// FAIL-CLOSED BY OMISSION, deliberately: if a `Ty` variant that carries an `EnumId`/`StructId`
/// is missing from this walk, the topological order may intern its def too early, and
/// `remap_ty` then finds a `None` and DECLINES the body. A miss costs coverage, never
/// correctness — which is why this mirrors `remap_ty`'s recursive structure rather than trying
/// to be clever. `Ty::Array`/`Ty::Closure`/`Ty::FatPtr(Slice)` name the TYPES / closure tables,
/// which intern strictly after both def tables, so they are not DAG nodes here; a def field
/// naming one already declines in `remap_ty` against the empty maps, exactly as before.
fn collect_def_refs(ty: &Ty, out: &mut Vec<DefNode>) {
    match ty {
        Ty::Enum(e) => out.push(DefNode::Enum(e.as_usize())),
        Ty::Struct(sid) => out.push(DefNode::Struct(sid.as_usize())),
        Ty::Vector(inner, _)
        | Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => collect_def_refs(inner, out),
        Ty::Tuple(elems) => {
            for e in elems {
                collect_def_refs(e, out);
            }
        }
        _ => {}
    }
}

/// The DAG edges out of one definition node: every enum/struct its field types name.
/// `None` = the node index is out of range (refuse the body).
fn def_node_refs(r: &BodyRecord, n: DefNode, out: &mut Vec<DefNode>) -> Option<()> {
    out.clear();
    match n {
        DefNode::Enum(i) => {
            for variant in &r.enums.get(i)?.variants {
                for fty in &variant.fields {
                    collect_def_refs(fty, out);
                }
            }
        }
        DefNode::Struct(j) => {
            for field in &r.structs.get(j)?.fields {
                collect_def_refs(&field.ty, out);
            }
        }
    }
    Some(())
}

/// Trust (#181): the STABLE CLASS NAME of a validation error, for the ratchet.
///
/// The variant name ONLY, never the payload: payloads carry block ids, struct ids and type
/// spellings that differ per body, so a histogram keyed on those would produce a different set
/// of buckets every run — unrankable, which is exactly the failure the anonymous `Other`
/// coverage tag caused before it was made exhaustive.
///
/// EVERY variant reports its OWN name. An earlier cut of this mapped anything outside a
/// hand-written allowlist to `"Other"`, and the first full-corpus run promptly produced an
/// `Other` bucket of 49 — an unplannable blob, the very thing this function exists to prevent,
/// reintroduced by the function itself. The allowlist is gone: the name is derived from `Debug`,
/// which renders `VariantName { .. }` / `VariantName(..)`, so a new upstream variant names
/// itself the day it first fires and needs no maintenance here.
fn validation_error_class(e: &trust_ir_build::ValidationError) -> String {
    let rendered = format!("{e:?}");
    let name: String = rendered
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    // A `Debug` impl that does not start with an identifier would yield an empty string; report
    // that as a named bucket rather than a blank field, so it is visible instead of silent.
    if name.is_empty() { "UnnamedVariant".to_string() } else { name }
}

fn prepare_body_tables(r: &BodyRecord, module: &mut Module) -> Option<(Function, FuncTy)> {
    let (Some(func), Some(func_ty)) = (&r.function, &r.func_ty) else {
        return None;
    };
    // Trust (#174): TOPOLOGICAL intern of the enum+struct DAG, replacing the old fixed
    // "enums FIRST, then structs" order.
    //
    // That fixed order was the ONLY thing forcing enum variant fields to be table-free — an
    // enum def could not name a struct id because structs had not been interned yet. It was an
    // assembler convention, never a format rule: verified in first-party/trust-ir that
    // `ty_layout_shape_inner`'s `Ty::Struct(id)` arm resolves by LOOKUP in `self.structs`, and
    // that the validator's enum-variant-field check is a dangling-reference check through
    // `module.struct_def(id)` — also a lookup. Both require RESOLVABILITY, neither requires an
    // ordering. So the constraint moves here, where it belongs: intern each def only after
    // everything it references, whichever kind that is.
    //
    // The graph is acyclic in practice (`register_enum`/`register_struct` decline recursive
    // ADTs via `adt_visit_stack`), but that is NOT assumed — a back edge fails the body closed
    // rather than looping. Likewise an out-of-range reference. Every failure mode here is a
    // `None` = "body not spliced, recorded in coverage", never a mis-linked id.
    //
    // The maps become sparse (`Vec<Option<_>>`) because they are filled out of body order;
    // `remap_ty` resolves through the Option, so a reference to a not-yet-interned def is a
    // decline instead of a wrong id. They are densified back before the types/closure/global
    // phases below, which still run strictly after both def tables.
    let n_enums = r.enums.len();
    let n_structs = r.structs.len();
    let total_defs = n_enums.checked_add(n_structs)?;
    // Node numbering: enums [0, n_enums), structs [n_enums, total_defs).
    let node_of = |n: DefNode| match n {
        DefNode::Enum(i) => i,
        DefNode::Struct(j) => n_enums + j,
    };
    const UNVISITED: u8 = 0;
    const ON_PATH: u8 = 1;
    const DONE: u8 = 2;
    let mut state = vec![UNVISITED; total_defs];
    let mut order: Vec<DefNode> = Vec::with_capacity(total_defs);
    let mut stack: Vec<(DefNode, bool)> = Vec::new();
    let mut refs: Vec<DefNode> = Vec::new();
    let starts = (0..n_enums).map(DefNode::Enum).chain((0..n_structs).map(DefNode::Struct));
    for start in starts {
        if state[node_of(start)] == DONE {
            continue;
        }
        stack.push((start, false));
        while let Some((n, expanded)) = stack.pop() {
            let k = node_of(n);
            if expanded {
                // Post-order: every dependency of `n` is already in `order`.
                state[k] = DONE;
                order.push(n);
                continue;
            }
            if state[k] == DONE {
                // Reached twice through different parents; the first visit already placed it.
                continue;
            }
            if state[k] == ON_PATH {
                return None; // defensive: a back edge is a cycle — fail closed.
            }
            state[k] = ON_PATH;
            stack.push((n, true));
            def_node_refs(r, n, &mut refs)?;
            for m in refs.drain(..) {
                let mk = match m {
                    DefNode::Enum(i) if i < n_enums => node_of(m),
                    DefNode::Struct(j) if j < n_structs => node_of(m),
                    // Out-of-range id: refuse the body rather than intern against a table
                    // that cannot resolve it.
                    _ => return None,
                };
                match state[mk] {
                    UNVISITED => stack.push((m, false)),
                    ON_PATH => return None, // cycle
                    _ => {}
                }
            }
        }
    }
    let mut enum_map: Vec<Option<EnumId>> = vec![None; n_enums];
    let mut struct_map: Vec<Option<StructId>> = vec![None; n_structs];
    for n in &order {
        match *n {
            DefNode::Enum(i) => {
                let mut remapped = r.enums.get(i)?.clone();
                for variant in &mut remapped.variants {
                    for fty in &mut variant.fields {
                        // Trust (B3-3 + #174): a nested first-class enum field, and now a
                        // struct-payload field, both resolve through the maps — which the
                        // topological order guarantees are already filled for everything this
                        // def names.
                        *fty = remap_ty(fty, &enum_map, &struct_map, &[], &[])?;
                    }
                }
                enum_map[i] = Some(module.add_enum_def(remapped));
            }
            DefNode::Struct(j) => {
                let mut remapped = r.structs.get(j)?.clone();
                for field in &mut remapped.fields {
                    field.ty = remap_ty(&field.ty, &enum_map, &struct_map, &[], &[])?;
                }
                struct_map[j] = Some(module.add_struct_def(remapped));
            }
        }
    }
    // Densify: the traversal covers every node, so a `None` here would mean the walk missed
    // one — refuse rather than let a later phase index a hole.
    let enum_map: Vec<EnumId> = enum_map.into_iter().collect::<Option<Vec<_>>>()?;
    let struct_map: Vec<StructId> = struct_map.into_iter().collect::<Option<Vec<_>>>()?;
    let enum_map: Vec<Option<EnumId>> = enum_map.into_iter().map(Some).collect();
    let struct_map: Vec<Option<StructId>> = struct_map.into_iter().map(Some).collect();
    let mut ty_map: Vec<TyId> = Vec::with_capacity(r.types.len());
    for t in &r.types {
        // (A types entry cannot reference a closure type — `type_entry_ok` refuses it —
        // so the closure map, built AFTER this loop, is passed empty: fail-closed.)
        let remapped = remap_ty(t, &enum_map, &struct_map, &ty_map, &[])?;
        ty_map.push(intern_ty(module, remapped));
    }
    // Trust (B6): closure-type table — after types (a ClosureTy's captures may reference
    // structs/types entries; its `func` indexes the BODY's func_types table and is
    // re-interned into the assembled module here). Captures are table-free by the
    // producer's thin-capture gate — re-checked in `splice_ok`, remapped defensively
    // anyway (a `?`-decline refuses the body, never a guess).
    let mut closure_map: Vec<trust_ir::ClosureTyId> = Vec::with_capacity(r.closure_types.len());
    for ct in &r.closure_types {
        let mut ft = r.func_types.get(ct.func.as_usize())?.clone();
        for t in ft.params.iter_mut().chain(ft.returns.iter_mut()) {
            *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)?;
        }
        let func = intern_func_ty(module, ft);
        let mut captures = ct.captures.clone();
        for t in captures.iter_mut() {
            *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)?;
        }
        closure_map.push(intern_closure_ty(module, trust_ir::ClosureTy { func, captures }));
    }
    // Trust (wave-16): globals last (they reference no table — validated scalar in `splice_ok`).
    // Append each into the assembled module under a crate-unique deterministic name (the
    // producer's body-local `__trust_promoted_<i>` would collide across bodies), producing a
    // per-body `GlobalId` remap (body position `i` → assembled index). Appended pre-remap like
    // the enum/struct/type tables above (a later `?`-decline leaves at most an unreferenced
    // global — harmless, and structurally unreachable since `splice_ok` validated the body).
    let mut global_map: Vec<GlobalId> = Vec::with_capacity(r.globals.len());
    for g in &r.globals {
        let new_idx = module.globals.len();
        let mut g = g.clone();
        g.name = format!("__trust_promoted_{new_idx}");
        // Trust (wave-17): a bytes `Ty::Array(TyId, N)` global's element `TyId` indexes the body's
        // types table — remap it to the assembled module's interned id (the `ty_map` built above,
        // globals come after the types loop). A wave-16 SCALAR global's `ty` is table-free, so this
        // is a no-op there. `?`-decline (an out-of-range id) refuses the body, consistent with the
        // enum/struct/type table remaps; `splice_ok` already validated the id, so it never fires.
        g.ty = remap_ty(&g.ty, &enum_map, &struct_map, &ty_map, &closure_map)?;
        module.globals.push(g);
        global_map.push(GlobalId::new(new_idx as u32));
    }
    if enum_map.is_empty()
        && struct_map.is_empty()
        && ty_map.is_empty()
        && global_map.is_empty()
        && closure_map.is_empty()
    {
        // Fast path: no TABLES to remap — but spans still cross module boundaries, and a span
        // file id is only meaningful against the table that minted it (C2-spans).
        let mut f = func.clone();
        for block in &mut f.blocks {
            for node in &mut block.body {
                remap_node_span(node, &r.files, module);
            }
        }
        remap_func_scopes(&mut f, &r.files, module);
        return Some((f, func_ty.clone()));
    }
    let mut ft = func_ty.clone();
    for t in ft.params.iter_mut().chain(ft.returns.iter_mut()) {
        *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)?;
    }
    let mut f = func.clone();
    for block in &mut f.blocks {
        for (_, ty) in &mut block.params {
            *ty = remap_ty(ty, &enum_map, &struct_map, &ty_map, &closure_map)?;
        }
        for node in &mut block.body {
            remap_node_span(node, &r.files, module);
            for t in inst_embedded_tys_mut(&mut node.inst)? {
                *t = remap_ty(t, &enum_map, &struct_map, &ty_map, &closure_map)?;
            }
            // Trust (wave-16): remap a promoted-borrow `Inst::GlobalAddr`'s per-body `GlobalId`
            // to its assembled-module index (`splice_ok` validated the id is in range).
            if let Inst::GlobalAddr { global } = &mut node.inst {
                *global = *global_map.get(global.as_usize())?;
            }
        }
    }
    remap_func_scopes(&mut f, &r.files, module);
    Some((f, ft))
}

/// Trust: rewrite every `EnumId`/`StructId`/`TyId` embedded in `ty` through the pass-1 maps
/// (`enum_map[k]` / `struct_map[i]` / `ty_map[j]` = the assembled module's id for the body's
/// positional entry `k`/`i`/`j`). `None` for an out-of-range id or a variant the remap does
/// not model — the caller refuses the body (fail-closed), never emits a guess.
/// Trust (#174): `enum_map`/`struct_map` are SPARSE — the topological intern in
/// `prepare_body_tables` fills them out of body order, so an entry is `None` until its def has
/// been interned. Both lookups therefore double-`?`: an id that is out of range OR not yet
/// interned declines the body. That is the whole safety property of the reordering — a
/// reference the order has not yet satisfied can never resolve to a wrong id, only to no id.
fn remap_ty(
    ty: &Ty,
    enum_map: &[Option<EnumId>],
    struct_map: &[Option<StructId>],
    ty_map: &[TyId],
    closure_map: &[trust_ir::ClosureTyId],
) -> Option<Ty> {
    Some(match ty {
        Ty::Vector(elem, n) => {
            Ty::Vector(Box::new(remap_ty(elem, enum_map, struct_map, ty_map, closure_map)?), *n)
        }
        Ty::Tuple(elems) => Ty::Tuple(
            elems
                .iter()
                .map(|e| remap_ty(e, enum_map, struct_map, ty_map, closure_map))
                .collect::<Option<Vec<_>>>()?,
        ),
        Ty::Ref(inner) => {
            Ty::Ref(Box::new(remap_ty(inner, enum_map, struct_map, ty_map, closure_map)?))
        }
        Ty::RefMut(inner) => {
            Ty::RefMut(Box::new(remap_ty(inner, enum_map, struct_map, ty_map, closure_map)?))
        }
        Ty::PtrConst(inner) => {
            Ty::PtrConst(Box::new(remap_ty(inner, enum_map, struct_map, ty_map, closure_map)?))
        }
        Ty::PtrMut(inner) => {
            Ty::PtrMut(Box::new(remap_ty(inner, enum_map, struct_map, ty_map, closure_map)?))
        }
        Ty::Rc(inner) => {
            Ty::Rc(Box::new(remap_ty(inner, enum_map, struct_map, ty_map, closure_map)?))
        }
        Ty::Struct(sid) => Ty::Struct((*struct_map.get(sid.as_usize())?)?),
        Ty::Enum(eid) => Ty::Enum((*enum_map.get(eid.as_usize())?)?),
        Ty::Array(tid, n) => Ty::Array(*ty_map.get(tid.as_usize())?, *n),
        // Trust (B6): first-class closure types remap through the pass-1 closure map
        // (per-body positional id -> assembled-module id, exactly like structs/enums).
        Ty::Closure(cid) => Ty::Closure(*closure_map.get(cid.as_usize())?),
        // Trust (B2): a slice fat pointer's ELEMENT id remaps through the types map;
        // the id-less fat kinds are table-free (handled by the catch below).
        // (B2-3: `TraitObject { trait_id }` clones VERBATIM there — sound because
        // trait_id is a CONTENT hash of the trait's def path, never a positional
        // table id; the producer's mint tripwire fail-closes hash collisions.)
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(tid)) => {
            Ty::FatPtr(trust_ir::FatPtrKind::Slice(*ty_map.get(tid.as_usize())?))
        }
        other if ty_table_free(other) => other.clone(),
        _ => return None,
    })
}

/// Equality-interning into `Module::types` (`add_type` itself never dedups) — the `TyId`
/// counterpart of [`intern_func_ty`].
fn intern_ty(module: &mut Module, ty: Ty) -> TyId {
    match module.types.iter().position(|existing| *existing == ty) {
        Some(i) => TyId::new(i as u32),
        None => module.add_type(ty),
    }
}

/// Trust (B6): equality-interning into `Module::closure_types` — the `ClosureTyId`
/// counterpart of [`intern_ty`] (`ClosureTy` identity IS `(func, captures)`, the ty#4145
/// rule, so structural dedup is the correct merge).
fn intern_closure_ty(module: &mut Module, ct: trust_ir::ClosureTy) -> trust_ir::ClosureTyId {
    match module.closure_types.iter().position(|existing| *existing == ct) {
        Some(i) => trust_ir::ClosureTyId::new(i as u32),
        None => module.add_closure_type(ct),
    }
}

/// Trust: is a per-body `FuncTyId` (embedded in `Inst::CallIndirect { sig }` /
/// `Inst::Const { ty: Ty::Func(_) }`) resolvable AND movable? It must index the body's own
/// snapshot table (`BodyRecord::func_types`), and the signature must be non-vararg with
/// table-free params/returns — `ty_table_free` rejects `Ty::Func` itself, so a higher-order
/// signature fails here and the pass-2 re-interning never needs to recurse (the producer's
/// `map_fn_ptr_ty` enforces the same bound at emission; checked again, not assumed).
fn body_sig_ok(r: &BodyRecord, sig: FuncTyId) -> bool {
    match r.func_types.get(sig.as_usize()) {
        Some(ft) => !ft.is_vararg && ft.params.iter().chain(ft.returns.iter()).all(ty_table_free),
        None => false,
    }
}

/// True iff `ty` references no module-level table (`structs`/`enums`/`types`/`func_types`/
/// `records`/`closure_types`) — i.e. it survives being moved between modules verbatim.
/// Allow-list, so any future `Ty` variant fails closed.
fn ty_table_free(ty: &Ty) -> bool {
    match ty {
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        // Trust (v25 B1): Isize/Usize (pointer-width ints, 64-bit on the pinned target) and
        // Char (32-bit unsigned carrier) are bare scalar variants referencing no module-level
        // table — table-free exactly like the fixed-width ints they used to be respelled as.
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::Unit
        | Ty::Never => true,
        // Trust (B2): FatPtr is table-free ONLY for the id-less kinds — a
        // `FatPtrKind::Slice(TyId)` references the module `types` table and
        // moving it verbatim would dangle the element id (the pre-B2 wholesale
        // `Ty::FatPtr(_) => true` arm was a latent splice bug, caught by the
        // B2 mapping sweep before any producer emitted the Slice kind).
        Ty::FatPtr(trust_ir::FatPtrKind::Str)
        | Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. }) => true,
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(_)) => false,
        Ty::Vector(elem, _) => ty_table_free(elem),
        Ty::Tuple(elems) => elems.iter().all(ty_table_free),
        Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => ty_table_free(inner),
        // Struct/Enum/Func/Record/Closure/Array/Set/Sequence (table-indexed) and anything new.
        _ => false,
    }
}


/// Trust (wave-16): is `g` a spliceable global? Two strict allow-listed shapes (any other fails
/// closed, so the assembled module can only carry the exact globals the producer mints):
///   * a promoted-borrow SCALAR global — a scalar `ty` with a matching scalar `Constant`
///     initializer (`eval_promotable_scalar`);
///   * Trust (wave-17): a BYTES `[u8; N]` global — a `Ty::Array(TyId, N)` whose element `TyId`
///     resolves to an integer scalar in the body's types table (`ty_spliceable` re-checks the id
///     is in range; `scalar_int_ty` checks the resolved element) with a `Constant::Array` of
///     scalar `Int`s (`emit_bytes_global`, the string / byte-string literal path).
fn global_spliceable(r: &BodyRecord, g: &Global) -> bool {
    // The global's declared type must be remappable into the assembled module (pass 1 remaps
    // `Struct`/`Enum`/`Array` ids; a scalar/tuple is table-free) AND its initializer must MATCH
    // that type in a splice-carriable shape. Both checked, never assumed.
    match &g.initializer {
        Some(c) => ty_spliceable(r, &g.ty) && global_const_ok(r, &g.ty, c),
        None => false,
    }
}

/// Trust (wave-16/17/PA): does constant `c` match global type `ty` in a shape the splice can carry?
/// Allow-list (any other `(ty, c)` pair fails closed, so the assembled module carries only the
/// exact globals the producer mints):
///   * a table-free SCALAR `ty` with an `Int`/`U128`/`Float`/`Bool` initializer (wave-16 promoted borrow);
///   * a BYTES `Ty::Array(TyId, N)` whose element resolves to an integer scalar with a matching
///     `Constant::Array` of `Int`s (wave-17 string / byte-string literal);
///   * Trust (wave-PA): a `Ty::Tuple`/`Ty::Struct` AGGREGATE with a `Constant::Aggregate` whose
///     every element/field recursively matches (a promoted borrow of a const array/tuple/struct of
///     scalars — `eval_promotable_aggregate`). The `Ty::Struct`/element ids are `ty_spliceable`-
///     and struct-table-validated by `splice_ok`, so a resolvable aggregate remaps cleanly.
fn global_const_ok(r: &BodyRecord, ty: &Ty, c: &Constant) -> bool {
    match (ty, c) {
        (Ty::U128, Constant::U128(_)) => true,
        (_, Constant::U128(_)) => false,
        (t, _) if scalar_global_ty(t) => scalar_global_const(c),
        (Ty::Array(tid, n), Constant::Array(elems)) => {
            // Trust (wave-17): declared length MUST equal the initializer element count (checked,
            // never assumed — a mismatch from any future minting path refuses the body).
            *n as usize == elems.len()
                && r.types.get(tid.as_usize()).is_some_and(scalar_int_ty)
                && elems.iter().all(|e| matches!(e, Constant::Int(_)))
        }
        (Ty::Tuple(elems), Constant::Aggregate(cs)) => {
            elems.len() == cs.len() && elems.iter().zip(cs).all(|(t, c)| global_const_ok(r, t, c))
        }
        (Ty::Struct(sid), Constant::Aggregate(cs)) => {
            r.structs.get(sid.as_usize()).is_some_and(|sd| {
                sd.id == *sid
                    && sd.fields.len() == cs.len()
                    && sd.fields.iter().zip(cs).all(|(f, c)| global_const_ok(r, &f.ty, c))
            })
        }
        _ => false,
    }
}

/// Trust (wave-17): is `ty` an integer scalar a bytes-array global's element may be? (The producer
/// only ever emits `Ty::U8`, but any fixed-width int with an all-`Int` initializer is consistent.)
fn scalar_int_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128
            | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128
            // Trust (v25 B1): Isize/Usize (pointer-width, 64-bit on the pinned target) are
            // integer scalars; Char is a 32-bit unsigned Int-carrying scalar (its constants
            // are `Constant::Int` leaves), so an all-`Int` array initializer stays consistent.
            | Ty::Isize | Ty::Usize | Ty::Char
    )
}

/// Trust (wave-16): is `ty` a table-FREE scalar a promoted-borrow global may declare? Only the
/// int/bool/float scalars the producer emits (`&5`/`&true`/`&1.5f32`); `Struct`/`Enum`/`Array`/
/// pointer/`Tuple`/anything table-indexed or aggregate fails closed.
fn scalar_global_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128
            | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128
            // Trust (v25 B1): a promoted borrow may now declare the first-class
            // isize/usize (pointer-width, 64-bit on the pinned target) and char (32-bit
            // unsigned carrier) scalars — their initializers are the bare `Int` leaves
            // `scalar_global_const` already admits.
            | Ty::Isize | Ty::Usize | Ty::Char
            | Ty::F32 | Ty::F64
    )
}

/// Trust (wave-16): is `c` a legacy scalar initializer a promoted-borrow global may carry?
/// Bare `Int`/`Float`/`Bool` only; v24 `U128` is handled separately in
/// `global_const_ok` so it can be pinned specifically to `Ty::U128`. Rejects every
/// aggregate, function/symbol payload, and pending-const sentinel.
fn scalar_global_const(c: &Constant) -> bool {
    matches!(c, Constant::Int(_) | Constant::Float(_) | Constant::Bool(_))
}

/// True iff the constant contains no `FuncId` (and no symbol-by-name reference, which function
/// renaming would break). Allow-list, so any future `Constant` variant fails closed.
fn constant_funcid_free(c: &Constant) -> bool {
    match c {
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::PhantomData => true,
        Constant::Aggregate(elems)
        | Constant::Array(elems)
        | Constant::Vector(elems)
        | Constant::Sequence(elems)
        | Constant::Set(elems) => elems.iter().all(constant_funcid_free),
        Constant::Record(fields) => fields.iter().all(|(_, v)| constant_funcid_free(v)),
        // FnDef, Closure, SymbolAddr, and anything new.
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// coverage.json — hand-rolled, deterministic (fixed key order, pre-sorted rows,
// no timestamps). No serde_json dependency in this rustc_private crate.
// ---------------------------------------------------------------------------

const ARTIFACT_PUBLICATION_SCHEMA: &str = "trust.thir-lower.artifact-set.v1";
const ARTIFACT_DIGEST_DOMAIN: &str = "trust.thir-lower.artifact.v1";

/// Turn coverage.json into the artifact-set commit marker. The marker is
/// installed only after binary and text data are durable, and binds their exact
/// bytes so a stale/mixed generation is mechanically distinguishable from a
/// current set.
fn coverage_publication_manifest(
    coverage: &str,
    binary_name: &str,
    binary: &[u8],
    text_name: &str,
    text: &[u8],
) -> Result<Vec<u8>, String> {
    use std::fmt::Write as _;

    let Some(mut prefix) = coverage.strip_suffix("}\n").map(str::to_string) else {
        return Err("internal coverage JSON lacks its canonical closing delimiter".to_string());
    };
    if prefix.ends_with('\n') {
        prefix.pop();
    }

    let binary_digest = artifact_digest_hex(binary);
    let text_digest = artifact_digest_hex(text);
    let _ = writeln!(prefix, ",");
    let _ = writeln!(prefix, "  \"publication\": {{");
    let _ = writeln!(prefix, "    \"schema\": \"{ARTIFACT_PUBLICATION_SCHEMA}\",");
    let _ = writeln!(prefix, "    \"digest_algorithm\": \"sha256-domain-v1\",");
    let _ = writeln!(prefix, "    \"digest_domain\": \"{ARTIFACT_DIGEST_DOMAIN}\",");
    let _ = writeln!(prefix, "    \"commit_marker\": true,");
    let _ = writeln!(prefix, "    \"artifacts\": [");
    let _ = writeln!(
        prefix,
        "      {{ \"name\": \"{}\", \"bytes\": {}, \"digest\": \"sha256:{}\" }},",
        json_escape(binary_name),
        binary.len(),
        binary_digest,
    );
    let _ = writeln!(
        prefix,
        "      {{ \"name\": \"{}\", \"bytes\": {}, \"digest\": \"sha256:{}\" }}",
        json_escape(text_name),
        text.len(),
        text_digest,
    );
    let _ = writeln!(prefix, "    ]");
    let _ = writeln!(prefix, "  }}");
    let _ = writeln!(prefix, "}}");
    Ok(prefix.into_bytes())
}

fn artifact_digest_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;

    let digest = trust_ir::ProofDigest::sha256_domain(ARTIFACT_DIGEST_DOMAIN, bytes);
    let mut hex = String::with_capacity(64);
    for byte in digest.bytes {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

fn coverage_json(
    crate_name: &str,
    rows: &[CoverageRow],
    spliced: usize,
    decls: usize,
) -> Result<String, String> {
    use std::fmt::Write as _;

    let lowered = rows.iter().filter(|r| r.lowered).count();
    // Trust (totality Batch C): lowered-but-symbolic rows (schema-additive).
    let symbolic_n = rows.iter().filter(|r| r.symbolic).count();
    // Trust: initializer bodies (const-init + static-init rows) — schema-additive totals entry
    // so the scorecard can track the non-fn-body ratchet without re-deriving it from rows.
    let initializer_bodies = rows.iter().filter(|r| r.kind != "fn").count();
    let instr_total: u64 = rows.iter().map(|r| r.instr_count).sum();
    let unsupported_total: u64 =
        rows.iter().flat_map(|r| r.unsupported.iter().map(|(_, n)| *n)).sum();
    let resolved: u64 = rows.iter().map(|r| r.calls_resolved).sum();
    let externs: u64 = rows.iter().map(|r| r.calls_extern).sum();
    let unresolved: u64 = rows.iter().map(|r| r.calls_unresolved).sum();

    let mut out = String::new();
    // Writing to a String never fails; `let _ =` keeps this expect-free.
    let _ = writeln!(out, "{{");
    let _ = writeln!(out, "  \"schema\": \"trust.thir-lower.crate-module.coverage.v2\",");
    let _ = writeln!(out, "  \"crate\": \"{}\",", json_escape(crate_name));
    let _ = writeln!(
        out,
        "  \"direct_obligation_capability\": \"{}\",",
        DIRECT_OBLIGATION_CAPABILITY.marker()
    );
    let _ = writeln!(
        out,
        "  \"proof_authority\": {},",
        DIRECT_OBLIGATION_CAPABILITY.grants_proof_authority()
    );
    let _ = writeln!(
        out,
        "  \"native_verification_requests\": {},",
        DIRECT_OBLIGATION_CAPABILITY.emits_native_verification_requests()
    );
    let _ = writeln!(out, "  \"totals\": {{");
    let _ = writeln!(out, "    \"bodies\": {},", rows.len());
    let _ = writeln!(out, "    \"lowered\": {lowered},");
    let _ = writeln!(out, "    \"symbolic\": {symbolic_n},");
    let _ = writeln!(out, "    \"spliced\": {spliced},");
    let _ = writeln!(out, "    \"declarations\": {decls},");
    let _ = writeln!(out, "    \"initializer_bodies\": {initializer_bodies},");
    let _ = writeln!(out, "    \"instr_count\": {instr_total},");
    let _ = writeln!(out, "    \"unsupported\": {unsupported_total},");
    let _ = writeln!(
        out,
        "    \"calls\": {{ \"resolved\": {resolved}, \"extern_decls\": {externs}, \"unresolved\": {unresolved} }}"
    );
    let _ = writeln!(out, "  }},");
    let _ = writeln!(out, "  \"bodies\": [");
    for (i, r) in rows.iter().enumerate() {
        let unsupported = r
            .unsupported
            .iter()
            .map(|(reason, n)| format!("[\"{}\", {n}]", json_escape(reason)))
            .collect::<Vec<_>>()
            .join(", ");
        // Trust (v2 Phase 0a): per-tag detail examples — `{"tag": ["ex", ...], ...}`. Additive
        // field (consumers key-index); empty object when the body is clean.
        let unsupported_details = r
            .unsupported_details
            .iter()
            .map(|(tag, exs)| {
                let ex_list = exs
                    .iter()
                    .map(|e| format!("\"{}\"", json_escape(e)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("\"{}\": [{}]", json_escape(tag), ex_list)
            })
            .collect::<Vec<_>>()
            .join(", ");
        // Trust (v2 Phase 0b): the collect-all pass rows (empty arrays for clean bodies).
        let fmt_pairs = |v: &Vec<(String, u64)>| {
            v.iter()
                .map(|(reason, n)| format!("[\"{}\", {n}]", json_escape(reason)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let collect_primary = fmt_pairs(&r.collect_primary);
        let collect_cascade = fmt_pairs(&r.collect_cascade);
        let seam = match (r.deferred_to_seam, &r.seam) {
            (false, None) => "{ \"state\": \"not-applicable\" }".to_string(),
            (true, Some(outcome)) => format!(
                "{{ \"state\": \"resolved\", \"verdict\": \"{}\", \"samples\": {}, \
                 \"detail\": \"{}\" }}",
                outcome.verdict.marker(),
                outcome.samples,
                json_escape(&outcome.detail),
            ),
            (true, None) => {
                return Err(format!(
                    "coverage row `{}` (def index {}) is deferred but lacks a resolved seam \
                     outcome",
                    r.def_path, r.def_index
                ));
            }
            (false, Some(_)) => {
                return Err(format!(
                    "coverage row `{}` (def index {}) is not deferred but carries a seam \
                     outcome",
                    r.def_path, r.def_index
                ));
            }
        };
        let comma = if i + 1 == rows.len() { "" } else { "," };
        // Trust (L1): the lineage digest (schema-additive). `null` = no single-function
        // mini-module existed for this record, so no green recording / flip was possible.
        // The digest string is `Display`-formatted (`sha256:<hex>`), matching the flip
        // event's `lineage` field byte-for-byte.
        let lineage = match &r.lineage {
            Some(digest) => format!("\"{digest}\""),
            None => "null".to_string(),
        };
        // Trust (L1): the assembled-module address (schema-additive). `null` = the body was
        // not spliced, so it has no function in the artifact to point at.
        let func_id = match r.func_id {
            Some(id) => id.to_string(),
            None => "null".to_string(),
        };
        let _ = writeln!(
            out,
            "    {{ \"def_path\": \"{}\", \"def_index\": {}, \"kind\": \"{}\", \"lowered\": {}, \
             \"symbolic\": {}, \
             \"spliced\": {}, \"lineage\": {}, \"func_id\": {}, \"instr_count\": {}, \
             \"unsupported\": [{}], \
             \"unsupported_details\": {{{}}}, \
             \"collect_primary\": [{}], \"collect_cascade\": [{}], \"calls\": {{ \
             \"resolved\": {}, \"extern_decls\": {}, \"unresolved\": {} }}, \
             \"differentials\": {{ \"interpreter\": {{ \"verdict\": \"{}\", \
             \"samples\": {}, \"detail\": \"{}\" }}, \"derived_mir\": {{ \"verdict\": \
             \"{}\", \"detail\": \"{}\", \"markers_exact\": {}, \"markers_detail\": \
             \"{}\" }}, \"deferred_to_seam\": {}, \"seam\": {} }} }}{}",
            json_escape(&r.def_path),
            r.def_index,
            r.kind,
            r.lowered,
            r.symbolic,
            r.spliced,
            lineage,
            func_id,
            r.instr_count,
            unsupported,
            unsupported_details,
            collect_primary,
            collect_cascade,
            r.calls_resolved,
            r.calls_extern,
            r.calls_unresolved,
            r.interpreter.verdict.marker(),
            r.interpreter.samples,
            json_escape(&r.interpreter.detail),
            r.derived_mir.verdict.marker(),
            json_escape(&r.derived_mir.detail),
            r.derived_mir.markers_exact,
            json_escape(&r.derived_mir.markers_detail),
            r.deferred_to_seam,
            seam,
            comma,
        );
    }
    let _ = writeln!(out, "  ]");
    let _ = writeln!(out, "}}");
    Ok(out)
}

#[cfg(test)]
mod authority_tests {
    use super::*;

    fn evidence(verdict: ArtifactVerdict) -> InterpreterEvidence {
        InterpreterEvidence { verdict, samples: 0, detail: verdict.marker().to_string() }
    }

    fn coverage_row(def_index: u32, deferred_to_seam: bool) -> CoverageRow {
        CoverageRow {
            def_path: format!("probe::{def_index}"),
            def_index,
            kind: "fn",
            lowered: true,
            symbolic: false,
            spliced: true,
            instr_count: 0,
            unsupported: Vec::new(),
            unsupported_details: Vec::new(),
            collect_primary: Vec::new(),
            collect_cascade: Vec::new(),
            calls_resolved: 0,
            calls_extern: 0,
            calls_unresolved: 0,
            interpreter: evidence(ArtifactVerdict::NotRun),
            derived_mir: DerivedMirEvidence {
                verdict: ArtifactVerdict::Unsupported,
                detail: "unsupported".to_string(),
                markers_exact: false,
                markers_detail: "not compared".to_string(),
            },
            deferred_to_seam,
            seam: None,
            lineage: None,
            func_id: None,
        }
    }

    #[test]
    fn artifact_verdicts_preserve_agreement_mismatch_unsupported_and_not_run() {
        use crate::differential::DiffMode;

        assert_eq!(
            classify_interpreter_verdict(DiffMode::Agreed, true, false),
            Ok(ArtifactVerdict::Agreed)
        );
        assert_eq!(
            classify_interpreter_verdict(DiffMode::MirOracle, false, false),
            Ok(ArtifactVerdict::Mismatch)
        );
        assert_eq!(
            classify_interpreter_verdict(DiffMode::NotRun, false, true),
            Ok(ArtifactVerdict::Unsupported)
        );
        assert_eq!(
            classify_interpreter_verdict(DiffMode::NotRun, false, false),
            Ok(ArtifactVerdict::NotRun)
        );

        for inconsistent in [
            (DiffMode::Agreed, false, false),
            (DiffMode::Agreed, true, true),
            (DiffMode::MirOracle, true, false),
            (DiffMode::MirOracle, false, true),
            (DiffMode::NotRun, true, false),
        ] {
            assert!(
                classify_interpreter_verdict(inconsistent.0, inconsistent.1, inconsistent.2)
                    .is_err(),
                "inconsistent report {inconsistent:?} must fail closed"
            );
        }
    }

    #[test]
    fn coverage_is_rendered_only_with_an_exact_resolved_seam_inventory() {
        use crate::differential::DiffMode;

        let mut rows = vec![coverage_row(3, true), coverage_row(7, false)];
        assert!(
            coverage_json("probe", &rows, 2, 0).is_err(),
            "a deferred row without a seam result must not serialize"
        );

        let seam = [SeamVerdict {
            def_index: 3,
            equal: true,
            samples: 4,
            mode: DiffMode::Agreed,
            note: "linked agreement".to_string(),
        }];
        assert!(install_seam_outcomes(&mut rows, &seam).is_empty());
        let coverage = coverage_json("probe", &rows, 2, 0).expect("resolved coverage");
        assert!(coverage.contains("trust.thir-lower.crate-module.coverage.v2"));
        assert!(coverage.contains(
            "\"seam\": { \"state\": \"resolved\", \"verdict\": \"agreed\", \"samples\": 4"
        ));
        assert!(coverage.contains("\"seam\": { \"state\": \"not-applicable\" }"));
        assert!(
            !coverage.contains("\"equal\""),
            "the ambiguous producer boolean must not enter the artifact schema"
        );
    }

    #[test]
    fn seam_inventory_rejects_missing_duplicate_unexpected_and_zero_sample_agreement() {
        use crate::differential::DiffMode;

        let agreed = |def_index, samples| SeamVerdict {
            def_index,
            equal: true,
            samples,
            mode: DiffMode::Agreed,
            note: "agreement".to_string(),
        };

        let mut missing = vec![coverage_row(3, true)];
        assert!(install_seam_outcomes(&mut missing, &[])[0].contains("omitted deferred body"));

        let mut duplicate = vec![coverage_row(3, true)];
        let errors = install_seam_outcomes(&mut duplicate, &[agreed(3, 1), agreed(3, 1)]);
        assert!(errors.iter().any(|error| error.contains("duplicate verdicts")));

        let mut unexpected = vec![coverage_row(7, false)];
        let errors = install_seam_outcomes(&mut unexpected, &[agreed(7, 1), agreed(9, 1)]);
        assert!(errors.iter().any(|error| error.contains("non-deferred body")));
        assert!(errors.iter().any(|error| error.contains("unknown def index 9")));

        let mut vacuous = vec![coverage_row(3, true)];
        let errors = install_seam_outcomes(&mut vacuous, &[agreed(3, 0)]);
        assert!(errors.iter().any(|error| error.contains("without a sampled execution")));
        assert!(vacuous[0].seam.is_none());
    }

    /// Trust (L1): the artifact row renders the lineage digest exactly as the flip event
    /// logs it (`Display`: `sha256:<hex>`), and `null` for digest-less records — so the
    /// two carriers are matchable byte-for-byte.
    #[test]
    fn test_coverage_rows_render_lineage_digest_and_null() {
        let mut module = Module::new("lineage_row_probe");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(FuncId::new(0), "probe", ty, BlockId::new(0)));
        let digest = crate::lineage::body_lineage_digest(&module, &[])
            .expect("single-function probe module must digest");

        let mut with_digest = coverage_row(3, false);
        with_digest.lineage = Some(digest);
        with_digest.func_id = Some(4);
        let rows = vec![with_digest, coverage_row(7, false)];
        let coverage = coverage_json("probe", &rows, 2, 0).expect("resolved coverage");
        assert!(
            coverage.contains(&format!("\"lineage\": \"{digest}\"")),
            "a digest-bearing row must render the Display form the flip event logs"
        );
        assert!(
            coverage.contains("\"lineage\": \"sha256:"),
            "the rendered digest must be algorithm-prefixed"
        );
        assert!(
            coverage.contains("\"lineage\": null"),
            "a digest-less record must render an explicit null, never a fabricated value"
        );
        assert!(
            coverage.contains("\"func_id\": 4"),
            "a spliced row must publish its index into the assembled function table"
        );
        assert!(
            coverage.contains("\"func_id\": null"),
            "an un-spliced row has no assembled function to address, and must say so"
        );
    }

    /// A per-body record whose mini-module is the minimal spliceable shape: one
    /// zero-argument, block-free function, no tables, no callees. `lineage` is minted by
    /// the production function over that same mini-module, exactly as `record` does.
    fn lineage_body_record(def_index: u32, fn_name: &str) -> BodyRecord {
        let mut module = Module::new("lineage_assembly_probe");
        let func_ty = FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false };
        let ty = module.add_func_type(func_ty.clone());
        module.add_function(Function::new(FuncId::new(0), fn_name, ty, BlockId::new(0)));
        let lineage = crate::lineage::body_lineage_digest(&module, &[])
            .expect("the minimal per-body mini-module must digest");
        let function = module.functions.remove(0);
        BodyRecord {
            def_index,
            kind: BodyKind::Fn,
            symbolic: false,
            def_path: fn_name.to_string(),
            place_path_carrier: false,
            function: Some(function),
            func_ty: Some(func_ty),
            files: Vec::new(),
            closure_types: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            types: Vec::new(),
            globals: Vec::new(),
            unsupported: Vec::new(),
            unsupported_details: Vec::new(),
            collect_primary: Vec::new(),
            collect_cascade: Vec::new(),
            instr_count: 0,
            callees: Vec::new(),
            func_types: Vec::new(),
            pending_consts: Vec::new(),
            deferred: false,
            interpreter: evidence(ArtifactVerdict::NotRun),
            derived_mir: DerivedMirEvidence {
                verdict: ArtifactVerdict::Agreed,
                detail: "agreed".to_string(),
                markers_exact: true,
                markers_detail: "identical".to_string(),
            },
            differential_errors: Vec::new(),
            mir_snapshot: None,
            lineage: Some(lineage),
        }
    }

    /// Trust (L1), the assembly leg of the lineage chain: assembly SORTS bodies, assigns
    /// fresh dense `FuncId`s, re-interns types and rewrites callees — and the row must come
    /// out the other side carrying (a) the digest minted BEFORE any of that, unchanged, and
    /// (b) the address of the function it became. Those two facts are what let an external
    /// consumer say "the body the flip selected is THIS function of the artifact".
    ///
    /// What this test does NOT establish — deliberately, and stated so no reader mistakes
    /// the plumbing for the theorem: that the assembled function still MEANS what the
    /// pre-assembly mini-module meant. That is the canonical-remapping certificate, which
    /// does not exist (see `crate::lineage`, "Future work").
    #[test]
    fn test_assembly_preserves_lineage_digest_and_addresses_the_assembled_function() {
        // Deliberately out of DefIndex order: assembly sorts, and the row must follow its
        // own body rather than its input position.
        let mut sorted =
            vec![lineage_body_record(9, "probe::second"), lineage_body_record(2, "probe::first")];
        sorted.sort_by_key(|r| r.def_index);

        let assembled = assemble("lineage_assembly_probe", &sorted);
        assert_eq!(assembled.spliced, 2, "both minimal bodies must splice");

        for record in &sorted {
            let row = assembled
                .coverage_rows
                .iter()
                .find(|row| row.def_index == record.def_index)
                .expect("every record must produce a coverage row");
            assert_eq!(
                row.lineage, record.lineage,
                "assembly must carry the pre-assembly digest through unchanged"
            );
            let func_id = row.func_id.expect("a spliced row must address its assembled function");
            let function = assembled
                .module
                .functions
                .get(func_id as usize)
                .expect("func_id must index the assembled function table");
            assert_eq!(
                function.id.index(),
                func_id,
                "the assembler's `functions[i].id == i` invariant is what makes func_id an address"
            );
            assert_eq!(
                function.name, record.def_path,
                "func_id must address the function this row is about, not merely some function"
            );
        }

        let first = assembled.coverage_rows.iter().find(|r| r.def_index == 2).expect("row");
        let second = assembled.coverage_rows.iter().find(|r| r.def_index == 9).expect("row");
        assert_ne!(
            first.lineage, second.lineage,
            "distinct bodies must be distinguishable by digest, or matching is meaningless"
        );
        assert_ne!(first.func_id, second.func_id, "distinct bodies must get distinct addresses");
    }

    #[test]
    fn direct_thir_artifacts_are_explicitly_non_authoritative() {
        let assembled = assemble("direct_authority_tripwire", &[]);
        let coverage = coverage_json(
            "direct_authority_tripwire",
            &assembled.coverage_rows,
            assembled.spliced,
            assembled.declarations,
        )
        .expect("empty coverage inventory is resolved");

        assert_eq!(DIRECT_OBLIGATION_CAPABILITY, DirectObligationCapability::StructuralParityOnly);
        assert!(!DIRECT_OBLIGATION_CAPABILITY.grants_proof_authority());
        assert!(!DIRECT_OBLIGATION_CAPABILITY.emits_native_verification_requests());
        assert!(assembled.module.proof_obligations.is_empty());
        assert!(
            !assembled.module.proof_summary().is_fully_verified_strict(),
            "an empty direct obligation table must never mean strictly verified"
        );
        assert!(
            coverage.contains("\"direct_obligation_capability\": \"structural-parity-only-v1\"")
        );
        assert!(coverage.contains("\"proof_authority\": false"));
        assert!(coverage.contains("\"native_verification_requests\": false"));
        assert!(direct_authority_inventory_errors(&assembled.module).is_empty());
    }

    #[test]
    fn direct_thir_authority_inventory_fails_closed_on_future_claim_wiring() {
        let mut module = Module::new("direct_authority_violation");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "direct", ty, BlockId::new(0));
        function.proofs.push(trust_ir::proof::ProofAnnotation::NoOverflow);
        function.summary = Some(trust_ir::FunctionSummary::new());
        module.add_function(function);
        module.spec_modules.push(SpecModule::linked("claimed_machine"));

        let errors = direct_authority_inventory_errors(&module);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("obligations 1"));
        assert!(errors[0].contains("function claims 1"));
        assert!(errors[0].contains("function summaries 1"));
        assert!(errors[0].contains("linked spec modules 1"));
    }

    /// The tripwire bounds PROOF CONTENT, not module population. Measured
    /// 2026-07-29 because a design doc had recorded the opposite, and sent the
    /// next reader chasing a capability flip they do not need.
    ///
    /// Two-language design item 11 (§1 converse) lowers a Clean `def` into this
    /// same module as an ordinary executable function. Such a function carries no
    /// obligations, no claims and no summary, so it must add ZERO to every one of
    /// the seven counters — and therefore must NOT require flipping
    /// `DIRECT_OBLIGATION_CAPABILITY`, which is documented as "a deliberate
    /// soundness event". Adding proof content to that same function still trips
    /// the wire, which is what keeps the distinction meaningful rather than a
    /// loophole: the pin below asserts BOTH directions on one function.
    #[test]
    fn a_proof_free_function_does_not_trip_the_direct_authority_tripwire() {
        let mut module = Module::new("proof_free_population");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        // The shape a lowered Clean `def` would have: real executable content,
        // empty `proofs`, no `summary`.
        let plain = Function::new(FuncId::new(0), "clean_def_gcd", ty, BlockId::new(0));
        assert!(plain.proofs.is_empty(), "the lowered-def shape carries no claims");
        assert!(plain.summary.is_none(), "the lowered-def shape carries no summary");
        module.add_function(plain);

        assert!(
            direct_authority_inventory_errors(&module).is_empty(),
            "populating `functions` is not proof authority; the tripwire bounds \
             obligations/certificates/diagnostics/claims/summaries/spec-proofs/linked-specs"
        );
        assert_eq!(
            DIRECT_OBLIGATION_CAPABILITY,
            DirectObligationCapability::StructuralParityOnly,
            "and it stays StructuralParityOnly while doing so"
        );

        // The other direction, on the SAME function: one claim is enough to trip.
        module.functions[0].proofs.push(trust_ir::proof::ProofAnnotation::NoOverflow);
        let errors = direct_authority_inventory_errors(&module);
        assert_eq!(errors.len(), 1, "a claim-bearing function must still fail closed");
        assert!(errors[0].contains("function claims 1"));
    }

    #[test]
    fn direct_thir_finalization_requires_an_exact_body_inventory() {
        assert!(body_inventory_errors(&[], &[]).is_empty());
        assert!(body_inventory_errors(&[7, 2, 11], &[2, 7, 11]).is_empty());

        let errors = body_inventory_errors(&[2, 7, 11], &[2, 13]);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("missing def indices [7, 11]"));
        assert!(errors[0].contains("unexpected def indices [13]"));

        let errors = body_inventory_errors(&[2, 2], &[2, 2]);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("duplicate expected ids 1"));
        assert!(errors[0].contains("duplicate recorded ids 1"));
    }

    #[test]
    fn direct_thir_registry_retains_duplicate_callbacks_for_finalization() {
        let mut records = BTreeMap::new();
        let mut duplicates = Vec::new();
        insert_registry_record(&mut records, &mut duplicates, 2, "first");
        insert_registry_record(&mut records, &mut duplicates, 7, "other");
        insert_registry_record(&mut records, &mut duplicates, 2, "replayed");

        assert_eq!(records.get(&2), Some(&"first"));
        assert_eq!(duplicates, [2]);

        let mut recorded = records.keys().copied().collect::<Vec<_>>();
        recorded.extend(duplicates);
        let errors = body_inventory_errors(&[2, 7], &recorded);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("duplicate recorded ids 1"));
    }

    #[test]
    fn direct_module_without_obligation_birth_cannot_enter_mir_native_planner() {
        let mut module = Module::new("direct_without_obligations");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(
            Function::new(FuncId::new(0), "direct", ty, BlockId::new(0))
                .with_producer(trust_ir::Producer::TRust),
        );
        let error = trust_ir_bridge::native_verification_bundle_from_module(
            module,
            trust_ir::ProofDigest::sha256([0x51; 32]),
            FuncId::new(0),
        )
        .expect_err("an obligation-free direct module must fail closed");

        assert_eq!(error, trust_ir_bridge::NativeVerificationBundleBuildError::EmptyObligations);
    }

    #[test]
    fn coverage_commit_marker_binds_exact_binary_and_text_generations() {
        assert_eq!(
            artifact_digest_hex(b""),
            "a28e05a07a056643c31e80c62a564f20fa655ef4b90d22a2728ef057745e496b",
            "artifact digest must remain domain-framed SHA-256, not a self-consistent substitute"
        );
        let base = coverage_json("publication", &[], 0, 0).expect("empty coverage is resolved");
        let first = coverage_publication_manifest(
            &base,
            "publication.trust-ir.bin",
            b"binary-a",
            "publication.trust-ir.txt",
            b"text-a",
        )
        .expect("build first publication commit marker");
        let changed_binary = coverage_publication_manifest(
            &base,
            "publication.trust-ir.bin",
            b"binary-b",
            "publication.trust-ir.txt",
            b"text-a",
        )
        .expect("build second publication commit marker");
        let changed_text = coverage_publication_manifest(
            &base,
            "publication.trust-ir.bin",
            b"binary-a",
            "publication.trust-ir.txt",
            b"text-b",
        )
        .expect("build third publication commit marker");

        let first = String::from_utf8(first).unwrap();
        assert!(first.contains("\"schema\": \"trust.thir-lower.artifact-set.v1\""));
        assert!(first.contains("\"commit_marker\": true"));
        assert!(first.contains("\"name\": \"publication.trust-ir.bin\""));
        assert!(first.contains("\"name\": \"publication.trust-ir.txt\""));
        assert_ne!(first.as_bytes(), changed_binary.as_slice());
        assert_ne!(first.as_bytes(), changed_text.as_slice());
    }

    #[test]
    fn first_class_emit_target_preserves_exact_binary_path_and_distinct_companions() {
        let target = emit_publication_target(std::path::Path::new("nested/foo.trust-ir.bin"))
            .expect("valid first-class emit target");
        assert_eq!(target.directory, PathBuf::from("nested"));
        assert_eq!(target.binary_name, "foo.trust-ir.bin");
        assert_eq!(target.text_name, "foo.trust-ir.txt");
        assert_eq!(target.coverage_name, "foo.trust-ir.coverage.json");

        let local = emit_publication_target(std::path::Path::new("foo.trust-ir.bin"))
            .expect("parentless output is relative to the current directory");
        assert_eq!(local.directory, PathBuf::from("."));

        assert!(
            emit_publication_target(std::path::Path::new("foo.txt")).is_err(),
            "an output whose extension swap aliases its text companion must fail closed"
        );
    }
}

#[cfg(test)]
mod temporal_tests {
    use super::*;

    fn action(
        owner: &'static str,
        name: &'static str,
        function: u32,
    ) -> TemporalActionDecl<&'static str> {
        TemporalActionDecl {
            owner,
            name: name.to_string(),
            function: FuncId::new(function),
            rust_symbol: format!("{owner}::{name}"),
            span: "fixture.rs:1:1".to_string(),
            guard: None,
            ghost: None,
        }
    }

    fn var(
        owner: &'static str,
        name: &'static str,
        leaf_field: usize,
    ) -> TemporalVarDecl<&'static str> {
        TemporalVarDecl { owner, name: name.to_string(), kind: "Int".to_string(), leaf_field }
    }

    fn resolve(
        edges: &[TemporalFieldEdge<&'static str>],
        vars: &[TemporalVarDecl<&'static str>],
        actions: &[TemporalActionDecl<&'static str>],
    ) -> Result<Vec<ResolvedTemporalMachine<&'static str>>, TemporalCarryError> {
        resolve_temporal_machines(edges, vars, actions, str::to_string)
    }

    #[test]
    fn direct_temporal_carry_is_explicitly_non_certifying() {
        let spec = direct_temporal_spec_module("crate::Machine".to_string());
        assert_eq!(spec.enforcement, trust_ir::SpecEnforcementMode::DesignOnly);

        let mut module = Module::new("temporal_metadata");
        module.spec_modules.push(spec);
        assert!(direct_authority_inventory_errors(&module).is_empty());
    }

    #[test]
    fn grid_storage_var_is_owned_by_outer_grid_with_full_path_and_typed_action() {
        let machines = resolve(
            &[TemporalFieldEdge { holder: "crate::Grid", held: "crate::GridStorage", field: 2 }],
            &[var("crate::GridStorage", "scrollback", 1)],
            &[action("crate::Grid", "Erase", 7)],
        )
        .expect("two-level temporal ownership must resolve");

        assert_eq!(machines.len(), 1);
        assert_eq!(machines[0].owner, "crate::Grid");
        assert_eq!(machines[0].vars[0].path, vec![2, 1]);
        assert_eq!(machines[0].actions[0].function, FuncId::new(7));
    }

    #[test]
    fn equal_bare_type_and_field_names_never_merge_defid_owners() {
        let machines = resolve(
            &[],
            &[var("crate::left::Machine", "state", 0), var("crate::right::Machine", "state", 0)],
            &[
                action("crate::left::Machine", "Step", 3),
                action("crate::right::Machine", "Step", 4),
            ],
        )
        .expect("distinct DefId owners must remain distinct");

        assert_eq!(machines.len(), 2);
        assert_eq!(machines[0].owner, "crate::left::Machine");
        assert_eq!(machines[1].owner, "crate::right::Machine");
        assert_eq!(machines[0].vars[0].path, vec![0]);
        assert_eq!(machines[1].vars[0].path, vec![0]);
    }

    #[test]
    fn multiple_by_value_holders_fail_closed() {
        let error = resolve(
            &[
                TemporalFieldEdge { holder: "crate::A", held: "crate::Storage", field: 0 },
                TemporalFieldEdge { holder: "crate::B", held: "crate::Storage", field: 1 },
            ],
            &[var("crate::Storage", "state", 0)],
            &[action("crate::A", "Step", 0)],
        )
        .expect_err("ambiguous ownership must not fall back to a flat projection");

        assert!(matches!(error, TemporalCarryError::AmbiguousHolder { .. }));
    }

    #[test]
    fn more_than_two_struct_levels_fail_closed() {
        let error = resolve(
            &[
                TemporalFieldEdge { holder: "crate::Middle", held: "crate::Inner", field: 1 },
                TemporalFieldEdge { holder: "crate::Outer", held: "crate::Middle", field: 2 },
            ],
            &[var("crate::Inner", "state", 0)],
            &[action("crate::Outer", "Step", 0)],
        )
        .expect_err("deep projection must not be truncated or flattened");

        assert!(matches!(error, TemporalCarryError::DeepOwnership { depth: 2, .. }));
    }

    #[test]
    fn duplicate_names_fail_closed_per_machine() {
        let duplicate_var = resolve(
            &[],
            &[var("crate::Machine", "state", 0), var("crate::Machine", "state", 1)],
            &[action("crate::Machine", "Step", 0)],
        )
        .expect_err("duplicate variable names must be rejected");
        assert!(matches!(duplicate_var, TemporalCarryError::DuplicateVariable { .. }));

        let duplicate_action = resolve(
            &[],
            &[var("crate::Machine", "state", 0)],
            &[action("crate::Machine", "Step", 0), action("crate::Machine", "Step", 1)],
        )
        .expect_err("duplicate action names must be rejected");
        assert!(matches!(duplicate_action, TemporalCarryError::DuplicateAction { .. }));
    }

    #[test]
    fn duplicate_projection_paths_fail_closed_even_with_distinct_names() {
        let error = resolve(
            &[],
            &[var("crate::Machine", "left", 0), var("crate::Machine", "right", 0)],
            &[action("crate::Machine", "Step", 0)],
        )
        .expect_err("one concrete field cannot project to two abstract variables");
        assert!(matches!(error, TemporalCarryError::DuplicateProjection { .. }));
    }

    #[test]
    fn action_owner_without_variables_fails_closed() {
        let error = resolve(&[], &[], &[action("crate::Machine", "Step", 0)])
            .expect_err("an action-only machine has no state projection");
        assert!(matches!(error, TemporalCarryError::ActionWithoutVariables { .. }));
    }

    #[test]
    fn ownership_cycle_before_any_action_owner_fails_closed() {
        let error = resolve(
            &[
                TemporalFieldEdge { holder: "crate::A", held: "crate::B", field: 0 },
                TemporalFieldEdge { holder: "crate::B", held: "crate::A", field: 0 },
            ],
            &[var("crate::A", "state", 0)],
            &[action("crate::Unrelated", "Step", 0)],
        )
        .expect_err("cyclic ownership must never loop or select a partial owner");
        assert!(matches!(error, TemporalCarryError::OwnershipCycle { .. }));
    }

    #[test]
    fn direct_action_owner_is_independent_of_ambiguous_non_action_wrappers() {
        let machines = resolve(
            &[
                TemporalFieldEdge { holder: "crate::Left", held: "crate::Machine", field: 0 },
                TemporalFieldEdge { holder: "crate::Right", held: "crate::Machine", field: 0 },
            ],
            &[var("crate::Machine", "state", 0)],
            &[action("crate::Machine", "Step", 0)],
        )
        .expect("the nearest action owner is a semantic boundary");
        assert_eq!(machines.len(), 1);
        assert_eq!(machines[0].owner, "crate::Machine");
        assert_eq!(machines[0].vars[0].path, vec![0]);
    }

    #[test]
    fn connected_inner_and_outer_action_owners_fail_explicitly() {
        let error = resolve(
            &[TemporalFieldEdge { holder: "crate::Outer", held: "crate::Inner", field: 0 }],
            &[var("crate::Inner", "state", 0)],
            &[action("crate::Inner", "InnerStep", 0), action("crate::Outer", "OuterStep", 1)],
        )
        .expect_err("connected action owners define competing machine boundaries");
        assert!(matches!(error, TemporalCarryError::NestedActionOwners { .. }));
    }

    #[test]
    fn annotated_var_without_action_owner_fails_closed() {
        let error = resolve(&[], &[var("crate::Storage", "state", 0)], &[])
            .expect_err("an unowned temporal variable must not create a detached module");
        assert!(matches!(error, TemporalCarryError::UnownedVariable { .. }));
    }

    #[test]
    fn semantic_temporal_error_is_reported_without_publication_state() {
        let mut module = Module::new("no_dump");
        let errors = install_temporal_modules(
            &mut module,
            Err(TemporalCarryError::UnownedVariable {
                owner: "crate::Storage".to_string(),
                name: "state".to_string(),
            }),
        );

        assert!(module.spec_modules.is_empty());
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("failed closed"));
        assert!(errors[0].contains("has no #[trust::action] owner"));
    }
}
