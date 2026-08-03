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
//! # Pending consts (reentrancy-safe eval)
//!
//! Before assembly, [`finalize_and_dump`] runs `resolve_pending_consts`: every named const the
//! hook deferred (the scalar leg defers LOCAL consts, because evaluating one inside `mir_built`
//! re-enters MIR building; the wave-SC `&str` leg has no locality split and defers non-local
//! consts too — see `crate::PendingConst`) is evaluated HERE via
//! `const_eval_resolve_for_typeck` — safe at this
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
//! without exactly one ledger identity, a FORCED-HAVOC one, or one whose LOCAL target's own
//! producer-signed `func_ty` does not structurally equal the claimed `Ty::Func` sig
//! (`fnptr_target_sig_ok` — arity is not implied by sig-resolvability); or any other `Constant`
//! outside the scalar/aggregate allow-list (`Closure`, `SymbolAddr`, …) makes the body
//! non-spliceable (recorded in
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
    /// Trust (union lane): the body registered >=1 UNION PLACEHOLDER LANE — a struct field whose
    /// Rust type is a `union`, spelled `Ty::Unit`. NEVER spliced (`splice_ok` checks this field):
    /// the assembled executable module must not contain a `StructDef` one of whose lanes claims
    /// zero bytes for bytes that exist. This is also what confines the forced-`contains_call`
    /// bodies out of the crate-seam interpreter — see `LowerCx::register_union_lane`.
    union_lane: bool,
    /// Trust (enum param lane): the body registered >=1 ENUM PARAM PLACEHOLDER LANE — a variant
    /// field whose ground-truth rustc type is a bare `ty::Param`, spelled `Ty::Unit`. NEVER
    /// spliced (`splice_ok` checks this field): the assembled executable module must not contain
    /// an `EnumDef` one of whose lanes claims zero bytes for a caller's `T`. This is also what
    /// confines the forced-`contains_call` bodies out of the crate-seam interpreter — see
    /// `LowerCx::register_enum_param_lane`, whose doc states the 3↔4 dependency in full.
    enum_param_lane: bool,
    /// `tcx.def_path_str` — unique, deterministic display identity within the crate.
    def_path: String,
    /// Trust (B3-2c seam guard): the body used a place-path VALUE carrier in a
    /// call arg (wave-RS/MC/receiver-value lanes) — CLEAN-ONLY by contract; the
    /// seam must not link+interpret it (a carried value hits the callee's real
    /// ptr param as a manufactured signature-mismatch defect verdict).
    place_path_carrier: bool,
    /// Trust (wave-ZC): the body passed a capture-free closure to a call as the ZST
    /// `Ty::Unit`/`Constant::PhantomData` value. `splice_ok` refuses the body on this
    /// field ALONE — see `crate::Lowered::zst_closure_arg` for why the refusal must be
    /// ours rather than a side effect of Rust having no syntax for a closure type.
    zst_closure_arg: bool,
    /// Trust (fn-ptr adapter lane): the body's mini-module carries a PRODUCER-SYNTHESIZED
    /// closure→fn-pointer adapter — a function with no rustc counterpart. `splice_ok` refuses the
    /// body on this field ALONE (and `run_seam_differentials` skips it on the same field), for
    /// the reason spelled out at `crate::Lowered::fnptr_adapter`: the per-body channel below is
    /// single-function, so the adapter is DROPPED at `record` and a spliced body would carry a
    /// `Constant::FnDef` naming a function the assembled module does not contain.
    fnptr_adapter: bool,
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
    /// Trust (v2 Phase 0a): per-tag DETAIL examples `(tag, truncated details)`, sorted by
    /// tag — decomposes the bare-"Ty"/"Other" catch-alls in the coverage JSON. At most
    /// `DETAIL_CAP_DEFAULT` per tag unless `TRUST_COVERAGE_DETAIL_CAP` says otherwise
    /// ([`coverage_detail_cap`]).
    unsupported_details: Vec<(String, Vec<String>)>,
    /// Trust (wave-EF): `(enum def path, decline reason)` rows from `register_enum`, aggregated
    /// and deduped — see `Lowered::enum_declines`. ALWAYS EMPTY unless
    /// `TRUST_ENUM_DECLINE_CENSUS=1`, and never merged into `unsupported`: a decline is not a
    /// body failure, so it must not move `lowered` for any body.
    enum_declines: Vec<(String, String)>,
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
    /// Trust: named consts the hook deferred (see `Lowered::pending_consts`). NOT necessarily
    /// LOCAL: the scalar leg defers only `def_id.is_local()` consts, but the wave-SC `&str` leg
    /// deliberately has no locality split — it gates on finalizer-DERIVABILITY (`is_type_const` +
    /// all-region args), which an upstream-crate const satisfies just as well. Do not reintroduce
    /// a locality assumption here. The finalizer —
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

/// Trust (v2 Phase 0b): the exact CASCADE tag set — a fail-closed tag that is the downstream
/// SHADOW of an earlier failed binding, not a leaf demand of its own. A body whose only remaining
/// tags are cascade tags is blocked by whatever failed to bind, so booking these as primary demand
/// would overstate the leaf work and mis-rank every coverage target derived from `collect_primary`.
///
/// MEASUREMENT ONLY. Nothing here gates splice/flip/differential (the five `unsupported.is_empty()`
/// gates do that), so a wrong entry corrupts ranking, never soundness.
///
/// Every entry must name a LIVE emitter in `lib.rs`; a tag with no emitter is deleted rather than
/// carried, so this table stays a description of the producer rather than of its history:
///   * `VarRef(unbound)`          — reading a local that was never `set_local`'d.
///   * `Borrow(unbound local)`    — `&x` where `x` has no live SSA value.
///   * `AssignOp(unbound local)`  — `x += …` where `x` has no live SSA value.
/// `Borrow(&mut unbound local)` was carried here with NO emitter anywhere in the crate and is
/// therefore absent; re-add it only together with the site that pushes it. `Borrow(slot missing)`
/// is deliberately NOT cascade: a promoted local with no `Alloca` means the local's own `let`
/// declined, which is leaf demand at that `let`.
///
/// `pub` because it is THE classifier, not one of two: the `mir_built` hook
/// (`rustc_mir_build::builder::mod.rs`, the collect-all debug event) used to carry a second inline
/// copy that had already drifted (it missed `AssignOp(unbound local)` and still listed the
/// emitter-less `Borrow(&mut unbound local)`). That copy now calls [`is_cascade_tag`], so the
/// pinning tests below govern every classification the coverage program ranks off.
pub const CASCADE_TAGS: [&str; 3] =
    ["VarRef(unbound)", "Borrow(unbound local)", "AssignOp(unbound local)"];

/// Trust: PRIMARY vs CASCADE classification for one collect-all tag. See [`CASCADE_TAGS`].
/// The single classifier — both the coverage recorder ([`record`]) and the `mir_built` hook's
/// collect-all debug event call THIS.
pub fn is_cascade_tag(tag: &str) -> bool {
    CASCADE_TAGS.contains(&tag)
}

/// Trust (tranche 4, 2026-07-31): how many DISTINCT detail examples a coverage row keeps per tag.
///
/// An enum, not a bare `usize`, because "no limit" is a different mode from "limit N" and the
/// two must not be spelled by a magic number (`0` on the wire, never in the type).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DetailCap {
    /// At most `n` distinct examples per tag. `Limited(DETAIL_CAP_DEFAULT)` is the default and
    /// reproduces every pre-tranche artifact byte-for-byte.
    Limited(usize),
    /// Every distinct example. Reached ONLY by `TRUST_COVERAGE_DETAIL_CAP=0`.
    Unbounded,
}

/// The shipped budget. Moving this constant moves EVERY census artifact — the env channel below
/// exists precisely so a measurement run does not have to.
const DETAIL_CAP_DEFAULT: usize = 3;

/// Per-example char budget (char-boundary safe by construction: `chars().take(..)`).
const DETAIL_CHARS_MAX: usize = 120;

impl DetailCap {
    /// Does a tag that already holds `recorded` distinct examples admit one more?
    fn admits(self, recorded: usize) -> bool {
        match self {
            DetailCap::Limited(cap) => recorded < cap,
            DetailCap::Unbounded => true,
        }
    }
}

/// Trust (tranche 4): parse `TRUST_COVERAGE_DETAIL_CAP`. Split out of [`coverage_detail_cap`] so
/// the parse is unit-testable without touching process-global env (the `OnceLock` below reads it
/// once per process; a test that set the variable would race every other test in the binary).
///
/// * absent → [`DetailCap::Limited`]`(DETAIL_CAP_DEFAULT)` — the default artifact is unchanged.
/// * `"0"` → [`DetailCap::Unbounded`].
/// * a `u32` → `Limited(n)` (`u32`, not `usize`: the wire value must mean the same thing on a
///   32-bit host, and no census wants more than 4G examples for one tag).
/// * ANYTHING else — non-UTF-8, negative, non-numeric, overflowing — → the DEFAULT, not a
///   panic and not unbounded. A typo must not silently move the artifact's bytes; the point of
///   the default being byte-stable is that it cannot be disturbed by accident.
fn parse_detail_cap(raw: Option<&std::ffi::OsStr>) -> DetailCap {
    match raw.and_then(|v| v.to_str()).and_then(|v| v.trim().parse::<u32>().ok()) {
        Some(0) => DetailCap::Unbounded,
        Some(n) => DetailCap::Limited(n as usize),
        None => DetailCap::Limited(DETAIL_CAP_DEFAULT),
    }
}

/// Trust (tranche 4): the process-wide detail budget, read once.
///
/// # Why the lift exists — the fixed cap of 3 discards 58% of the evidence (MEASURED)
///
/// Measured on the checked-in census dump `t4-census/dump/clean_kernel.coverage.json`, produced
/// by the pre-tranche loop this function's consumer replaces:
///
/// * **29,610 spans recorded against 70,303 total tag occurrences — 58% of all evidence is
///   discarded** by the fixed `3`-distinct-examples-per-tag cap;
/// * 4,516 of 25,135 `(body, tag)` entries are TRUNCATED, i.e. the row keeps 3 spans for a tag
///   the body hit more times, and the coverage JSON records no trace that anything was dropped.
///
/// # The consequence: root/containment analysis over a truncated census is UNSOUND
///
/// This is stronger than "incomplete". Every root-cause question asked of this artifact — "is
/// this tag a ROOT, or is it a PROPAGATION marker whose span strictly CONTAINS an inner tag's?",
/// "is this body blocked by this tag ALONE?", "which construct actually failed?" — is decided by
/// comparing the recorded spans of the tags a body carries. Truncation removes spans WITHOUT
/// removing the tag, so the missing spans are silently read as "this tag has no inner span
/// beneath it" ⇒ the analysis reports a ROOT where the evidence for containment merely was not
/// kept. The error is directional (it manufactures roots, never suppresses them) and it is not
/// detectable from the artifact, because the artifact does not record that it truncated.
/// Concretely, in the class this tranche examined: span-containment is unanswerable for 366 of
/// the 582 bodies carrying `EnumCtor(unsupported payload)`, and 185 occurrences that presented as
/// "silent" roots turned out to be ENTIRELY a truncation artifact — every one of them resolved to
/// a contained inner tag once the missing spans were recovered by hand. Any conclusion drawn from
/// a default-cap census about roots or containment must therefore be re-derived under
/// `TRUST_COVERAGE_DETAIL_CAP=0` before it is believed.
///
/// # What the default is, and why it is still 3
///
/// The cap is made CONFIGURABLE, not removed. Absent/garbage env ⇒
/// [`DetailCap::Limited`]`(`[`DETAIL_CAP_DEFAULT`]` == 3)` — the pre-tranche budget, unchanged.
/// Off-by-default is the same posture `TRUST_ENUM_DECLINE_CENSUS` takes
/// (`crate::enum_decline_census` docs): this channel gates a MEASUREMENT, an unbounded census is
/// substantially larger, and a dump whose bytes move when nobody asked cannot be diffed against a
/// prior dump. The lift is therefore something an analysis run OPTS INTO
/// (`TRUST_COVERAGE_DETAIL_CAP=0`), for exactly as long as it is answering a containment question.
///
/// # Effect on the emitted census artifact — stated plainly
///
/// * The DEFAULT emits the same bytes as before: `aggregate_detail_examples` under
///   `parse_detail_cap(None)` is pinned equal to a verbatim copy of the retired loop by
///   `default_cap_reproduces_the_pre_tranche_loop`. So THIS change, at its default, does not move
///   the artifact.
/// * `TRUST_COVERAGE_DETAIL_CAP=<n≠3>` or `=0` DOES move it, by design, and the moved dump is not
///   comparable byte-for-byte with a default one — only the recovered spans are added, but the
///   file differs.
/// * Separately, and NOT because of this cap: the census artifact of this branch as a whole is
///   **not** byte-stable against the pre-tranche dump, because the wave-ZC ZST-closure-arg lane
///   changes which tags bodies carry (`Closure(value position)` occurrences disappear where the
///   lane fires, and diverging-call arg arities move). Do not describe this branch's census as
///   byte-stable on the strength of the cap default alone.
///
/// # Not a gate
///
/// It runs after lowering has finished, and neither accepts nor refuses any body.
/// `unsupported_details` is consumed only by the JSON writer (`BodyRecord` field → the
/// `CoverageRow` clone → `write_coverage_json`) — never by `to_mir` / the flip registry / the
/// interpreter, and never by the `lowered_unsupported.is_empty()` predicates that decide
/// spliceability, `deferred`, and the differential — so NO value of this variable can change
/// what is spliced, flipped, or verified. The separation is structural: the field is write-only
/// after `record`.
fn coverage_detail_cap() -> DetailCap {
    static CAP: std::sync::OnceLock<DetailCap> = std::sync::OnceLock::new();
    *CAP.get_or_init(|| parse_detail_cap(std::env::var_os("TRUST_COVERAGE_DETAIL_CAP").as_deref()))
}

/// Trust (tranche 4): aggregate per-tag detail EXAMPLES for a coverage row.
///
/// Deterministic by construction: tags in `BTreeMap` order, examples in first-encounter order
/// within a tag, each truncated to [`DETAIL_CHARS_MAX`] chars and deduped AFTER truncation (two
/// spans sharing a 120-char prefix are one example — the pre-tranche behavior, preserved).
///
/// The linear `contains` is quadratic in the DISTINCT examples of a single tag within ONE body;
/// bounded by that body's occurrence count, and only reachable at all under the opt-in
/// `Unbounded` mode (the default's 3 makes it a three-element scan).
///
/// TyCtxt-free and pure: unit-tested directly in [`detail_cap_tests`].
fn aggregate_detail_examples(
    unsupported: &[(String, &'static str)],
    cap: DetailCap,
) -> Vec<(String, Vec<String>)> {
    let mut details_by_tag: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (detail, what) in unsupported {
        let ex: String = detail.chars().take(DETAIL_CHARS_MAX).collect();
        let examples = details_by_tag.entry((*what).to_string()).or_default();
        if cap.admits(examples.len()) && !examples.contains(&ex) {
            examples.push(ex);
        }
    }
    details_by_tag.into_iter().collect()
}

/// Trust (wave-EF R1): the three DIAGNOSTIC row vectors [`record`] derives from a body's
/// fail-closed tags and its `register_enum` decline ledger. Grouped into one return so the
/// derivation is a single pure function that can be tested without a `TyCtxt`.
struct BodyTagRows {
    /// Aggregated `(tag, count)` — the ONLY one of the three that is verdict-adjacent
    /// (`unsupported.is_empty()` is what "lowered" means).
    unsupported: Vec<(String, u64)>,
    unsupported_details: Vec<(String, Vec<String>)>,
    enum_declines: Vec<(String, String)>,
}

/// Trust (wave-EF R1): derive a body's diagnostic rows. Extracted from [`record`] verbatim so the
/// decline channel's central claim becomes a TESTABLE property rather than a comment.
///
/// THE PROPERTY, pinned by `enum_decline_census_tests`: the returned `unsupported` and
/// `unsupported_details` are a function of `lowered_unsupported` ALONE. `declines` cannot add,
/// remove, or reweight a single failure tag, so a body that lowers clean lowers clean whether or
/// not `TRUST_ENUM_DECLINE_CENSUS=1` — which is the promise the whole channel rests on. Before
/// this split that promise was enforced only by nobody having written the merge; a test now fails
/// if somebody does.
///
/// Declines are deduped and sorted (`BTreeSet`) because `mir_built` runs in parallel and the
/// coverage artifact must be byte-deterministic. The dedup is a SECOND line: `push_decline_row`
/// already deduped per body at push time, which is the one that bounds memory.
///
/// Trust (tranche 4 merge): the detail examples are NOT derived by a second inline copy of the
/// example loop here. This function delegates to [`aggregate_detail_examples`] under
/// [`coverage_detail_cap`], so `TRUST_COVERAGE_DETAIL_CAP` reaches the SHIPPING path rather than
/// only the helper — a verbatim second copy would have silently pinned the census back to the
/// fixed 3 and made the whole cap lift dead code. The env read is the one impurity, and it is the
/// same one [`record`] performed before this extraction: absent/garbage ⇒ `Limited(3)`, so every
/// pre-tranche assertion below still describes the default artifact exactly.
fn aggregate_body_tag_rows(
    lowered_unsupported: &[(String, &'static str)],
    declines: Vec<(String, String)>,
) -> BodyTagRows {
    // Aggregate fail-closed reasons into deterministic (reason, count) rows.
    let mut unsupported_by_tag: BTreeMap<String, u64> = BTreeMap::new();
    for (_detail, what) in lowered_unsupported {
        let count = unsupported_by_tag.entry((*what).to_string()).or_default();
        *count = count.saturating_add(1);
    }
    // Trust (v2 Phase 0a, RFC docs/TRUST_IR_V2.md §4): ALSO carry per-tag DETAIL examples into the
    // coverage row. Every push site already formats a detail string (`push((format!(..), TAG))`) —
    // the `.0` element, previously DROPPED here — and the bare-"Ty" (397 sole) / "Other" (83 sole)
    // catch-alls are undecomposable without it. Capped at `DETAIL_CAP_DEFAULT` distinct examples
    // per tag, each truncated to `DETAIL_CHARS_MAX` chars (char-boundary safe), deterministic
    // order (first-encounter within a tag; tags sorted). Purely additive diagnostics — no
    // lowering/flip behavior change.
    //
    // Trust (tranche 4): the cap is `TRUST_COVERAGE_DETAIL_CAP`-settable (`0` = every example),
    // because the fixed 3 discards 58% of the recorded evidence (29,610 spans kept of 70,303
    // occurrences; 4,516 of 25,135 tag-entries truncated, with nothing in the artifact recording
    // that they were) — which makes ROOT-tag attribution UNSOUND, not merely incomplete: a dropped
    // span reads as "no inner tag beneath this one", so the analysis MANUFACTURES roots. Default
    // is still 3, so this call's default output is byte-identical to the loop it replaced
    // (`default_cap_reproduces_the_pre_tranche_loop`) — the same off-by-default posture
    // `TRUST_ENUM_DECLINE_CENSUS` takes. That is not a claim that the branch's census is
    // byte-stable; the wave-ZC lane moves tags independently of this cap. See
    // [`coverage_detail_cap`] for the measurement and the full statement.
    let unsupported_details = aggregate_detail_examples(lowered_unsupported, coverage_detail_cap());
    BodyTagRows {
        unsupported: unsupported_by_tag.into_iter().collect(),
        unsupported_details,
        enum_declines: declines.into_iter().collect::<BTreeSet<_>>().into_iter().collect(),
    }
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
        zst_closure_arg,
        callees,
        pending_consts,
        // Trust (#173): MEASUREMENT ONLY — consumed by the `body class` debug event at the
        // mir_built hook, not by the crate assembler. Deliberately does NOT gate the splice the
        // way `symbolic` does: an opaque-collapse body is still offered to the splice and to the
        // differential, each of which declines on its own terms. Bound explicitly rather than
        // via `..` so a future field cannot slip past this destructure unnoticed.
        opaque_collapse: _opaque_collapse,
        // Trust (union lane): GATES, unlike `opaque_collapse`. Carried into the `BodyRecord` so
        // `splice_ok` can refuse the body by its own predicate. Bound explicitly for the same
        // reason the two above are.
        union_lane,
        // Trust (enum param lane): GATES, exactly like `union_lane`, and for the same reason —
        // `splice_ok` must refuse the body by its OWN predicate rather than inherit the
        // `symbolic` refusal. Bound explicitly for the same reason the others are.
        enum_param_lane,
        // Trust (fn-ptr adapter lane): GATES, exactly like `union_lane`. Carried into the
        // `BodyRecord` so `splice_ok` and the seam refuse the body by their own predicate rather
        // than by inheriting the `remove(0)` drop below. Bound explicitly for the same reason.
        fnptr_adapter,
        // Trust (wave-TR): does NOT gate the splice, and that is a decision, not an omission.
        //
        // STATED CORRECTLY, because an earlier draft of this comment claimed the spliced module is
        // "byte-identical to what the pre-wave-TR assembler would have produced minus the
        // fail-closed tag" — that is FALSE, and an adversarial review falsified it. Pre-wave-TR
        // `splice_ok` refused these bodies on its FIRST line (`!r.unsupported.is_empty()`), so the
        // assembler produced NOTHING for them. The assembled module gains a whole function.
        //
        // The true reason it may gain one: the arm emits ZERO instructions — it returns the
        // `ValueId` `lower_expr` already produced — so the function it adds makes no new claim
        // about layout, lanes, or synthesized functions, and every value in it is one the module
        // already contained. That is a claim about MISREPRESENTATION, and it is the property that
        // separates this lane from `union_lane` / `enum_param_lane` / `zst_closure_arg` /
        // `fnptr_adapter`, each of which puts a spelling into the module that stands for bytes it
        // does not describe.
        //
        // WHERE THE TWO GATES DIVERGE, explicitly, because the flip's stated reason
        // (`flip_registry::thin_reborrow_allows_flip`: "the producer holds no record it could hand
        // the flip about where the pointer came from") would, taken alone, argue for refusing here
        // too — a wave-TR body typically carries a call, hence is `deferred`, hence is what the
        // crate-seam differential's step 0 executes, and that is precisely the consequence cited
        // when `splice_ok` refuses the two placeholder lanes. The distinction this file takes: the
        // placeholder lanes are refused because the module MISDESCRIBES bytes, which no consumer
        // can detect; wave-TR's provenance gap is about what a CONSUMER can reconstruct, and the
        // flip is the consumer that must reconstruct a MIR body from it. A body whose value the
        // seam cannot follow is refused BY THE SEAM, on its own terms, not by pre-emptive
        // exclusion here. If that turns out to be wrong the correction is to gate the splice too —
        // NOT to weaken the flip refusal, which is the conservative side of the same question.
        //
        // Bound explicitly rather than via `..` for the same reason `opaque_collapse` is: a future
        // field must not slip past this destructure.
        thin_reborrow: _thin_reborrow,
        // Trust (wave-EF): the register_enum decline-reason ledger. Empty unless
        // `TRUST_ENUM_DECLINE_CENSUS=1`; carried to coverage BESIDE `unsupported`, never
        // inside it. Bound explicitly for the same reason `opaque_collapse` is.
        enum_declines: lowered_enum_declines,
    } = lowered;
    let deferred = lowered_unsupported.is_empty() && pending_consts.is_empty() && contains_call;
    // Trust: `functions[0]` is THE body function. The producer maintains that: both
    // `lower_fn` and `lower_const_body` add exactly one function, and the fn-ptr adapter lane
    // appends its synthetic functions only AFTER that one (`lower_module_inner`'s flush, which
    // fails the body closed unless exactly one function is already present). Everything past
    // index 0 is a producer-synthesized function with no rustc counterpart and is DROPPED here —
    // which is precisely why a body that carries one may never splice (`fnptr_adapter`).
    let function =
        if module.functions.is_empty() { None } else { Some(module.functions.remove(0)) };
    let func_ty = function.as_ref().and_then(|f| module.func_type(f.ty).cloned());
    let instr_count =
        function.as_ref().map(|f| f.blocks.iter().map(|b| b.body.len() as u64).sum()).unwrap_or(0);

    // Trust (wave-EF R1): tags, tag details, and the decline rows in one derivation — see
    // `aggregate_body_tag_rows` for the neutrality property it exists to make testable. The
    // decline rows are empty (⇒ the coverage key is omitted entirely) unless
    // `TRUST_ENUM_DECLINE_CENSUS=1`, so a default run stays byte-identical.
    //
    // Trust (tranche 4): the per-tag DETAIL examples this derivation returns are capped by
    // `TRUST_COVERAGE_DETAIL_CAP` (`0` = every example), read inside `aggregate_body_tag_rows` via
    // [`coverage_detail_cap`]. The default is still 3, so a default run's bytes do not move.
    let BodyTagRows { unsupported, unsupported_details, enum_declines } =
        aggregate_body_tag_rows(&lowered_unsupported, lowered_enum_declines);

    // Trust (v2 Phase 0b): the COLLECT-ALL second pass — measurement only. The caller re-lowers a
    // failed body once when either tracing or coverage requests it and shares that bounded tag
    // snapshot with this recorder. Aggregate ONLY its tag vector (the collect-all module itself
    // is discarded by construction, and the five `unsupported.is_empty()` gates keep any
    // tag-bearing body out of splice/flip/differential).
    // Tags are split PRIMARY vs CASCADE by [`is_cascade_tag`]: an unbound-local echo is the
    // downstream shadow of an earlier failed binding, not a leaf demand. See [`CASCADE_TAGS`].
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
        for (_detail, what) in collect_all {
            let dst = if is_cascade_tag(what) { &mut cascade_by_tag } else { &mut primary_by_tag };
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
        union_lane,
        enum_param_lane,
        def_path,
        place_path_carrier,
        zst_closure_arg,
        fnptr_adapter,
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
        enum_declines,
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
        // Trust (wave-ZC): a ZST-closure-arg body is refused by `splice_ok` on its own field, so
        // step 0 below already skips it (`func_of_def` → `None`). State the skip HERE too, on the
        // flag itself, so the seam wall is a SECOND decision of ours and not a consequence of the
        // splice verdict: if `splice_ok`'s line is ever relaxed (the recovery path needs a
        // positive witness at the callee's declared input — see `Lowered::zst_closure_arg`), the
        // linked interpreter must still not be handed a `Ty::Unit` standing in for a callee's
        // declared closure param, which is exactly the manufactured signature-mismatch defect the
        // `place_path_carrier` skip above exists to prevent.
        if r.zst_closure_arg {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: call args carry a ZST closure value (Ty::Unit/PhantomData \
                 standing in for a closure-typed param); linked interpretation not asserted \
                 (coverage-only)",
            ));
            continue;
        }
        // Trust (fn-ptr adapter lane): an adapter-bearing body is refused by `splice_ok` on its
        // own field, so step 0 below already skips it (`func_of_def` → `None`). State the skip
        // HERE too, on the flag itself, for the same reason the `zst_closure_arg` skip above is
        // stated twice: the linked interpreter must never be handed a body whose instruction
        // stream names a function the assembled module does not contain, and that must not depend
        // on `splice_ok`'s line staying where it is.
        if r.fnptr_adapter {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: module carries a producer-synthesized closure→fn-pointer \
                 adapter (no rustc counterpart, dropped at record); linked interpretation not \
                 asserted (coverage-only)",
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
        // Trust (wave-SC): the `&str`-const leg runs FIRST and per record, because it patches a
        // GLOBAL as well as the placeholder node and must never reach `eval_pending_const`'s
        // scalar/composite shape tripwire (a `&str` type matches none of its arms). Split out so
        // the borrow of `r.globals` is disjoint from the `r.function` patch below.
        for i in 0..r.pending_consts.len() {
            let pc = r.pending_consts[i].clone();
            let Some(gid) = pc.str_global else { continue };
            let Some(bytes) = eval_pending_str_const(tcx, &pc) else {
                bump_unsupported(&mut r.unsupported, "PendingStr(eval failed at finalize)");
                continue;
            };
            // FAIL CLOSED on the empty string, for the same reason `emit_bytes_global` refuses
            // `""`: a zero-length array global is not proven faithful end-to-end. `""` stays a
            // missed clean-rate opportunity rather than a guessed lowering.
            if bytes.is_empty() {
                bump_unsupported(&mut r.unsupported, "PendingStr(empty)");
                continue;
            }
            let Some(g) = r.globals.get_mut(gid.as_usize()) else {
                bump_unsupported(&mut r.unsupported, "PendingStr(global not patched)");
                continue;
            };
            if !patch_str_global(g, &bytes) {
                // The slot is not the untouched `[u8; 0]` placeholder: a desync, or a SECOND
                // record for the same deduped global carrying DIFFERENT bytes — the patch
                // conflict. (An already-patched slot carrying these EXACT bytes — the benign
                // repeated-read case — returns `true` and never reaches here.)
                bump_unsupported(&mut r.unsupported, "PendingStr(global patch conflict)");
                continue;
            }
            if !patch_placeholder(r.function.as_mut(), pc.value, Constant::Int(bytes.len() as i128))
            {
                bump_unsupported(&mut r.unsupported, "PendingConst(placeholder not found)");
            }
        }
        for pc in &r.pending_consts {
            // Trust (wave-SC): the str leg above already handled (and reported on) this record.
            if pc.str_global.is_some() {
                continue;
            }
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
        // Trust (wave-SC): the POSITIVE-LEDGER tripwire for str globals. This is REQUIRED, not
        // belt-and-braces: `global_const_ok` accepts `(Ty::Array(tid, 0), Constant::Array([]))` as
        // internally CONSISTENT (`0 == 0`), so an unpatched placeholder would otherwise splice
        // silently as the EMPTY STRING. The existing `is_const_sentinel` scan above cannot see it
        // — that scan reads instructions, and a global is not an instruction.
        //
        // A LEDGER, not a shape sniff: every `PendingConst` that CLAIMS a str global is checked to
        // have produced a patched one, so a record whose patch was skipped for any reason (missing
        // slot, conflict, an early `continue`) is caught by its own claim.
        check_str_global_ledger(&r.globals, &r.pending_consts, &mut r.unsupported);
    }
}

/// Trust (wave-SC): has `g` been rewritten from the `[u8; 0]` placeholder into a REAL bytes
/// global? Positive predicate: a non-empty `Ty::Array` whose declared length equals its
/// `Constant::Array` initializer's element count. The `*n > 0` clause is the load-bearing one —
/// without it the untouched placeholder `(Array(tid, 0), Array([]))` reads as "patched" and
/// splices as `""`.
fn str_global_patched(g: &Global) -> bool {
    matches!(
        (&g.ty, &g.initializer),
        (Ty::Array(_, n), Some(Constant::Array(elems)))
            if *n > 0 && *n as usize == elems.len()
    )
}

/// Trust (wave-SC): rewrite the `[u8; 0]` placeholder global in place from the const's CTFE bytes.
/// Keeps the placeholder's ELEMENT `TyId` (already interned into the body's `types` table by
/// `lower_str_named_const`), so the patch moves only the declared length and the initializer and
/// can never desync the table.
///
/// Returns `false` (caller fails the body closed) unless the slot is either the UNTOUCHED
/// placeholder — `[u8; 0]`, empty `Constant::Array`, immutable — or already carries EXACTLY these
/// bytes (the benign repeated-read case: one deduped global, several `PendingConst` records).
/// A slot already patched with DIFFERENT bytes is the patch CONFLICT and is refused; so is any
/// other shape. `bytes` must be non-empty (the caller reports `PendingStr(empty)` first).
fn patch_str_global(g: &mut Global, bytes: &[u8]) -> bool {
    if bytes.is_empty() || g.mutable {
        return false;
    }
    let init: Vec<Constant> = bytes.iter().map(|b| Constant::Int(i128::from(*b))).collect();
    match (&g.ty, &g.initializer) {
        // The untouched placeholder.
        (Ty::Array(tid, 0), Some(Constant::Array(elems))) if elems.is_empty() => {
            let tid = *tid;
            g.ty = Ty::Array(tid, bytes.len() as u64);
            g.initializer = Some(Constant::Array(init));
            true
        }
        // Already patched by an earlier record for the SAME deduped const — idempotent iff the
        // bytes agree, a conflict otherwise.
        (Ty::Array(_, n), Some(Constant::Array(elems)))
            if *n as usize == bytes.len() && elems.as_slice() == init.as_slice() =>
        {
            true
        }
        _ => false,
    }
}

/// Trust (wave-SC): the positive-ledger check described at its call site in
/// [`resolve_pending_consts`]. Every `PendingConst` claiming a `str_global` must point at a slot
/// that exists and that [`str_global_patched`] accepts; anything else marks the body unsupported
/// so `splice_ok` refuses it.
fn check_str_global_ledger(
    globals: &[Global],
    pending: &[PendingConst],
    unsupported: &mut Vec<(String, u64)>,
) {
    for pc in pending {
        let Some(gid) = pc.str_global else { continue };
        let patched = globals.get(gid.as_usize()).is_some_and(str_global_patched);
        if !patched {
            bump_unsupported(unsupported, "PendingStr(global not patched)");
        }
    }
}

/// Trust (wave-SC): CTFE the deferred `&str` const to its UTF-8 bytes, at the same reentrancy-safe
/// `analysis` seam and through the same query as [`eval_pending_const`] — `identity_for_item` +
/// region erasure + `const_eval_resolve_for_typeck` — because the producer's gate 4 only deferred
/// all-region, non-`type_const` items. Both preconditions are RE-CHECKED here, not assumed.
///
/// Fail-closed (`None`) on: an mgca type const; non-all-region identity args; a re-derived type
/// that is not a shared `&str` (the shape tripwire, the str twin of `eval_pending_const`'s
/// kind/width check); a resolution/evaluation failure; a valtree that is not a BRANCH (guarding
/// `try_to_raw_bytes`'s internal `to_branch()`, which `bug!`s on a Leaf — valtree.rs:180); or a
/// branch whose elements are not all `u8` leaves (`try_to_raw_bytes` returns `None`).
fn eval_pending_str_const(tcx: TyCtxt<'_>, pc: &PendingConst) -> Option<Vec<u8>> {
    if tcx.is_type_const(pc.def_id) {
        return None;
    }
    let args = ty::GenericArgs::identity_for_item(tcx, pc.def_id);
    if !args.iter().all(|a| a.as_region().is_some()) {
        return None;
    }
    // Shape tripwire: the const's declared type must still be a SHARED `&str`, and the record's
    // scalar flags must be the ones `lower_str_named_const` writes. Same tcx as the hook, so a
    // mismatch is a real bug — fail closed.
    let rty = tcx.type_of(pc.def_id).instantiate_identity().skip_normalization();
    let is_shared_str = matches!(
        rty.kind(),
        ty::Ref(_, pointee, rustc_hir::Mutability::Not) if matches!(pointee.kind(), ty::Str)
    );
    if !is_shared_str
        || pc.composite
        || pc.is_bool
        || pc.is_float
        || pc.signed
        || pc.bits != 64
    {
        return None;
    }
    let uv = ty::AliasConst::new(tcx, ty::AliasConstKind::new_from_def_id(tcx, pc.def_id), args);
    let uv = tcx.erase_and_anonymize_regions(uv);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let valtree = match tcx.const_eval_resolve_for_typeck(typing_env, uv, pc.span) {
        Ok(Ok(v)) => v,
        _ => return None,
    };
    let value = ty::Value { ty: rty, valtree };
    // `try_to_raw_bytes` calls `to_branch()` unconditionally after its type gate; a Leaf valtree
    // under a `&str` type would `bug!` (ICE) rather than return `None`. Refuse it here first.
    value.try_to_branch()?;
    value.try_to_raw_bytes(tcx).map(<[u8]>::to_vec)
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
    /// Trust (wave-EF): register_enum decline reasons (see `BodyRecord::enum_declines`). Empty
    /// unless `TRUST_ENUM_DECLINE_CENSUS=1`; the JSON key is OMITTED when empty, which is what
    /// keeps a default census run byte-identical to a pre-wave-EF one.
    enum_declines: Vec<(String, String)>,
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
    let mut prepared: Vec<(u32, Function, FuncTy, BodyMaps)> = Vec::new();
    for r in records {
        if splice_ok(r, records) {
            if let Some((func, func_ty, maps)) = prepare_body_tables(r, &mut module) {
                assigned.push((r.def_index, FuncId::new(assigned.len() as u32)));
                prepared.push((r.def_index, func, func_ty, maps));
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
            enum_declines: r.enum_declines.clone(),
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
        let Ok(pi) = prepared.binary_search_by_key(&r.def_index, |(d, _, _, _)| *d) else {
            rows.push(row);
            continue;
        };
        let (_, func, func_ty, body_maps) = &prepared[pi];

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
                    Inst::Call { callee, .. } => match resolve_callee(r, *callee, &lookup, body_maps) {
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
                            match resolve_callee(r, *fid, &lookup, body_maps) {
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
    maps: &BodyMaps,
) -> CalleeResolution {
    let idents: Vec<&CalleeRef> = r.callees.iter().filter(|c| c.func_id == callee).collect();
    match idents.as_slice() {
        // Trust (wave-20): a FORCED-HAVOC edge (a generic call site) declares — NEVER links — even
        // when its `DefIndex` has a clean local body. Linking a polymorphic call to the callee's
        // identity-lowered body is an identity lie AND re-opens the wave-19 fat/thin DST hole at a
        // generic site. The distinct `havoc:` key prefix keeps it from coalescing with any real
        // `local:`/`extern:` edge to the same symbol; it counts in the honest can't-resolve bucket.
        [c] if c.force_havoc => CalleeResolution::Decl {
            key: format!("havoc:{}{}", c.def_path, ret_key(c, maps)),
            name: c.def_path.clone(),
            is_extern: false,
            ret: decl_ret(c, maps),
        },
        [c] if c.is_local => match lookup(c.def_index) {
            Some(id) => CalleeResolution::Local(id),
            // A real local fn, but its own body did not lower cleanly — declare, don't link.
            None => CalleeResolution::Decl {
                key: format!("local-unlowered:{}{}", c.def_path, ret_key(c, maps)),
                name: c.def_path.clone(),
                is_extern: false,
                ret: decl_ret(c, maps),
            },
        },
        [c] => CalleeResolution::Decl {
            key: format!("extern:{}{}", c.def_path, ret_key(c, maps)),
            name: c.def_path.clone(),
            is_extern: true,
            ret: decl_ret(c, maps),
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
fn decl_ret(c: &crate::CalleeRef, maps: &BodyMaps) -> Option<Ty> {
    if c.ret_ty_conflict {
        return None;
    }
    // Trust (#184): the recorded type is in the BODY's numbering; a declaration lives in the
    // ASSEMBLED module, so it must be remapped or a `Ty::Struct(sid)` would name a different type.
    // Table-free types remap to themselves, so the previously-shipped scalar lane is unchanged.
    // A `None` here (out-of-range or not-yet-interned id) keeps the honest empty `returns`.
    maps.remap(c.ret_ty.as_ref()?)
}

/// Trust (#178): the declaration dedup-key suffix for a callee's agreed return type. Two call
/// sites that bind different types from one `def_path` must NOT collapse into one declaration —
/// its signature would contradict half of them. Empty for the unknown case, so a callee with no
/// agreed type keeps byte-identical keys to the pre-#178 producer.
fn ret_key(c: &crate::CalleeRef, maps: &BodyMaps) -> String {
    match decl_ret(c, maps) {
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
fn splice_ok(r: &BodyRecord, records: &[BodyRecord]) -> bool {
    if !r.unsupported.is_empty() {
        return false;
    }
    // Trust (totality Batch C): a symbolic body's module carries value-less
    // extern-immutable globals — lowered-for-coverage, never spliced.
    if r.symbolic {
        return false;
    }
    // Trust (union lane): the body's struct table carries a `StructDef` whose lane stands for a
    // `union`'s real bytes while spelling `Ty::Unit`. Refused with its OWN predicate, on ground
    // truth recorded by the producer's ledger — deliberately NOT inferred from the `()` lane type,
    // which is indistinguishable from an honest zero-sized field (104 shipped structs carry honest
    // ones). Two consequences ride on this refusal:
    //   * no such `StructDef` ever enters the assembled executable module, so the unclosed
    //     declared-`size` vs derived-field-`byte_size` layout disagreement cannot be reached
    //     through this lane;
    //   * these bodies carry a FORCED `contains_call` (their NotRun confinement), which makes them
    //     `deferred` — and the crate-seam differential's step 0 requires a spliced entry. Refusing
    //     here is therefore what keeps the seam interpreter away from them. See
    //     `LowerCx::register_union_lane`: the two gates are sound only together.
    if r.union_lane {
        return false;
    }
    // Trust (enum param lane): the body's enum table carries an `EnumDef` one of whose variant
    // fields stands for a caller's `T` — real bytes at the instantiation — while spelling
    // `Ty::Unit`, i.e. claiming zero. Refused with its OWN predicate, on the ground truth the
    // producer's ledger recorded (`matches!(rust_fty.kind(), ty::Param(_))`), and deliberately
    // NOT inferred from the `()` lane spelling: the B3-2c E1 respell mints the SAME `Ty::Unit`
    // for an honest drop-free ZST, and a `Ty`-keyed gate here would refuse the entire wave-EZ
    // `fmt::Result` / `Option<()>` family.
    //
    // Stated as its own line rather than left to `r.symbolic` two lines up — which does refuse
    // every body in this class today, because admitting a lane requires `map_ty` to have walked a
    // bare `ty::Param` and that arm sets `param_opaque`. That is a real wall, but it is a claim
    // about a SIDE EFFECT's ordering, not a decision about placeholder lanes, and this branch has
    // twice paid for a gate that was "safe because something else happens to refuse it".
    //
    // The second consequence is the load-bearing one: these bodies carry a FORCED `contains_call`
    // (their NotRun confinement — see `LowerCx::register_enum_param_lane`), which makes them
    // `deferred`, and the crate-seam differential's step 0 requires a SPLICED entry. Refusing
    // here is therefore what keeps the seam interpreter away from them. The two gates are sound
    // only together; neither may be dropped because the other exists.
    if r.enum_param_lane {
        return false;
    }
    // Trust (wave-ZC): a body that passed a capture-free closure as the ZST
    // `Ty::Unit`/`PhantomData` value. The producer and the oracle agree on that spelling, but
    // the ASSEMBLED module would carry it across a call edge whose callee declares a real
    // closure type, with nothing in the module recording that the two denote the same value.
    // No such callee is spliceable today — a closure-typed param can only be a generic `F`,
    // which goes `ty::Param` → `param_opaque` → `symbolic` → refused two lines up — but that
    // is a wall made of Rust's inability to SPELL a closure type, not a claim of ours. State
    // the refusal here, so filling that absence cannot open the lane silently. Recovering the
    // splice needs a POSITIVE witness (the callee's UNINSTANTIATED declared input at this
    // position is `ty::Param`/`Alias(Opaque)`), not the removal of this line.
    if r.zst_closure_arg {
        return false;
    }
    // Trust (fn-ptr adapter lane): the body's mini-module carried a PRODUCER-SYNTHESIZED
    // closure→fn-pointer adapter, and `record` DROPPED it (`functions.remove(0)` keeps only the
    // body). Splicing the body would put a `Constant::FnDef` into the assembled module naming a
    // function that is not in it.
    //
    // STATED HERE, on the producer's own ledger, rather than left to the two absences that also
    // happen to refuse it today: (a) the adapter's `FuncId` comes from the reserved synthetic band
    // and so has ZERO callee-ledger entries, which the `Constant::FnDef` arm below rejects with
    // its `!= 1` count; and (b) `run_seam_differentials`' step 0 needs a spliced entry. Both are
    // real, but (a) lives inside an arm someone could reasonably widen, and this branch has twice
    // paid for a gate that was "safe because nobody emits that yet". A future minting path for
    // synthetic functions must relax THIS line deliberately, with a second-function carrier, not
    // acquire the splice as a side effect.
    if r.fnptr_adapter {
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
                        // Trust: and the TARGET's own signature must actually be the one this
                        // constant claims — see `fnptr_target_sig_ok`. Sig-resolvability plus a
                        // unique ledger identity (the two checks above) say nothing about arity.
                        if !fnptr_target_sig_ok(r, records, *fid, *sig) {
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

/// Trust (#184): the per-body -> assembled-module id remaps `prepare_body_tables` builds, returned
/// so pass 2 can remap a type it did NOT get from the body's instruction stream — specifically the
/// call-result type recorded on a `CalleeRef`, which types a bodyless declaration's `returns`.
///
/// Without this the declaration lane was confined to TABLE-FREE types, which is the same wall
/// `body_sig_ok` puts on `CallIndirect` signatures and reified fn-pointer constants
/// (`params.chain(returns).all(ty_table_free)`); those are re-interned from the RAW body table with
/// no remap, which is sound ONLY because of that requirement. Handing the maps out lifts the wall
/// for all three consumers rather than just one.
#[derive(Clone, Default)]
struct BodyMaps {
    enum_map: Vec<Option<EnumId>>,
    struct_map: Vec<Option<StructId>>,
    ty_map: Vec<TyId>,
    closure_map: Vec<trust_ir::ClosureTyId>,
}

impl BodyMaps {
    /// Remap a BODY-numbered `Ty` into the assembled module's numbering. `None` (fail-closed) for
    /// an out-of-range id, a not-yet-interned def, or a variant `remap_ty` does not model.
    fn remap(&self, ty: &Ty) -> Option<Ty> {
        remap_ty(ty, &self.enum_map, &self.struct_map, &self.ty_map, &self.closure_map)
    }
}

fn prepare_body_tables(
    r: &BodyRecord,
    module: &mut Module,
) -> Option<(Function, FuncTy, BodyMaps)> {
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
        return Some((f, func_ty.clone(), BodyMaps::default()));
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
    Some((f, ft, BodyMaps { enum_map, struct_map, ty_map, closure_map }))
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
/// signature fails here and the pass-2 re-interning never needs to recurse.
///
/// TABLE-FREEDOM IS THIS GATE'S OWN REQUIREMENT, not a restatement of the producer's. Pass 2
/// re-interns the resolved `FuncTy` VERBATIM (`assemble`'s `Inst::CallIndirect` / `Inst::Const`
/// arms call `intern_func_ty` with no `remap_ty`), so a per-body `StructId`/`EnumId`/`TyId` carried
/// through would dangle against the assembled tables. The producer's `map_fn_ptr_ty` enforces only
/// the HIGHER-ORDER bound, and since `ty_contains_func_resolved` it deliberately admits
/// struct/enum-bearing signatures (the `fn() -> Name` shape behind the `LazyLock` statics) that
/// this gate then refuses — a `lowered`-only admission. See
/// `test_every_newly_admitted_component_is_still_refused_by_the_splice_predicate`: the two halves
/// are consistent precisely because every signature that widening newly admits fails
/// `ty_table_free`.
fn body_sig_ok(r: &BodyRecord, sig: FuncTyId) -> bool {
    match r.func_types.get(sig.as_usize()) {
        Some(ft) => !ft.is_vararg && ft.params.iter().chain(ft.returns.iter()).all(ty_table_free),
        None => false,
    }
}

/// Trust: does the TARGET of a fn-pointer constant `Inst::Const { ty: Ty::Func(sig), value:
/// Constant::FnDef(fid) }` actually carry the signature `sig` claims for it?
///
/// WHY THIS EXISTS. `body_sig_ok` proves `sig` RESOLVES and the ledger-uniqueness check proves
/// `fid` names ONE identity — neither says anything about the target's arity, and trust-ir's own
/// validator does not either (`shape.rs` `shape_matches_ty` is `(FnDef(_), Ty::Func(_)) => true`,
/// unconditionally). Today's only emitter, the `ReifyFnPointer` arm, is arity-exact by
/// construction (`resolve_reify_target` + `map_fn_ptr_ty` both read the SAME rustc fn signature),
/// so the hole has never been hit — i.e. the gate was "safe because nobody emits a bad `FnDef`
/// yet", which is an absence, not a predicate. The concrete program the absence was hiding: a
/// `ClosureFnPointer` coercion lowered as `Constant::FnDef(closure_body)` would be arity `N+1`
/// against an arity-`N` `Ty::Func`, because this producer signs every closure body
/// `[env, declared…]` (`lower_fn` prepends `closure_env_param_ty`; `signs_closure_env_slot`).
/// That is a silently wrong program at any indirect call through the pointer.
///
/// THE PREDICATE, and why the two admitting branches are not themselves absences:
///   * ONE ledger identity, never a FORCED-HAVOC edge. A havoc edge exists precisely to declare
///     an unconstrained target (`resolve_callee`'s `havoc:` key); taking its ADDRESS at a
///     concrete `Ty::Func` would claim the signature the havoc refuses to commit to.
///   * A LOCAL target with a record in this crate is the linkable case: compare its
///     producer-signed `func_ty` to `sig` STRUCTURALLY and refuse on any mismatch, on a record
///     with no signature at all, and on a target signature that is not table-free (the two sides
///     are numbered in DIFFERENT per-body tables, so only table-free types compare meaningfully;
///     `body_sig_ok` already forces the `sig` side).
///   * A target with NO record in this crate (cross-crate, or a local `DefIndex` this crate never
///     recorded) cannot be linked at all: pass 2's `resolve_callee` sends it to `decl_id`, and a
///     declaration is minted with the unknown-PARAMS encoding `FuncTy { params: [], is_vararg:
///     true, .. }` (~:3034) — this file's own minting, not an outside guarantee — so no ARITY is
///     asserted and there is nothing for `sig`'s param list to contradict.
///
/// WHAT THAT ARGUMENT DOES **NOT** COVER — stated because the same minting block asserts the other
/// half. `returns` is NOT unknown-encoded: ~:3035 fills it from `decl_ret(c, maps)`, so a declaration
/// whose call sites agreed on a table-free result type carries a POSITIVE return claim, and the two
/// admitting branches above do not compare it against `claimed.returns`. The return side of the
/// mismatch class therefore stays open on those branches; only the local-with-a-record branch
/// compares both halves (`target == claimed`). It is left open deliberately: `decl_ret` is the type
/// the CALL SITES agreed on (`ret_ty`, cleared to `None` on `ret_ty_conflict`), not the target's own
/// signature, so a disagreement with `claimed.returns` is not by itself evidence of a wrong program
/// — and refusing on it would add a second refusal whose splice-rate cost is as unmeasured as the
/// one below. The hole this predicate is here to close is the ARITY hole; the residual is named
/// rather than papered over.
///
/// SPLICE-RATE DELTA: UNMEASURED, pending a trustc rebuild + corpus run — and it could go either
/// way, so no "strengthening only" claim is made here. The specific branch that makes the optimistic
/// reading unsafe is `func_ty: None` (~:4062): a reify of a LOCAL fn whose own body did not lower
/// has no producer-signed signature to compare, and this predicate refuses it, which un-splices the
/// CALLER. Before this check that caller spliced and the edge simply became a `local-unlowered:`
/// declaration. `c.force_havoc` refuses a second previously-splicing shape for the same reason.
fn fnptr_target_sig_ok(r: &BodyRecord, records: &[BodyRecord], fid: FuncId, sig: FuncTyId) -> bool {
    let Some(claimed) = r.func_types.get(sig.as_usize()) else {
        return false;
    };
    let idents: Vec<&CalleeRef> = r.callees.iter().filter(|c| c.func_id == fid).collect();
    let [c] = idents.as_slice() else {
        return false;
    };
    if c.force_havoc {
        return false;
    }
    if !c.is_local {
        return true;
    }
    let Ok(i) = records.binary_search_by_key(&c.def_index, |t| t.def_index) else {
        // No record for this local `DefIndex` ⇒ `lookup` misses in pass 2 ⇒ bodyless
        // `local-unlowered:` declaration ⇒ no arity claim to contradict.
        return true;
    };
    let Some(target) = &records[i].func_ty else {
        return false;
    };
    if target.is_vararg || !target.params.iter().chain(target.returns.iter()).all(ty_table_free) {
        return false;
    }
    target == claimed
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
        // Trust (wave-EF): the register_enum decline reasons — `[["path", "reason"], ...]`.
        // OMITTED ENTIRELY when empty (i.e. always, unless `TRUST_ENUM_DECLINE_CENSUS=1`), so a
        // default census run is byte-identical to a pre-wave-EF one and old dumps stay diffable.
        // This is a measurement key: it never appears in `unsupported` and never moves `lowered`.
        let enum_declines = if r.enum_declines.is_empty() {
            String::new()
        } else {
            let rows = r
                .enum_declines
                .iter()
                .map(|(path, reason)| {
                    format!("[\"{}\", \"{}\"]", json_escape(path), json_escape(reason))
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!(" \"enum_declines\": [{rows}],")
        };
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
             \"unsupported_details\": {{{}}},{} \
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
            enum_declines,
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

/// Trust (tranche 4): the census detail-cap channel. Pure, TyCtxt-free, no process env touched
/// (see [`parse_detail_cap`] for why the parse is split from the `OnceLock` read).
#[cfg(test)]
mod detail_cap_tests {
    use super::*;
    use std::ffi::OsStr;

    /// The literal pre-tranche loop, kept verbatim as the byte-stability oracle.
    fn pre_tranche_loop(unsupported: &[(String, &'static str)]) -> Vec<(String, Vec<String>)> {
        let mut details_by_tag: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (detail, what) in unsupported {
            let ex: String = detail.chars().take(120).collect();
            let examples = details_by_tag.entry((*what).to_string()).or_default();
            if examples.len() < 3 && !examples.contains(&ex) {
                examples.push(ex);
            }
        }
        details_by_tag.into_iter().collect()
    }

    fn fixture() -> Vec<(String, &'static str)> {
        // One tag with FIVE distinct details (the truncated case the census hit 4,516 times),
        // a second tag interleaved (tag ordering must not depend on encounter order), and a
        // duplicate detail (dedup must survive the lift).
        let ctor: &'static str = "EnumCtor(unsupported payload)";
        let borrow: &'static str = "Borrow(non-local place)";
        vec![
            ("flat/db.rs:376:13".to_string(), ctor),
            ("flat/db.rs:1:1".to_string(), borrow),
            ("flat/db.rs:377:13".to_string(), ctor),
            ("flat/db.rs:378:13".to_string(), ctor),
            ("flat/db.rs:377:13".to_string(), ctor),
            ("flat/db.rs:379:13".to_string(), ctor),
            ("flat/db.rs:380:13".to_string(), ctor),
        ]
    }

    #[test]
    fn test_parse_detail_cap_absent_or_garbage_returns_the_shipped_default() {
        let default = DetailCap::Limited(DETAIL_CAP_DEFAULT);
        assert_eq!(parse_detail_cap(None), default, "absent must not move the artifact");
        for garbage in ["", " ", "three", "-1", "3.5", "0x0", "4294967296", "1e3"] {
            assert_eq!(
                parse_detail_cap(Some(OsStr::new(garbage))),
                default,
                "a typo ({garbage:?}) must fall back to the default, never to unbounded"
            );
        }
        // Non-UTF-8 takes the same path (`to_str` yields None) — asserted on the platform that
        // can spell it; on others the `to_str` arm is already covered by the strings above.
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            assert_eq!(parse_detail_cap(Some(OsStr::from_bytes(&[0xff, 0xfe]))), default);
        }
    }

    #[test]
    fn test_parse_detail_cap_zero_is_unbounded_and_n_is_limited_n() {
        assert_eq!(parse_detail_cap(Some(OsStr::new("0"))), DetailCap::Unbounded);
        assert_eq!(parse_detail_cap(Some(OsStr::new(" 0 "))), DetailCap::Unbounded);
        assert_eq!(parse_detail_cap(Some(OsStr::new("1"))), DetailCap::Limited(1));
        assert_eq!(parse_detail_cap(Some(OsStr::new("3"))), DetailCap::Limited(3));
        assert_eq!(
            parse_detail_cap(Some(OsStr::new("4294967295"))),
            DetailCap::Limited(4_294_967_295)
        );
    }

    #[test]
    fn test_detail_cap_admits_counts_strictly_below_the_limit() {
        assert!(DetailCap::Limited(3).admits(2));
        assert!(!DetailCap::Limited(3).admits(3));
        assert!(!DetailCap::Limited(0).admits(0), "Limited(0) records nothing");
        assert!(DetailCap::Unbounded.admits(usize::MAX));
    }

    #[test]
    fn default_cap_reproduces_the_pre_tranche_loop() {
        let input = fixture();
        assert_eq!(
            aggregate_detail_examples(&input, parse_detail_cap(None)),
            pre_tranche_loop(&input),
            "the DEFAULT census artifact must stay byte-identical to the pre-tranche one"
        );
    }

    #[test]
    fn test_aggregate_detail_examples_cap_zero_keeps_every_distinct_example() {
        let input = fixture();
        let capped = aggregate_detail_examples(&input, parse_detail_cap(None));
        let lifted = aggregate_detail_examples(&input, parse_detail_cap(Some(OsStr::new("0"))));

        // Tag order is BTreeMap order in both, independent of encounter order.
        let tags: Vec<&str> = lifted.iter().map(|(t, _)| t.as_str()).collect();
        assert_eq!(tags, vec!["Borrow(non-local place)", "EnumCtor(unsupported payload)"]);

        let capped_examples = &capped[1].1;
        let lifted_examples = &lifted[1].1;
        assert_eq!(capped_examples.len(), 3, "the default truncates — this is the 58% loss");
        assert_eq!(lifted_examples.len(), 5, "cap 0 recovers every DISTINCT example");
        // The repeated 377:13 detail is one example under BOTH caps: the lift changes the
        // budget, never the dedup.
        assert_eq!(lifted_examples.iter().filter(|e| e.ends_with("377:13")).count(), 1);
        // The default's examples are a PREFIX of the lifted ones (first-encounter order).
        assert_eq!(&lifted_examples[..3], &capped_examples[..]);
    }

    #[test]
    fn test_aggregate_detail_examples_truncates_at_the_char_budget_under_every_cap() {
        // Multi-byte chars: a byte-wise truncation would panic or split a char here.
        let long: String = "é".repeat(200);
        let input = vec![(long.clone(), "Ty")];
        for cap in [parse_detail_cap(None), DetailCap::Unbounded, DetailCap::Limited(9)] {
            let out = aggregate_detail_examples(&input, cap);
            assert_eq!(out[0].1[0].chars().count(), DETAIL_CHARS_MAX);
            assert!(long.starts_with(&out[0].1[0]));
        }
        // Two details sharing the 120-char prefix stay ONE example (dedup is post-truncation),
        // under the lifted cap too — pinned because the lift is the only thing that could have
        // exposed the second copy.
        let shared = vec![(format!("{long}A"), "Ty"), (format!("{long}B"), "Ty")];
        assert_eq!(aggregate_detail_examples(&shared, DetailCap::Unbounded)[0].1.len(), 1);
    }

    #[test]
    fn test_aggregate_detail_examples_empty_input_yields_no_rows() {
        assert!(aggregate_detail_examples(&[], DetailCap::Unbounded).is_empty());
    }
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
            enum_declines: Vec::new(),
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
            union_lane: false,
            enum_param_lane: false,
            def_path: fn_name.to_string(),
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
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
            enum_declines: Vec::new(),
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

    /// Trust (union lane) SPLICE REFUSAL, PINNED. A record that is spliceable in every other
    /// respect stops being spliceable the moment it reports a union placeholder lane — and the
    /// refusal keys on that flag alone, never on a `()` field type (which is indistinguishable
    /// from an honest zero-sized field; 104 shipped structs carry honest ones).
    ///
    /// The negative half is what makes the gate non-vacuous, and the positive half is what keeps
    /// the forced-`contains_call` confinement honest: these bodies are `deferred`, and the
    /// crate-seam differential's step 0 requires a SPLICED entry, so this refusal is the thing
    /// that keeps the seam interpreter away from them.
    #[test]
    fn union_lane_record_is_refused_by_the_splice() {
        let clean = lineage_body_record(1, "probe::clean");
        let records = vec![clean];
        assert!(
            splice_ok(&records[0], &records),
            "the minimal mini-module must splice — otherwise the union-lane half proves nothing"
        );

        let mut tainted = lineage_body_record(1, "probe::union_lane");
        tainted.union_lane = true;
        let tainted_records = vec![tainted];
        assert!(
            !splice_ok(&tainted_records[0], &tainted_records),
            "a body carrying a union placeholder lane must never enter the executable module"
        );
    }

    /// Trust (enum param lane) SPLICE REFUSAL, PINNED — and it is OURS.
    ///
    /// The negative half is what makes the gate non-vacuous: the SAME record with the flag
    /// cleared splices, and with `symbolic` ALSO false, so the only difference between the two
    /// verdicts is `enum_param_lane`. That matters here more than for most flags, because
    /// `symbolic` does refuse every body in this class today (admitting a lane requires `map_ty`
    /// to have walked a bare `ty::Param`, whose arm sets `param_opaque`) — a fact about a side
    /// effect's ordering, not a decision about placeholder lanes.
    ///
    /// The positive half is the load-bearing one: these bodies carry a FORCED `contains_call`,
    /// which makes them `deferred`, and `run_seam_differentials`' step 0 requires a SPLICED
    /// entry. This refusal is therefore what keeps the crate-seam interpreter away from them.
    /// Delete it and the forcing alone would route them INTO the seam.
    #[test]
    fn enum_param_lane_record_is_refused_by_the_splice() {
        let clean = vec![lineage_body_record(1, "probe::clean")];
        assert!(
            splice_ok(&clean[0], &clean),
            "the minimal mini-module must splice — otherwise the param-lane half proves nothing"
        );

        let mut tainted = lineage_body_record(1, "probe::enum_param_lane");
        tainted.enum_param_lane = true;
        // Deliberately NOT symbolic: the refusal must be this flag's, not inherited.
        assert!(!tainted.symbolic, "the fixture must isolate `enum_param_lane` from `symbolic`");
        let tainted_records = vec![tainted];
        assert!(
            !splice_ok(&tainted_records[0], &tainted_records),
            "a body carrying an enum param placeholder lane must never enter the executable \
             module — an `EnumDef` lane claiming zero bytes for a caller's `T`"
        );
    }

    /// A `Lowered` in the exact posture a param-lane body reaches the seams in: CLEAN (no
    /// unsupported shapes, no pending consts), no `Inst::Call` of its own, ledger non-empty.
    /// `contains_call` is COMPUTED by the production expression, never written down — that is
    /// what makes the test below a test of the forcing rather than of a fixture.
    fn param_lane_probe_lowered(
        body_emitted_a_call: bool,
        ledger_nonempty: bool,
    ) -> crate::Lowered {
        crate::Lowered {
            module: Module::new("param_lane_confinement_probe"),
            body_kind: BodyKind::Fn,
            opaque_collapse: ledger_nonempty,
            enum_declines: Vec::new(),
            union_lane: false,
            enum_param_lane: ledger_nonempty,
            // The class IS symbolic in fact; carried so the assertion below that the differential
            // is unmoved by it is made against the real posture, not a stripped one.
            symbolic: ledger_nonempty,
            unsupported: Vec::new(),
            contains_call: crate::param_lane_forces_not_interpretable(
                body_emitted_a_call,
                ledger_nonempty,
            ),
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
            thin_reborrow: false,
            callees: Vec::new(),
            pending_consts: Vec::new(),
        }
    }

    /// Trust (enum param lane) — THE CONFINEMENT, PINNED END TO END. **This test fails if the
    /// forced `contains_call` is removed.**
    ///
    /// The previous cut of this lane shipped without the forcing, on the argument that
    /// "`symbolic` already carries the differential refusal". It does not:
    /// [`crate::differential::compare`] never reads `symbolic`, and its only structural skip is
    /// [`crate::differential::contains_call_forces_not_run`]. A clean, call-free param-lane body
    /// would have been INTERPRETED, with both sides spelling the caller's `T` as a zero-byte
    /// `Unit` and reporting agreement about a function neither modelled.
    ///
    /// The three assertions are the three legs, in order:
    ///  1. a non-empty ledger forces the flag even though the body emitted NO call — remove the
    ///     forcing and this is the assertion that goes red;
    ///  2. with the flag set, the DIRECT differential skips the body — and the same probe with
    ///     `symbolic: true` but the flag CLEAR does not, which is the falsified claim, executed;
    ///  3. the flag makes the body `deferred_to_seam`, so the seam interpreter would take it —
    ///     and only the splice refusal closes that half. Requirements 3 and 4 are sound together
    ///     or not at all.
    #[test]
    fn enum_param_lane_forced_contains_call_routes_the_body_away_from_both_differentials() {
        // (1) The forcing itself, at the production expression.
        let probe = param_lane_probe_lowered(/* body_emitted_a_call */ false, true);
        assert!(
            probe.contains_call,
            "a non-empty param-lane ledger must FORCE `contains_call` even though the body \
             emitted no call — this is the correction the reverted cut omitted"
        );

        // (2) That flag, and nothing else on `Lowered`, is what the direct differential skips on.
        assert!(
            crate::differential::contains_call_forces_not_run(&probe),
            "the direct interpretation differential must skip a param-lane body"
        );
        let symbolic_only = crate::Lowered {
            symbolic: true,
            contains_call: false,
            enum_param_lane: true,
            ..param_lane_probe_lowered(false, false)
        };
        assert!(
            !crate::differential::contains_call_forces_not_run(&symbolic_only),
            "`symbolic` alone does NOT route a body away from the direct differential — the \
             falsified confinement argument, executed rather than argued"
        );

        // (3) The forcing defers the body to the crate-finalize seam, whose step 0 needs a
        //     SPLICED entry — which `splice_ok` refuses. The two gates close the loop together.
        assert!(
            crate::differential::deferred_to_seam(&probe),
            "a clean body with the forced flag is deferred — so the splice refusal is required"
        );
        let mut rec = lineage_body_record(1, "probe::enum_param_lane_seam");
        rec.enum_param_lane = true;
        rec.deferred = true;
        let records = vec![rec];
        assert!(
            !splice_ok(&records[0], &records),
            "the seam interpreter reaches only SPLICED entries; refusing the splice is what \
             keeps the deferred param-lane body away from it"
        );

        // Control: an empty ledger forces nothing, so a body that meets no param lane keeps its
        // own `contains_call` and its own differential verdict, exactly as before this change.
        let untouched = param_lane_probe_lowered(false, false);
        assert!(!untouched.contains_call, "the forcing must be keyed on the ledger, not blanket");
        assert!(!crate::differential::contains_call_forces_not_run(&untouched));
        assert!(param_lane_probe_lowered(true, false).contains_call, "a real call still counts");
    }

    /// Trust (wave-ZC): the ZST-closure-arg splice refusal is OURS, not a side effect of the
    /// `ty::Param` → `symbolic` wall that also happens to stop these bodies today. The
    /// positive half is what makes this a test of the predicate rather than of the fixture:
    /// the SAME record with the flag cleared splices, so the only difference between the two
    /// verdicts is the flag. If a closure-typed callee param ever becomes spliceable —
    /// filling the absence the old wall was made of — this test still fails the body closed.
    #[test]
    fn test_splice_refuses_a_zst_closure_arg_body_on_its_own_predicate() {
        let clean = vec![lineage_body_record(1, "probe::minimal")];
        assert!(
            splice_ok(&clean[0], &clean),
            "the minimal record must be spliceable, or the refusal below proves nothing"
        );
        let mut flagged = lineage_body_record(1, "probe::zst_closure_arg");
        flagged.zst_closure_arg = true;
        let flagged_records = vec![flagged];
        assert!(
            !splice_ok(&flagged_records[0], &flagged_records),
            "a body carrying a ZST closure call argument must be refused by `splice_ok`'s own \
             predicate, independently of `symbolic` or of any table check"
        );
    }

    /// Trust (fn-ptr adapter lane): the SPLICE refusal is OURS, on the producer's ledger, not a
    /// side effect of the adapter's `FuncId` happening to carry zero callee-ledger entries (which
    /// the `Constant::FnDef` arm would also reject) or of the seam's step-0 spliced-entry demand.
    /// The positive half is what makes it a test of the predicate rather than of the fixture: the
    /// SAME record with the flag cleared splices, so the flag is the only difference.
    #[test]
    fn test_splice_refuses_an_fnptr_adapter_body_on_its_own_predicate() {
        let clean = vec![lineage_body_record(1, "probe::minimal")];
        assert!(
            splice_ok(&clean[0], &clean),
            "the minimal record must be spliceable, or the refusal below proves nothing"
        );
        let mut flagged = lineage_body_record(1, "probe::fnptr_adapter");
        flagged.fnptr_adapter = true;
        let flagged_records = vec![flagged];
        assert!(
            !splice_ok(&flagged_records[0], &flagged_records),
            "a body whose mini-module carried a producer-synthesized adapter must be refused by \
             `splice_ok`'s own predicate: `record` DROPPED that adapter, so splicing would put a \
             `Constant::FnDef` into the assembled module naming a function that is not in it"
        );
    }

    /// Trust (fn-ptr adapter lane) THE WHOLE CLAIM OF THE LANE, ASSEMBLED. A body carrying a
    /// synthesized adapter counts as `lowered` and is NEVER `spliced` — coverage moves, the
    /// executable module does not, and no trust claim is made.
    ///
    /// `lowered` is `r.function.is_some() && r.unsupported.is_empty()`, computed from the
    /// BodyRecord that `record` built by taking `functions[0]`; the adapter sat at index 1 and was
    /// dropped there. `lineage` is `None` for exactly the same reason the flip refuses (the digest
    /// needs a single-function module), and that must NOT move `lowered` — a null lineage is an
    /// attestation absence, not a lowering failure.
    #[test]
    fn test_fnptr_adapter_body_is_lowered_but_never_spliced() {
        let mut r = lineage_body_record(1, "probe::adapter_bearing");
        r.fnptr_adapter = true;
        // What `record` would have recorded for such a body: the adapter never reaches the
        // BodyRecord (single-function channel), and the digest refused the two-function module.
        r.lineage = None;
        let assembled = assemble("fnptr_adapter_probe", &[r]);
        assert_eq!(assembled.lowered, 1, "the body itself lowered clean and must be counted");
        assert_eq!(assembled.spliced, 0, "and it must contribute nothing to the executable module");
        assert!(
            assembled.module.functions.is_empty(),
            "no function from an adapter-bearing body may enter the assembled module"
        );
        let row = &assembled.coverage_rows[0];
        assert!(row.lowered && !row.spliced);
        assert!(row.func_id.is_none(), "an un-spliced row addresses no assembled function");
        assert!(row.lineage.is_none(), "and it carries no attestation digest");
    }

    /// Trust (fn-ptr adapter lane) ARITY HONESTY, ON THE GATE'S OWN TERMS. The adapter exists
    /// precisely so the reified constant does not lie about its target's signature, and the
    /// measure of that is `fnptr_target_sig_ok` — the gate written to refuse the naive fix.
    ///
    /// Both halves are asserted against the SAME caller and the SAME claimed `Ty::Func`:
    ///   * a target signed `[f64, f64] -> f64` — the adapter, whose `Function::ty` IS the coerced
    ///     fn pointer's own `FuncTyId` — PASSES;
    ///   * a target signed `[Ptr, f64, f64] -> f64` — the closure BODY, with the env slot
    ///     `lower_fn` prepends — is REFUSED.
    /// The gate is untouched by this lane; if a future edit ever made the closure-body row pass,
    /// the adapter would have stopped being the thing that earns the constant.
    #[test]
    fn test_fnptr_adapter_signature_is_what_the_target_gate_accepts() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let adapter_shaped = vec![target_with_sig(42, vec![Ty::F64, Ty::F64])];
        assert!(
            fnptr_target_sig_ok(&caller, &adapter_shaped, FuncId::new(42), FuncTyId::new(1)),
            "the adapter's signature IS the coerced fn pointer's signature and must satisfy the \
             gate on its own terms"
        );
        let closure_body_shaped = vec![target_with_sig(42, vec![Ty::Ptr, Ty::F64, Ty::F64])];
        assert!(
            !fnptr_target_sig_ok(&caller, &closure_body_shaped, FuncId::new(42), FuncTyId::new(1)),
            "the closure body it wraps must still be refused — that refusal is the reason the \
             adapter is minted at all"
        );
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

    fn probe_def_id(index: u32) -> DefId {
        DefId { krate: LOCAL_CRATE, index: rustc_span::def_id::DefIndex::from_u32(index) }
    }

    /// A ledger entry for `fid`, pointing at `def_index` in (or out of) this crate.
    fn probe_callee(fid: u32, is_local: bool, force_havoc: bool) -> CalleeRef {
        CalleeRef {
            func_id: FuncId::new(fid),
            is_local,
            def_index: fid,
            def_id: probe_def_id(fid),
            def_path: format!("probe::target{fid}"),
            force_havoc,
            site_def_id: probe_def_id(fid),
            site_args: None,
            ret_ty: None,
            ret_ty_conflict: false,
        }
    }

    /// A caller record carrying ONE fn-pointer constant: `Ty::Func(FuncTyId(1))` over
    /// `fn(f64, f64) -> f64`, targeting `FuncId(fid)` with the given ledger entry.
    fn fnptr_caller(callee: CalleeRef) -> BodyRecord {
        let mut r = lineage_body_record(1, "probe::caller");
        r.func_types = vec![
            FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false },
            FuncTy { params: vec![Ty::F64, Ty::F64], returns: vec![Ty::F64], is_vararg: false },
        ];
        r.callees = vec![callee];
        r
    }

    fn target_with_sig(def_index: u32, params: Vec<Ty>) -> BodyRecord {
        let mut t = lineage_body_record(def_index, "probe::target");
        t.func_ty = Some(FuncTy { params, returns: vec![Ty::F64], is_vararg: false });
        t
    }

    /// THE ARITY HOLE, closed by its own predicate. A `Constant::FnDef` naming a CLOSURE body
    /// claims the coercion's `fn(f64, f64) -> f64` while the producer signs that body
    /// `[env, f64, f64] -> f64` (`lower_fn` prepends `closure_env_param_ty`). Sig-resolvability
    /// (`body_sig_ok`) and ledger uniqueness both hold for it, and trust-ir's own
    /// `shape_matches_ty` is `(FnDef(_), Ty::Func(_)) => true` unconditionally — so before this
    /// check the only thing stopping the miscompile was that nobody emitted it yet.
    #[test]
    fn test_fnptr_target_sig_refuses_closure_env_arity_mismatch() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let records = vec![target_with_sig(42, vec![Ty::Ptr, Ty::F64, Ty::F64])];
        assert!(body_sig_ok(&caller, FuncTyId::new(1)), "the claimed sig itself resolves");
        assert!(
            !fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)),
            "an env-slot body must never satisfy the arity-N fn-pointer sig claiming it"
        );
    }

    /// The exact-match case still admits — the check is not a ban on `Constant::FnDef` (this is the
    /// shape today's `ReifyFnPointer` lane produces). It does NOT follow that nothing that spliced
    /// before is refused now: see the UNMEASURED splice-rate note on `fnptr_target_sig_ok`, and
    /// `test_fnptr_target_sig_refuses_signature_less_local_target` for the branch that makes the
    /// delta genuinely unknown.
    #[test]
    fn test_fnptr_target_sig_admits_exact_signature_match() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let records = vec![target_with_sig(42, vec![Ty::F64, Ty::F64])];
        assert!(fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)));
    }

    /// THE JOINT-CHANGE LEMMA, pinned on THIS side of the boundary.
    ///
    /// `crate::ty_contains_func_resolved` widened `map_fn_ptr_ty` to admit a fn-pointer signature
    /// whose params/returns carry a `Ty::Struct`/`Ty::Enum` (the 611 `LazyLock` `fn() -> Name`
    /// statics). This gate was NOT widened with it, and must not be: pass 2 re-interns a
    /// `CallIndirect { sig }` / `Const { ty: Ty::Func(sig) }` id VERBATIM out of
    /// `BodyRecord::func_types` (`assemble`, the `Inst::CallIndirect` / `Inst::Const` arms) with no
    /// `remap_ty` in sight, so a per-body `StructId`/`EnumId` moved that way would dangle against
    /// the assembled tables.
    ///
    /// The two halves are consistent because of an EXACT relationship, asserted here rather than
    /// argued: a signature the widening newly admits necessarily contains a `Ty::Struct` or a
    /// `Ty::Enum` — otherwise the table-free `ty_contains_func` would already have admitted it —
    /// and `ty_table_free` rejects both, at top level and nested inside a `Ty::Tuple`. So every
    /// newly-lowered body carrying such a signature is refused HERE, by this gate's own predicate,
    /// keyed on the property pass 2 actually needs. Net: `lowered` moves, `spliced` cannot.
    #[test]
    fn test_every_newly_admitted_component_is_still_refused_by_the_splice_predicate() {
        let structs = [trust_ir::StructDef {
            id: StructId::new(0),
            name: "Name".into(),
            fields: vec![trust_ir::FieldDef { name: "k".into(), ty: Ty::U64, offset: None }],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
        }];
        let enums = [trust_ir::EnumDef::new(
            trust_ir::EnumId::new(0),
            "K",
            vec![trust_ir::EnumVariant {
                name: "A".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            }],
        )];
        for newly_admitted in [
            Ty::Struct(StructId::new(0)),
            Ty::Enum(trust_ir::EnumId::new(0)),
            Ty::Tuple(vec![Ty::U64, Ty::Struct(StructId::new(0))]),
            Ty::Tuple(vec![Ty::Enum(trust_ir::EnumId::new(0))]),
        ] {
            assert!(
                crate::ty_contains_func(&newly_admitted),
                "{newly_admitted:?} is refused by the table-free wall (so it IS newly admitted)"
            );
            assert!(
                !crate::ty_contains_func_resolved(&newly_admitted, &structs, &enums),
                "{newly_admitted:?} is admitted once the tables answer"
            );
            assert!(
                !ty_table_free(&newly_admitted),
                "{newly_admitted:?} must still be refused by the splice's own predicate"
            );
        }
        // Stated as the gate, not only as the predicate: a body whose indirect-call signature
        // carries the widened shape does not splice.
        let mut r = lineage_body_record(1, "probe::struct_bearing_sig");
        r.func_types = vec![
            FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false },
            FuncTy {
                params: Vec::new(),
                returns: vec![Ty::Struct(StructId::new(0))],
                is_vararg: false,
            },
        ];
        assert!(
            !body_sig_ok(&r, FuncTyId::new(1)),
            "`fn() -> Name` resolves, and is still not MOVABLE — that is the whole distinction"
        );
    }

    /// A return-type disagreement is the same defect on the other side of the arrow.
    #[test]
    fn test_fnptr_target_sig_refuses_return_mismatch() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let mut target = target_with_sig(42, vec![Ty::F64, Ty::F64]);
        target.func_ty =
            Some(FuncTy { params: vec![Ty::F64, Ty::F64], returns: Vec::new(), is_vararg: false });
        let records = vec![target];
        assert!(!fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)));
    }

    /// A FORCED-HAVOC edge exists to declare a target whose signature we refuse to commit to;
    /// taking its address at a concrete `Ty::Func` would commit to it anyway.
    #[test]
    fn test_fnptr_target_sig_refuses_forced_havoc_edge() {
        let caller = fnptr_caller(probe_callee(42, true, true));
        let records = vec![target_with_sig(42, vec![Ty::F64, Ty::F64])];
        assert!(
            !fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)),
            "a havoc edge must not be given a concrete signature by its address site"
        );
    }

    /// A target with no record in this crate (cross-crate, or a local `DefIndex` never recorded)
    /// cannot be LINKED: pass 2 mints a bodyless declaration with the unknown-PARAMS encoding
    /// (`is_vararg: true`, empty `params`), so no ARITY is asserted and there is nothing for the
    /// claimed sig's param list to contradict. Admitting here is a decision about THIS file's decl
    /// minting, not a bet on an absence. It is a decision about the PARAMS half only: the same
    /// minting fills `returns` from `decl_ret(c, maps)`, which these branches do not compare — the named
    /// residual on `fnptr_target_sig_ok`.
    #[test]
    fn test_fnptr_target_sig_admits_targets_that_can_only_become_declarations() {
        // Cross-crate: even with a same-`DefIndex` LOCAL record present, `is_local == false`
        // routes to an `extern:` declaration, so the local record is not the target.
        let extern_caller = fnptr_caller(probe_callee(42, false, false));
        let records = vec![target_with_sig(42, vec![Ty::Ptr, Ty::F64, Ty::F64])];
        assert!(fnptr_target_sig_ok(&extern_caller, &records, FuncId::new(42), FuncTyId::new(1)));

        // Local `DefIndex` this crate never recorded: `lookup` misses ⇒ `local-unlowered:` decl.
        let local_caller = fnptr_caller(probe_callee(42, true, false));
        assert!(fnptr_target_sig_ok(&local_caller, &[], FuncId::new(42), FuncTyId::new(1)));
    }

    /// No ledger entry, or two behind one DefIndex-derived `FuncId`: refuse rather than pick.
    #[test]
    fn test_fnptr_target_sig_refuses_zero_or_ambiguous_ledger_identity() {
        let records = vec![target_with_sig(42, vec![Ty::F64, Ty::F64])];

        let mut none = fnptr_caller(probe_callee(42, true, false));
        none.callees.clear();
        assert!(!fnptr_target_sig_ok(&none, &records, FuncId::new(42), FuncTyId::new(1)));

        let mut two = fnptr_caller(probe_callee(42, true, false));
        two.callees.push(probe_callee(42, false, false));
        assert!(!fnptr_target_sig_ok(&two, &records, FuncId::new(42), FuncTyId::new(1)));
    }

    /// A local target with a record but NO signature at all is unverifiable, so it is refused —
    /// the check never falls back to "assume it matches".
    #[test]
    fn test_fnptr_target_sig_refuses_signature_less_local_target() {
        let caller = fnptr_caller(probe_callee(42, true, false));
        let mut target = target_with_sig(42, vec![Ty::F64, Ty::F64]);
        target.func_ty = None;
        let records = vec![target];
        assert!(!fnptr_target_sig_ok(&caller, &records, FuncId::new(42), FuncTyId::new(1)));
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

/// Trust: the PRIMARY-vs-CASCADE split is measurement, and measurement is what ranks every
/// coverage target. These pin the set EXACTLY (not merely "these are cascade"), so a tag rename at
/// a `lib.rs` push site cannot silently reclassify an echo as leaf demand, or vice versa.
///
/// They govern EVERY classification made anywhere, because there is exactly one classifier: both
/// [`record`]'s primary/cascade histogram and the `mir_built` hook's collect-all debug event
/// (`rustc_mir_build::builder::mod.rs`) call [`is_cascade_tag`]. That was not true when this
/// module was written — the hook held a second, already-divergent inline copy — and pinning one of
/// two disagreeing copies pins nothing.
#[cfg(test)]
mod cascade_tag_tests {
    use super::{CASCADE_TAGS, is_cascade_tag};

    /// The whole table, as a literal. A change here must be a deliberate edit to this list.
    #[test]
    fn test_cascade_tags_exact_set_is_pinned() {
        assert_eq!(
            CASCADE_TAGS,
            ["VarRef(unbound)", "Borrow(unbound local)", "AssignOp(unbound local)"],
        );
    }

    #[test]
    fn test_is_cascade_tag_every_table_entry_classifies_cascade() {
        for tag in CASCADE_TAGS {
            assert!(is_cascade_tag(tag), "table entry `{tag}` must classify as cascade");
        }
    }

    /// The two conditions inside the shared-`Borrow` arm carry DISTINCT tags, and they land on
    /// OPPOSITE sides of the split. `Borrow(unbound local)` is an echo of a binding that never
    /// happened; `Borrow(slot missing)` means the promoted local's own `let` declined, which is
    /// leaf demand at that `let`. Collapsing them again would re-book real demand as an echo.
    #[test]
    fn test_borrow_slot_missing_is_primary_not_cascade() {
        assert!(is_cascade_tag("Borrow(unbound local)"));
        assert!(!is_cascade_tag("Borrow(slot missing)"));
    }

    /// Neighbouring fail-closed tags from the same `Borrow` arm are leaf demand, not echoes. Each
    /// names a real shape the lowering refuses on its own predicate.
    #[test]
    fn test_borrow_arm_neighbours_classify_primary() {
        for tag in [
            "Borrow(slot missing)",
            "Borrow(non-scalar pointee)",
            "Borrow(of a borrow ptr)",
            "Borrow(non-local place)",
            "Borrow(&mut unpromoted local)",
            "Borrow(&mut slot missing)",
            "Borrow(&mut non-local place)",
            "Borrow(other)",
        ] {
            assert!(!is_cascade_tag(tag), "`{tag}` is leaf demand, not a cascade echo");
        }
    }

    /// `Borrow(&mut unbound local)` sat in this table with NO emitter anywhere in the crate. It is
    /// absent now, and this pins the ABSENCE OF THE STRING rather than a classification for it:
    /// re-adding the tag to the table is fine, but only alongside the site that pushes it.
    #[test]
    fn test_borrow_mut_unbound_local_has_no_table_entry() {
        assert!(!CASCADE_TAGS.contains(&"Borrow(&mut unbound local)"));
    }

    /// A tag the table does not name is primary by default — the conservative direction for
    /// ranking (it overstates leaf demand rather than hiding it).
    #[test]
    fn test_is_cascade_tag_unknown_tag_classifies_primary() {
        for tag in ["", "Ty", "Other", "Call(unsupported arg)", "varref(unbound)"] {
            assert!(!is_cascade_tag(tag), "unknown tag `{tag}` must default to primary");
        }
    }
}

#[cfg(test)]
mod enum_decline_neutrality_tests {
    use super::*;

    fn tags(rows: &[(&str, &'static str)]) -> Vec<(String, &'static str)> {
        rows.iter().map(|(d, t)| ((*d).to_string(), *t)).collect()
    }

    fn declines(rows: &[(&str, &str)]) -> Vec<(String, String)> {
        rows.iter().map(|(p, r)| ((*p).to_string(), (*r).to_string())).collect()
    }

    /// THE NEUTRALITY PROPERTY, and the reason `aggregate_body_tag_rows` exists as a separate
    /// function at all. A `register_enum` decline is NOT a body failure — the declining enum
    /// collapses to the wave-EL opaque lane and the body may lower perfectly cleanly. A body
    /// whose only "problem" is a full decline ledger must therefore still produce ZERO failure
    /// tags, i.e. still count as lowered.
    ///
    /// This is the test that fails if the absence ever gets filled in: at wave-EF nothing merged
    /// declines into `unsupported` only because nobody had written that merge, which is a wall
    /// made of an absence. Fold the ledger into either tag vector and this assertion breaks.
    #[test]
    fn a_full_decline_ledger_produces_no_failure_tag() {
        let rows = aggregate_body_tag_rows(
            &[],
            declines(&[
                ("clean_kernel::env::EnvError", "field:Unit+Name in variant `UnknownConst`"),
                ("clean_kernel::flat::FlatError", "no-canonical-tag"),
                ("clean_kernel::cert::DictTrainError", "adt-depth"),
            ]),
        );
        assert!(rows.unsupported.is_empty(), "a decline must never mint a failure tag");
        assert!(rows.unsupported_details.is_empty(), "a decline must never mint a tag detail");
        assert_eq!(rows.enum_declines.len(), 3);
    }

    /// Stronger form of the same claim: the two tag vectors are a function of the tag input
    /// ALONE. Same tags, wildly different ledgers, identical verdict-adjacent output — which is
    /// what makes `TRUST_ENUM_DECLINE_CENSUS=1` safe to run against a lowering that can flip
    /// codegen.
    #[test]
    fn the_decline_ledger_cannot_perturb_tag_rows() {
        let t = tags(&[("d1", "Call(unsupported arg)"), ("d2", "VarRef(unbound)")]);
        let without = aggregate_body_tag_rows(&t, Vec::new());
        let with = aggregate_body_tag_rows(
            &t,
            declines(&[("k::A", "recursive-adt"), ("k::B", "discriminants/repr")]),
        );
        assert_eq!(without.unsupported, with.unsupported);
        assert_eq!(without.unsupported_details, with.unsupported_details);
        assert!(without.enum_declines.is_empty());
        assert_eq!(with.enum_declines.len(), 2);
    }

    /// The artifact must be byte-deterministic under parallel `mir_built`, so the rows are
    /// deduped and SORTED here regardless of the order `register_enum` refused in. (Push-time
    /// dedup in `push_decline_row` is what bounds memory; this is what bounds the bytes.)
    #[test]
    fn decline_rows_are_deduped_and_sorted_independently_of_arrival_order() {
        let forward =
            declines(&[("k::B", "adt-depth"), ("k::A", "recursive-adt"), ("k::B", "adt-depth")]);
        let reverse =
            declines(&[("k::B", "adt-depth"), ("k::B", "adt-depth"), ("k::A", "recursive-adt")]);
        let expected = declines(&[("k::A", "recursive-adt"), ("k::B", "adt-depth")]);
        assert_eq!(aggregate_body_tag_rows(&[], forward).enum_declines, expected);
        assert_eq!(aggregate_body_tag_rows(&[], reverse).enum_declines, expected);
    }

    /// Pins the pre-existing tag/detail behavior across the wave-EF R1 code motion: counts
    /// aggregate per tag, details cap at 3 DISTINCT examples in first-encounter order, tags sort.
    #[test]
    fn tag_aggregation_and_detail_capping_survive_the_extraction() {
        let rows = aggregate_body_tag_rows(
            &tags(&[
                ("z1", "Zeta"),
                ("a1", "Alpha"),
                ("a2", "Alpha"),
                ("a1", "Alpha"),
                ("a3", "Alpha"),
                ("a4", "Alpha"),
            ]),
            Vec::new(),
        );
        assert_eq!(
            rows.unsupported,
            vec![("Alpha".to_string(), 5u64), ("Zeta".to_string(), 1u64)]
        );
        assert_eq!(rows.unsupported_details[0].0, "Alpha");
        assert_eq!(rows.unsupported_details[0].1, vec!["a1", "a2", "a3"]);
        assert_eq!(rows.unsupported_details[1].0, "Zeta");
    }

    /// Detail truncation is CHAR-based, not byte-based: a multi-byte detail must not panic on a
    /// split code point, and must keep exactly 120 chars.
    #[test]
    fn a_multibyte_detail_truncates_on_a_char_boundary() {
        let long: String = "é".repeat(300);
        let rows = aggregate_body_tag_rows(&tags(&[(long.as_str(), "Ty")]), Vec::new());
        assert_eq!(rows.unsupported_details[0].1[0].chars().count(), 120);
    }
}

#[cfg(test)]
mod str_const_finalize_tests {
    use super::*;
    use rustc_span::def_id::DefIndex;

    fn dummy_def_id() -> DefId {
        DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(0) }
    }

    /// A `PendingConst` in exactly the shape `lower_str_named_const` mints.
    fn str_pending(global: Option<GlobalId>) -> PendingConst {
        PendingConst {
            value: ValueId::new(7),
            def_id: dummy_def_id(),
            span: rustc_span::DUMMY_SP,
            is_bool: false,
            is_float: false,
            signed: false,
            bits: 64,
            composite: false,
            str_global: global,
        }
    }

    /// The `[u8; 0]` placeholder exactly as the producer emits it.
    fn placeholder_global() -> Global {
        Global {
            name: "__trust_strconst_0".to_string(),
            ty: Ty::Array(TyId::new(0), 0),
            mutable: false,
            initializer: Some(Constant::Array(Vec::new())),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        }
    }

    fn bytes_global(bytes: &[u8]) -> Global {
        let mut g = placeholder_global();
        g.ty = Ty::Array(TyId::new(0), bytes.len() as u64);
        g.initializer =
            Some(Constant::Array(bytes.iter().map(|b| Constant::Int(i128::from(*b))).collect()));
        g
    }

    /// THE HAZARD THIS WHOLE LEDGER EXISTS FOR, pinned as a property of the SPLICE gate rather
    /// than asserted in prose: `global_const_ok` reads the untouched `[u8; 0]` placeholder as
    /// internally CONSISTENT (`0 == 0`), so an unpatched global would splice silently as the
    /// EMPTY STRING. If this test ever starts failing because `global_const_ok` learned to refuse
    /// zero-length arrays, the positive ledger becomes redundant — but not before.
    #[test]
    fn test_global_const_ok_accepts_the_unpatched_placeholder() {
        let mut r = minimal_record();
        r.types = vec![Ty::U8];
        let g = placeholder_global();
        assert!(
            global_const_ok(&r, &g.ty, g.initializer.as_ref().expect("placeholder has an init")),
            "the splice gate does NOT refuse a zero-length bytes global — which is exactly why \
             `check_str_global_ledger` must"
        );
    }

    /// THE KEY GATE. The untouched placeholder must NOT read as patched. The `*n > 0` clause in
    /// `str_global_patched` is the only thing standing between an unpatched global and a spliced
    /// `""`, so it is pinned on its own.
    #[test]
    fn test_str_global_patched_refuses_the_untouched_placeholder() {
        assert!(
            !str_global_patched(&placeholder_global()),
            "the `[u8; 0]` placeholder is NOT a patched global"
        );
    }

    #[test]
    fn test_str_global_patched_accepts_a_real_bytes_global_and_refuses_a_desync() {
        assert!(str_global_patched(&bytes_global(b"Clean.BVC.bvAppend")));
        // Declared length vs initializer element count disagree — a desync from any future
        // minting path must not read as patched.
        let mut desynced = bytes_global(b"ab");
        desynced.ty = Ty::Array(TyId::new(0), 5);
        assert!(!str_global_patched(&desynced));
        // A non-array initializer under an array type.
        let mut wrong = bytes_global(b"ab");
        wrong.initializer = Some(Constant::Int(2));
        assert!(!str_global_patched(&wrong));
        // No initializer at all (the symbolic/extern shape) is not a patched bytes global.
        let mut bare = bytes_global(b"ab");
        bare.initializer = None;
        assert!(!str_global_patched(&bare));
    }

    #[test]
    fn test_patch_str_global_rewrites_the_placeholder_and_keeps_the_element_tyid() {
        let mut g = placeholder_global();
        g.ty = Ty::Array(TyId::new(3), 0);
        assert!(patch_str_global(&mut g, b"Bool.or"));
        assert_eq!(
            g.ty,
            Ty::Array(TyId::new(3), 7),
            "the ELEMENT TyId must survive the patch — it is already interned in the body's \
             types table and the splice remaps it"
        );
        assert_eq!(
            g.initializer,
            Some(Constant::Array(
                b"Bool.or".iter().map(|b| Constant::Int(i128::from(*b))).collect()
            )),
        );
        assert!(str_global_patched(&g));
    }

    /// `""` fails closed, for the same reason `emit_bytes_global` refuses it: a zero-length array
    /// global is not proven faithful end-to-end. The caller reports `PendingStr(empty)`.
    #[test]
    fn test_patch_str_global_refuses_empty_bytes() {
        let mut g = placeholder_global();
        assert!(!patch_str_global(&mut g, b""));
        assert_eq!(g.ty, Ty::Array(TyId::new(0), 0), "a refused patch must not mutate the slot");
        assert!(!str_global_patched(&g));
    }

    /// One deduped global, several `PendingConst` records (two reads of one const in one body):
    /// the second patch is a no-op that still reports success. A patch with DIFFERENT bytes is
    /// the CONFLICT and is refused — a wrong-but-plausible string is never written.
    #[test]
    fn test_patch_str_global_is_idempotent_but_refuses_a_byte_conflict() {
        let mut g = placeholder_global();
        assert!(patch_str_global(&mut g, b"same"));
        assert!(patch_str_global(&mut g, b"same"), "repeated read of one const must be benign");
        assert!(!patch_str_global(&mut g, b"diff"), "a byte conflict must fail closed");
        assert!(!patch_str_global(&mut g, b"same-but-longer"));
        assert_eq!(
            g.initializer,
            Some(Constant::Array(b"same".iter().map(|b| Constant::Int(i128::from(*b))).collect())),
            "a refused patch must leave the earlier bytes untouched"
        );
        // A MUTABLE slot is never a str-const placeholder.
        let mut m = placeholder_global();
        m.mutable = true;
        assert!(!patch_str_global(&mut m, b"x"));
    }

    /// The positive ledger fires on a claim whose global was never patched, and stays silent on a
    /// patched one. A record that claims NO str global is not the ledger's business at all.
    #[test]
    fn test_check_str_global_ledger_fires_only_on_an_unfulfilled_claim() {
        let gid = GlobalId::new(0);

        let mut rows = Vec::new();
        check_str_global_ledger(&[placeholder_global()], &[str_pending(Some(gid))], &mut rows);
        assert_eq!(rows, vec![("PendingStr(global not patched)".to_string(), 1)]);

        let mut rows = Vec::new();
        check_str_global_ledger(&[bytes_global(b"ok")], &[str_pending(Some(gid))], &mut rows);
        assert!(rows.is_empty(), "a fulfilled claim must not tag the body");

        // A claim pointing past the end of the globals table (a side-table/IR desync).
        let mut rows = Vec::new();
        check_str_global_ledger(&[], &[str_pending(Some(GlobalId::new(9)))], &mut rows);
        assert_eq!(rows, vec![("PendingStr(global not patched)".to_string(), 1)]);

        // A non-str pending const claims nothing, so the ledger has nothing to check.
        let mut rows = Vec::new();
        check_str_global_ledger(&[placeholder_global()], &[str_pending(None)], &mut rows);
        assert!(rows.is_empty());

        // Two records sharing ONE unpatched deduped global report once EACH — the ledger counts
        // claims, not globals, so a body cannot hide a second unfulfilled claim behind the first.
        let mut rows = Vec::new();
        check_str_global_ledger(
            &[placeholder_global()],
            &[str_pending(Some(gid)), str_pending(Some(gid))],
            &mut rows,
        );
        assert_eq!(rows, vec![("PendingStr(global not patched)".to_string(), 2)]);
    }

    /// The METADATA node the str lane emits is `Inst::Const { ty: Ty::U64, value: PhantomData }` —
    /// already inside the sentinel set, so the leftover-sentinel tripwire covers the str lane with
    /// no widening. Pinned because the str lane now DEPENDS on that membership.
    #[test]
    fn test_is_const_sentinel_covers_the_u64_metadata_node() {
        assert!(is_const_sentinel(&Inst::Const {
            ty: Ty::U64,
            value: Constant::PhantomData
        }));
        // A REAL length is not a sentinel — this is the shape the finalizer patches in, and it
        // must not read as a leak afterwards.
        assert!(!is_const_sentinel(&Inst::Const { ty: Ty::U64, value: Constant::Int(7) }));
    }

    /// Minimal `BodyRecord` for the pure splice-gate probes above.
    fn minimal_record() -> BodyRecord {
        BodyRecord {
            def_index: 0,
            kind: BodyKind::Fn,
            symbolic: false,
            union_lane: false,
            enum_param_lane: false,
            def_path: "probe".to_string(),
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
            function: None,
            func_ty: None,
            files: Vec::new(),
            closure_types: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            types: Vec::new(),
            globals: Vec::new(),
            unsupported: Vec::new(),
            unsupported_details: Vec::new(),
            enum_declines: Vec::new(),
            collect_primary: Vec::new(),
            collect_cascade: Vec::new(),
            instr_count: 0,
            callees: Vec::new(),
            func_types: Vec::new(),
            pending_consts: Vec::new(),
            deferred: false,
            interpreter: InterpreterEvidence {
                verdict: ArtifactVerdict::NotRun,
                samples: 0,
                detail: "not run".to_string(),
            },
            derived_mir: DerivedMirEvidence {
                verdict: ArtifactVerdict::NotRun,
                detail: "not run".to_string(),
                markers_exact: false,
                markers_detail: String::new(),
            },
            differential_errors: Vec::new(),
            mir_snapshot: None,
            lineage: None,
        }
    }
}
